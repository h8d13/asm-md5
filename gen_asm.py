#!/usr/bin/env python3
# Emit a complete md5 program for Linux x86-64 as asm, no libc.
#
# Regular files are mmap'd and hashed out of the page cache, anything
# else goes through a read() loop with a 256 KiB buffer.

K = [
	0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee,
	0xf57c0faf, 0x4787c62a, 0xa8304613, 0xfd469501,
	0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be,
	0x6b901122, 0xfd987193, 0xa679438e, 0x49b40821,
	0xf61e2562, 0xc040b340, 0x265e5a51, 0xe9b6c7aa,
	0xd62f105d, 0x02441453, 0xd8a1e681, 0xe7d3fbc8,
	0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed,
	0xa9e3e905, 0xfcefa3f8, 0x676f02d9, 0x8d2a4c8a,
	0xfffa3942, 0x8771f681, 0x6d9d6122, 0xfde5380c,
	0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70,
	0x289b7ec6, 0xeaa127fa, 0xd4ef3085, 0x04881d05,
	0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665,
	0xf4292244, 0x432aff97, 0xab9423a7, 0xfc93a039,
	0x655b59c3, 0x8f0ccc92, 0xffeff47d, 0x85845dd1,
	0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1,
	0xf7537e82, 0xbd3af235, 0x2ad7d2bb, 0xeb86d391,
]

S = [[7, 12, 17, 22], [5, 9, 14, 20], [4, 11, 16, 23], [6, 10, 15, 21]]

REGS = ["%eax", "%ebx", "%ecx", "%edx"]

SAVED = ["%r8d", "%r9d", "%r14d", "%r15d"]

T1, T2, M = "%r11d", "%r12d", "%r10d"

BUFSZ = 256 * 1024
SYS = {"read": 0, "write": 1, "open": 2, "fstat": 5, "lseek": 8, "mmap": 9,
	"exit": 60}

def g(i):
	if i < 16: return i
	if i < 32: return (5 * i + 1) % 16
	if i < 48: return (3 * i + 5) % 16
	return (7 * i) % 16

# Block function register roles follow OpenSSL's md5-x86_64: state in
# eax..edx rotating through a/b/c/d, saved copies in r8/r9/r14/r15, r10
# message word, r11/r12 round temps, rbp state pointer, rsi block, rdi
# end.

# Per step the chain from the newest value (b) is: round function
# op(s), add, rol, add. Rounds 2 and 3 have one op, rounds 1 and 4 two,
# so the floor is 16*(5+4+4+5) = 288 cycles per block. Everything off
# the chain (a + K + M, the next step's temps, the next M load) is
# placed so it overlaps. Lands at 290 cycles/block, libcrypto 290.

# %eax -> %rax, %r10d -> %r10: lea addressing needs 64-bit names
def r64(r):
	return "%r" + r[2:] if r[1] == "e" else r[:-1]

def signed(k):
	return k - (1 << 32) if k >= (1 << 31) else k

def regs(i):
	return [REGS[(k - i) % 4] for k in range(4)]

# temps for step i. reads only c and d of step i (old values), so it is
# emitted inside step i-1 once that step consumed the temps
def prep(i):
	a, b, c, d = regs(i)
	r = i // 16
	if r == 0:
		# F = ((c ^ d) & b) ^ d
		return ["mov %s, %s" % (d, T1), "xor %s, %s" % (c, T1)]
	if r == 1:
		# G = (b & d) + (c & ~d), terms disjoint so + == |, and the
		# second term joins a + K + M off the chain
		return ["mov %s, %s" % (d, T2), "andn %s, %s, %s" % (c, d, T1)]
	if r == 2:
		# H = b ^ c ^ d. the previous round-3 step left r11 = its
		# b^c^d; its d is our a register (not yet written): one xor
		# gives our c^d. depends on the chain value, 2 cycles of slack
		if i > 32:
			return ["xor %s, %s" % (a, T1)]
		return ["mov %s, %s" % (c, T1), "xor %s, %s" % (d, T1)]
	# I = c ^ (b | ~d) = ~(c ^ (~b & d)), every op needs b: nothing to
	# prep. the ~ becomes a sub, see step()
	return []

def step(i):
	a, b, c, d = regs(i)
	r = i // 16
	s = S[r][i % 4]
	# a + K + M first, off the chain. next M load reuses r10 right after
	# round 4: a + ~x == a - 1 - x, the -1 folds into K
	k = K[i] - 1 if r == 3 else K[i]
	out = ["lea %d(%s,%s), %s" % (signed(k), r64(a), r64(M), a)]
	load = ["mov %d(%%rsi), %s" % (4 * g(i + 1), M)] if i < 63 else []
	if r == 0:
		out += ["and %s, %s" % (b, T1)] + load + ["xor %s, %s" % (d, T1),
			"add %s, %s" % (T1, a)]
	elif r == 1:
		out += ["and %s, %s" % (b, T2)] + load + ["add %s, %s" % (T1, a),
			"add %s, %s" % (T2, a)]
	elif r == 2:
		out += ["xor %s, %s" % (b, T1)] + load + ["add %s, %s" % (T1, a)]
	else:
		out += ["andn %s, %s, %s" % (d, b, T1)] + load + [
			"xor %s, %s" % (c, T1), "sub %s, %s" % (T1, a)]
	out.append("rol $%d, %s" % (s, a))
	if i < 63:
		out += prep(i + 1)
		out.append("add %s, %s" % (b, a))
	else:
		# block boundary: saved B goes into b off the chain first, so
		# the newest value sees one add, not two, before step 0
		out += ["add %s, %s" % (b, SAVED[1]), "add %s, %s" % (SAVED[1], a)]
	return out

# process_blocks(rdi = state, rsi = block, rdx = nblocks)
def process_blocks():
	out = [".p2align 4", ".globl process_blocks",
		".type process_blocks, @function", "process_blocks:"]
	out += ["push %s" % r for r in ["%rbp", "%rbx", "%r12", "%r14", "%r15"]]
	out += ["mov %rdi, %rbp", "shl $6, %rdx", "lea (%rsi,%rdx), %rdi"]
	out += ["mov %d(%%rbp), %s" % (4 * n, r) for n, r in enumerate(REGS)]
	out += ["cmp %rdi, %rsi", "je .Lend", ".p2align 4", ".Lloop:"]
	out += ["mov %s, %s" % (r, sv) for r, sv in zip(REGS, SAVED)]
	out += ["mov (%%rsi), %s" % M] + prep(0)
	for i in range(64):
		if i % 16 == 0:
			out.append("# round %d" % (i // 16 + 1))
		out += step(i)
	out += ["add %s, %s" % (sv, r) for r, sv in zip(REGS, SAVED)
		if sv != SAVED[1]]
	out += ["add $64, %rsi", "cmp %rdi, %rsi", "jb .Lloop", ".Lend:"]
	out += ["mov %s, %d(%%rbp)" % (r, 4 * n) for n, r in enumerate(REGS)]
	out += ["pop %s" % r for r in ["%r15", "%r14", "%r12", "%rbx", "%rbp"]]
	out += ["ret", ".size process_blocks, .-process_blocks"]
	return out

# r12 fd, r13 carry (partial block bytes at buf front), r14 total bytes,
# r15 mmap base. process_blocks preserves r12..r15 and rbx
def syscall(name):
	n = SYS[name]
	return ["xor %eax, %eax" if n == 0 else "mov $%d, %%eax" % n, "syscall"]

# argv[1] if given, else stdin
def open_input():
	out = [".globl _start", "_start:",
		"mov (%rsp), %rax", "xor %r12d, %r12d", "cmp $2, %rax",
		"jb .Lhave_fd", "mov 16(%rsp), %rdi", "xor %esi, %esi"]
	out += syscall("open")
	out += ["test %rax, %rax", "js .Lopen_err", "mov %rax, %r12",
		".Lhave_fd:"]
	return out

# regular file with a size, at offset 0: mmap it and hash the whole
# thing. a redirected stdin may already be partly consumed, the read
# loop hashes from the current offset. any failure falls back to the
# read loop. st_mode at 24, st_size at 48
def mmap_path():
	out = ["mov %r12, %rdi", "lea statbuf(%rip), %rsi"]
	out += syscall("fstat")
	out += ["test %rax, %rax", "jnz .Lread_init",
		"mov statbuf+24(%rip), %eax", "and $0170000, %eax",
		"cmp $0100000, %eax", "jne .Lread_init",
		"mov statbuf+48(%rip), %r14", "test %r14, %r14", "jz .Lread_init",
		# lseek(fd, 0, SEEK_CUR)
		"mov %r12, %rdi", "xor %esi, %esi", "mov $1, %edx"]
	out += syscall("lseek")
	out += ["test %rax, %rax", "jnz .Lread_init",
		# mmap(0, size, PROT_READ, MAP_PRIVATE | MAP_POPULATE, fd, 0)
		"xor %edi, %edi", "mov %r14, %rsi", "mov $1, %edx",
		"mov $0x8002, %r10d", "mov %r12, %r8", "xor %r9d, %r9d"]
	out += syscall("mmap")
	out += ["cmp $-4096, %rax", "ja .Lread_init", "mov %rax, %r15",
		"lea state(%rip), %rdi", "mov %r15, %rsi", "mov %r14, %rdx",
		"shr $6, %rdx", "call process_blocks",
		# rest = base + full, carry = size % 64
		"mov %r14, %rcx", "and $63, %rcx", "mov %r14, %rsi",
		"and $-64, %rsi", "add %r15, %rsi", "jmp .Lfinalize"]
	return out

# read after the carried bytes, hash every full block in place, move
# the trailing partial block to the front. EINTR retries
def read_loop():
	out = [".Lread_init:", "xor %r13d, %r13d", "xor %r14d, %r14d",
		".Lread:", "mov %r12, %rdi", "lea buf(%rip), %rsi",
		"add %r13, %rsi", "mov $%d, %%edx" % BUFSZ, "sub %r13, %rdx"]
	out += syscall("read")
	out += ["test %rax, %rax", "jz .Lread_done", "js .Lread_err",
		"add %rax, %r14",
		"lea (%r13,%rax), %rbx", "mov %rbx, %rdx", "shr $6, %rdx",
		"lea state(%rip), %rdi", "lea buf(%rip), %rsi",
		"call process_blocks",
		"mov %rbx, %r13", "and $63, %r13", "mov %rbx, %rsi",
		"and $-64, %rsi", "lea buf(%rip), %rdi", "add %rdi, %rsi",
		"mov %r13, %rcx", "rep movsb", "jmp .Lread",
		".Lread_err:", "cmp $-4, %rax", "je .Lread",
		"lea eread(%rip), %rsi", "jmp .Lfail",
		".Lread_done:", "lea buf(%rip), %rsi", "mov %r13, %rcx"]
	return out

# rsi = trailing partial block, rcx = its length, r14 = total bytes.
# copy into tail, 0x80, zeros up to 56 mod 64, bit length LE, hash
# one or two blocks
def finalize():
	out = [".Lfinalize:", "lea tail(%rip), %rdi", "mov %rcx, %rbx",
		"rep movsb", "movb $0x80, (%rdi)", "inc %rdi",
		"mov $64, %edx", "cmp $56, %rbx", "jb 1f", "mov $128, %edx",
		# zero count = tail + total - 8 - rdi
		"1:", "lea tail(%rip), %rcx", "add %rdx, %rcx", "sub $8, %rcx",
		"sub %rdi, %rcx", "xor %eax, %eax", "rep stosb",
		"mov %r14, %rax", "shl $3, %rax", "mov %rax, (%rdi)",
		"lea state(%rip), %rdi", "lea tail(%rip), %rsi", "shr $6, %rdx",
		"call process_blocks"]
	return out

# 16 state bytes as 32 hex chars plus newline on stdout, exit 0
def print_hash():
	out = ["lea state(%rip), %rsi", "lea out(%rip), %rdi",
		"lea hex(%rip), %r8", "xor %ecx, %ecx",
		".Lhex:", "movzbl (%rsi,%rcx), %eax", "mov %eax, %edx",
		"shr $4, %eax", "and $15, %edx",
		"movzbl (%r8,%rax), %eax", "mov %al, (%rdi,%rcx,2)",
		"movzbl (%r8,%rdx), %eax", "mov %al, 1(%rdi,%rcx,2)",
		"inc %ecx", "cmp $16, %ecx", "jb .Lhex",
		"movb $10, 32(%rdi)",
		"mov $1, %edi", "lea out(%rip), %rsi", "mov $33, %edx"]
	out += syscall("write")
	out += ["xor %edi, %edi"] + syscall("exit")
	return out

# rsi = message, 12 bytes, to stderr, exit 1
def fail():
	out = [".Lopen_err:", "lea eopen(%rip), %rsi",
		".Lfail:", "mov $2, %edi", "mov $12, %edx"]
	out += syscall("write")
	out += ["mov $1, %edi"] + syscall("exit")
	return out

def data():
	return [".data",
		"state:\t.long 0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476",
		"hex:\t.ascii \"0123456789abcdef\"",
		"eopen:\t.ascii \"open failed\\n\"",
		"eread:\t.ascii \"read failed\\n\"",
		".bss", ".p2align 6",
		"buf:\t.skip %d" % (BUFSZ + 64),
		"tail:\t.skip 128",
		"out:\t.skip 33",
		"statbuf: .skip 144",
		".section .note.GNU-stack,\"\",@progbits"]

# labels and data definitions flush left, everything else indented
def emit(lines):
	for l in lines:
		flush = l.endswith(":") or (l[0] not in ".#" and ":\t" in l) \
			or l.startswith("statbuf:")
		print(l if flush else "\t" + l)

def main():
	emit([".text"])
	emit(process_blocks())
	emit(open_input() + mmap_path() + read_loop() + finalize()
		+ print_hash() + fail())
	emit(data())

main()
