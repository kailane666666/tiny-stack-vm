// Tiny stack VM for make.fun's ISA v1, written from the spec in the kit's ISA.md.
// Runs every instance under the input dir, writes each answer under the output dir.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const INPUT = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUTPUT = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// Opcode metadata [immediate bytes, pops, pushes] by opcode byte; missing = unknown (trap 5).
const META = {
  0x00: [0, 0, 0], 0x01: [1, 0, 1], 0x02: [4, 0, 1], 0x03: [0, 1, 0],
  0x04: [0, 1, 2], 0x05: [0, 2, 2], 0x06: [0, 2, 3], 0x07: [0, 3, 3],
  0x10: [0, 2, 1], 0x11: [0, 2, 1], 0x12: [0, 2, 1], 0x13: [0, 2, 1],
  0x14: [0, 2, 1], 0x15: [0, 2, 1], 0x16: [0, 2, 1], 0x17: [0, 1, 1],
  0x18: [0, 2, 1], 0x19: [0, 2, 1], 0x1a: [0, 2, 1], 0x1b: [0, 1, 1],
  0x1c: [0, 2, 1], 0x1d: [0, 2, 1], 0x1e: [0, 2, 1], 0x20: [0, 2, 1],
  0x21: [0, 2, 1], 0x22: [0, 2, 1], 0x30: [2, 0, 0], 0x31: [2, 1, 0],
  0x32: [2, 1, 0], 0x33: [2, 0, 0], 0x34: [0, 0, 0], 0x40: [0, 1, 1],
  0x41: [0, 2, 0], 0x50: [0, 1, 0], 0x51: [0, 1, 0], 0x52: [0, 0, 1],
  0x53: [0, 1, 0],
};

// Runs one bytecode program on its input bytes; returns what it wrote and its exit code.
function run(prog, inp) {
  const len = prog.length;
  const data = new Int32Array(256); // data stack
  let dp = 0;
  const ret = new Int32Array(64); // call stack
  let rp = 0;
  const mem = new Int32Array(256);
  const out = new Uint8Array(65536);
  let op = 0; // output length
  let ip = 0; // input position
  let pc = 0;
  let steps = 0;
  let exit = 0;

  loop: for (;;) {
    if (steps === 1000000) { exit = 10; break; }
    if (pc < 0 || pc >= len) { exit = 9; break; }
    const meta = META[prog[pc]];
    if (meta === undefined) { exit = 5; break; }
    const imm = meta[0];
    if (pc + imm >= len) { exit = 9; break; }
    steps++;
    const next = pc + 1 + imm;
    if (dp < meta[1]) { exit = 2; break; }
    if (dp - meta[1] + meta[2] > 256) { exit = 3; break; }
    const code = prog[pc];
    pc = next;
    switch (code) {
      case 0x00: // HALT
        exit = 0;
        break loop;
      case 0x01: // PUSH8, sign-extended
        data[dp++] = (prog[next - 1] << 24) >> 24;
        break;
      case 0x02: // PUSH32, little-endian
        data[dp++] = prog[next - 4] | (prog[next - 3] << 8) | (prog[next - 2] << 16) | (prog[next - 1] << 24);
        break;
      case 0x03: // POP
        dp--;
        break;
      case 0x04: // DUP
        data[dp] = data[dp - 1];
        dp++;
        break;
      case 0x05: { // SWAP
        const t = data[dp - 1];
        data[dp - 1] = data[dp - 2];
        data[dp - 2] = t;
        break;
      }
      case 0x06: // OVER
        data[dp] = data[dp - 2];
        dp++;
        break;
      case 0x07: { // ROT
        const a = data[dp - 3];
        data[dp - 3] = data[dp - 2];
        data[dp - 2] = data[dp - 1];
        data[dp - 1] = a;
        break;
      }
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        // Binary ops: b on top, a below; the result replaces a.
        const b = data[dp - 1];
        const a = data[dp - 2];
        let r;
        if (code === 0x10) r = (a + b) | 0;
        else if (code === 0x11) r = (a - b) | 0;
        else if (code === 0x12) r = Math.imul(a, b);
        else if (code === 0x13) {
          if (b === 0) { exit = 4; break loop; }
          r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
        } else if (code === 0x14) {
          if (b === 0) { exit = 4; break loop; }
          r = b === -1 ? 0 : (a % b) | 0;
        } else if (code === 0x15) {
          if (b === 0) { exit = 4; break loop; }
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
        } else if (code === 0x16) {
          if (b === 0) { exit = 4; break loop; }
          r = ((a >>> 0) % (b >>> 0)) | 0;
        } else if (code === 0x18) r = a & b;
        else if (code === 0x19) r = a | b;
        else if (code === 0x1a) r = a ^ b;
        else if (code === 0x1c) r = a << (b & 31);
        else if (code === 0x1d) r = a >> (b & 31);
        else if (code === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (code === 0x20) r = a === b ? 1 : 0;
        else if (code === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0; // LTU
        dp--;
        data[dp - 1] = r;
        break;
      }
      case 0x17: // NEG
        data[dp - 1] = -data[dp - 1] | 0;
        break;
      case 0x1b: // NOT
        data[dp - 1] = ~data[dp - 1];
        break;
      case 0x30: case 0x31: case 0x32: {
        // Jumps: signed 16-bit offset from the next instruction.
        const rel = ((prog[next - 2] | (prog[next - 1] << 8)) << 16) >> 16;
        let take = true;
        if (code !== 0x30) {
          const v = data[--dp];
          take = code === 0x31 ? v === 0 : v !== 0;
        }
        if (take) pc = next + rel;
        break;
      }
      case 0x33: // CALL: unsigned 16-bit target
        if (rp === 64) { exit = 7; break loop; }
        ret[rp++] = next;
        pc = prog[next - 2] | (prog[next - 1] << 8);
        break;
      case 0x34: // RET
        if (rp === 0) { exit = 8; break loop; }
        pc = ret[--rp];
        break;
      case 0x40: { // LOAD
        const addr = data[dp - 1];
        if (addr < 0 || addr > 255) { exit = 6; break loop; }
        data[dp - 1] = mem[addr];
        break;
      }
      case 0x41: { // STORE: value below, address on top
        const addr = data[dp - 1];
        if (addr < 0 || addr > 255) { exit = 6; break loop; }
        mem[addr] = data[dp - 2];
        dp -= 2;
        break;
      }
      case 0x50: { // PRINT: decimal ASCII, no newline
        const s = String(data[dp - 1]);
        if (op + s.length > 65536) { exit = 11; break loop; }
        dp--;
        for (let i = 0; i < s.length; i++) out[op++] = s.charCodeAt(i);
        break;
      }
      case 0x51: // PUTC: one byte, low 8 bits
        if (op + 1 > 65536) { exit = 11; break loop; }
        out[op++] = data[--dp] & 255;
        break;
      case 0x52: // IN: next input byte, or -1 past the end
        data[dp++] = ip < inp.length ? inp[ip++] : -1;
        break;
      case 0x53: // EXIT: low byte of the top value
        exit = data[--dp] & 255;
        break loop;
    }
  }
  return { out: out.slice(0, op), exit };
}

for (const id of readdirSync(INPUT).sort()) {
  const prog = readFileSync(join(INPUT, id, 'program.bin'));
  const inp = readFileSync(join(INPUT, id, 'input.bin'));
  const { out, exit } = run(prog, inp);
  mkdirSync(join(OUTPUT, id), { recursive: true });
  writeFileSync(join(OUTPUT, id, 'stdout.bin'), out);
  writeFileSync(join(OUTPUT, id, 'exit.txt'), exit + '\n');
}
