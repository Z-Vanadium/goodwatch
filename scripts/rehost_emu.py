#!/usr/bin/env python3
"""
MSP430 Rehosting Emulator for goodwatch.elf (CC430F6137)

A focused MSP430 emulator that runs the goodwatch firmware in a simulated
environment, bypassing hardware peripheral dependencies. Captures the 
dmesg (diagnostic message) log from firmware execution.

Architecture: MSP430 (16-bit, little-endian), MSP430X small memory model.
"""

import struct
import sys
from elftools.elf.elffile import ELFFile

# ============================================================
# MSP430 CPU State
# ============================================================

class MSP430:
    def __init__(self):
        # Register file: R0-R15
        # R0=PC, R1=SP, R2=SR/CG1, R3=CG2
        self.r = [0] * 16
        self.r[1] = 0x2400  # SP initial (top of RAM at 0x2400)
        self.r[2] = 0       # SR
        self.r[3] = 0       # CG2
        
        # Flat 64KB memory
        self.mem = bytearray(65536)
        
        # Peripheral MMIO state (for registers the firmware reads)
        self.periph = bytearray(65536)
        
        # Execution tracking
        self.cycles = 0
        self.instruction_count = 0
        self.max_instructions = 2000000
        
        # Hooks for logging
        self.log = []
        
        # SR bit positions
        self.V_BIT = 8  # Overflow
        self.SCZ_BIT = 6  # SCG1
        self.SC1_BIT = 6
        self.SC0_BIT = 5
        self.OSC_BIT = 4  # OscOff (not to be confused with SCG)
        self.CPUOFF_BIT = 4
        self.GIE_BIT = 3  # General Interrupt Enable
        self.N_BIT = 2
        self.Z_BIT = 1
        self.C_BIT = 0
    
    # --- SR flag helpers ---
    def _sr_get(self, bit):
        return (self.r[2] >> bit) & 1
    
    def _sr_set(self, bit, val):
        if val:
            self.r[2] |= (1 << bit)
        else:
            self.r[2] &= ~(1 << bit)
    
    def get_c(self): return self._sr_get(self.C_BIT)
    def set_c(self, v): self._sr_set(self.C_BIT, v)
    def get_z(self): return self._sr_get(self.Z_BIT)
    def set_z(self, v): self._sr_set(self.Z_BIT, v)
    def get_n(self): return self._sr_get(self.N_BIT)
    def set_n(self, v): self._sr_set(self.N_BIT, v)
    def get_v(self): return self._sr_get(self.V_BIT)
    def set_v(self, v): self._sr_set(self.V_BIT, v)
    
    @property
    def pc(self):
        return self.r[0]
    @pc.setter
    def pc(self, v):
        self.r[0] = v & 0xFFFF
    
    @property
    def sp(self):
        return self.r[1]
    @sp.setter
    def sp(self, v):
        self.r[1] = v & 0xFFFF
    
    # --- Memory access ---
    def read_byte(self, addr):
        addr &= 0xFFFF
        if addr < 0x0200:
            # Simulate timer CCIFG flags always set
            if addr == 0x0346 or addr == 0x0347:  # TA0CCTL2
                return 0x01  # CCIFG=1
            if addr == 0x0356 or addr == 0x0357:  # TA0CCR2 (won't have CCIFG)
                return 0x01
            if addr == 0x0342 or addr == 0x0343:  # TA0CCTL0
                return 0x01
            if addr == 0x0344 or addr == 0x0345:  # TA0CCTL1
                return 0x01
            if addr == 0x0348 or addr == 0x0349:  # TA0CCTL3
                return 0x01
            if addr == 0x034A or addr == 0x034B:  # TA0CCTL4
                return 0x01
            # PMMIFG: always set delay flags
            if addr == 0x012C or addr == 0x012D:
                return 0xFF  # All PMM flags ready
            return self.periph[addr]
        return self.mem[addr]
    
    def read_word(self, addr):
        addr &= 0xFFFE
        lo = self.read_byte(addr)
        hi = self.read_byte(addr + 1)
        return (hi << 8) | lo
    
    def write_byte(self, addr, val):
        addr &= 0xFFFF
        val &= 0xFF
        self._handle_mmio_write(addr, val, True)
        if addr >= 0x0200:
            self.mem[addr] = val
    
    def write_word(self, addr, val):
        addr &= 0xFFFE
        val &= 0xFFFF
        self._handle_mmio_write(addr, val, False)
        if addr >= 0x0200:
            self.mem[addr] = val & 0xFF
            self.mem[addr+1] = (val >> 8) & 0xFF
    
    # --- MMIO handling ---
    def _handle_mmio_write(self, addr, val, bytemode):
        """Intercept writes to peripheral registers."""
        self.periph[addr & 0xFFFF] = val & 0xFF
        if not bytemode:
            self.periph[(addr+1) & 0xFFFF] = (val >> 8) & 0xFF
        
        # Handle special writes
        if addr == 0x015C:  # WDTCTL
            # WDT password + config, accept silently
            pass
        elif addr == 0x0100 or addr == 0x0101:  # SFRIE1
            pass  # Accept interrupt enable writes
    
    # --- Instruction fetch ---
    def fetch_word(self):
        w = self.read_word(self.pc)
        self.pc += 2
        return w
    
    # --- Operand decoding ---
    def decode_src(self, mode, reg):
        """Decode source operand. Returns (value, extra_cycles)."""
        if mode == 0 and reg == 3:  # CG2: constant 0
            return 0, 0
        elif mode == 0 and reg == 2:  # CG1: register mode = SR value (handled as register below)
            pass  # Fall through to register direct
        elif mode == 0:  # Register direct
            return self.r[reg] & 0xFFFF, 0
        elif mode == 1 and reg == 3:  # CG2: constant 1
            return 1, 0
        elif mode == 1 and reg == 2:  # CG1: absolute addressing via SR
            addr = self.fetch_word()
            return self.read_word(addr), 3
        elif mode == 1:  # Indexed mode (register + X(pc))
            x = self.fetch_word()
            if reg == 0:  # Symbolic mode (PC-relative)
                return self.read_word((self.r[reg] + x) & 0xFFFF), 3
            return self.read_word((self.r[reg] + x) & 0xFFFF), 3
        elif mode == 2 and reg == 3:  # CG2: constant 2
            return 2, 0
        elif mode == 2 and reg == 2:  # CG1: constant 4
            return 4, 0
        elif mode == 2 and reg == 1:  # Absolute addressing @address (SR-based)
            addr = self.fetch_word()
            return self.read_word(addr), 2
        elif mode == 2:  # @Rn indirect
            return self.read_word(self.r[reg]), 2
        elif mode == 3 and reg == 3:  # CG2: constant -1 (0xFFFF)
            return 0xFFFF, 0
        elif mode == 3 and reg == 0:  # Immediate mode (@PC+)
            v = self.fetch_word()
            return v, 1
        elif mode == 3:  # @Rn+ indirect auto-increment
            addr = self.r[reg]
            self.r[reg] = (addr + (1 if False else 2)) & 0xFFFF  # word increment
            return self.read_word(addr), 2
        return 0, 0
    
    def decode_dst_write_addr(self, mode, reg):
        """Get the write address for a destination operand. Returns (addr, is_register)."""
        if mode == 0:  # Register direct
            return reg, True
        elif mode == 1:  # Indexed / Symbolic
            x = self.fetch_word()
            if reg == 2:  # Absolute addressing via SR/CG1
                return x & 0xFFFF, False
            elif reg == 0:  # PC-relative
                return ((self.r[reg] + x) & 0xFFFF), False
            else:
                return ((self.r[reg] + x) & 0xFFFF), False
        elif mode == 2:  # @Rn indirect
            if reg == 2:  # CG1: constant 4
                return 4, False  # Actually this returns address 4
            elif reg == 3:  # CG2: constant 0
                return 0, False
            return self.r[reg] & 0xFFFF, False
        elif mode == 3:  # @Rn+ indirect auto-increment
            if reg == 0:  # immediate (for src only)
                return 0, False
            addr = self.r[reg] & 0xFFFF
            self.r[reg] = (addr + 2) & 0xFFFF
            return addr, False
        return 0, False
    
    def dst_write(self, mode, reg, value, bytemode=False):
        """Write to a destination operand."""
        value &= 0xFFFF
        if mode == 0:
            if bytemode:
                existing = self.r[reg] & 0xFF00
                self.r[reg] = existing | (value & 0xFF)
            else:
                self.r[reg] = value
        else:
            addr, _ = self.decode_dst_write_addr(mode, reg)
            if bytemode:
                self.write_byte(addr, value & 0xFF)
            else:
                self.write_word(addr, value)
    
    def dst_read(self, mode, reg, bytemode=False):
        """Read from a destination operand location."""
        if mode == 0:
            v = self.r[reg] & 0xFFFF
            return (v & 0xFF) if bytemode else v
        elif mode == 1:
            x = self.fetch_word()
            if reg == 2:  # Absolute addressing via SR/CG1
                addr = x & 0xFFFF
            elif reg == 0:  # PC-relative
                addr = (self.r[reg] + x) & 0xFFFF
            else:
                addr = (self.r[reg] + x) & 0xFFFF
            return self.read_byte(addr) if bytemode else self.read_word(addr)
        elif mode == 2:
            if reg == 2:
                return 4
            elif reg == 3:
                return 0
            addr = self.r[reg] & 0xFFFF
            return self.read_byte(addr) if bytemode else self.read_word(addr)
        elif mode == 3:
            if reg == 0:  # immediate
                v = self.fetch_word()
                return v
            addr = self.r[reg] & 0xFFFF
            self.r[reg] = (addr + (1 if bytemode else 2)) & 0xFFFF
            return self.read_byte(addr) if bytemode else self.read_word(addr)
        return 0
    
    # --- Instruction execution ---
    def step(self):
        """Execute one instruction. Returns True if should continue."""
        self.instruction_count += 1
        if self.instruction_count > self.max_instructions:
            return False
        
        op = self.fetch_word()
        
        # Double-operand instructions
        # Format: [15:12]=opcode [11:8]=src_reg [7]=ad [6]=bw [5:4]=as [3:0]=dst_reg
        sop = (op >> 12) & 0xF
        dreg = op & 0xF
        ad = (op >> 7) & 1
        bw = (op >> 6) & 1  # 0=word, 1=byte
        as_mode = (op >> 4) & 3
        sreg = (op >> 8) & 0xF
        
        if sop >= 4:  # Double-operand: MOV, ADD, ADDC, SUBC, SUB, CMP, DADD, BIT, BIC, BIS, XOR, AND
            self._exec_double(sop, sreg, as_mode, bw, dreg, ad)
            self.cycles += 2
            return True
        
        # Jump instructions (bits [15:13] = 001)
        if (op >> 13) == 1:
            jump_op = (op >> 10) & 0x7
            offset = op & 0x3FF
            if offset & 0x200:
                offset = (offset - 0x400)  # Sign extend 10-bit
            
            take = False
            if jump_op == 0: take = not self.get_z()      # JNE/JNZ
            elif jump_op == 1: take = self.get_z()         # JEQ/JZ
            elif jump_op == 2: take = not self.get_c()     # JNC/JLO
            elif jump_op == 3: take = self.get_c()         # JC/JHS
            elif jump_op == 4: take = self.get_n()         # JN
            elif jump_op == 5: take = (self.get_n() == self.get_v())  # JGE
            elif jump_op == 6: take = (self.get_n() != self.get_v())  # JL
            elif jump_op == 7: take = True                 # JMP
            
            if take:
                self.pc = (self.pc + offset * 2) & 0xFFFF
            self.cycles += 2
            return True
        
        # Single-operand instructions
        # Format: [15:7]=opcode [6]=bw [5:4]=as [3:0]=reg
        # Use masked comparison for reliable opcode matching
        single_op = op & 0xFF80  # mask out bw, as, reg
        
        if single_op == 0x1000:  # RRC
            self._exec_single_simple(0x1000, (op >> 6) & 1, (op >> 4) & 3, op & 0xF)
            self.cycles += 1
            return True
        elif single_op == 0x1080:  # SWPB
            self._exec_single_simple(0x1080, (op >> 6) & 1, (op >> 4) & 3, op & 0xF)
            self.cycles += 1
            return True
        elif single_op == 0x1100:  # RRA
            self._exec_single_simple(0x1100, (op >> 6) & 1, (op >> 4) & 3, op & 0xF)
            self.cycles += 1
            return True
        elif single_op == 0x1180:  # SXT
            self._exec_single_simple(0x1180, (op >> 6) & 1, (op >> 4) & 3, op & 0xF)
            self.cycles += 1
            return True
        elif single_op == 0x1200:  # PUSH / PUSH.B
            src_val, _ = self.decode_src((op >> 4) & 3, op & 0xF)
            if (op >> 6) & 1:
                src_val &= 0xFF
            self.sp = (self.sp - 2) & 0xFFFF
            self.write_word(self.sp, src_val)
            self.cycles += 3
            return True
        elif single_op == 0x1280:  # CALL / CALLA (MSP430X)
            target, _ = self.decode_src((op >> 4) & 3, op & 0xF)
            self.sp = (self.sp - 2) & 0xFFFF
            self.write_word(self.sp, self.pc)
            self.pc = target & 0xFFFF
            self.cycles += 4
            return True
        elif single_op == 0x1300:  # RETI
            self.r[2] = self.read_word(self.sp)
            self.sp = (self.sp + 2) & 0xFFFF
            self.pc = self.read_word(self.sp)
            self.sp = (self.sp + 2) & 0xFFFF
            self.cycles += 5
            return True
        
        # MSP430X extended instructions (0x1400-0x17FF)
        ext_op = (op >> 8) & 0xFF
        ext_nn = op & 0xFF
        
        if ext_op == 0x15:  # PUSHM.W
            n = (ext_nn >> 4) + 1
            rdst = ext_nn & 0xF
            for i in range(n-1, -1, -1):
                reg = (rdst + i) & 0xF
                if reg > 4:
                    val = self.r[reg] & 0xFFFF
                else:
                    val = self.r[reg] & 0xFFFF
                self.sp = (self.sp - 2) & 0xFFFF
                self.write_word(self.sp, val)
            self.cycles += n + 1
            return True
        
        if ext_op == 0x16:  # POPM.W
            n = (ext_nn >> 4) + 1
            rdst = ext_nn & 0xF
            for i in range(n):
                reg = (rdst + i) & 0xF
                self.r[reg] = self.read_word(self.sp)
                self.sp = (self.sp + 2) & 0xFFFF
            self.cycles += n + 1
            return True
        
        if ext_op == 0x14:  # RRAM/RLAM/RRAM/RLAM (Rotate Arithmetic Multiple)
            n = ((ext_nn >> 4) & 0xF)
            rnum = ext_nn & 0xF
            direction = (ext_nn >> 4) & 1  # 0=left, 1=right? Depends on exact encoding
            if n == 0:
                n = 1  # Single shift
            val = self.r[rnum] & 0xFFFF
            for _ in range(n):
                c = self.get_c()
                self.set_c(val & 1)
                val = (c << 15) | (val >> 1)
            self.set_z(val == 0)
            self.set_n((val >> 15) & 1)
            self.r[rnum] = val
            self.cycles += n
            return True
        
        if ext_op == 0x16:  # POPM.A (20-bit) - simplified as 16-bit
            n = (ext_nn >> 4) + 1
            rdst = ext_nn & 0xF
            for i in range(n):
                reg = (rdst + i) & 0xF
                self.r[reg] = self.read_word(self.sp)
                self.sp = (self.sp + 2) & 0xFFFF
            self.cycles += n + 1
            return True
        
        if ext_op == 0x17:  # POPM.W (16-bit)
            n = (ext_nn >> 4) + 1
            rdst = ext_nn & 0xF
            for i in range(n):
                reg = (rdst + i) & 0xF
                self.r[reg] = self.read_word(self.sp)
                self.sp = (self.sp + 2) & 0xFFFF
            self.cycles += n + 1
            return True
        
        # Jump instructions
        # Format: [15:13]=001 [12:10]=condition [9:0]=offset (sign extended)
        jump_op = (op >> 10) & 0x7
        offset = op & 0x3FF
        if offset & 0x200:  # Sign extend
            offset |= 0xFC00
        
        if (op >> 13) == 1:  # Jump instructions (bits [15:13] = 001)
            jump_op = (op >> 10) & 0x7
            offset = op & 0x3FF
            if offset & 0x200:
                offset = (offset - 0x400)  # Sign extend 10-bit
            
            take = False
            if jump_op == 0:  # JNE/JNZ
                take = not self.get_z()
            elif jump_op == 1:  # JEQ/JZ
                take = self.get_z()
            elif jump_op == 2:  # JNC/JLO
                take = not self.get_c()
            elif jump_op == 3:  # JC/JHS
                take = self.get_c()
            elif jump_op == 4:  # JN
                take = self.get_n()
            elif jump_op == 5:  # JGE
                take = (self.get_n() == self.get_v())
            elif jump_op == 6:  # JL
                take = (self.get_n() != self.get_v())
            elif jump_op == 7:  # JMP
                take = True
            
            if take:
                self.pc = (self.pc + offset * 2) & 0xFFFF
            self.cycles += 2
            return True
        
        self.log.append(f"[0x{(self.pc-2):04x}] UNKNOWN opcode: 0x{op:04x}")
        print(f"  UNKNOWN opcode: 0x{op:04x} at PC=0x{(self.pc-2):04x} (inst #{self.instruction_count})")
        return False
    
    def _exec_double(self, sop, sreg, as_mode, bw, dreg, ad):
        """Execute double-operand instruction."""
        bytemode = bw
        src_val, _ = self.decode_src(as_mode, sreg)
        
        if bytemode:
            src_val &= 0xFF
        else:
            src_val &= 0xFFFF
        
        # dd - For instructions that need to read dst before computing result
        # Note: MOV (sop=4) must NOT read dst first - it would consume
        # the indexed mode offset word before dst_write can use it
        if sop in (5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15):
            dst_val = self.dst_read(ad, dreg, bytemode)
        
        if sop == 4:  # MOV
            self.dst_write(ad, dreg, src_val, bytemode)
        elif sop == 5:  # ADD
            result = dst_val + src_val
            if not bytemode:
                result &= 0xFFFF
                self.set_c(result > 0xFFFF)
                self.set_z(result == 0)
                self.set_n((result >> 15) & 1)
                self.set_v((((~(dst_val ^ src_val)) & (dst_val ^ result)) >> 15) & 1)
            else:
                result &= 0xFF
                self.set_c(result > 0xFF)
                self.set_z((result & 0xFF) == 0)
                self.set_n((result >> 7) & 1)
            self.dst_write(ad, dreg, result, bytemode)
        elif sop == 6:  # ADDC
            c = self.get_c()
            result = dst_val + src_val + c
            if not bytemode:
                self.set_c(result > 0xFFFF)
                result &= 0xFFFF
                self.set_z(result == 0)
                self.set_n((result >> 15) & 1)
            else:
                self.set_c(result > 0xFF)
                result &= 0xFF
                self.set_z(result == 0)
                self.set_n((result >> 7) & 1)
            self.dst_write(ad, dreg, result, bytemode)
        elif sop == 7:  # SUBC
            c = self.get_c()
            result = dst_val - src_val - 1 + c
            if not bytemode:
                self.set_c(dst_val >= (src_val + 1 - c))
                result &= 0xFFFF
                self.set_z(result == 0)
                self.set_n((result >> 15) & 1)
            else:
                self.set_c((dst_val & 0xFF) >= ((src_val & 0xFF) + 1 - c))
                result &= 0xFF
                self.set_z(result == 0)
                self.set_n((result >> 7) & 1)
            self.dst_write(ad, dreg, result, bytemode)
        elif sop == 8:  # SUB
            result = dst_val - src_val
            if not bytemode:
                self.set_c(dst_val >= src_val)
                result &= 0xFFFF
                self.set_z(result == 0)
                self.set_n((result >> 15) & 1)
                self.set_v((((dst_val ^ src_val) & (dst_val ^ result)) >> 15) & 1)
            else:
                self.set_c((dst_val & 0xFF) >= (src_val & 0xFF))
                result &= 0xFF
                self.set_z(result == 0)
                self.set_n((result >> 7) & 1)
            self.dst_write(ad, dreg, result, bytemode)
        elif sop == 9:  # CMP (same as SUB but doesn't store result)
            result = dst_val - src_val
            if not bytemode:
                self.set_c(dst_val >= src_val)
                result &= 0xFFFF
                self.set_z(result == 0)
                self.set_n((result >> 15) & 1)
                self.set_v((((dst_val ^ src_val) & (dst_val ^ result)) >> 15) & 1)
            else:
                self.set_c((dst_val & 0xFF) >= (src_val & 0xFF))
                result &= 0xFF
                self.set_z(result == 0)
                self.set_n((result >> 7) & 1)
        elif sop == 10:  # DADD
            self.log.append(f"DADD: dst=0x{dst_val:04x} src=0x{src_val:04x}")
            # Complex BCD addition - simplified
            result = dst_val + src_val + self.get_c()
            self.set_c(result > 0xFFFF)
            result &= 0xFFFF
            self.set_z(result == 0)
            self.set_n((result >> 15) & 1)
            self.dst_write(ad, dreg, result, bytemode)
        elif sop == 11:  # BIT
            result = dst_val & src_val
            self.set_z(result == 0)
            self.set_n((result >> (7 if bytemode else 15)) & 1)
            self.set_c(result != 0)  # Not sure about this
            self.set_v(0)
        elif sop == 12:  # BIC
            result = dst_val & ~src_val
            self.dst_write(ad, dreg, result, bytemode)
        elif sop == 13:  # BIS
            result = dst_val | src_val
            # Detect BIS to SR (status register write)
            if ad == 0 and dreg == 2:
                # Writing to SR - this is likely LPM entry
                new_sr = result
                if (new_sr & 0xF0):  # LPM bits or GIE set
                    self.r[2] = new_sr & 0xFFFF
            else:
                self.dst_write(ad, dreg, result, bytemode)
        elif sop == 14:  # XOR
            result = dst_val ^ src_val
            self.set_c(result != 0)
            self.set_z(result == 0)
            self.set_n((result >> (7 if bytemode else 15)) & 1)
            self.set_v((result >> (7 if bytemode else 15)) & 1)
            self.dst_write(ad, dreg, result, bytemode)
        elif sop == 15:  # AND
            result = dst_val & src_val
            self.set_c(result != 0)
            self.set_z(result == 0)
            self.set_n((result >> (7 if bytemode else 15)) & 1)
            self.set_v(0)
            self.dst_write(ad, dreg, result, bytemode)
    
    def _exec_single_simple(self, opcode, bw, as_mode, reg):
        """Execute single-operand instruction."""
        bytemode = bw
        
        if opcode == 0x100:  # RRC
            v = self.dst_read(as_mode, reg, bytemode)
            shift = 7 if bytemode else 15
            mask = 0x7F if bytemode else 0x7FFF
            c = self.get_c()
            result = (c << shift) | ((v >> 1) & mask)
            self.set_c(v & 1)
            self.set_z(result == 0)
            self.set_n(result & (0x80 if bytemode else 0x8000))
            self.set_v(0)
            self.dst_write(as_mode, reg, result, bytemode)
        elif opcode == 0x108:  # SWPB
            if bytemode:
                self.log.append("ERROR: illegal SWPB.B")
                return
            v = self.dst_read(as_mode, reg, False)
            result = ((v & 0xFF) << 8) | ((v >> 8) & 0xFF)
            self.dst_write(as_mode, reg, result, False)
        elif opcode == 0x110:  # RRA
            v = self.dst_read(as_mode, reg, bytemode)
            shift = 7 if bytemode else 15
            mask = 0x7F if bytemode else 0x7FFF
            sign = v & (0x80 if bytemode else 0x8000)
            result = sign | ((v >> 1) & mask)
            self.set_c(v & 1)
            self.set_z(result == 0)
            self.set_n(result & (0x80 if bytemode else 0x8000))
            self.set_v(0)
            self.dst_write(as_mode, reg, result, bytemode)
        elif opcode == 0x118:  # SXT
            v = self.dst_read(as_mode, reg, False)
            result = v & 0xFF
            if result & 0x80:
                result |= 0xFF00
            self.set_z(result == 0)
            self.set_n(result & 0x8000)
            self.set_c(result != 0)
            self.set_v(0)
            self.dst_write(as_mode, reg, result, False)
        elif opcode == 0x120:  # PUSH
            src_val, _ = self.decode_src(as_mode, reg)
            if bytemode:
                self.sp = (self.sp - 2) & 0xFFFF
                self.write_word(self.sp, src_val & 0xFF)
            else:
                self.sp = (self.sp - 2) & 0xFFFF
                self.write_word(self.sp, src_val)
        elif opcode == 0x128:  # CALL
            target, _ = self.decode_src(as_mode, reg)
            self.sp = (self.sp - 2) & 0xFFFF
            self.write_word(self.sp, self.pc)
            self.pc = target


def load_elf(cpu, elffile):
    """Load ELF binary into CPU memory."""
    elf = ELFFile(open(elffile, 'rb'))
    
    # Get entry point
    entry = elf.header.e_entry
    cpu.pc = entry
    
    print(f"Entry point: 0x{entry:04x}")
    
    # Load segments
    for seg in elf.iter_segments():
        if seg.header.p_type == 'PT_LOAD':
            vaddr = seg.header.p_vaddr & 0xFFFF
            filesz = seg.header.p_filesz
            memsz = seg.header.p_memsz
            data = seg.data()
            
            print(f"  Loading segment: vaddr=0x{vaddr:04x} filesz={filesz} memsz={memsz}")
            
            for i in range(filesz):
                cpu.mem[(vaddr + i) & 0xFFFF] = data[i]
            
            # Zero-fill .bss
            for i in range(filesz, memsz):
                cpu.mem[(vaddr + i) & 0xFFFF] = 0
    
    # Also load .vectors section for interrupt table
    for sec in elf.iter_sections():
        if sec.name == '.vectors':
            vaddr = sec.header.sh_addr
            data = sec.data()
            for i in range(len(data)):
                cpu.mem[(vaddr + i) & 0xFFFF] = data[i]
            print(f"  Loaded .vectors at 0x{vaddr:04x} ({len(data)} bytes)")
    
    return elf


def init_peripherals(cpu):
    """Initialize peripheral MMIO state for rehosting.
    Set registers to values that make the firmware pass hardware checks."""
    
    # Clear ALL peripheral registers first
    for i in range(0x0200):
        cpu.periph[i] = 0
    
    # PMMCTL0: default core voltage level 0
    cpu.periph[0x0120] = 0x00  # PMMCTL0_L
    cpu.periph[0x0121] = 0x00  # PMMCTL0_H
    
    # PMMIFG: set SVM high-side delay flag (makes power_vcoreup succeed)
    cpu.periph[0x012C] = 0x02  # SVSMHDLYIFG set
    cpu.periph[0x012D] = 0x00
    
    # SFRIFG1: clear oscillator fault
    cpu.periph[0x0102] = 0x00
    cpu.periph[0x0103] = 0x00
    
    # UCSCTL7: no clock faults
    cpu.periph[0x016E] = 0x00
    cpu.periph[0x016F] = 0x00
    
    # LCD registers: no errors
    cpu.periph[0x0A1E] = 0x00  # LCDBIV - no interrupt
    cpu.periph[0x0A02] = 0x00  # LCDBCTL1 - no cap fault
    
    # RF1AIFERR: no radio errors
    cpu.periph[0x0F06] = 0x00
    cpu.periph[0x0F07] = 0x00
    
    # RF1AIFCTL1: radio command interface always ready
    cpu.periph[0x0F02] = 0x20  # RFINSTRIFG set
    
    # RTC registers: provide a valid time
    cpu.periph[0x04B0] = 0x00  # RTCSEC = 0
    cpu.periph[0x04B1] = 0x00
    cpu.periph[0x04B2] = 0x30  # RTCMIN = 30
    cpu.periph[0x04B3] = 0x00
    cpu.periph[0x04B4] = 0x11  # RTCDAY = 17 (day field of RTCDATE)
    cpu.periph[0x04B5] = 0x06  # RTCMON = 6 (month field)
    cpu.periph[0x04B6] = 0x26  # RTCYEAR LSB
    cpu.periph[0x04B7] = 0x00  # RTCYEAR MSB
    
    # Port registers: no key presses (all high)
    cpu.periph[0x0200] = 0xFF  # P1IN
    cpu.periph[0x0220] = 0xFF  # P2IN
    
    # Timer A: CCIFG flags set (so spin-waits don't block)
    cpu.periph[0x0346] = 0x01  # TA0CCTL2: CCIFG=1
    cpu.periph[0x0356] = 0x01  # TA0CCR2: CCIFG (actually CCIFG is in CCTL)
    cpu.periph[0x0342] = 0x01  # TA0CCTL0: CCIFG=1
    cpu.periph[0x0344] = 0x01  # TA0CCTL1: CCIFG=1
    
    # UART: ready for TX
    cpu.periph[0x05CA] = 0x02  # UCA0STAT: TX ready
    
    # REFCTL0: reference off
    cpu.periph[0x01B0] = 0x00
    
    print("Peripherals initialized for rehosting.")


def extract_dmesg(cpu):
    """Extract the dmesg log from the ring buffer at 0x2400."""
    # dmesg_buffer starts at 0x2400, size 2048 bytes
    # dmesg_index is a uint16_t in .noinit section
    # Find the actual dmesg_index from the noinit section
    
    # The dmesg structure:
    # - dmesg_magic: uint32_t at noinit (offset varies, could be at 0x1C00+)
    # - dmesg_index: uint16_t after dmesg_magic
    # - dmesg_buffer: char* pointing to 0x2400
    
    # Since we can't easily find dmesg_index in noinit, scan the buffer
    # Look for the start of dmesg output (after "----\n")
    buf = bytes(cpu.mem[0x2400:0x2800])
    
    # Try to find the beginning marker "----\n"
    marker = b'----\n'
    start_pos = buf.find(marker)
    
    if start_pos < 0:
        start_pos = 0
    
    # Extract meaningful text
    text = buf[start_pos:]
    # Remove nulls and non-printable chars (keep newlines, carriage returns)
    result = ''
    for b in text:
        if b == 0:
            continue
        if 32 <= b < 127 or b in (10, 13):
            result += chr(b)
        elif b == 0xFF:
            continue
        else:
            result += '.'
    
    return result


def run_rehost(elffile, max_instructions=2000000):
    """Run the rehosted goodwatch firmware."""
    cpu = MSP430()
    cpu.max_instructions = max_instructions
    
    print(f"Loading {elffile}...")
    elf = load_elf(cpu, elffile)
    init_peripherals(cpu)
    
    print(f"\nStarting emulation from PC=0x{cpu.pc:04x}...")
    print(f"Max instructions: {max_instructions}")
    print("-" * 60)
    
    last_log_count = 0
    running = True
    tick_count = 0
    
    while running:
        running = cpu.step()
        
        # Every 10000 instructions, give a status update
        if cpu.instruction_count % 100000 == 0:
            print(f"  ... {cpu.instruction_count} instructions executed, PC=0x{cpu.pc:04x}")
        
        # Check for simulation end marker
        if cpu.read_word(0x2800) == 0xDEAD:
            print(f"\n  Simulation complete marker detected at 0x2800!")
            print(f"  Instructions: {cpu.instruction_count}")
            break
        
        tick_count += 1
    
    print(f"\nEmulation stopped after {cpu.instruction_count} instructions.")
    print(f"Final PC: 0x{cpu.pc:04x}")
    print(f"Final SP: 0x{cpu.sp:04x}")
    print(f"Final SR: 0x{cpu.r[2]:04x}")
    print("-" * 60)
    
    # Extract dmesg
    print("\n=== DMESG LOG ===\n")
    log_text = extract_dmesg(cpu)
    print(log_text)
    print("\n=== END DMESG LOG ===\n")
    
    # Also show hex dump of dmesg buffer for debugging
    print("\n=== DMESG BUFFER HEX DUMP (first 512 bytes) ===")
    for i in range(0, 512, 16):
        hex_str = ' '.join(f'{cpu.mem[0x2400+i+j]:02x}' for j in range(16))
        ascii_str = ''.join(chr(cpu.mem[0x2400+i+j]) if 32 <= cpu.mem[0x2400+i+j] < 127 else '.' for j in range(16))
        print(f"  0x2400+{i:03x}: {hex_str}  {ascii_str}")
    
    return cpu


if __name__ == '__main__':
    elffile = sys.argv[1] if len(sys.argv) > 1 else 'goodwatch.elf'
    max_instr = int(sys.argv[2]) if len(sys.argv) > 2 else 2000000
    run_rehost(elffile, max_instr)
