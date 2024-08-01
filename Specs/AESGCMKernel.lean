/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
import Arm.BitVec
import Specs.AESArm
import Specs.GCM
import Specs.AESV8
import Specs.GCMV8

namespace AESGCMKernel

open BitVec

structure AESGCMLoopVars (in_bytes : Nat) where
  plaintext : BitVec (in_bytes * 8)
  input_ptr : Nat -- how many bytes have been processed
  main_end_input_ptr : Nat -- number of bytes to be processed in main loop
  Xi : BitVec 128
  Htable : List (BitVec 128)
  key : AESV8.AESKey

  ctr0 : BitVec 128
  ctr1 : BitVec 128
  ctr2 : BitVec 128
  ctr3 : BitVec 128

  aes0 : BitVec 128
  aes1 : BitVec 128
  aes2 : BitVec 128
  aes3 : BitVec 128

  ciphertext : BitVec (in_bytes * 8)
deriving DecidableEq, Repr

set_option diagnostics true
set_option maxRecDepth 100000

def AESGCMEncKernelLoop {Param : AESArm.KBR} (vars : AESGCMLoopVars in_bytes)
  : AESGCMLoopVars in_bytes :=
  if input_ptr ≥ main_end_input_ptr then vars
  else
    let bit_len := in_bytes * 8
    let ctr3 := GCM.inc_s 32 vars.ctr2 (by omega) (by omega)
    let vars := {vars with ctr3 := ctr3}
    let H1 := vars.Htable.get! 0
    let H2 := vars.Htable.get! 2
    let H3 := vars.Htable.get! 3
    let H4 := vars.Htable.get! 5
    let Xi := GCMV8.gcm_ghash_block H4 vars.Xi vars.aes0
    let Xi := GCMV8.gcm_ghash_block H3 Xi vars.aes1
    let Xi := GCMV8.gcm_ghash_block H2 Xi vars.aes2
    let Xi := GCMV8.gcm_ghash_block H1 Xi vars.aes3
    let start := bit_len - vars.ptr
    let block0 := extractLsb (start - 1) (start - 128) vars.plaintext
    let block1 := extractLsb (start - 129) (start - 256) vars.plaintext
    let block2 := extractLsb (start - 257) (start - 384) vars.plaintext
    let block3 := extractLsb (start - 385) (start - 512) vars.plaintext
    let aes0 := block0 ^^^
      (AESArm.AES_encrypt_with_ks (Param := Param) vars.ctr0 vars.key.rd_key)
    let aes1 := block1 ^^^
      (AESArm.AES_encrypt_with_ks (Param := Param) vars.ctr1 vars.key.rd_key)
    let aes2 := block2 ^^^
      (AESArm.AES_encrypt_with_ks (Param := Param) vars.ctr2 vars.key.rd_key)
    let aes3 := block3 ^^^
      (AESArm.AES_encrypt_with_ks (Param := Param) vars.ctr3 vars.key.rd_key)
    let ctr0 := GCM.inc_s 32 ctr3 (by omega) (by omega)
    let ctr1 := GCM.inc_s 32 ctr0 (by omega) (by omega)
    let ctr2 := GCM.inc_s 32 ctr1 (by omega) (by omega)
    let ciphertext := BitVec.partInstall (vars.ptr + 127) vars.ptr aes0 vars.ciphertext
    let ciphertext := BitVec.partInstall (vars.ptr + 255) (vars.ptr + 128) aes1 ciphertext
    let ciphertext := BitVec.partInstall (vars.ptr + 383) (vars.ptr + 256) aes2 ciphertext
    let ciphertext := BitVec.partInstall (vars.ptr + 511) (vars.ptr + 384) aes3 ciphertext
    let vars : AESGCMLoopVars in_bytes :=
      { plaintext := vars.plaintext,
        ptr := vars.ptr + 128 * 4,
        Xi := Xi,
        Htable := vars.Htable,
        key := vars.key,
        ctr0 := ctr0, ctr1 := ctr1,
        ctr2 := ctr2, ctr3 := vars.ctr3,
        aes0 := aes0, aes1 := aes1,
        aes2 := aes2, aes3 := aes3,
        ciphertext := ciphertext }
    AESGCMEncKernelLoop (Param := Param) vars

def AESGCMEncKernelHelper {Param : AESArm.KBR}
  (in_stream : BitVec (in_bytes * 8))
  (Xi : BitVec 128) (ivec : BitVec 128)
  (key : AESV8.AESKey) (Htable : List (BitVec 128))
  : (List (BitVec 8) × BitVec 128) :=
  let input_ptr := 0
  -- subtracting 1 from in_bytes because the asssembly wants
  -- last four blocks be handled in tail code
  let main_end_input_ptr := input_ptr + ((in_bytes - 1) / 64 * 64)
  let end_input_ptr := input_ptr + in_bytes
  if input_ptr ≥ main_end_input_ptr -- if less or equal to 4 blocks
  then sorry -- tail code
  else
    let ciphertext := BitVec.zero (in_bytes * 8)

    have h1 : 128 = Param.block_size := by sorry
    let ctr0 := BitVec.cast h1 ivec
    let ctr1 := GCM.inc_s 32 ctr0 (by omega) (by omega)
    let ctr2 := GCM.inc_s 32 ctr1 (by omega) (by omega)
    let ctr3 := GCM.inc_s 32 ctr2 (by omega) (by omega)

    let lo := input_ptr * 8
    let hi := lo + 127
    have h2 : hi - lo + 1 = 128 := by sorry
    let block0 := BitVec.cast h2 $ extractLsb 127 0 in_stream
    let lo := hi + 1
    let hi := lo + 127
    let block1 := BitVec.cast h2 $ extractLsb 255 128 in_stream
    let lo := hi + 1
    let hi := lo + 127
    let block2 := BitVec.cast h2 $ extractLsb 383 256 in_stream
    let lo := hi + 1
    let hi := lo + 127
    let block3 := BitVec.cast h2 $ extractLsb 511 384 in_stream

    let aes0 := block0 ^^^ (BitVec.cast h1.symm
      (AESArm.AES_encrypt_with_ks (Param := Param) ctr0 key.rd_key))
    let aes1 := block1 ^^^ (BitVec.cast h1.symm
      (AESArm.AES_encrypt_with_ks (Param := Param) ctr1 key.rd_key))
    let aes2 := block2 ^^^ (BitVec.cast h1.symm
      (AESArm.AES_encrypt_with_ks (Param := Param) ctr2 key.rd_key))
    let aes3 := block3 ^^^ (BitVec.cast h1.symm
      (AESArm.AES_encrypt_with_ks (Param := Param) ctr3 key.rd_key))

    let ciphertext := BitVec.partInstall 127 0 aes0 ciphertext
    let ciphertext := BitVec.partInstall 255 128 aes1 ciphertext
    let ciphertext := BitVec.partInstall 383 256 aes2 ciphertext
    let ciphertext := BitVec.partInstall 511 384 aes3 ciphertext

    let ctr3 := BitVec.cast h1.symm ctr3
    let ctr4 := GCM.inc_s 32 ctr3 (by omega) (by omega)
    let ctr5 := GCM.inc_s 32 ctr4 (by omega) (by omega)
    let ctr6 := GCM.inc_s 32 ctr5 (by omega) (by omega)
    -- let ctr7 := GCM.inc_s 32 ctr6 (by omega) (by omega)
    let vars : AESGCMLoopVars in_bytes :=
      { plaintext := in_stream,
        input_ptr := input_ptr + 64,
        main_end_input_ptr := main_end_input_ptr,
        Xi := Xi,
        Htable := Htable,
        key := key,
        ctr0 := ctr4, ctr1 := ctr5, ctr2 := ctr6, ctr3 := ctr3,
        aes0 := aes0, aes1 := aes1, aes2 := aes2, aes3 := aes3,
        ciphertext := ciphertext }
    let res := AESGCMEncKernelLoop (Param := Param) vars
    ( split (BitVec.reverse res.ciphertext) 8 (by omega), res.Xi)

def AESGCMEncKernel (in_blocks : List (BitVec 8))
  (in_bits : BitVec 64) (Xi : BitVec 128) (ivec : BitVec 128)
  (key : AESV8.AESKey) (Htable : List (BitVec 128))
  (h1 : key.rounds = 10#64 ∨ key.rounds = 12#64 ∨ key.rounds = 14#64)
  (h2: 128 ∣ in_bits.toNat)  -- in_blocks only contains whole blocks
  (h3: 8 * in_blocks.length = in_bits.toNat)
  : (List (BitVec 8) × BitVec 128) :=
  let in_bytes := in_bits.toNat/8
  have h: 8 * in_blocks.reverse.length = in_bytes * 8 := by
    simp only [List.length_reverse, h3, in_bytes]; omega
  let in_stream : BitVec (in_bytes * 8) :=
    BitVec.cast h $ BitVec.flatten $ List.reverse in_blocks
  let p := AESV8.KBR_from_AESKey key h1
  AESGCMEncKernelHelper (Param := p) in_stream Xi ivec key Htable

def AESGCMDecKernel (in_blocks : List (BitVec 8)) (in_bits : BitVec 64)
  (Xi : BitVec 128) (ivec : BitVec 128) (key : AESKey)
  (Htable : List (BitVec 128)) : (List (BitVec 8) × BitVec 128) :=
  sorry

end AESGCMKernel
