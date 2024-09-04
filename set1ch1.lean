/-
Author: Kyle Ellefsen
Created: 2024-09-04
Run Using Lean 4.12.0-rc1
First Problem in https://cryptopals.com/sets/1/challenges/1
-/

import Mathlib
import Init.Data.ByteArray
import Batteries.Data.ByteArray
import Init.Data.BitVec

open Std (HashSet)


abbrev Fin1 := Fin (2^0)    -- A natural number where n = 0.
abbrev Fin7 := Fin (2^3)    -- A natural number where n ≤ 7. Hexidecimal rep.
abbrev Fin63 := Fin (2^6)   -- A natural number where n ≤ 63. A Base64 num
abbrev Fin255 := Fin (2^8)  -- A natural number where n ≤ 255. A full byte
#eval BitVec.ofFin (255 : Fin255)



namespace Char
def toUInt8_of_hexchar (c: Char) : Option UInt8 :=
  let possible_vals : HashSet Char := HashSet.ofList
    ['a','b','c','d','e','f','g','A','B','C','D','E','F','G',
    '0','1','2','3','4','5','6','7','8','9']
  if ¬(possible_vals.contains c) then none else
  if c.isDigit then some (c.toNat - 48).toUInt8
  else if c.isAlpha then some (c.toLower.toNat - 87).toUInt8
  else none
end Char
#eval '0'.toUInt8_of_hexchar.get! -- 0
#eval 'G'.toUInt8_of_hexchar.get! -- 16
#eval 'H'.toUInt8_of_hexchar -- none

namespace Nat
/-- Nat division that rounds up instead of (the default) down. -/
def div_ceil (a b : ℕ): ℕ :=
  let floor := a / b
  if a % b = 0
  then floor
  else floor + 1
end Nat

namespace String
/-This uses all the bits of UInt8. -/
def toByteArray_of_hex (hexstr: String) : Option ByteArray:=
  let chunk_size : ℕ := 2  -- 2 hex (2⁴) elements in a byte (2⁸).
  let num_chunks : ℕ := hexstr.length.div_ceil chunk_size
  let chunk_start_idxs: Array ℕ :=
    (List.range num_chunks).toArray.map (·*chunk_size)
  let idxs := List.range chunk_size  -- [0, 1]
  let arr := chunk_start_idxs.map λ offset ↦
    let nat_byte : ℕ := idxs.foldl (init := 0)
      λ acc i ↦
        let i' := offset + i
        let c : Char := hexstr.toList.toArray[i']!
        let b: UInt8 := c.toUInt8_of_hexchar.get!
        acc + b.toNat * 16^(1-i)
    nat_byte.toUInt8
  some (ByteArray.mk arr)
end String


namespace UInt8
def toBitVec (b : UInt8) : BitVec 8 :=
  BitVec.ofFin (b.toNat : Fin255)
end UInt8

namespace List
/--Aggregates every n elements of a list into a nested list -/
def aggN {α : Type} (xs : List α) (n : ℕ) : List (List α) :=
  if n = 0 then [xs] else
  if 0 < xs.length then
    let xs_split := (xs.splitAt n)
    let chunk := xs_split.1
    let xs' := xs_split.2
    if xs'.length = 0 then [chunk] else
    if xs'.length < xs.length then
      [chunk] ++ aggN xs' n
    else [chunk]
  else
    [xs]
end List

def mylist := [1,2,3,4,5,6,7,8,9,10,11,12,13]
#eval mylist.aggN 3  -- [[1, 2, 3], [4, 5, 6], [7, 8, 9], [10, 11, 12], [13]]

namespace ByteArray
def aggN (arr: ByteArray) (n: ℕ) : Array ByteArray:=
  (arr.toList.aggN n).map
    (λel ↦ ByteArray.mk el.toArray)
  |>.toArray

def toBitVec (arr: ByteArray): Array (BitVec 8) :=
  (arr.toList.map λx ↦ x.toBitVec).toArray
end ByteArray

def concatBitVecs {n : Nat} (bvs : Array (BitVec n)) : BitVec (n * bvs.size) :=
  bvs.size.fold (init := BitVec.zero (n * bvs.size)) fun i acc =>
    let shiftAmount := (bvs.size - 1 - i) * n
    acc ||| (bvs[i]!.zeroExtend (n * bvs.size) <<< shiftAmount)

#eval concatBitVecs #[0x12#8, 0x34#8, 0x56#8, 0x78#8] -- 0x12345678#32

/- Generates boolean array of length n, where elements from start (inclusive)
to end (exclusive) are true, and everything else is false. -/
def mk_bool_mask (n start stop : ℕ) :=
  Array.ofFn (λ (idx: Fin n) ↦ if start ≤ idx ∧ idx < stop then true else false)
#eval mk_bool_mask 8 1 3 -- #[false, true, true, false, false, false, false, false]

def mk_bool_masks (veclen mask_size: ℕ) :=
  let mk_mask := λ(i j : ℕ) ↦ mk_bool_mask veclen i j
  let num_masks : ℕ := Nat.div_ceil veclen mask_size
  let mask_start_idxs: Array ℕ :=
    (List.range num_masks).toArray.map (· * mask_size)
  let masks := mask_start_idxs.toList.map λ start_idx ↦
    (mk_mask start_idx (start_idx+mask_size))
  masks.reverse


/-- Gets the character representation of a Base64 UInt8. -/
def char_of_b64 (b : UInt8) :=
  let n : ℕ := b.toNat
  if 0 ≤ n ∧ n ≤ 25
  then Char.ofNat (n + 65)
  else if 26 ≤ n ∧ n ≤ 51
  then Char.ofNat (n + 71)
  else if 52 ≤ n ∧ n ≤ 61
  then Char.ofNat (n - 4)
  else if b = 62 then '+'
  else if b = 63 then '/'
  else '⊥'

def get_hex_rep_big_bytearray (bigbytearray : ByteArray) :=
  let num_bytes := bigbytearray.size
  let num_bits := num_bytes * 8
  let mask_size := 6  -- Base64 uses 6 bits (2⁶=64)
  let num_masks := num_bits / mask_size
  let bignat := (concatBitVecs bigbytearray.toBitVec).toNat
  let masks :=  mk_bool_masks num_bits mask_size
  let result := masks.map λ mask ↦ ((BitVec.ofBoolListLE mask.toList).toNat.land bignat)
  let offsets := ((List.range num_masks).map (· * mask_size)).reverse
  let result_arr := (List.zip result offsets).map λ⟨r, i⟩ ↦ (r >>> i).toUInt8
  String.mk (result_arr.map char_of_b64)

def b64str_of_bytearray (bytearr: ByteArray) : String :=
  let num_bytes_to_fuse := 3
  String.join ((bytearr.aggN num_bytes_to_fuse).toList.map get_hex_rep_big_bytearray)


def hexstr := "49276d206b696c6c696e6720796f757220627261696e206c696b65206120706f69736f6e6f7573206d757368726f6f6d"
#eval b64str_of_bytearray (hexstr.toByteArray_of_hex.get!)
