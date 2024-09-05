
import Mathlib
open Std (HashMap)


def concatBitVecs {n : Nat} (bvs : Array (BitVec n)) : BitVec (n * bvs.size) :=
  bvs.size.fold (init := BitVec.zero (n * bvs.size)) fun i acc =>
    let shiftAmount := (bvs.size - 1 - i) * n
    acc ||| (bvs[i]!.zeroExtend (n * bvs.size) <<< shiftAmount)

namespace UInt8
def toBitVec (b : UInt8) : BitVec 8 :=
  BitVec.ofFin (b.toNat : Fin 256)
end UInt8

namespace ByteArray
def toBitVec (arr: ByteArray): Array (BitVec 8) :=
  (arr.toList.map λx ↦ x.toBitVec).toArray
end ByteArray

namespace ByteArray
def toNat (ba : ByteArray) := (concatBitVecs ba.toBitVec).toNat
end ByteArray

def hexcharmap : HashMap (Fin 16) Char :=
  HashMap.ofList
    (List.zip (List.range 16) "0123456789abcdefg".toList)

def asciicharmap : HashMap (Fin 256) Char :=
  HashMap.ofList
    (List.zip (List.range 256) ((List.range 256).map (Char.ofNat ·)))

#eval asciicharmap

namespace Nat

/-- Nat division that rounds up instead of (the default) down. -/
def div_ceil (a b : ℕ): ℕ :=
  let floor := a / b
  if a % b = 0
  then floor
  else floor + 1

def to_hexstr (n : ℕ) :=
  match n with
  | 0 => ""
  | k + 1 =>
    let lsb : Fin 16 := ((k+1) % 16) -- least significant byte
    let rem : ℕ := (k+1) / 16
    let leftchar := (hexcharmap[lsb]!).toString
    to_hexstr (rem) ++ leftchar

def to_ascii (n : ℕ) :=
  match n with
  | 0 => ""
  | k + 1 =>
    let lsb : Fin 256 := ((k+1) % 256) -- least significant byte
    let rem : ℕ := (k+1) / 256
    let leftchar := (asciicharmap[lsb]!).toString
    to_ascii (rem) ++ leftchar

def num_bytes (n : ℕ) : ℕ := n.to_hexstr.length
def num_words (n : ℕ) : ℕ := n.num_bytes.div_ceil  2
end Nat

/- replicates word b n times. -/
def replicate_word (b : Fin (2^8)) (n : ℕ) : ℕ:=
  List.replicate n b
  |>.map (BitVec.ofFin ·)
  |>.toArray
  |> (concatBitVecs ·)
  |>.toNat
def replicate_byte (b : Fin (2^16)) (n : ℕ) : ℕ:=
  List.replicate n b
  |>.map (BitVec.ofFin ·)
  |>.toArray
  |> (concatBitVecs ·)
  |>.toNat

-- #eval (replicate_word 1 2).to_hexstr  -- "11"
-- #eval (replicate_byte 1 2).to_hexstr  -- "10001"
-- #eval (replicate_byte 1 4).to_hexstr  -- "1000100010001"



def input_str := 0x1b37373331363f78151b7f2b783431333d78397828372d363c78373e783a393b3736
#eval input_str.num_words
#eval (input_str ^^^ (replicate_word 1 input_str.num_words))

def all_possibilities := (List.range 256).map λ(n:ℕ) ↦
                            ((replicate_word n input_str.num_words) ^^^ input_str)
                            |>.to_ascii
#eval all_possibilities
def X := 88
#eval all_possibilities[X]!
