/-
Author: Kyle Ellefsen
Created: 2024-09-05
Run Using Lean 4.12.0-rc1
https://cryptopals.com/sets/1/challenges/2
-/

import Mathlib
open Std (HashMap)

def hexcharmap : HashMap (Fin 16) Char :=
  HashMap.ofList
    (List.zip (List.range 16) "0123456789abcdefg".toList)

def hexstr_of_nat (n : ℕ) :=
  match n with
  | 0 => ""
  | k + 1 =>
    let lsb : Fin 16 := ((k+1) % 16) -- least significant byte
    let rem : ℕ := (k+1) / 16
    let leftchar := (hexcharmap[lsb]!).toString
    hexstr_of_nat (rem) ++ leftchar

def hex1 : ℕ := 0x1c0111001f010100061a024b53535009181c
def hex2 : ℕ := 0x686974207468652062756c6c277320657965
def hex3 : ℕ := hex1 ^^^ hex2  -- XOR
#eval hexstr_of_nat hex3
