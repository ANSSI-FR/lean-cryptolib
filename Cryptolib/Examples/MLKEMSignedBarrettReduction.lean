/-
Proof of correctness for the signed Barrett reduction
used in the reference implementation of Kyber/MLKEM
https://github.com/pq-crystals/kyber/blob/main/ref/reduce.c#L25-L42
-/

import Cryptolib.Arithmetic.SignedBarrettReduction

section MLKEMExample
def M: ℕ := 16    -- 16 bits
def q: ℕ := 3329  -- prime modulus used for MLKEM
def R: ℕ := 2 ^ 26
def k: ℕ := 2

-- This follows closely the original C code, though in ℤ
def mlkem_barrett_reduce (a: ℤ): ℤ :=
  let v := 20159
  let t := (v * a + (1 <<< 25)) >>> (26: ℕ)
  let t := t * 3329
  a - t

lemma mlkem_barrett_reduce_correct (a: ℤ) (Ha: |a| ≤ 2 ^ 15):
  mlkem_barrett_reduce a = a.bmod q := by
  rw [← barrett_reduce_spec a M R k q]
  . rw [mlkem_barrett_reduce, barrett_reduce, R, q]; simp
    rw [show (round (67108864 / (3329:ℚ))) = 20159 by native_decide]
    rw [Int.shiftRight_eq_div_pow, round_eq]
    rw [div_add_div] <;> try simp
    rw [show ↑a * 20159 * 2 + 67108864 = (20159 * a + 33554432) * (2:ℚ) by linarith]
    rw [mul_div_mul_right _ _ (by simp)]
    rw [show 20159 * ↑a + (33554432:ℚ) = ↑(20159 * a + (33554432:ℤ)) by simp]
    rw [show (67108864:ℚ) = ↑(67108864:ℕ) by simp]
    rw [Rat.floor_intCast_div_natCast]; simp; omega
  . simp [k]
  . native_decide
  . use (q/2); native_decide
  . native_decide
  . native_decide
  . transitivity; apply Ha; native_decide

-- This is basically the C code translated manually into Lean
def mlkem_barrett_reduce_impl (a: Int16): Int16 :=
  let v: Int16 := 20159
  let t: Int32 := (v.toInt32 * a.toInt32 + ((1: Int32) <<< 25)) >>> 26
  let t: Int16 := t.toInt16 * 3329
  a - t

-- TODO: Waiting for better support of bv_decide for Int16/Int32
/- lemma mlkem_barrett_reduce_impl_correct (a: Int16):
  Int16.toInt (mlkem_barrett_reduce_impl a) = (Int16.toInt a).bmod q :=
  sorry
 -/
end MLKEMExample
