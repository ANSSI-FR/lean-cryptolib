-- Additional properties about Int.bmod

import Mathlib.Data.Int.DivMod
import Mathlib.Tactic

namespace Int

lemma abs_bmod_le (x: ℤ) (m: ℕ) (Hm: 0 < m):
  |x.bmod m| ≤ m / 2 := by
  rw [abs_le]; apply And.intro; apply Int.le_bmod Hm
  transitivity; apply Int.bmod_le Hm
  omega

lemma bmod_eq' (x: ℤ) (m: ℕ):
  x.bmod m = x - m * (round (x / (m: ℚ))) := by
  rw [round_eq, Int.bmod]
  have X: x % m < (m + 1) / 2 ↔ 2 * (x % m) < m := by omega
  cases Nat.eq_zero_or_pos m with
  | inl Hz => rw [Hz]; simp
  | inr Hpos =>
    rw [div_add_div] <;> simp <;> try linarith
    split_ifs with Hcond <;> rw [X] at Hcond
    . rw [Int.emod_def]; simp; left
      rw [show m * (2:ℚ) = ↑(2 * m) by simp; linarith]
      rw [show x * 2 + (m:ℚ) = ↑(2 * x + m) by simp; linarith]
      rw [Rat.floor_intCast_div_natCast]; symm
      apply ((@Int.ediv_emod_unique _ _ (2 * (x % m) + m) _ (by omega)).mpr ?_).left
      apply And.intro
      . nth_rw 3 [← Int.ediv_add_emod x m]; simp
        linarith
      . have X := @Int.emod_nonneg x m (by omega)
        simp; apply And.intro <;> linarith
    . rw [show m * (2:ℚ) = ↑(2 * m) by simp; linarith]
      rw [show x * 2 + (m:ℚ) = ↑(2 * x + m) by simp; linarith]
      rw [Rat.floor_intCast_div_natCast]
      rw [Int.emod_def]; simp
      nth_rw 3 [← mul_one m]
      rw [Int.sub_sub, Nat.cast_mul, ← mul_add]; simp
      left; symm
      apply ((@Int.ediv_emod_unique _ _ (2 * (x % m) - m) _ (by omega)).mpr ?_).left
      apply And.intro
      . nth_rw 3 [← Int.ediv_add_emod x m]
        linarith
      . have X := @Int.emod_lt_of_pos x m (by omega)
        simp; apply And.intro <;> try linarith

lemma emod_def' (x: ℤ) (m: ℕ):
  x % ↑m = if x.bmod m < 0 then m + x.bmod m else x.bmod m := by
  simp [Int.bmod_def]
  split_ifs <;> try omega
  . cases Nat.eq_zero_or_pos m with
    | inl Hz => rw [Hz]; simp
    | inr Hpos =>
      have X := @Int.emod_nonneg x m (by omega); linarith
  . cases Nat.eq_zero_or_pos m with
    | inl Hz => rw [Hz]; simp
    | inr Hpos =>
      have X := @Int.emod_lt_of_pos x m (by omega); linarith

end Int
