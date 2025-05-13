-- Additional facts about `Floor`

import Mathlib.Algebra.Order.Floor

section LinearOrderedField

variable {α : Type*}
variable [LinearOrderedField α] [FloorRing α]

lemma floor_sub_abs (a b: α):
  |⌊a⌋ - ⌊b⌋| ≤ ⌈|a - b|⌉ := by
  wlog Hab: a ≥ b
  . rw [abs_sub_comm ⌊a⌋, abs_sub_comm a]
    apply this; apply le_of_not_ge at Hab; assumption
  . rw [abs_of_nonneg, abs_of_nonneg] <;> [skip; linarith; (simp; apply Int.floor_mono; assumption)]
    nth_rw 2 [← Int.fract_add_floor a]
    nth_rw 2 [← Int.fract_add_floor b]
    rw [show (Int.fract a + ↑⌊a⌋ - (Int.fract b + ↑⌊b⌋) = (Int.fract a - Int.fract b) + ↑(⌊a⌋ - ⌊b⌋)) by
        rw [Int.cast_sub]; linarith]
    rw [Int.ceil_add_int]; simp
    rw [show (0 = -1 + 1) by omega]
    rw [Int.add_one_le_ceil_iff]; simp
    have Ha₀: 0 ≤ Int.fract a := by apply Int.fract_nonneg
    have Hb₁: Int.fract b < 1 := by apply Int.fract_lt_one
    linarith

lemma floor_lt_iff (a b: α):
  ⌊a⌋ < ⌊b⌋ ↔ ∃ (n: ℤ), a < ↑n ∧ ↑n ≤ b := by
  apply Iff.intro
  . intro H; cases lt_or_ge a ↑⌊b⌋ with
    | inl Hlt => use ↑⌊b⌋; apply And.intro; assumption; exact Int.floor_le b
    | inr Hge =>
      apply Int.le_floor.mpr at Hge; linarith
  . intro ⟨n, Ha, Hb⟩
    have H := Int.floor_le_floor Hb
    rw [Int.floor_intCast] at H
    apply @lt_of_lt_of_le _ _ _ n; exact Int.floor_lt.mpr Ha; assumption

end LinearOrderedField
