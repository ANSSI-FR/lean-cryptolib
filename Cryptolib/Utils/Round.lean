-- Additional facts about `Round`

import Mathlib.Algebra.Order.Round
import Cryptolib.Utils.Floor

section LinearOrderedField

variable {α : Type*}
variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]

lemma round_sub_abs (a b: α):
  |round a - round b| ≤ ⌈|a - b|⌉ := by
  rw [round_eq, round_eq]
  rw [show (a - b = (a + 1/2) - (b + 1/2)) by linarith]
  apply floor_sub_abs

lemma round_lt_iff (a b: α):
  round a < round b ↔ ∃ (n: ℤ), a < n + 1/2 ∧ n + 1/2 ≤ b := by
  apply Iff.intro
  . rw [round_eq, round_eq]; intro H
    rw [floor_lt_iff] at H
    let ⟨n, Ha, Hb⟩ := H
    use (n - 1); apply And.intro <;> (simp; linarith)
  . intro ⟨n, Ha, Hb⟩
    rw [round_eq, round_eq]
    rw [floor_lt_iff]
    use (n + 1); apply And.intro <;> (simp; linarith)

end LinearOrderedField
