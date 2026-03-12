-- clog equivalent of Nat.log2

import Mathlib.Data.Nat.Log
import Mathlib.Tactic

namespace Nat

def clog2: ℕ → ℕ := Nat.clog 2

lemma le_clog2_self (n: ℕ):
  n ≤ 2 ^ (n.clog2) := by
  apply le_pow_clog (by simp) n

lemma log2_le_clog2 (n: ℕ):
  n.log2 ≤ n.clog2 := by
  rw [log2_eq_log_two]
  apply Nat.log_le_clog 2 n

lemma le_pow_iff_clog2_le {x y: ℕ}:
  x ≤ 2 ^ y ↔ clog2 x ≤ y :=
  by symm; apply Nat.clog_le_iff_le_pow; simp

lemma clog2_le_log2 (n: ℕ):
  n.clog2 ≤ n.log2 + 1 := by
  rw [log2_eq_log_two]
  rw [← le_pow_iff_clog2_le]
  apply le_of_lt
  cases n with
  | zero => simp
  | succ n =>
    rw [← log2_eq_log_two, ← Nat.log2_lt (by simp)]
    simp

lemma clog2_eq (n: ℕ):
  n.clog2 = if 2 ^ n.log2 < n then n.log2 + 1 else n.log2 := by
  have H₀ := clog2_le_log2 n
  have H₁ := log2_le_clog2 n
  split_ifs with Hcond <;> rw [← Nat.lt_clog_iff_pow_lt (by simp), ← clog2] at Hcond <;> linarith
