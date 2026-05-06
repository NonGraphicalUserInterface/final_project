import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

open Real -- like namespace in C++

/- GOAL: to prove Binet's Theorem for all n ∈ ℕ, n > 0 -/

/- The Golden Ratio and its ``conjugate" -/
noncomputable def φ : ℝ := (1 + √5) / 2
noncomputable def ψ : ℝ := (1 - √5) / 2

def F : ℕ → ℕ
| 0 => 0
| 1 => 1
| (n+2) => F n + F (n + 1)

/- Goal: prove, for conditions listed above, that F_n = (φ^n - ψ^n) / √5 -/
-- Additional lemmas: needed because Lean wasn't simplifying the way I wanted and I also needed
-- to introduce some new lemmas about the behaviour of φ and ψ anyway.
lemma φ_plus_ψ : φ + ψ = 1 := by
  rw[ψ, φ]
  ring

lemma φ_times_ψ : φ*ψ = -1 := by
  rw[ψ, φ]
  ring_nf -- Lean told me to do this -- I know we didn't cover it in class
  simp
  ring

lemma k_plus_two (k : ℕ) (hn : 0 ≤ k) : φ^(k+2) - ψ^(k+2) = φ^k * (1 + φ) - ψ^k * (1 + ψ) := by
  calc
    φ^(k+2) - ψ^(k+2) = φ^k*((φ+ψ)^2 - φ*ψ - ψ*(φ+ψ)) - ψ^k*((φ+ψ)^2 - φ*ψ - φ*(φ+ψ)) := by ring
    _ = φ^k*(1^2 - (-1) - ψ*1) - ψ^k*(1^2 - (-1) - φ*1) := by rw[φ_plus_ψ, φ_times_ψ]
    _ = φ^k*(2 - ψ) - ψ^k*(2 - φ) := by ring
    _ = φ^k*(2 - (1 - √5) / 2) - ψ^k*(2 - (1 + √5) / 2) := by rw[φ, ψ]
    _ = φ^k*(1 + (1 + √5) / 2) - ψ^k*(1 + (1 - √5) / 2) := by ring

theorem binet (n : ℕ) (hn : 0 ≤ n) : F n = (φ^n - ψ^n) / sqrt 5 := by
  -- Initiate induction (I know that this is different from Macbeth, but just thought it
  -- would be a good chance to get used to more standard Lean)
  induction n using Nat.twoStepInduction with
  | zero =>
    simp
  | one =>
    simp only [pow_one] -- Lean itself told me to use "only [pow_one]"; same as "simp"
    rw [F, φ, ψ]
    ring_nf -- Lean told me to use _nf, even though it doesn't seem to make any difference in goal
    -- ring
    have h_sqrt : √5 ≠ 0 := by
      have h_5 : (5 : ℝ) ≠ 0 := by norm_num
      have h_leq : (0 : ℝ) ≤ 5 := by norm_num
      rw[sqrt_ne_zero]
      · exact h_5
      exact h_leq
    simp
  | more k ih_k ih_k1 =>
    rw[F]
    simp only [Nat.cast_add] -- Again, Lean told me to add this and I didn't like the yellow line
    rw[ih_k, ih_k1]
    · rw[k_plus_two]
      · ring
      · linarith
    · linarith
    · linarith
