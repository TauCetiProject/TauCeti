/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Basic results on graded algebras

For a `ℤ`-graded algebra concentrated in nonnegative degrees, the degree-zero component of a
product is the product of the degree-zero components, as for gradings by a canonically ordered
monoid (`GradedRing.projZeroRingHom`). Consequently an idempotent with no degree-zero component
vanishes: its powers have no components below any given degree.

## Main results

* `TauCeti.GradedAlgebra.mul_le_grade_add`: the product of two homogeneous components is
  contained in the component indexed by the sum of their degrees.
* `TauCeti.GradedAlgebra.coe_decompose_mul_zero_of_nonneg`: in nonnegative degrees, the degree-zero
  component is multiplicative.
* `TauCeti.GradedAlgebra.eq_zero_of_isIdempotentElem_of_decompose_zero`: in nonnegative degrees,
  an idempotent with zero degree-zero component is zero.
-/

public section

namespace TauCeti.GradedAlgebra

open DirectSum

section Mul

variable {R A ι : Type*} [Add ι] [CommSemiring R] [Semiring A] [Algebra R A]
  (𝒜 : ι → Submodule R A) [SetLike.GradedMul 𝒜]

/-- The product of two homogeneous components lies in the component of the sum of the degrees. -/
theorem mul_le_grade_add (i j : ι) : 𝒜 i * 𝒜 j ≤ 𝒜 (i + j) :=
  Submodule.mul_le.mpr fun _ ha _ hb ↦ SetLike.mul_mem_graded ha hb

end Mul

section Nonneg

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜]

/-- **The degree-zero component is multiplicative in nonnegative degrees.** This is the
`ℤ`-graded counterpart of `GradedRing.projZeroRingHom`, which needs a canonically ordered grading
monoid. -/
theorem coe_decompose_mul_zero_of_nonneg (hneg : ∀ p < 0, 𝒜 p = ⊥) (x y : A) :
    (decompose 𝒜 (x * y) 0 : A) = decompose 𝒜 x 0 * decompose 𝒜 y 0 := by
  have hzero {p : ℤ} (hp : p < 0) {c : A} (hc : c ∈ 𝒜 p) : c = 0 := by
    rwa [hneg p hp, Submodule.mem_bot] at hc
  induction x using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | add x x' hx hx' => simp only [add_mul, decompose_add, add_apply, Submodule.coe_add, hx, hx']
  | @homogeneous i x =>
    obtain ⟨c, hc⟩ := x
    induction y using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | add y y' hy hy' =>
      simp only [mul_add, decompose_add, add_apply, Submodule.coe_add, hy, hy']
    | @homogeneous j y =>
      obtain ⟨c', hc'⟩ := y
      dsimp only
      rcases lt_or_ge i 0 with hi | hi
      · simp [hzero hi hc]
      rcases lt_or_ge j 0 with hj | hj
      · simp [hzero hj hc']
      by_cases h : i + j = 0
      · obtain rfl : i = 0 := by omega
        obtain rfl : j = 0 := by omega
        rw [decompose_of_mem_same 𝒜 (by simpa using SetLike.GradedMul.mul_mem hc hc'),
          decompose_of_mem_same 𝒜 hc, decompose_of_mem_same 𝒜 hc']
      · rw [decompose_of_mem_ne 𝒜 (SetLike.GradedMul.mul_mem hc hc') h]
        rcases eq_or_ne i 0 with rfl | h'
        · rw [decompose_of_mem_ne 𝒜 hc' (by omega), mul_zero]
        · rw [decompose_of_mem_ne 𝒜 hc h', zero_mul]

/-- **An idempotent with no degree-zero component vanishes** in nonnegative degrees. -/
theorem eq_zero_of_isIdempotentElem_of_decompose_zero (hneg : ∀ p < 0, 𝒜 p = ⊥) {f : A}
    (hf : IsIdempotentElem f) (h0 : (decompose 𝒜 f 0 : A) = 0) : f = 0 := by
  -- The components of `f` vanish below degree one, so those of `f ^ n` vanish below degree `n`,
  -- and `f` is its own `n`th power for every `n ≥ 1`.
  have hzero {p : ℤ} (hp : p < 0) {c : A} (hc : c ∈ 𝒜 p) : c = 0 := by
    rwa [hneg p hp, Submodule.mem_bot] at hc
  set r := decompose 𝒜 f with hr
  have hr1 : ∀ i < (1 : ℤ), r i = 0 := by
    intro i hi
    rcases lt_or_eq_of_le (show i ≤ 0 by omega) with hi | rfl
    · exact Subtype.ext (hzero hi (r i).2)
    · exact Subtype.ext h0
  have hpow (n : ℕ) : r = r ^ (n + 1) := by
    have h : decompose 𝒜 (f ^ (n + 1)) = decompose 𝒜 f ^ (n + 1) :=
      map_pow (decomposeRingEquiv 𝒜) f (n + 1)
    rw [hr, ← h, hf.pow_succ_eq]
  have hvan : ∀ n : ℕ, ∀ i < ((n + 1 : ℕ) : ℤ), r i = 0 := by
    intro n
    induction n with
    | zero => simpa using hr1
    | succ n ih =>
      intro i hi
      rw [hpow (n + 1), pow_succ, ← hpow n]
      exact mul_apply_eq_zero ih hr1 (by push_cast at hi ⊢; omega)
  have : r = 0 := by
    ext i : 1
    exact hvan i.toNat i (by omega)
  simpa [hr] using congrArg (decompose 𝒜).symm this

end Nonneg

end TauCeti.GradedAlgebra
