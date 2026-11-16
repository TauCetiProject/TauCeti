/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Basic
public import TauCeti.Analysis.Normed.Lp.Shift

/-!
# Fredholmness and index of unilateral shifts on `ℓᵖ`

For `1 ≤ p ≤ ∞`, the unilateral left and right shifts on `ℓ^p(ℕ, E)` constructed in
`TauCeti.Analysis.Normed.Lp.Shift` have kernels and cokernels linearly isomorphic to `E` and `0`
(or `0` and `E`), so over any nontrivial normed ring with bounded scalar action their indices are
`(finrank 𝕜 E : ℤ)` and `-(finrank 𝕜 E : ℤ)` (`lp.index_leftShift`, `lp.index_rightShift`). More
generally, for any free `𝕜`-module `E` over a normed ring satisfying the strong rank condition, the
`m`-th powers have indices `m * finrank 𝕜 E` and `-(m * finrank 𝕜 E)` (`lp.index_leftShift_pow`,
`lp.index_rightShift_pow`).

Over a nontrivially normed field `𝕜` (with no completeness assumption on `𝕜` or `E`), both shifts
are Fredholm if and only if `E` is finite-dimensional (`lp.isFredholm_rightShift_iff`,
`lp.isFredholm_leftShift_iff`), and every natural-number power of either shift remains Fredholm
(`lp.isFredholm_rightShift_pow`, `lp.isFredholm_leftShift_pow`). In particular, powers of the
scalar unilateral shifts realize every integer `n : ℤ` as a Fredholm index on `ℓ^p(ℕ, 𝕜)`
(`lp.exists_isFredholm_and_index_eq`).

## Main declarations

* `lp.index_leftShift`, `lp.index_rightShift`, `lp.index_leftShift_pow`,
  `lp.index_rightShift_pow`: index formulas for the unilateral shifts and their powers.
* `lp.isFredholm_rightShift_iff`, `lp.isFredholm_leftShift_iff`: characterization of Fredholmness
  of the unilateral shifts by `FiniteDimensional 𝕜 E`.
* `lp.isFredholm_rightShift_pow`, `lp.isFredholm_leftShift_pow`: Fredholmness of natural-number
  powers of the shifts for finite-dimensional `E`.
* `lp.exists_isFredholm_and_index_eq`: every integer is the index of a Fredholm endomorphism of
  `ℓ^p(ℕ, 𝕜)`.

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Springer, 1990, Chapter XI, §3.
* H. B. Lawson, Jr., and M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989,
  Chapter III, §7, Example 7.5.
-/

public section

open Module
open scoped ENNReal lp

namespace lp

section Index

section Single

variable (𝕜 E : Type*) (p : ℝ≥0∞) [NormedRing 𝕜] [Nontrivial 𝕜] [NormedAddCommGroup E]
  [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [Fact (1 ≤ p)]

/-- The unilateral left shift on `ℓ^p(ℕ, E)` has index `finrank 𝕜 E`. -/
@[simp]
theorem index_leftShift :
    (leftShift 𝕜 E p).index = (finrank 𝕜 E : ℤ) := by
  rw [(leftShift 𝕜 E p).index_of_surjective (leftShift_surjective 𝕜 E p),
    (kerLeftShiftEquiv 𝕜 E p).finrank_eq]

/-- The unilateral right shift on `ℓ^p(ℕ, E)` has index `-finrank 𝕜 E`. -/
@[simp]
theorem index_rightShift :
    (rightShift 𝕜 E p).index = -(finrank 𝕜 E : ℤ) := by
  rw [(rightShift 𝕜 E p).index_of_injective (rightShift_injective 𝕜 E p),
    (cokerRightShiftEquiv 𝕜 E p).finrank_eq]

end Single

section Pow

variable (𝕜 E : Type*) (p : ℝ≥0∞) [NormedRing 𝕜] [StrongRankCondition 𝕜] [NormedAddCommGroup E]
  [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [Module.Free 𝕜 E] [Fact (1 ≤ p)]

/-- For a free `𝕜`-module `E` over a normed ring satisfying the strong rank condition, the `m`-th
power of `leftShift` on `ℓ^p(ℕ, E)` has index `m * finrank 𝕜 E`. -/
@[simp]
theorem index_leftShift_pow (m : ℕ) :
    (leftShift 𝕜 E p ^ m).index = (m : ℤ) * (finrank 𝕜 E : ℤ) := by
  rw [(leftShift 𝕜 E p ^ m).index_of_surjective (leftShift_pow_surjective 𝕜 E p m),
    (kerLeftShiftPowEquiv 𝕜 E p m).finrank_eq, Module.finrank, rank_fun_eq_lift_mul]
  simp [Module.finrank, Cardinal.toNat_mul]

/-- For a free `𝕜`-module `E` over a normed ring satisfying the strong rank condition, the `m`-th
power of `rightShift` on `ℓ^p(ℕ, E)` has index `-(m * finrank 𝕜 E)`. -/
@[simp]
theorem index_rightShift_pow (m : ℕ) :
    (rightShift 𝕜 E p ^ m).index = -((m : ℤ) * (finrank 𝕜 E : ℤ)) := by
  rw [(rightShift 𝕜 E p ^ m).index_of_injective (rightShift_pow_injective 𝕜 E p m),
    (cokerRightShiftPowEquiv 𝕜 E p m).finrank_eq, Module.finrank, rank_fun_eq_lift_mul]
  simp [Module.finrank, Cardinal.toNat_mul]

end Pow

end Index

section Fredholm

variable (𝕜 E : Type*) (p : ℝ≥0∞) [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [Fact (1 ≤ p)]

/-- For finite-dimensional `E`, the unilateral right shift on `ℓ^p(ℕ, E)` is Fredholm. -/
theorem isFredholm_rightShift [FiniteDimensional 𝕜 E] :
    (rightShift 𝕜 E p).IsFredholm :=
  (isClosedEmbedding_rightShift 𝕜 E p).isFredholm
    (Module.Finite.equiv (cokerRightShiftEquiv 𝕜 E p).symm)

/-- The unilateral right shift on `ℓ^p(ℕ, E)` is Fredholm if and only if `E` is
finite-dimensional. -/
@[simp]
theorem isFredholm_rightShift_iff :
    (rightShift 𝕜 E p).IsFredholm ↔ FiniteDimensional 𝕜 E := by
  refine ⟨fun h ↦ ?_, fun _ ↦ isFredholm_rightShift 𝕜 E p⟩
  have := h.finite_coker
  exact (cokerRightShiftEquiv 𝕜 E p).finiteDimensional

/-- For finite-dimensional `E`, the unilateral left shift on `ℓ^p(ℕ, E)` is Fredholm. -/
theorem isFredholm_leftShift [FiniteDimensional 𝕜 E] :
    (leftShift 𝕜 E p).IsFredholm :=
  (isQuotientMap_leftShift 𝕜 E p).isFredholm
    ((leftShift 𝕜 E p).closedComplemented_ker_of_rightInverse (rightShift 𝕜 E p)
      (leftInverse_leftShift_rightShift 𝕜 E p))
    (kerLeftShiftEquiv 𝕜 E p).symm.finiteDimensional

/-- The unilateral left shift on `ℓ^p(ℕ, E)` is Fredholm if and only if `E` is
finite-dimensional. -/
@[simp]
theorem isFredholm_leftShift_iff :
    (leftShift 𝕜 E p).IsFredholm ↔ FiniteDimensional 𝕜 E := by
  refine ⟨fun h ↦ ?_, fun _ ↦ isFredholm_leftShift 𝕜 E p⟩
  have := h.finite_ker
  exact (kerLeftShiftEquiv 𝕜 E p).finiteDimensional

/-- For finite-dimensional `E`, every natural-number power of `rightShift` on `ℓ^p(ℕ, E)` is
Fredholm (without requiring completeness of `𝕜`). -/
theorem isFredholm_rightShift_pow [FiniteDimensional 𝕜 E] (m : ℕ) :
    (rightShift 𝕜 E p ^ m).IsFredholm :=
  (isClosedEmbedding_rightShift_pow 𝕜 E p m).isFredholm
    (Module.Finite.equiv (cokerRightShiftPowEquiv 𝕜 E p m).symm)

/-- For finite-dimensional `E`, every natural-number power of `leftShift` on `ℓ^p(ℕ, E)` is
Fredholm (without requiring completeness of `𝕜`). -/
theorem isFredholm_leftShift_pow [FiniteDimensional 𝕜 E] (m : ℕ) :
    (leftShift 𝕜 E p ^ m).IsFredholm :=
  (isQuotientMap_leftShift_pow 𝕜 E p m).isFredholm
    ((leftShift 𝕜 E p ^ m).closedComplemented_ker_of_rightInverse
      (rightShift 𝕜 E p ^ m) (leftInverse_leftShift_pow_rightShift_pow 𝕜 E p m))
    (Module.Finite.equiv (kerLeftShiftPowEquiv 𝕜 E p m).symm)

end Fredholm

/-- Over any nontrivially normed field `𝕜`, every integer is the index of a Fredholm endomorphism
of `ℓ^p(ℕ, 𝕜)`. -/
theorem exists_isFredholm_and_index_eq (𝕜 : Type*) (p : ℝ≥0∞) [NontriviallyNormedField 𝕜]
    [Fact (1 ≤ p)] (n : ℤ) :
    ∃ T : ℓ^p(ℕ, 𝕜) →L[𝕜] ℓ^p(ℕ, 𝕜), T.IsFredholm ∧ T.index = n := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · exact ⟨leftShift 𝕜 𝕜 p ^ m, isFredholm_leftShift_pow 𝕜 𝕜 p m, by simp⟩
  · exact ⟨rightShift 𝕜 𝕜 p ^ m, isFredholm_rightShift_pow 𝕜 𝕜 p m, by simp⟩

end lp
