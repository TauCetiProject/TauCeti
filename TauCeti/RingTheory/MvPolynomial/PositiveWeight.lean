/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import TauCeti.RingTheory.GradedAlgebra.Connected
import TauCeti.Data.Finsupp.Weight

/-!
# Positively weighted polynomial rings as connected graded algebras

For a weight function `w : σ → M` taking values in an ordered additive commutative monoid `M`:

* If `0 ≤ w i` for every variable `i`, then every exponent vector `d : σ →₀ ℕ` has `0 ≤ d.weight w`,
  so `MvPolynomial.weightedHomogeneousSubmodule R w m = ⊥` whenever `m < 0`.
* If `0 < w i` for every variable `i`, then `d.weight w = 0 ↔ d = 0`, so the degree-zero weighted
  homogeneous component of `φ : MvPolynomial σ R` is `C (φ.coeff 0)` and the degree-zero weighted
  homogeneous submodule is the image of `algebraMap R (MvPolynomial σ R)`.

Note that Mathlib's `MvPolynomial.weightedHomogeneousComponent_zero` and
`Finsupp.weight_eq_zero_iff_eq_zero` assume `[CanonicallyOrderedAdd M]`, which holds for `ℕ` but not
for `ℤ`. Specializing `M = ℤ` with strictly positive integer weights makes `MvPolynomial σ R` a
connected nonnegatively `ℤ`-graded `R`-algebra whose canonical graded augmentation is
`MvPolynomial.constantCoeff`.

## Main results

* `MvPolynomial.weightedHomogeneousComponent_zero_of_pos`: degree-zero weighted homogeneous
  component for strictly positive weights in an ordered additive monoid.
* `MvPolynomial.connectedAugmentation_weightedHomogeneousSubmodule_eq_constantCoeff`:
  agreement of `GradedAlgebra.connectedAugmentation` with `MvPolynomial.constantCoeff`.
* `TauCeti.weightedHomogeneousSubmodule_eq_bot_of_lt_zero`,
  `TauCeti.weightedHomogeneousSubmodule_zero_eq_range`: negative-degree vanishing and
  connectedness of `MvPolynomial.weightedHomogeneousSubmodule R w`.
-/

public section

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R]

/-- If every variable has strictly positive weight in an ordered additive commutative monoid `M`,
the degree-zero weighted homogeneous component of `φ` is `C (φ.coeff 0)`. -/
@[simp]
theorem weightedHomogeneousComponent_zero_of_pos {M : Type*} [AddCommMonoid M] [PartialOrder M]
    [IsOrderedAddMonoid M] (φ : MvPolynomial σ R) {w : σ → M} (hw : ∀ i, 0 < w i) :
    weightedHomogeneousComponent w 0 φ = C (φ.coeff 0) := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent, coeff_C]
  by_cases hd : d = 0
  · subst hd
    simp
  · simp [(d.weight_eq_zero_iff_of_pos hw).not.mpr hd, Ne.symm hd]

section IntWeights

attribute [local instance] weightedGradedAlgebra

/-- For any `ℤ`-weight function `w : σ → ℤ` making `MvPolynomial σ R` a connected nonnegatively
graded `R`-algebra, the canonical graded augmentation agrees with `MvPolynomial.constantCoeff`. -/
@[simp]
theorem connectedAugmentation_weightedHomogeneousSubmodule_eq_constantCoeff
    (φ : MvPolynomial σ R) {w : σ → ℤ}
    (hneg : ∀ m < 0, weightedHomogeneousSubmodule R w m = ⊥)
    (hzero : ∀ ψ ∈ weightedHomogeneousSubmodule R w 0,
      ψ ∈ LinearMap.range (Algebra.linearMap R (MvPolynomial σ R))) :
    TauCeti.GradedAlgebra.connectedAugmentation hneg hzero φ = constantCoeff φ := by
  rcases subsingleton_or_nontrivial R with _ | _
  · exact Subsingleton.elim _ _
  have hw : ∀ i, 0 < w i := fun i ↦ by
    classical
    rcases lt_trichotomy (w i) 0 with hlt | h0 | hgt
    · have hX : (X i : MvPolynomial σ R) ∈ weightedHomogeneousSubmodule R w (w i) :=
        isWeightedHomogeneous_X R w i
      rw [hneg (w i) hlt, Submodule.mem_bot] at hX
      exact absurd (congrArg (·.coeff (Finsupp.single i 1)) hX) (by simp)
    · have hX : (X i : MvPolynomial σ R) ∈ weightedHomogeneousSubmodule R w 0 :=
        h0 ▸ isWeightedHomogeneous_X R w i
      obtain ⟨c, hc⟩ := hzero (X i) hX
      have h1 := congrArg (·.coeff (Finsupp.single i 1)) hc
      simp [Algebra.linearMap_apply, algebraMap_eq, coeff_C, eq_comm (a := (0 : σ →₀ ℕ))] at h1
    · exact hgt
  have h := congrArg constantCoeff
    (TauCeti.GradedAlgebra.algebraMap_connectedAugmentation hneg hzero φ)
  have hdec : (DirectSum.decompose (weightedHomogeneousSubmodule R w) φ 0 : MvPolynomial σ R) =
      weightedHomogeneousComponent w 0 φ :=
    weightedDecomposition.decompose'_apply R w φ 0
  rwa [algebraMap_eq, constantCoeff_C, hdec, φ.weightedHomogeneousComponent_zero_of_pos hw,
    constantCoeff_C] at h

end IntWeights

end MvPolynomial

namespace TauCeti

open MvPolynomial

section OrderedMonoid

variable (R : Type*) [CommSemiring R] {σ M : Type*}
  [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]

/-- For nonnegative weights `w : σ → M`, every weighted homogeneous submodule of strictly negative
degree vanishes. -/
theorem weightedHomogeneousSubmodule_eq_bot_of_lt_zero {w : σ → M} (hw : ∀ i, 0 ≤ w i) {m : M}
    (hm : m < 0) : weightedHomogeneousSubmodule R w m = ⊥ :=
  (Submodule.eq_bot_iff _).mpr fun _ hφ ↦
    IsWeightedHomogeneous.eq_zero_of_no_monomials hφ fun d ↦
      ne_of_gt (lt_of_lt_of_le hm (d.weight_nonneg hw))

/-- For strictly positive weights `w : σ → M`, the degree-zero weighted homogeneous submodule of
`MvPolynomial σ R` is the image of `algebraMap R (MvPolynomial σ R)`. -/
theorem weightedHomogeneousSubmodule_zero_eq_range {w : σ → M} (hw : ∀ i, 0 < w i) :
    weightedHomogeneousSubmodule R w 0 =
      LinearMap.range (Algebra.linearMap R (MvPolynomial σ R)) := by
  ext φ
  rw [mem_weightedHomogeneousSubmodule, LinearMap.mem_range]
  constructor
  · intro hφ
    refine ⟨φ.coeff 0, ?_⟩
    rw [Algebra.linearMap_apply, algebraMap_eq, C_apply]
    exact (IsWeightedHomogeneous.eq_monomial_of_unique_weight hφ
      fun d hd ↦ (d.weight_eq_zero_iff_of_pos hw).mp hd).symm
  · rintro ⟨c, rfl⟩
    rw [Algebra.linearMap_apply, algebraMap_eq]
    exact isWeightedHomogeneous_C w c

end OrderedMonoid

end TauCeti
