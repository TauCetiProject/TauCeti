/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import TauCeti.RingTheory.GradedAlgebra.Connected
import TauCeti.RingTheory.MvPolynomial.WeightedHomogeneous.PositiveWeight

/-!
# Connected augmentation of positively weighted polynomial rings

Specializing `TauCeti.GradedAlgebra.connectedAugmentation` to `MvPolynomial σ R` with a `ℤ`-weight
function `w : σ → ℤ` that makes `MvPolynomial σ R` a connected nonnegatively graded `R`-algebra
recovers `MvPolynomial.constantCoeff`.

## Main results

* `MvPolynomial.connectedAugmentation_weightedHomogeneousSubmodule_eq_constantCoeff`:
  agreement of `GradedAlgebra.connectedAugmentation` with `MvPolynomial.constantCoeff`.
-/

public section

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R]

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

end MvPolynomial
