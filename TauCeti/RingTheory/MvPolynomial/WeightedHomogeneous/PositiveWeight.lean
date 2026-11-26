/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import TauCeti.Data.Finsupp.Weight

/-!
# Positively weighted polynomial rings over ordered additive monoids

For a weight function `w : σ → M` taking values in an ordered additive commutative monoid `M`,
if `0 < w i` for every variable `i`, then `d.weight w = 0 ↔ d = 0`, so the degree-zero weighted
homogeneous component of `φ : MvPolynomial σ R` is `C (φ.coeff 0)` and the degree-zero weighted
homogeneous submodule is the image of `algebraMap R (MvPolynomial σ R)`.

Note that Mathlib's `MvPolynomial.weightedHomogeneousComponent_zero` and
`Finsupp.weight_eq_zero_iff_eq_zero` assume `[CanonicallyOrderedAdd M]`, which holds for `ℕ` but not
for `ℤ`.

## Main results

* `MvPolynomial.weightedHomogeneousComponent_zero_of_pos`: degree-zero weighted homogeneous
  component for strictly positive weights in an ordered additive monoid.
* `MvPolynomial.weightedHomogeneousSubmodule_zero_eq_range`: degree-zero characterization of
  `MvPolynomial.weightedHomogeneousSubmodule R w`.
* `MvPolynomial.weight_pos_of_connected`: converse positivity of weights when
  `MvPolynomial.weightedHomogeneousSubmodule R w` is connected and nonnegatively graded over a
  nontrivial ring.
-/

public section

namespace MvPolynomial

section OrderedAddMonoid

variable {σ R M : Type*} [CommSemiring R] [AddCommMonoid M] [PartialOrder M]
  [IsOrderedAddMonoid M]

/-- If every variable has strictly positive weight in an ordered additive commutative monoid `M`,
the degree-zero weighted homogeneous component of `φ` is `C (φ.coeff 0)`. -/
@[simp]
theorem weightedHomogeneousComponent_zero_of_pos (φ : MvPolynomial σ R) {w : σ → M}
    (hw : ∀ i, 0 < w i) :
    weightedHomogeneousComponent w 0 φ = C (φ.coeff 0) := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent, coeff_C]
  by_cases hd : d = 0
  · subst hd
    simp
  · simp [(d.weight_eq_zero_iff_of_pos hw).not.mpr hd, Ne.symm hd]

variable (R) in
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
    rw [Algebra.linearMap_apply, algebraMap_eq, ← φ.weightedHomogeneousComponent_zero_of_pos hw]
    exact weightedHomogeneousComponent_eq_self hφ
  · rintro ⟨c, rfl⟩
    rw [Algebra.linearMap_apply, algebraMap_eq]
    exact isWeightedHomogeneous_C w c

end OrderedAddMonoid

section LinearOrder

variable {σ R M : Type*} [CommSemiring R] [Nontrivial R] [AddCommMonoid M] [LinearOrder M]

/-- If `MvPolynomial σ R` is nonnegatively `M`-graded and connected for a weight function
`w : σ → M` over a nontrivial ring `R`, then every variable has strictly positive weight. -/
theorem weight_pos_of_connected {w : σ → M}
    (hneg : ∀ m < 0, weightedHomogeneousSubmodule R w m = ⊥)
    (hzero : ∀ ψ ∈ weightedHomogeneousSubmodule R w 0,
      ψ ∈ LinearMap.range (Algebra.linearMap R (MvPolynomial σ R))) (i : σ) :
    0 < w i := by
  classical
  rcases lt_trichotomy (w i) 0 with hlt | h0 | hgt
  · have hX : (X i : MvPolynomial σ R) ∈ weightedHomogeneousSubmodule R w (w i) :=
      isWeightedHomogeneous_X R w i
    rw [hneg (w i) hlt, Submodule.mem_bot] at hX
    exact absurd hX (X_ne_zero i)
  · have hX : (X i : MvPolynomial σ R) ∈ weightedHomogeneousSubmodule R w 0 :=
      h0 ▸ isWeightedHomogeneous_X R w i
    obtain ⟨c, hc⟩ := hzero (X i) hX
    have h1 := congrArg (·.coeff (Finsupp.single i 1)) hc
    simp [eq_comm (a := (0 : σ →₀ ℕ))] at h1
  · exact hgt

end LinearOrder

end MvPolynomial
