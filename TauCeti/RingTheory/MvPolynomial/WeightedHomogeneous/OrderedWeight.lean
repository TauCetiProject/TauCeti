/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import TauCeti.Data.Finsupp.Weight

/-!
# Nonnegatively and positively weighted polynomial rings over ordered additive monoids

For a weight function `w : σ → M` taking values in an ordered additive commutative monoid `M`:

* if `0 ≤ w i` for every variable `i`, then every weighted homogeneous polynomial of negative
  weight vanishes (`MvPolynomial.IsWeightedHomogeneous.eq_zero_of_neg`,
  `MvPolynomial.weightedHomogeneousSubmodule_eq_bot_of_neg`);
* if `0 < w i` for every variable `i`, then `d.weight w = 0 ↔ d = 0`, so every weighted homogeneous
  polynomial of weight zero is constant (`MvPolynomial.IsWeightedHomogeneous.eq_C_coeff_zero`), the
  degree-zero weighted homogeneous component of `φ : MvPolynomial σ R` is `C (φ.coeff 0)`, and the
  degree-zero weighted homogeneous submodule is the image of
  `algebraMap R (MvPolynomial σ R)`.

Note that Mathlib's `MvPolynomial.weightedHomogeneousComponent_zero` and
`Finsupp.weight_eq_zero_iff_eq_zero` assume `[CanonicallyOrderedAdd M]`, which holds for `ℕ` but not
for `ℤ`.

## Main results

* `MvPolynomial.IsWeightedHomogeneous.eq_zero_of_neg`: for nonnegative weights, weighted homogeneous
  polynomials of negative weight vanish.
* `MvPolynomial.weightedHomogeneousSubmodule_eq_bot_of_neg`: for nonnegative weights, the weighted
  homogeneous submodules of negative weight vanish.
* `MvPolynomial.IsWeightedHomogeneous.eq_C_coeff_zero`: for positive weights, a weighted
  homogeneous polynomial of weight zero is constant.
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

/-- For nonnegative weights, a weighted homogeneous polynomial of negative weight vanishes. -/
theorem IsWeightedHomogeneous.eq_zero_of_neg {w : σ → M} {φ : MvPolynomial σ R} {n : M}
    (hφ : φ.IsWeightedHomogeneous w n) (hw : ∀ i, 0 ≤ w i) (hn : n < 0) : φ = 0 := by
  ext d
  by_contra hd
  have h0 : 0 ≤ Finsupp.weight w d := by
    rw [Finsupp.weight_apply]
    exact Finsupp.sum_nonneg fun i _ ↦ nsmul_nonneg (hw i) _
  exact (hφ hd ▸ h0).not_gt hn

/-- For positive weights, a weighted homogeneous polynomial of weight zero is a constant. -/
theorem IsWeightedHomogeneous.eq_C_coeff_zero {w : σ → M} {φ : MvPolynomial σ R}
    (hφ : φ.IsWeightedHomogeneous w 0) (hw : ∀ i, 0 < w i) : φ = C (φ.coeff 0) := by
  classical
  ext d
  rw [coeff_C]
  split_ifs with hd
  · rw [hd]
  by_contra hcoeff
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 (Ne.symm hd)
  have := Finsupp.le_weight_of_ne_zero (fun j ↦ (hw j).le) hi
  rw [hφ hcoeff] at this
  exact (hw i).not_ge this

/-- For nonnegative weights, the weighted homogeneous submodules of negative weight vanish. -/
theorem weightedHomogeneousSubmodule_eq_bot_of_neg {w : σ → M} (hw : ∀ i, 0 ≤ w i) {n : M}
    (hn : n < 0) : weightedHomogeneousSubmodule R w n = ⊥ :=
  (Submodule.eq_bot_iff _).2 fun _ hφ ↦ IsWeightedHomogeneous.eq_zero_of_neg hφ hw hn

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
