/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Covector
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.AlternatingForm

/-!
# The Hodge star of covectors

On an oriented finite-dimensional real inner product space `V` of dimension `n`, the covectors
`TauCeti.Covector V k` carry the Gram norm transported from `⋀ᵏ V`. For `k + l = n` the Hodge
star of `⋀ᵏ V` therefore transports to a linear isometric equivalence
`Orientation.covectorHodgeStar o hkl : Covector V k ≃ₗᵢ[ℝ] Covector V l`. On the underlying forms it
is `Orientation.formHodgeStar`, so it inherits the wedge identity `α ∧ ⋆β = ⟪α, β⟫ vol`, the law
`⋆⋆ = (-1) ^ (k l)` and the sign change under reversal of orientation. Since it is an isometry,
its adjoint is `(-1) ^ (k l) ⋆`: `⟪⋆α, β⟫ = (-1) ^ (k l) ⟪α, ⋆β⟫`.

The volume form has Gram norm one, being the star of the constant `1`, whose Gram norm is one
(`TauCeti.Covector.norm_toCovector_constOfIsEmpty`).

These are the pointwise identities behind the Hodge star of square-integrable differential forms
and the codifferential `δ = ± ⋆ d ⋆`. The pointwise identity `⟪⋆α, β⟫ = (-1) ^ (k l) ⟪α, ⋆β⟫` is
one ingredient, combined with the Leibniz rule and integration by parts, of the adjointness of the
codifferential to the exterior derivative.

## Main definitions

* `Orientation.covectorHodgeStar`: the Hodge star of covectors, a linear isometric equivalence.

## Main results

* `Orientation.ofCovector_covectorHodgeStar`: on the underlying forms it is
  `Orientation.formHodgeStar`.
* `Orientation.wedge_ofCovector_covectorHodgeStar_apply`: `α ∧ ⋆β = ⟪α, β⟫ vol`.
* `Orientation.covectorHodgeStar_covectorHodgeStar`: `⋆⋆α = (-1) ^ (k l) α`.
* `Orientation.inner_covectorHodgeStar_left`: `⟪⋆α, β⟫ = (-1) ^ (k l) ⟪α, ⋆β⟫`.
* `Orientation.norm_toCovector_volumeFormL`: the volume form has Gram norm one.

## References

* F. W. Warner, *Foundations of Differentiable Manifolds and Lie Groups*, Graduate Texts in
  Mathematics 94, Springer (1983), §6.1.
* D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques,
  and applications*, Acta Numerica 15 (2006), §2.
-/

public section

noncomputable section

open Module exteriorPower TauCeti TauCeti.Covector
open scoped RealInnerProductSpace

namespace Orientation

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {n : ℕ} [Fact (finrank ℝ V = n)] (o : Orientation ℝ V (Fin n)) {k l : ℕ}

/-- The Hodge star of covectors of degree `k` into covectors of degree `l`, for
`k + l = finrank ℝ V`: the Hodge star of `⋀ᵏ V` transported along the musical isometries
`TauCeti.Covector.toExteriorPower`. On the underlying forms it is `Orientation.formHodgeStar`
(`Orientation.ofCovector_covectorHodgeStar`). -/
def covectorHodgeStar (hkl : k + l = finrank ℝ V) : Covector V k ≃ₗᵢ[ℝ] Covector V l :=
  ((toExteriorPower V k).trans (o.hodgeStarIsometry hkl)).trans (toExteriorPower V l).symm

/-- The musical isometry sends the Hodge star of covectors to the Hodge star of `⋀ᵏ V`. -/
theorem toExteriorPower_covectorHodgeStar (hkl : k + l = finrank ℝ V) (α : Covector V k) :
    toExteriorPower V l (o.covectorHodgeStar hkl α) = o.hodgeStar hkl (toExteriorPower V k α) := by
  simp only [covectorHodgeStar, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply, hodgeStarIsometry_apply]

/-- On the underlying forms, the Hodge star of covectors is the Hodge star of forms. -/
@[simp]
theorem ofCovector_covectorHodgeStar (hkl : k + l = finrank ℝ V) (α : Covector V k) :
    (o.covectorHodgeStar hkl α).ofCovector = o.formHodgeStar hkl α.ofCovector := by
  apply (alternatingFormEquiv V l).symm.injective
  rw [← toExteriorPower_apply, toExteriorPower_covectorHodgeStar, toExteriorPower_apply,
    alternatingFormEquiv_symm_formHodgeStar]

/-- The Hodge star of a wrapped form is the wrapped Hodge star of the form. -/
@[simp]
theorem covectorHodgeStar_toCovector (hkl : k + l = finrank ℝ V) (α : V [⋀^Fin k]→L[ℝ] ℝ) :
    o.covectorHodgeStar hkl (toCovector α) = toCovector (o.formHodgeStar hkl α) := by
  ext1
  rw [ofCovector_covectorHodgeStar, ofCovector_toCovector, ofCovector_toCovector]

/-- **The wedge characterization of the Hodge star of covectors**: `α ∧ ⋆β = ⟪α, β⟫ vol` for
covectors `α, β` of degree `k`, where `vol` is the volume form of the orientation, read in degree
`k + l = finrank ℝ V`. -/
theorem wedge_ofCovector_covectorHodgeStar_apply (hkl : k + l = finrank ℝ V) (α β : Covector V k)
    (v : Fin (k + l) → V) :
    α.ofCovector.wedge (o.covectorHodgeStar hkl β).ofCovector v =
      ⟪α, β⟫ * o.volumeForm (v ∘ finCongr (hkl.trans Fact.out).symm) := by
  rw [ofCovector_covectorHodgeStar, o.wedge_formHodgeStar_apply, inner_eq_alternatingFormInner]

/-- **The square of the Hodge star of covectors**: `⋆⋆α = (-1) ^ (k l) α` for a covector `α` of
degree `k`, where `k + l = finrank ℝ V`. -/
theorem covectorHodgeStar_covectorHodgeStar (hkl : k + l = finrank ℝ V)
    (hlk : l + k = finrank ℝ V) (α : Covector V k) :
    o.covectorHodgeStar hlk (o.covectorHodgeStar hkl α) = (-1 : ℝ) ^ (k * l) • α := by
  ext1
  rw [ofCovector_covectorHodgeStar, ofCovector_covectorHodgeStar, o.formHodgeStar_formHodgeStar,
    ofCovector_smul]

/-- The inverse of the Hodge star of covectors is `(-1) ^ (k l)` times the Hodge star in the
complementary degree. -/
theorem covectorHodgeStar_symm_apply (hkl : k + l = finrank ℝ V) (hlk : l + k = finrank ℝ V)
    (β : Covector V l) :
    (o.covectorHodgeStar hkl).symm β = (-1 : ℝ) ^ (k * l) • o.covectorHodgeStar hlk β := by
  apply (o.covectorHodgeStar hkl).injective
  rw [LinearIsometryEquiv.apply_symm_apply, map_smul, mul_comm k l,
    o.covectorHodgeStar_covectorHodgeStar hlk hkl, smul_smul, ← pow_add, ← two_mul, pow_mul]
  simp

/-- **The adjoint of the Hodge star of covectors**: `⟪⋆α, β⟫ = (-1) ^ (k l) ⟪α, ⋆β⟫` for a
covector `α` of degree `k` and a covector `β` of degree `l`, where `k + l = finrank ℝ V`. -/
theorem inner_covectorHodgeStar_left (hkl : k + l = finrank ℝ V) (hlk : l + k = finrank ℝ V)
    (α : Covector V k) (β : Covector V l) :
    ⟪o.covectorHodgeStar hkl α, β⟫ = (-1 : ℝ) ^ (k * l) * ⟪α, o.covectorHodgeStar hlk β⟫ := by
  rw [← (toExteriorPower V l).inner_map_map, toExteriorPower_covectorHodgeStar,
    o.inner_hodgeStar_left hkl hlk, ← toExteriorPower_covectorHodgeStar,
    (toExteriorPower V k).inner_map_map]

/-- Reversing the orientation negates the Hodge star of covectors. -/
@[simp]
theorem covectorHodgeStar_neg_orientation (hkl : k + l = finrank ℝ V) (α : Covector V k) :
    (-o).covectorHodgeStar hkl α = -o.covectorHodgeStar hkl α := by
  ext1
  rw [ofCovector_covectorHodgeStar, ofCovector_neg, ofCovector_covectorHodgeStar,
    formHodgeStar_neg_orientation]

/-- The volume form of an orientation has Gram norm one. -/
@[simp]
theorem norm_toCovector_volumeFormL : ‖toCovector o.volumeFormL‖ = 1 := by
  have hn : 0 + n = finrank ℝ V := by rw [zero_add]; exact (Fact.out : finrank ℝ V = n).symm
  rw [← one_smul ℝ o.volumeFormL, ← o.formHodgeStar_constOfIsEmpty hn,
    ← covectorHodgeStar_toCovector, LinearIsometryEquiv.norm_map,
    norm_toCovector_constOfIsEmpty, abs_one]

end Orientation
