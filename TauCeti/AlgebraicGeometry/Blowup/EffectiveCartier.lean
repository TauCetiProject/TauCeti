/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Blowup.Exceptional
public import TauCeti.AlgebraicGeometry.Blowup.IdealSheaf

/-!
# Effective Cartier divisors on the blowup along an ideal sheaf

On the blowup `Bl_I X ⟶ X` of an arbitrary scheme `X` along an arbitrary ideal sheaf `I`, the
exceptional divisor `I.comap I.blowupToBase` is an effective Cartier divisor, and more generally
the inverse image `D.comap I.blowupToBase` of any effective Cartier divisor `D` on `X` remains an
effective Cartier divisor.

These results depend only on the affine-chart description of `Bl_I X` (`Blowup.IdealSheaf`) and the
affine exceptional divisor (`Blowup.Exceptional`), without pulling in the universal property of the
blowup.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.comap_blowupChart_comap_blowupToBase`: on the chart
  over an affine open `U`, the exceptional divisor of `Bl_I X` is the exceptional divisor of the
  blowup of `Spec Γ(X, U)` along `V(I(U))`.
* `AlgebraicGeometry.Scheme.IdealSheafData.isEffectiveCartier_comap_blowupToBase`: the exceptional
  divisor of `Bl_I X` is an effective Cartier divisor.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier.comap_blowupToBase`: pullback of an
  effective Cartier divisor along an arbitrary blowup is an effective Cartier divisor.

## References

* [The Stacks Project, Tag 01OF](https://stacks.math.columbia.edu/tag/01OF): blowing up along a
  quasi-coherent sheaf of ideals.
-/

public section

noncomputable section

open CategoryTheory reesAlgebra

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

open TauCeti.AlgebraicGeometry

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- **The exceptional divisor on an affine chart.** Over an affine open `U` of `X`, the inverse
image of the centre `V(I)` under the blowup `Bl_I X ⟶ X`, restricted to the chart
`Proj Γ(X, U)[I(U)t]` over `U`, is the exceptional divisor of the blowup of `Spec Γ(X, U)` along
`V(I(U))`. -/
theorem comap_blowupChart_comap_blowupToBase {U : X.Opens} (hU : IsAffineOpen U) :
    (I.comap I.blowupToBase).comap (I.blowupChart hU) =
      (ofIdealTop ((I.ideal ⟨U, hU⟩).map (Scheme.ΓSpecIso Γ(X, U)).inv.hom)).comap
        (Proj.toSpecCoeff (grade (I.ideal ⟨U, hU⟩))) := by
  rw [← comap_comp, blowupChart_blowupToBase, comap_comp, comap_fromSpec_eq_ofIdealTop]

/-- **The exceptional divisor is an effective Cartier divisor.** The inverse image of the centre
`V(I)` under the blowup `Bl_I X ⟶ X` along an arbitrary ideal sheaf `I` is an effective Cartier
divisor on `Bl_I X`. -/
theorem isEffectiveCartier_comap_blowupToBase : (I.comap I.blowupToBase).IsEffectiveCartier := by
  refine isEffectiveCartier_of_forall_exists_isOpenImmersion _ fun x ↦ ?_
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show I.blowupToBase x ∈ ⊤ from trivial)
  refine ⟨_, I.blowupChart hU, inferInstance, ?_, ?_⟩
  · rw [← Scheme.Hom.coe_opensRange, opensRange_blowupChart]
    exact hxU
  · rw [comap_blowupChart_comap_blowupToBase, toSpecCoeff_reesAlgebra]
    exact isEffectiveCartier_comap_toSpecZero_reesAlgebra (I.ideal ⟨U, hU⟩)

/-- **Pullback of an effective Cartier divisor along an arbitrary blowup.** For any scheme `X`,
any ideal sheaf `I`, and any effective Cartier divisor `D` on `X`, the inverse image
`D.comap I.blowupToBase` on `Bl_I X` is again an effective Cartier divisor. No flatness,
integrality, reducedness, or Noetherian assumption is needed. -/
theorem IsEffectiveCartier.comap_blowupToBase {D : X.IdealSheafData} (hD : D.IsEffectiveCartier)
    (I : X.IdealSheafData) : (D.comap I.blowupToBase).IsEffectiveCartier := by
  refine isEffectiveCartier_of_forall_exists_isOpenImmersion _ fun x ↦ ?_
  obtain ⟨U, hxU, d, hd, hDd⟩ := (isEffectiveCartier_iff D).mp hD (I.blowupToBase x)
  have hU : IsAffineOpen U.val := U.property
  refine ⟨_, I.blowupChart hU, inferInstance, ?_, ?_⟩
  · rw [← Scheme.Hom.coe_opensRange, opensRange_blowupChart]
    exact hxU
  · rw [← comap_comp, blowupChart_blowupToBase, comap_comp, comap_fromSpec_eq_ofIdealTop, hDd,
      Ideal.map_span, Set.image_singleton]
    exact Ideal.isEffectiveCartier_comap_toSpecCoeff_span_singleton (I.ideal ⟨U.val, hU⟩) hd

end AlgebraicGeometry.Scheme.IdealSheafData
