/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Affine charts of a closed immersion

Let `j : X ⟶ Z` be a closed immersion and `U` an affine open of `Z`. Over `U`, the closed
subscheme `X` is `Spec (Γ(Z, U) ⧸ I(U))`, for `I = ker j` the ideal sheaf of `j`. This file
records the corresponding open immersion

`j.affineChart U : Spec (Γ(Z, U) ⧸ I(U)) ⟶ X`,

the chart of Mathlib's cover `I.subschemeCover` of the closed subscheme `V(I)`, transported to `X`
along `j.toImage : X ⟶ V(I)`, which is an isomorphism because `j` is a closed immersion
(`asIso j.toImage : X ≅ V(I)`). Composed with `j`, it is the closed immersion
`Spec (Γ(Z, U) ⧸ I(U)) ⟶ Spec Γ(Z, U)` followed by the open immersion `U.fromSpec` into `Z`
(`affineChart_comp`), and its image is `j⁻¹ U` (`mem_range_affineChart_iff`).

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.affineChart j U`: the open immersion
  `Spec (Γ(Z, U) ⧸ (ker j)(U)) ⟶ X`.
* `AlgebraicGeometry.Scheme.Hom.affineChart_comp`: composed with `j`, it is the quotient map
  followed by `U.fromSpec`.
* `AlgebraicGeometry.Scheme.Hom.mem_range_affineChart_iff`, `opensRange_affineChart`: its image is
  the preimage of `U`.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Z : Scheme.{u}} (j : X ⟶ Z) [IsClosedImmersion j] (U : Z.affineOpens)

/-- The affine chart `Spec (Γ(Z, U) ⧸ I(U)) ⟶ X` of a closed immersion `j : X ⟶ Z` over an affine
open `U` of `Z`, for `I = ker j`: the member of Mathlib's cover `I.subschemeCover` of the closed
subscheme `V(I)` over `U`, followed by the inverse of the isomorphism `j.toImage : X ⟶ V(I)`. -/
noncomputable def affineChart : Spec (.of (Γ(Z, U) ⧸ j.ker.ideal U)) ⟶ X :=
  j.ker.subschemeCover.f U ≫ inv j.toImage

/-- The affine chart is the member of `(ker j).subschemeCover` over `U`, followed by the inverse
of `j.toImage`. -/
theorem affineChart_def : j.affineChart U = j.ker.subschemeCover.f U ≫ inv j.toImage :=
  (rfl)

/-- The affine chart of a closed immersion is an open immersion. -/
instance isOpenImmersion_affineChart : IsOpenImmersion (j.affineChart U) :=
  have := j.ker.subschemeCover.map_prop U
  IsOpenImmersion.comp (j.ker.subschemeCover.f U) _

/-- Composed with `j`, the affine chart over `U` is the closed immersion
`Spec (Γ(Z, U) ⧸ I(U)) ⟶ Spec Γ(Z, U)` followed by the open immersion `U.fromSpec` into `Z`. -/
@[reassoc]
theorem affineChart_comp :
    j.affineChart U ≫ j =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (j.ker.ideal U))) ≫ U.property.fromSpec := by
  have h : j.affineChart U ≫ j = j.ker.subschemeCover.f U ≫ j.ker.subschemeι :=
    (Category.assoc _ _ _).trans
      (congrArg (_ ≫ ·) ((IsIso.inv_comp_eq _).mpr j.toImage_imageι.symm))
  exact h.trans ((j.ker.subschemeCover_map_subschemeι U).trans (Category.assoc _ _ _))

/-- The open image of the affine chart over `U` is the preimage of `U`. -/
@[simp]
theorem opensRange_affineChart : (j.affineChart U).opensRange = j ⁻¹ᵁ U.val := by
  have := j.ker.subschemeCover.map_prop U
  refine (Scheme.Hom.opensRange_comp (j.ker.subschemeCover.f U) (inv j.toImage)).trans ?_
  -- Transport the image of the cover member, computed by Mathlib, along `j.toImage`.
  refine (congrArg ((asIso j.toImage).inv ''ᵁ ·) (j.ker.opensRange_subschemeCover_map U)).trans ?_
  rw [Scheme.Hom.inv_image, asIso_hom, ← Scheme.Hom.comp_preimage, j.toImage_imageι]

/-- A point of `X` lies in the image of the affine chart over `U` exactly when its image under `j`
lies in `U`. -/
theorem mem_range_affineChart_iff {x : X} : x ∈ Set.range (j.affineChart U) ↔ j x ∈ U.val := by
  rw [← Scheme.Hom.coe_opensRange, SetLike.mem_coe, opensRange_affineChart,
    Scheme.Hom.mem_preimage]

end AlgebraicGeometry.Scheme.Hom
