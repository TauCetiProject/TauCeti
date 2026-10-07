/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Base change of ideal sheaves

This file identifies the closed subscheme of an ideal sheaf pulled back along a fibre-product
projection with the corresponding base change. It also records the resulting preservation of
flatness for the closed subscheme, and the affine-local form of that flatness: over affine opens
`W ⊆ S` and `U ⊆ f⁻¹ W`, the quotient `Γ(X, U) ⧸ I(U)` is flat over `Γ(S, W)`
(`flat_appLE_comp_ofHom_quotient_mk`). Conversely, flatness of that quotient is exactly flatness
of the restricted subscheme morphism (`TauCeti.flat_resLE_subschemeι_iff`).
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {S T X : Scheme.{u}}

/-- The closed subscheme cut out by the pullback of an ideal sheaf along a fibre-product
projection is the base change of its original closed subscheme. -/
noncomputable def comapPullbackFstIso (I : X.IdealSheafData) (f : X ⟶ S)
    (g : T ⟶ S) :
    (I.comap (pullback.fst f g)).subscheme ≅ pullback (I.subschemeι ≫ f) g :=
  I.comapIso (pullback.fst f g) ≪≫
    pullbackSymmetry (pullback.fst f g) I.subschemeι ≪≫
      pullbackRightPullbackFstIso f g I.subschemeι

/-- The base-change comparison preserves the projection to the original closed subscheme. -/
@[reassoc (attr := simp)]
theorem comapPullbackFstIso_hom_fst (I : X.IdealSheafData) (f : X ⟶ S)
    (g : T ⟶ S) :
    (I.comapPullbackFstIso f g).hom ≫ pullback.fst (I.subschemeι ≫ f) g =
      subschemeMap _ _ (pullback.fst f g) (I.le_map_comap _) := by
  simp [comapPullbackFstIso, Category.assoc]

/-- The inverse base-change comparison preserves the projection to the original closed
subscheme. -/
@[reassoc (attr := simp)]
theorem comapPullbackFstIso_inv_fst (I : X.IdealSheafData) (f : X ⟶ S)
    (g : T ⟶ S) :
    (I.comapPullbackFstIso f g).inv ≫
        subschemeMap _ _ (pullback.fst f g) (I.le_map_comap _) =
      pullback.fst (I.subschemeι ≫ f) g := by
  rw [← comapPullbackFstIso_hom_fst, ← Category.assoc, Iso.inv_hom_id,
    Category.id_comp]

/-- The base-change comparison preserves the projection to the new base. -/
@[reassoc (attr := simp)]
theorem comapPullbackFstIso_hom_snd (I : X.IdealSheafData) (f : X ⟶ S)
    (g : T ⟶ S) :
    (I.comapPullbackFstIso f g).hom ≫ pullback.snd (I.subschemeι ≫ f) g =
      (I.comap (pullback.fst f g)).subschemeι ≫ pullback.snd f g := by
  simp [comapPullbackFstIso, Category.assoc]

/-- Flatness of the closed subscheme over the base is preserved by arbitrary base change. -/
theorem flat_comap_subschemeι_comp_snd (I : X.IdealSheafData) (f : X ⟶ S)
    (g : T ⟶ S) [Flat (I.subschemeι ≫ f)] :
    Flat ((I.comap (pullback.fst f g)).subschemeι ≫ pullback.snd f g) := by
  rw [← comapPullbackFstIso_hom_snd]
  infer_instance

/-- If the closed subscheme of `I` is flat over `S`, then over an affine open `W` of `S`, the
quotient `Γ(X, U) ⧸ I(U)` is flat over `Γ(S, W)` for every affine open `U ⊆ f⁻¹ W`. -/
theorem flat_appLE_comp_ofHom_quotient_mk (I : X.IdealSheafData) (f : X ⟶ S)
    [Flat (I.subschemeι ≫ f)] {W : S.Opens} (hW : IsAffineOpen W) (U : X.affineOpens)
    (hUW : U.1 ≤ f ⁻¹ᵁ W) :
    (f.appLE W U hUW ≫ CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U))).hom.Flat := by
  have h := (I.subschemeι ≫ f).flat_appLE hW (U.2.preimage I.subschemeι)
    ((Scheme.Hom.preimage_mono _ hUW).trans_eq rfl)
  rw [← Scheme.Hom.appLE_comp_appLE I.subschemeι f W U.1 _ hUW le_rfl,
    ← Scheme.Hom.app_eq_appLE, subschemeι_app, ← Category.assoc] at h
  exact (RingHom.Flat.respectsIso.cancel_right_isIso _ _).mp h

end AlgebraicGeometry.Scheme.IdealSheafData

namespace TauCeti

open AlgebraicGeometry AlgebraicGeometry.Scheme.IdealSheafData

variable {S X : Scheme.{u}}

/-- Flatness of the closed subscheme cut out by `I` over a pair of affine opens is equivalent
to flatness of its quotient algebra of sections over the base. -/
theorem flat_resLE_subschemeι_iff {I : X.IdealSheafData} {f : X ⟶ S}
    {W : S.Opens} (hW : IsAffineOpen W) (U : X.affineOpens)
    (hUW : U.1 ≤ f ⁻¹ᵁ W) :
    Flat ((I.subschemeι ≫ f).resLE W (I.subschemeι ⁻¹ᵁ U.1)
      ((Scheme.Hom.preimage_mono I.subschemeι hUW).trans_eq rfl)) ↔
      (f.appLE W U hUW ≫ CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U))).hom.Flat := by
  have : IsAffine W.toScheme := hW
  have : IsAffine (I.subschemeι ⁻¹ᵁ U.1).toScheme := U.2.preimage I.subschemeι
  rw [HasRingHomProperty.iff_of_isAffine (P := @Flat),
    RingHom.Flat.respectsIso.arrow_mk_iso_iff (arrowResLEAppIso _ _ _ _),
    ← Scheme.Hom.appLE_comp_appLE I.subschemeι f W U.1 _ hUW le_rfl,
    ← Scheme.Hom.app_eq_appLE, subschemeι_app, ← Category.assoc]
  exact RingHom.Flat.respectsIso.cancel_right_isIso _ _

end TauCeti
