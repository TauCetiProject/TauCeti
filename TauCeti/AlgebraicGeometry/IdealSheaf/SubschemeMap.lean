/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Maps between closed subschemes on sections

Let `f : X ⟶ Y` be a morphism of schemes, and let `I` and `J` be ideal sheaves on `X` and `Y` with
`J ≤ I.map f`, so that `f` restricts to the morphism `subschemeMap I J f H : V(I) ⟶ V(J)` of
closed subschemes. This file describes that morphism on sections.

For opens `U ⊆ Y` and `V ⊆ f⁻¹ U`, restricting sections to the closed subschemes commutes with
the section maps of `f` and of `subschemeMap I J f H` (`subschemeι_app_subschemeMap_appLE`).
Consequently, when `U` and `V` are affine, the section map `Γ(Y, U) ⟶ Γ(X, V)` of `f` carries
`J(U)` into `I(V)` (`ideal_le_comap_ideal_of_le_map`), and under the identifications
`Γ(V(J), U) ≅ Γ(Y, U) ⧸ J(U)` and `Γ(V(I), V) ≅ Γ(X, V) ⧸ I(V)` the section map of
`subschemeMap I J f H` is the induced map of quotients (`subschemeMap_appLE`).

For the pullback ideal sheaf `I.comap f`, the square formed by `subschemeMap`, `f` and the two
closed immersions is cartesian (`isPullback_comap_subschemeι`).
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}} {I : X.IdealSheafData} {J : Y.IdealSheafData} {f : X ⟶ Y}

/-- The inverse image under `subschemeMap I J f H` of the part of `V(J)` over an open `U` of `Y`
is the part of `V(I)` over `f⁻¹ U`. -/
theorem preimage_subschemeMap (H : J ≤ I.map f) (U : Y.Opens) :
    subschemeMap I J f H ⁻¹ᵁ (J.subschemeι ⁻¹ᵁ U) = I.subschemeι ⁻¹ᵁ (f ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, subschemeMap_subschemeι, Scheme.Hom.comp_preimage]

/-- **Restriction to closed subschemes commutes with section maps.** For opens `U ⊆ Y` and
`V ⊆ f⁻¹ U`, restricting a section of `𝒪_Y` over `U` to `V(J)` and then applying
`subschemeMap I J f H` agrees with applying `f` and then restricting to `V(I)`. -/
@[reassoc]
theorem subschemeι_app_subschemeMap_appLE (H : J ≤ I.map f) (U : Y.Opens) (V : X.Opens)
    (hVU : V ≤ f ⁻¹ᵁ U) :
    J.subschemeι.app U ≫ (subschemeMap I J f H).appLE (J.subschemeι ⁻¹ᵁ U)
        (I.subschemeι ⁻¹ᵁ V)
        ((I.subschemeι.preimage_mono hVU).trans (preimage_subschemeMap H U).ge) =
      f.appLE U V hVU ≫ I.subschemeι.app V := by
  rw [I.subschemeι.app_eq_appLE]
  refine ((Scheme.Hom.comp_appLE (subschemeMap I J f H) J.subschemeι U _ _).symm.trans ?_).trans
    (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  -- The two composites agree as morphisms; their section maps then agree by proof irrelevance.
  congr 1
  exact subschemeMap_subschemeι I J f H

/-- If `J ≤ I.map f`, the section map of `f` over affine opens `U` and `V ⊆ f⁻¹ U` carries the
ideal `J(U)` into `I(V)`. -/
theorem ideal_le_comap_ideal_of_le_map (H : J ≤ I.map f) (U : Y.affineOpens)
    (V : X.affineOpens) (hVU : V.val ≤ f ⁻¹ᵁ U.val) :
    J.ideal U ≤ (I.ideal V).comap (f.appLE U V hVU).hom := by
  intro a ha
  rw [← ker_subschemeι_app] at ha
  rw [Ideal.mem_comap, ← ker_subschemeι_app, RingHom.mem_ker, ← CommRingCat.comp_apply,
    ← subschemeι_app_subschemeMap_appLE H, CommRingCat.comp_apply, RingHom.mem_ker.mp ha,
    map_zero]

/-- **The map of closed subschemes on affine charts.** If `J ≤ I.map f`, then over affine opens
`U` and `V ⊆ f⁻¹ U`, the section map of `subschemeMap I J f H` is, under the identifications
`Γ(V(J), U) ≅ Γ(Y, U) ⧸ J(U)` and `Γ(V(I), V) ≅ Γ(X, V) ⧸ I(V)`, the map of quotients induced by
the section map `f.appLE U V` of `f`. -/
theorem subschemeMap_appLE (H : J ≤ I.map f) (U : Y.affineOpens) (V : X.affineOpens)
    (hVU : V.val ≤ f ⁻¹ᵁ U.val) :
    (subschemeMap I J f H).appLE (J.subschemeι ⁻¹ᵁ U.val) (I.subschemeι ⁻¹ᵁ V.val)
        ((I.subschemeι.preimage_mono hVU).trans (preimage_subschemeMap H U.val).ge) =
      (J.subschemeObjIso U).hom ≫
        CommRingCat.ofHom (Ideal.quotientMap (I.ideal V) (f.appLE U V hVU).hom
          (ideal_le_comap_ideal_of_le_map H U V hVU)) ≫
        (I.subschemeObjIso V).inv := by
  have := ConcreteCategory.epi_of_surjective _ (J.subschemeι_app_surjective U)
  rw [← cancel_epi (J.subschemeι.app U), subschemeι_app_subschemeMap_appLE H U V hVU,
    subschemeι_app, subschemeι_app, Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc,
    ← Category.assoc, ← CommRingCat.ofHom_comp, Ideal.quotientMap_comp_mk, CommRingCat.ofHom_comp,
    CommRingCat.ofHom_hom]

/-- **The pullback square of a pullback ideal sheaf.** The closed subscheme of `I.comap f` is the
fibre product of `f` with the closed immersion of `I`, along the maps `(I.comap f).subschemeι`
and `subschemeMap`. -/
theorem isPullback_comap_subschemeι (I : Y.IdealSheafData) (f : X ⟶ Y) :
    IsPullback (I.comap f).subschemeι (subschemeMap (I.comap f) I f (I.le_map_comap f)) f
      I.subschemeι :=
  .of_iso_pullback ⟨(subschemeMap_subschemeι _ _ _ _).symm⟩ (I.comapIso f) (by simp) (by simp)

end AlgebraicGeometry.Scheme.IdealSheafData
