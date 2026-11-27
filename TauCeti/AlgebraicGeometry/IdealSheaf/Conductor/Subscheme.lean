/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.Conductor.Basic
public import TauCeti.AlgebraicGeometry.IdealSheaf.SubschemeMap

import TauCeti.AlgebraicGeometry.IdealSheaf.Affine

/-!
# The canonical map between conductor subschemes

Let `f : X ⟶ Y` be a finite morphism of schemes with conductor ideal sheaf `I = f.conductor` on
`Y`, and let `J = I.comap f` be its inverse image on `X`. The closed subschemes `C = V(I)` of `Y`
and `D = V(J)` of `X` are the **conductor subschemes** of `f`, and `f` restricts to the
**conductor map** `f.conductorSubschemeMap : D ⟶ C`. Together with `f` and the two closed
immersions it forms the cartesian square

```
D ──→ X
│     │ f
↓     ↓
C ──→ Y
```

(`AlgebraicGeometry.Scheme.Hom.isPullback_conductorSubschemeMap`), so the conductor map is finite.
For the normalization of a reduced curve this is the map from the conductor subscheme of the
normalization to the conductor subscheme of the curve, along which the curve is recovered from its
normalization by pinching.

Over an affine open `U` of `Y`, put `A = Γ(Y, U)`, `B = Γ(X, f⁻¹ U)` and `f_U : A → B`. The ideal
`J(f⁻¹ U)` is exactly the ambient conductor `K = c(f_U(A), B)` of the image of `A`, the largest
ideal of `B` contained in `f_U(A)`, and not just an ideal with the same radical
(`AlgebraicGeometry.Scheme.Hom.ideal_comap_conductor`). Under the identifications
`Γ(C, U) ≅ A ⧸ I(U)` and `Γ(D, f⁻¹ U) ≅ B ⧸ K`, the conductor map is the map `A ⧸ I(U) → B ⧸ K`
induced by `f_U` (`AlgebraicGeometry.Scheme.Hom.conductorSubschemeMap_appLE`).

No reducedness, Noetherian, birationality or schematic dominance hypothesis is needed.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.conductorSubschemeMap f`: the conductor map `V(f.conductor.comap f)
  ⟶ V(f.conductor)` of a finite morphism `f`.
* `AlgebraicGeometry.Scheme.Hom.conductorComapObjIso f U`: the sections of the source conductor
  subscheme over `f⁻¹ U` are `Γ(X, f⁻¹ U)` modulo the ambient conductor.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isPullback_conductorSubschemeMap`: the conductor square is
  cartesian.
* `AlgebraicGeometry.Scheme.Hom.ideal_comap_conductor`: the source conductor ideal over `f⁻¹ U`
  is the ambient conductor of the image of `Γ(Y, U)`.
* `AlgebraicGeometry.Scheme.Hom.map_conductor_ideal`: the target conductor ideal extends to the
  ambient conductor.
* `AlgebraicGeometry.Scheme.Hom.conductorSubschemeMap_appLE`: on affine charts the conductor map is
  the induced map of quotient rings.
* `AlgebraicGeometry.Scheme.Hom.isIso_conductorSubschemeMap_iff_of_conductor_eq_bot`: when the
  conductor is zero, the conductor map is an isomorphism exactly when `f` is.

## References

* D. Ferrand, *Conducteur, descente et pincement*, Bull. Soc. Math. France 131 (2003),
  Introduction and Théorème 5.1.
* J. Witaszek, *Relative semiampleness in mixed characteristic*, Definition 2.27.
* [Stacks Project, Lemma 0C6L](https://stacks.math.columbia.edu/tag/0C6L).
-/

public section

noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]

section Ideal

/-- The image of the conductor ideal over an affine open `U` under the section map of `f` is the
ambient conductor of the image of `Γ(Y, U)` in `Γ(X, f⁻¹ U)`, as a set. -/
theorem image_conductor_ideal (U : Y.affineOpens) :
    (f.app U).hom '' f.conductor.ideal U = (f.app U).hom.range.conductor := by
  let := (f.app U).hom.toAlgebra
  rw [conductor_ideal]
  exact TauCeti.Algebra.image_conductor

/-- Extending the conductor ideal over an affine open `U` along the section map of `f` gives the
ambient conductor of the image of `Γ(Y, U)` in `Γ(X, f⁻¹ U)`. -/
theorem map_conductor_ideal (U : Y.affineOpens) :
    (f.conductor.ideal U).map (f.app U).hom = (f.app U).hom.range.conductor := by
  let := (f.app U).hom.toAlgebra
  rw [conductor_ideal]
  exact TauCeti.Algebra.map_conductor

/-- **The source conductor ideal.** Over the inverse image of an affine open `U`, the inverse image
of the conductor ideal sheaf of `f` is the ambient conductor of the image of `Γ(Y, U)` in
`Γ(X, f⁻¹ U)`: the largest ideal of `Γ(X, f⁻¹ U)` contained in that image. -/
theorem ideal_comap_conductor (U : Y.affineOpens) :
    (f.conductor.comap f).ideal ⟨f ⁻¹ᵁ U, U.property.preimage f⟩ =
      (f.app U).hom.range.conductor := by
  rw [f.conductor.ideal_comap_of_le f U ⟨f ⁻¹ᵁ U, U.property.preimage f⟩ le_rfl,
    Scheme.Hom.appLE_eq_app, map_conductor_ideal]

/-- The section map of `f` over an affine open `U` carries the conductor ideal into the ambient
conductor of its image. -/
theorem conductor_ideal_le_comap (U : Y.affineOpens) :
    f.conductor.ideal U ≤ (f.app U).hom.range.conductor.comap (f.app U).hom := by
  simpa [ideal_comap_conductor, Scheme.Hom.appLE_eq_app] using
    Scheme.IdealSheafData.ideal_le_comap_ideal_of_le_map (f.conductor.le_map_comap f) U
      ⟨f ⁻¹ᵁ U, U.property.preimage f⟩ le_rfl

/-- A section `b` over `f⁻¹ U` lies in the source conductor ideal exactly when `b * c` lies in the
image of `Γ(Y, U)` for every section `c` over `f⁻¹ U`. -/
theorem mem_ideal_comap_conductor_iff {U : Y.affineOpens} {b : Γ(X, f ⁻¹ᵁ U)} :
    b ∈ (f.conductor.comap f).ideal ⟨f ⁻¹ᵁ U, U.property.preimage f⟩ ↔
      ∀ c : Γ(X, f ⁻¹ᵁ U), ∃ a : Γ(Y, U), f.app U a = b * c := by
  simp [ideal_comap_conductor, eq_comm]

end Ideal

/-- The **conductor map** of a finite morphism `f : X ⟶ Y`: the restriction of `f` to the closed
subscheme of `X` cut out by the inverse image of the conductor of `f`, landing in the conductor
closed subscheme of `Y`. -/
def conductorSubschemeMap : (f.conductor.comap f).subscheme ⟶ f.conductor.subscheme :=
  Scheme.IdealSheafData.subschemeMap _ _ f (f.conductor.le_map_comap f)

/-- The conductor map is the map of closed subschemes induced by `f`. -/
theorem conductorSubschemeMap_eq_subschemeMap :
    f.conductorSubschemeMap =
      Scheme.IdealSheafData.subschemeMap _ _ f (f.conductor.le_map_comap f) :=
  (rfl)

/-- The conductor map followed by the target conductor inclusion is the source conductor inclusion
followed by `f`. -/
@[reassoc (attr := simp)]
theorem conductorSubschemeMap_subschemeι :
    f.conductorSubschemeMap ≫ f.conductor.subschemeι = (f.conductor.comap f).subschemeι ≫ f :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

/-- **The conductor square is cartesian.** The source conductor subscheme is the fibre product of
`f` with the target conductor subscheme. -/
theorem isPullback_conductorSubschemeMap :
    IsPullback (f.conductor.comap f).subschemeι f.conductorSubschemeMap f
      f.conductor.subschemeι :=
  f.conductor.isPullback_comap_subschemeι f

/-- The conductor map is finite, being a base change of `f`. -/
instance : IsFinite f.conductorSubschemeMap :=
  MorphismProperty.of_isPullback (P := @IsFinite) f.isPullback_conductorSubschemeMap ‹_›

/-- The conductor map is the only morphism between the conductor subschemes compatible with `f`
and the closed immersions. -/
theorem eq_conductorSubschemeMap
    {g : (f.conductor.comap f).subscheme ⟶ f.conductor.subscheme}
    (hg : g ≫ f.conductor.subschemeι = (f.conductor.comap f).subschemeι ≫ f) :
    g = f.conductorSubschemeMap := by
  rw [← cancel_mono f.conductor.subschemeι, hg, conductorSubschemeMap_subschemeι]

/-- The inverse image under the conductor map of the part of the target conductor subscheme over
an open `U` is the part of the source conductor subscheme over `f⁻¹ U`. -/
theorem preimage_conductorSubschemeMap (U : Y.Opens) :
    f.conductorSubschemeMap ⁻¹ᵁ (f.conductor.subschemeι ⁻¹ᵁ U) =
      (f.conductor.comap f).subschemeι ⁻¹ᵁ (f ⁻¹ᵁ U) :=
  Scheme.IdealSheafData.preimage_subschemeMap _ U

/-- On sections over an open `U` of `Y`, restricting to the target conductor subscheme and then
applying the conductor map agrees with applying `f` and then restricting to the source conductor
subscheme. -/
@[reassoc]
theorem subschemeι_app_conductorSubschemeMap_appLE (U : Y.Opens) :
    f.conductor.subschemeι.app U ≫ f.conductorSubschemeMap.appLE (f.conductor.subschemeι ⁻¹ᵁ U)
        ((f.conductor.comap f).subschemeι ⁻¹ᵁ (f ⁻¹ᵁ U))
        (f.preimage_conductorSubschemeMap U).ge =
      f.app U ≫ (f.conductor.comap f).subschemeι.app (f ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.appLE_eq_app f]
  exact Scheme.IdealSheafData.subschemeι_app_subschemeMap_appLE _ U _ le_rfl

section Chart

variable (U : Y.affineOpens)

/-- Over the inverse image of an affine open `U`, the sections of the source conductor subscheme
are `Γ(X, f⁻¹ U)` modulo the ambient conductor of the image of `Γ(Y, U)`. -/
def conductorComapObjIso :
    Γ((f.conductor.comap f).subscheme, (f.conductor.comap f).subschemeι ⁻¹ᵁ (f ⁻¹ᵁ U)) ≅
      CommRingCat.of (Γ(X, f ⁻¹ᵁ U) ⧸ (f.app U).hom.range.conductor) :=
  (f.conductor.comap f).subschemeObjIso ⟨f ⁻¹ᵁ U, U.property.preimage f⟩ ≪≫
    (Ideal.quotEquivOfEq (f.ideal_comap_conductor U)).toCommRingCatIso

/-- Restricting a section over `f⁻¹ U` to the source conductor subscheme and reading it in the
chart `conductorComapObjIso` gives its class modulo the ambient conductor. -/
@[reassoc (attr := simp)]
theorem subschemeι_app_conductorComapObjIso_hom :
    (f.conductor.comap f).subschemeι.app (f ⁻¹ᵁ U) ≫ (f.conductorComapObjIso U).hom =
      CommRingCat.ofHom (Ideal.Quotient.mk (f.app U).hom.range.conductor) := by
  rw [conductorComapObjIso, Iso.trans_hom, ← Category.assoc,
    Scheme.IdealSheafData.subschemeι_app _ ⟨f ⁻¹ᵁ U, U.property.preimage f⟩]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  ext b
  exact Ideal.quotEquivOfEq_mk (f.ideal_comap_conductor U) b

/-- **The conductor map on affine charts.** Over an affine open `U`, under the identifications
`Γ(V(f.conductor), U) ≅ Γ(Y, U) ⧸ f.conductor(U)` and `conductorComapObjIso`, the conductor map is
the map `Γ(Y, U) ⧸ f.conductor(U) → Γ(X, f⁻¹ U) ⧸ K` induced by the section map of `f`, where `K`
is the ambient conductor of its image. -/
theorem conductorSubschemeMap_appLE :
    f.conductorSubschemeMap.appLE (f.conductor.subschemeι ⁻¹ᵁ U)
        ((f.conductor.comap f).subschemeι ⁻¹ᵁ (f ⁻¹ᵁ U))
        (f.preimage_conductorSubschemeMap U).ge ≫ (f.conductorComapObjIso U).hom =
      (f.conductor.subschemeObjIso U).hom ≫
        CommRingCat.ofHom (Ideal.quotientMap (f.app U).hom.range.conductor (f.app U).hom
          (f.conductor_ideal_le_comap U)) := by
  refine (congrArg (· ≫ _) (Scheme.IdealSheafData.subschemeMap_appLE _ U
    ⟨f ⁻¹ᵁ U, U.property.preimage f⟩ le_rfl)).trans ?_
  simp only [conductorComapObjIso, Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc]
  congr 1
  ext a
  simp [Scheme.Hom.appLE_eq_app]

end Chart

section Iso

/-- The conductor map of an isomorphism is an isomorphism. -/
instance [IsIso f] : IsIso f.conductorSubschemeMap :=
  f.isPullback_conductorSubschemeMap.isIso_snd_of_isIso

/-- **The conductor map when the conductor vanishes.** If the conductor of `f` is zero, both
conductor subschemes are the whole schemes, and the conductor map is an isomorphism exactly when
`f` is. -/
theorem isIso_conductorSubschemeMap_iff_of_conductor_eq_bot (h : f.conductor = ⊥) :
    IsIso f.conductorSubschemeMap ↔ IsIso f := by
  have : IsIso f.conductor.subschemeι :=
    (Scheme.isIso_subschemeι_iff_eq_bot _).mpr h
  have : IsIso (f.conductor.comap f).subschemeι :=
    (Scheme.isIso_subschemeι_iff_eq_bot _).mpr (by
      rw [h, Scheme.IdealSheafData.comap_bot])
  rw [← isIso_comp_right_iff f.conductorSubschemeMap f.conductor.subschemeι,
    conductorSubschemeMap_subschemeι, isIso_comp_left_iff]

end Iso

end AlgebraicGeometry.Scheme.Hom
