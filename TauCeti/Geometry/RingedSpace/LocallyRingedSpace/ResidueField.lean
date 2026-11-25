/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace.ResidueField
public import TauCeti.Geometry.RingedSpace.LocallyRingedSpace.Restrict

/-!
# Residue-field evaluation and vanishing ideals on locally ringed spaces

On an open restriction `L.restrict U.isOpenEmbedding` of a locally ringed space `L` to
`U : Opens L`, evaluating a section `s ∈ Γ(U, O_L)` at `x ∈ U` and applying the canonical
residue-field map of `L.ofRestrict U.isOpenEmbedding` agrees with global evaluation `Γevaluation`
on `L.restrict U.isOpenEmbedding` after transporting `s` along
`PresheafedSpace.restrictTopSectionsIso`.

The file also defines `AlgebraicGeometry.LocallyRingedSpace.vanishingIdeal X U`, the radical ideal
in `Γ(U, O_X)` of sections vanishing in the residue field at every point of `U`, together with its
membership, radicality, pullback along morphisms and isomorphisms, and compatibility with open
restrictions.

## Main definitions

* `AlgebraicGeometry.LocallyRingedSpace.vanishingIdeal`: the radical ideal in `Γ(U, O_X)` of
  sections vanishing in the residue field at every point of `U`.

## Main results

* `AlgebraicGeometry.LocallyRingedSpace.residueFieldMap_injective` and
  `AlgebraicGeometry.LocallyRingedSpace.residueFieldMap_eq_zero_iff`: `residueFieldMap f x` is
  injective and reflects zero.
* `AlgebraicGeometry.LocallyRingedSpace.residueFieldMap_ofRestrict_evaluation`: compatibility of
  `LocallyRingedSpace.evaluation` on `U` with `LocallyRingedSpace.Γevaluation` on
  `L.restrict U.isOpenEmbedding`.
* `AlgebraicGeometry.LocallyRingedSpace.mem_vanishingIdeal`,
  `AlgebraicGeometry.LocallyRingedSpace.mem_vanishingIdeal_top`: membership characterizations for
  `vanishingIdeal`.
* `AlgebraicGeometry.LocallyRingedSpace.isRadical_vanishingIdeal`,
  `AlgebraicGeometry.LocallyRingedSpace.radical_vanishingIdeal`: `X.vanishingIdeal U` is radical.
* `AlgebraicGeometry.LocallyRingedSpace.vanishingIdeal_le_comap`,
  `AlgebraicGeometry.LocallyRingedSpace.comap_vanishingIdeal_of_subset_range`,
  `AlgebraicGeometry.LocallyRingedSpace.comap_vanishingIdeal_top_of_surjective`: functoriality and
  pullback of `vanishingIdeal` along morphisms whose range covers `V`.
* `AlgebraicGeometry.LocallyRingedSpace.comap_vanishingIdeal_of_iso`,
  `AlgebraicGeometry.LocallyRingedSpace.comap_vanishingIdeal_top_of_iso`: pullback of
  `vanishingIdeal` along isomorphisms of locally ringed spaces.
* `AlgebraicGeometry.LocallyRingedSpace.comap_vanishingIdeal_restrictTopSectionsIso_hom`,
  `AlgebraicGeometry.LocallyRingedSpace.comap_vanishingIdeal_restrictTopSectionsIso_inv`:
  compatibility of `vanishingIdeal` with open restriction `X.restrict U.isOpenEmbedding`.
-/

public section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.LocallyRingedSpace

/-- The residue-field homomorphism induced by a morphism of locally ringed spaces is injective. -/
theorem residueFieldMap_injective {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (x : X) :
    Function.Injective (residueFieldMap f x) :=
  RingHom.injective ((residueFieldMap f x).hom : Y.residueField (f.base x) →+* X.residueField x)

-- In `simp`, `@map_eq_zero` already simplifies `residueFieldMap f x a = 0`; this explicit lemma
-- supports `rw` and term-mode rewrites where `CommRingCat` hom coercions block `rw [map_eq_zero]`.
/-- A residue-field homomorphism induced by a morphism of locally ringed spaces reflects zero. -/
theorem residueFieldMap_eq_zero_iff {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (x : X)
    (a : Y.residueField (f.base x)) :
    residueFieldMap f x a = 0 ↔ a = 0 :=
  map_eq_zero ((residueFieldMap f x).hom : Y.residueField (f.base x) →+* X.residueField x)

/-- Evaluating `s ∈ Γ(U, O_L)` at `x ∈ U` and mapping into the residue field of
`L.restrict U.isOpenEmbedding` agrees with global evaluation on `L.restrict U.isOpenEmbedding`
under `PresheafedSpace.restrictTopSectionsIso`. -/
theorem residueFieldMap_ofRestrict_evaluation (L : LocallyRingedSpace.{u}) (U : Opens L)
    (x : L.restrict U.isOpenEmbedding) (s : L.presheaf.obj (op U)) :
    have hx : x ∈ (Opens.map (L.ofRestrict U.isOpenEmbedding).base).obj U :=
      (Opens.inclusion'_map_eq_top U).symm ▸ Opens.mem_top x
    residueFieldMap (L.ofRestrict U.isOpenEmbedding) x
        (L.evaluation ⟨(L.ofRestrict U.isOpenEmbedding).base x, hx⟩ s) =
      (L.restrict U.isOpenEmbedding).Γevaluation x
        ((L.toPresheafedSpace.restrictTopSectionsIso U).hom s) := by
  let j : L.restrict U.isOpenEmbedding ⟶ L := L.ofRestrict U.isOpenEmbedding
  have hU : (Opens.map j.base).obj U = (⊤ : Opens (L.restrict U.isOpenEmbedding)) :=
    Opens.inclusion'_map_eq_top U
  have hxU : x ∈ (Opens.map j.base).obj U := hU.symm ▸ Opens.mem_top x
  let sTop : (L.restrict U.isOpenEmbedding).presheaf.obj (op ⊤) :=
    (L.toPresheafedSpace.restrictTopSectionsIso U).hom s
  have hmap : (L.toPresheafedSpace.restrictTopSectionsIso U).hom ≫
      (L.restrict U.isOpenEmbedding).presheaf.map (homOfLE hU.le).op = j.c.app (op U) := by
    have hjc : j.c.app (op U) = (L.toPresheafedSpace.ofRestrict U.isOpenEmbedding).c.app (op U) :=
      rfl
    rw [hjc, PresheafedSpace.ofRestrict_c_app, PresheafedSpace.restrictTopSectionsIso_hom]
    exact (L.presheaf.map_comp _ _).symm.trans (congrArg L.presheaf.map (Subsingleton.elim _ _))
  have hs : j.c.app (op U) s =
      (L.restrict U.isOpenEmbedding).presheaf.map (homOfLE hU.le).op sTop :=
    (ConcreteCategory.congr_hom hmap s).symm.trans (ConcreteCategory.comp_apply _ _ s)
  have hgerm : (L.restrict U.isOpenEmbedding).presheaf.germ ((Opens.map j.base).obj U) x hxU
      (j.c.app (op U) s) =
      (L.restrict U.isOpenEmbedding).presheaf.germ ⊤ x (Opens.mem_top x) sTop := by
    rw [hs]
    exact TopCat.Presheaf.germ_res_apply (L.restrict U.isOpenEmbedding).presheaf
      (homOfLE hU.le) x hxU sTop
  have heval : (L.restrict U.isOpenEmbedding).evaluation ⟨x, hxU⟩ (j.c.app (op U) s) =
      (L.restrict U.isOpenEmbedding).Γevaluation x sTop := by
    rw [Γevaluation, evaluation, evaluation, ConcreteCategory.comp_apply,
      ConcreteCategory.comp_apply, hgerm]
  exact (evaluation_naturality_apply j ⟨x, hxU⟩ s).trans heval

section VanishingIdeal

/-- The ideal of sections over `U` vanishing in the residue field at every point of `U`. -/
noncomputable def vanishingIdeal (X : LocallyRingedSpace.{u}) (U : Opens X) :
    Ideal (X.presheaf.obj (op U)) :=
  ⨅ x : U, RingHom.ker (X.evaluation x).hom

/-- A section `s ∈ Γ(U, O_X)` belongs to `X.vanishingIdeal U` if and only if it vanishes in the
residue field at every point of `U`. -/
@[simp]
theorem mem_vanishingIdeal {X : LocallyRingedSpace.{u}} {U : Opens X}
    {s : X.presheaf.obj (op U)} :
    s ∈ X.vanishingIdeal U ↔ ∀ x : U, X.evaluation x s = 0 := by
  simp [vanishingIdeal, RingHom.mem_ker]

/-- A global section belongs to `X.vanishingIdeal ⊤` if and only if it vanishes in the residue
field at every point of `X`. -/
theorem mem_vanishingIdeal_top {X : LocallyRingedSpace.{u}} {s : X.presheaf.obj (op ⊤)} :
    s ∈ X.vanishingIdeal ⊤ ↔ ∀ x : X, X.Γevaluation x s = 0 := by
  rw [mem_vanishingIdeal]
  exact ⟨fun h x ↦ h ⟨x, Opens.mem_top x⟩, fun h ⟨x, _⟩ ↦ h x⟩

/-- The vanishing ideal on any open is radical, being an intersection of prime ideals. -/
theorem isRadical_vanishingIdeal (X : LocallyRingedSpace.{u}) (U : Opens X) :
    (X.vanishingIdeal U).IsRadical := by
  intro s hs
  rw [mem_vanishingIdeal]
  intro x
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hs
  exact eq_zero_of_pow_eq_zero (by simpa only [map_pow] using mem_vanishingIdeal.mp hn x)

/-- The radical of `X.vanishingIdeal U` equals `X.vanishingIdeal U`. -/
@[simp]
theorem radical_vanishingIdeal (X : LocallyRingedSpace.{u}) (U : Opens X) :
    (X.vanishingIdeal U).radical = X.vanishingIdeal U :=
  (X.isRadical_vanishingIdeal U).radical

/-- Any morphism `f : X ⟶ Y` of locally ringed spaces sends `Y.vanishingIdeal V` into the
vanishing ideal of `f ⁻¹' V` on `X`. -/
theorem vanishingIdeal_le_comap {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (V : Opens Y) :
    Y.vanishingIdeal V ≤
      (X.vanishingIdeal ((Opens.map f.base).obj V)).comap (f.c.app (op V)).hom := by
  intro s hs
  refine Ideal.mem_comap.mpr (mem_vanishingIdeal.mpr fun x ↦ ?_)
  exact (evaluation_naturality_apply f x s).symm.trans
    ((residueFieldMap_eq_zero_iff f x.val _).mpr
      (mem_vanishingIdeal.mp hs ⟨f.base x.val, x.property⟩))

/-- If `V ⊆ Set.range f.base`, the preimage of `X.vanishingIdeal (f ⁻¹' V)` along `f.c.app (op V)`
equals `Y.vanishingIdeal V`. -/
theorem comap_vanishingIdeal_of_subset_range {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)
    {V : Opens Y} (hV : (V : Set Y) ⊆ Set.range f.base) :
    (X.vanishingIdeal ((Opens.map f.base).obj V)).comap (f.c.app (op V)).hom =
      Y.vanishingIdeal V := by
  refine le_antisymm ?_ (vanishingIdeal_le_comap f V)
  intro s hs
  have hs' := mem_vanishingIdeal.mp (Ideal.mem_comap.mp hs)
  refine mem_vanishingIdeal.mpr fun y ↦ ?_
  obtain ⟨x, hx⟩ := hV y.property
  have hxV : x ∈ (Opens.map f.base).obj V := Opens.mem_map.mpr (hx.symm ▸ y.property)
  have hev : residueFieldMap f x (Y.evaluation ⟨f.base x, hxV⟩ s) = 0 :=
    (evaluation_naturality_apply f ⟨x, hxV⟩ s).trans (hs' ⟨x, hxV⟩)
  have hyx : (⟨f.base x, hxV⟩ : V) = y := Subtype.ext hx
  exact hyx ▸ (residueFieldMap_eq_zero_iff f x _).mp hev

/-- A morphism `f : X ⟶ Y` with surjective base map pulls `X.vanishingIdeal ⊤` back to
`Y.vanishingIdeal ⊤` on global sections. -/
theorem comap_vanishingIdeal_top_of_surjective {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)
    (hf : Function.Surjective f.base) :
    (X.vanishingIdeal ⊤).comap (f.c.app (op ⊤)).hom = Y.vanishingIdeal ⊤ :=
  comap_vanishingIdeal_of_subset_range f (hf.range_eq.symm ▸ Set.subset_univ _)

/-- An isomorphism `e : X ≅ Y` of locally ringed spaces pulls `X.vanishingIdeal (e ⁻¹' V)` back to
`Y.vanishingIdeal V` along `e.hom.c.app (op V)`. -/
theorem comap_vanishingIdeal_of_iso {X Y : LocallyRingedSpace.{u}} (e : X ≅ Y) (V : Opens Y) :
    (X.vanishingIdeal ((Opens.map e.hom.base).obj V)).comap (e.hom.c.app (op V)).hom =
      Y.vanishingIdeal V :=
  comap_vanishingIdeal_of_subset_range e.hom
    ((TopCat.homeoOfIso (forgetToTop.mapIso e)).surjective.range_eq.symm ▸ Set.subset_univ _)

/-- An isomorphism `e : X ≅ Y` of locally ringed spaces pulls `X.vanishingIdeal ⊤` back to
`Y.vanishingIdeal ⊤` along `e.hom.c.app (op ⊤)`. -/
theorem comap_vanishingIdeal_top_of_iso {X Y : LocallyRingedSpace.{u}} (e : X ≅ Y) :
    (X.vanishingIdeal ⊤).comap (e.hom.c.app (op ⊤)).hom = Y.vanishingIdeal ⊤ :=
  comap_vanishingIdeal_top_of_surjective e.hom
    (TopCat.homeoOfIso (forgetToTop.mapIso e)).surjective

/-- Under `PresheafedSpace.restrictTopSectionsIso`, the global vanishing ideal on
`X.restrict U.isOpenEmbedding` pulls back to `X.vanishingIdeal U`. -/
theorem comap_vanishingIdeal_restrictTopSectionsIso_hom (X : LocallyRingedSpace.{u}) (U : Opens X) :
    ((X.restrict U.isOpenEmbedding).vanishingIdeal ⊤).comap
        (CommRingCat.Hom.hom (R := X.presheaf.obj (op U))
          (S := (X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤))
          (X.toPresheafedSpace.restrictTopSectionsIso U).hom) =
      X.vanishingIdeal U :=
  Ideal.ext fun s ↦ Ideal.mem_comap.trans <| mem_vanishingIdeal_top.trans <|
    (forall_congr' fun x ↦
      (X.evaluation_eq_zero_iff_restrict_Γevaluation_eq_zero U x s).symm).trans
      mem_vanishingIdeal.symm

/-- Under `(PresheafedSpace.restrictTopSectionsIso U).inv`, `X.vanishingIdeal U` pulls back to the
global vanishing ideal on `X.restrict U.isOpenEmbedding`. -/
theorem comap_vanishingIdeal_restrictTopSectionsIso_inv (X : LocallyRingedSpace.{u}) (U : Opens X) :
    (X.vanishingIdeal U).comap
        (CommRingCat.Hom.hom (R := (X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤))
          (S := X.presheaf.obj (op U))
          (X.toPresheafedSpace.restrictTopSectionsIso U).inv) =
      (X.restrict U.isOpenEmbedding).vanishingIdeal ⊤ := by
  refine Ideal.ext fun s ↦ Ideal.mem_comap.trans ?_
  rw [← comap_vanishingIdeal_restrictTopSectionsIso_hom X U]
  refine Ideal.mem_comap.trans (Iff.of_eq ?_)
  have hs : (X.toPresheafedSpace.restrictTopSectionsIso U).hom
      ((X.toPresheafedSpace.restrictTopSectionsIso U).inv s) = s :=
    Iso.inv_hom_id_apply (X.toPresheafedSpace.restrictTopSectionsIso U) s
  exact congrArg (· ∈ (X.restrict U.isOpenEmbedding).vanishingIdeal ⊤) hs

end VanishingIdeal

end AlgebraicGeometry.LocallyRingedSpace
