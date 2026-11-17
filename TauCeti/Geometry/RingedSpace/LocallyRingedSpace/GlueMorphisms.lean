/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.RingedSpace.OpenImmersion
public import TauCeti.Geometry.RingedSpace.PresheafedSpace.Restrict

import TauCeti.Geometry.RingedSpace.PresheafedSpace.GlueMorphisms

/-!
# Gluing morphisms out of a locally ringed space

Let `X` and `Y` be locally ringed spaces, and let `U i` be a family of opens covering `X`.
Morphisms of locally ringed spaces `f i : X|_{U i} ⟶ Y` agreeing on the overlaps glue to a unique
morphism `X ⟶ Y` restricting to each `f i` (EGA I, Ch. I, 2.2.4 and 10.4.6).

The underlying morphisms of presheafed spaces glue by
`AlgebraicGeometry.PresheafedSpace.glueMorphisms`, using that the forgetful functor from locally
ringed spaces to presheafed spaces preserves pullbacks along open immersions. Locality of the
glued stalk map at a point `x ∈ U i` follows by composing with the local stalk map of the open
inclusion `X|_{U i} ⟶ X`.

We also provide the inclusion `restrictHomOfLE : X|_V ⟶ X|_W` for nested opens `V ≤ W`, and the
canonical identification of `X|_{U ∩ V}` with the pullback of `X|_U ⟶ X` and `X|_V ⟶ X`, so that
overlap compatibility for gluing can be checked directly on `X|_{U i ⊓ U j}`.

## Main definitions

* `AlgebraicGeometry.LocallyRingedSpace.restrictHomOfLE`: the inclusion `X|_V ⟶ X|_W` for `V ≤ W`.
* `AlgebraicGeometry.LocallyRingedSpace.restrictInfIsoPullback`: the canonical isomorphism
  `X|_{U ⊓ V} ≅ X|_U ×_X X|_V`.
* `AlgebraicGeometry.LocallyRingedSpace.glueMorphisms`: the morphism glued from a family of
  morphisms out of the restrictions of `X` to an open cover, agreeing on the overlaps.

## Main results

* `AlgebraicGeometry.LocallyRingedSpace.restrictHomOfLE_ofRestrict`: composing `X|_V ⟶ X|_W`
  with `X|_W ⟶ X` gives `X|_V ⟶ X`.
* `AlgebraicGeometry.LocallyRingedSpace.ofRestrict_glueMorphisms`: the glued morphism restricts to
  the given morphism on each open of the cover.
* `AlgebraicGeometry.LocallyRingedSpace.hom_ext_of_ofRestrict`: two morphisms out of `X` agreeing
  on every open of a cover are equal.
* `AlgebraicGeometry.LocallyRingedSpace.pullback_fst_comp_eq_of_restrictHomOfLE`: overlap
  compatibility on the pullback follows from equality on `X|_{U ⊓ V}`.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. I, 2.2.4 and 10.4.6.
-/

public section

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.LocallyRingedSpace

universe w u

section RestrictHomOfLE

variable (X : LocallyRingedSpace.{u})

/-- For opens `V ≤ W` of a locally ringed space `X`, the inclusion `X|_V ⟶ X|_W` of restrictions. -/
@[expose]
def restrictHomOfLE {V W : Opens X} (h : V ≤ W) :
    X.restrict V.isOpenEmbedding ⟶ X.restrict W.isOpenEmbedding where
  toHom := X.toPresheafedSpace.restrictHomOfLE h
  prop x := by
    let x' : X.toPresheafedSpace.restrict V.isOpenEmbedding := x
    have hfac := PresheafedSpace.restrictHomOfLE_ofRestrict X.toPresheafedSpace h
    have hisoComp : IsIso ((X.toPresheafedSpace.restrictHomOfLE h ≫
        X.toPresheafedSpace.ofRestrict W.isOpenEmbedding).stalkMap x') := by
      rw [PresheafedSpace.stalkMap.congr_hom _ _ hfac x']
      have : IsIso ((X.toPresheafedSpace.ofRestrict V.isOpenEmbedding).stalkMap x') :=
        PresheafedSpace.IsOpenImmersion.stalk_iso _ _
      exact IsIso.comp_isIso
    rw [PresheafedSpace.stalkMap.comp] at hisoComp
    have hisoW : IsIso ((X.toPresheafedSpace.ofRestrict W.isOpenEmbedding).stalkMap
        ((X.toPresheafedSpace.restrictHomOfLE h).base x')) :=
      PresheafedSpace.IsOpenImmersion.stalk_iso _ _
    have : IsIso ((X.toPresheafedSpace.restrictHomOfLE h).stalkMap x') :=
      @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ hisoW hisoComp
    exact isLocalHom_of_isIso ((X.toPresheafedSpace.restrictHomOfLE h).stalkMap x')

/-- The underlying presheafed-space morphism of `restrictHomOfLE`. -/
@[simp]
theorem restrictHomOfLE_toHom {V W : Opens X} (h : V ≤ W) :
    (X.restrictHomOfLE h).toHom = X.toPresheafedSpace.restrictHomOfLE h :=
  (rfl)

/-- The base map of `restrictHomOfLE` is the inclusion `V ⟶ W`. -/
theorem restrictHomOfLE_base {V W : Opens X} (h : V ≤ W) :
    (X.restrictHomOfLE h).base = (Opens.toTopCat X.toTopCat).map (homOfLE h) :=
  (rfl)

/-- The sheaf component of `restrictHomOfLE` is the corresponding restriction map of
`X.presheaf`. -/
@[simp]
theorem restrictHomOfLE_c_app {V W : Opens X} (h : V ≤ W)
    (Q : (Opens (X.restrict W.isOpenEmbedding))ᵒᵖ) :
    (X.restrictHomOfLE h).c.app Q =
      X.presheaf.map (homOfLE (Opens.functor_obj_map_homOfLE_obj_le h Q.unop)).op :=
  (rfl)

/-- The inclusion `X|_V ⟶ X|_W` followed by `X|_W ⟶ X` is `X|_V ⟶ X`. -/
@[reassoc (attr := simp)]
theorem restrictHomOfLE_ofRestrict {V W : Opens X} (h : V ≤ W) :
    X.restrictHomOfLE h ≫ X.ofRestrict W.isOpenEmbedding = X.ofRestrict V.isOpenEmbedding :=
  Hom.ext' (X.toPresheafedSpace.restrictHomOfLE_ofRestrict h)

/-- The inclusion of a restriction into itself is the identity. -/
@[simp]
theorem restrictHomOfLE_refl (V : Opens X) :
    X.restrictHomOfLE (le_refl V) = 𝟙 (X.restrict V.isOpenEmbedding) := by
  rw [← cancel_mono (X.ofRestrict V.isOpenEmbedding), restrictHomOfLE_ofRestrict, Category.id_comp]

/-- Inclusions between restrictions to nested opens compose. -/
@[reassoc (attr := simp)]
theorem restrictHomOfLE_comp {U V W : Opens X} (h : U ≤ V) (k : V ≤ W) :
    X.restrictHomOfLE h ≫ X.restrictHomOfLE k = X.restrictHomOfLE (h.trans k) := by
  rw [← cancel_mono (X.ofRestrict W.isOpenEmbedding), Category.assoc, restrictHomOfLE_ofRestrict,
    restrictHomOfLE_ofRestrict, restrictHomOfLE_ofRestrict]

/-- The inclusion `X|_V ⟶ X|_W` of restrictions to nested opens is an open immersion. -/
instance isOpenImmersion_restrictHomOfLE {V W : Opens X} (h : V ≤ W) :
    IsOpenImmersion (X.restrictHomOfLE h) := by
  have hr : Set.range (X.ofRestrict V.isOpenEmbedding).base ⊆
      Set.range (X.ofRestrict W.isOpenEmbedding).base := by
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨x.1, h x.2⟩, rfl⟩
  have heq : X.restrictHomOfLE h =
      IsOpenImmersion.lift (X.ofRestrict W.isOpenEmbedding) (X.ofRestrict V.isOpenEmbedding) hr :=
    IsOpenImmersion.lift_uniq _ _ hr _ (X.restrictHomOfLE_ofRestrict h)
  rw [heq]
  have := IsOpenImmersion.pullback_snd_isIso_of_range_subset
    (X.ofRestrict W.isOpenEmbedding) (X.ofRestrict V.isOpenEmbedding) hr
  dsimp only [IsOpenImmersion.lift]
  infer_instance

/-- The canonical isomorphism between `X|_{U ⊓ V}` and the pullback of `X|_U ⟶ X` and `X|_V ⟶ X`. -/
noncomputable def restrictInfIsoPullback (U V : Opens X) :
    X.restrict (U ⊓ V).isOpenEmbedding ≅
      pullback (X.ofRestrict U.isOpenEmbedding) (X.ofRestrict V.isOpenEmbedding) := by
  have hrange : Set.range (pullback.fst (X.ofRestrict U.isOpenEmbedding)
      (X.ofRestrict V.isOpenEmbedding) ≫ X.ofRestrict U.isOpenEmbedding).base ⊆
      Set.range (X.ofRestrict (U ⊓ V).isOpenEmbedding).base := by
    rintro _ ⟨z, rfl⟩
    have hU : (pullback.fst (X.ofRestrict U.isOpenEmbedding)
        (X.ofRestrict V.isOpenEmbedding) ≫ X.ofRestrict U.isOpenEmbedding).base z ∈ U :=
      ((pullback.fst (X.ofRestrict U.isOpenEmbedding)
        (X.ofRestrict V.isOpenEmbedding)).base z).2
    have hV : (pullback.fst (X.ofRestrict U.isOpenEmbedding)
        (X.ofRestrict V.isOpenEmbedding) ≫ X.ofRestrict U.isOpenEmbedding).base z ∈ V := by
      rw [pullback.condition]
      exact ((pullback.snd (X.ofRestrict U.isOpenEmbedding)
        (X.ofRestrict V.isOpenEmbedding)).base z).2
    exact ⟨⟨_, hU, hV⟩, rfl⟩
  refine
    { hom := pullback.lift (X.restrictHomOfLE (inf_le_left : U ⊓ V ≤ U))
        (X.restrictHomOfLE (inf_le_right : U ⊓ V ≤ V)) (by simp)
      inv := IsOpenImmersion.lift (X.ofRestrict (U ⊓ V).isOpenEmbedding)
        (pullback.fst _ _ ≫ X.ofRestrict U.isOpenEmbedding) hrange
      hom_inv_id := by
        rw [← cancel_mono (X.ofRestrict (U ⊓ V).isOpenEmbedding), Category.assoc,
          IsOpenImmersion.lift_fac, pullback.lift_fst_assoc, restrictHomOfLE_ofRestrict,
          Category.id_comp]
      inv_hom_id := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, Category.id_comp,
            ← cancel_mono (X.ofRestrict U.isOpenEmbedding), Category.assoc,
            restrictHomOfLE_ofRestrict, IsOpenImmersion.lift_fac]
        · rw [Category.assoc, pullback.lift_snd, Category.id_comp,
            ← cancel_mono (X.ofRestrict V.isOpenEmbedding), Category.assoc,
            restrictHomOfLE_ofRestrict, IsOpenImmersion.lift_fac, pullback.condition] }

/-- Composing `restrictInfIsoPullback` with `pullback.fst` recovers
`restrictHomOfLE inf_le_left`. -/
@[reassoc (attr := simp)]
theorem restrictInfIsoPullback_hom_fst (U V : Opens X) :
    (X.restrictInfIsoPullback U V).hom ≫
        pullback.fst (X.ofRestrict U.isOpenEmbedding) (X.ofRestrict V.isOpenEmbedding) =
      X.restrictHomOfLE (inf_le_left : U ⊓ V ≤ U) :=
  pullback.lift_fst _ _ _

/-- Composing `restrictInfIsoPullback` with `pullback.snd` recovers
`restrictHomOfLE inf_le_right`. -/
@[reassoc (attr := simp)]
theorem restrictInfIsoPullback_hom_snd (U V : Opens X) :
    (X.restrictInfIsoPullback U V).hom ≫
        pullback.snd (X.ofRestrict U.isOpenEmbedding) (X.ofRestrict V.isOpenEmbedding) =
      X.restrictHomOfLE (inf_le_right : U ⊓ V ≤ V) :=
  pullback.lift_snd _ _ _

/-- Overlap compatibility on the pullback of two open restrictions follows from equality on the
intersection `U ⊓ V`. -/
theorem pullback_fst_comp_eq_of_restrictHomOfLE {Y : LocallyRingedSpace.{u}} {U V : Opens X}
    {f : X.restrict U.isOpenEmbedding ⟶ Y} {g : X.restrict V.isOpenEmbedding ⟶ Y}
    (h : X.restrictHomOfLE (inf_le_left : U ⊓ V ≤ U) ≫ f =
      X.restrictHomOfLE (inf_le_right : U ⊓ V ≤ V) ≫ g) :
    pullback.fst (X.ofRestrict U.isOpenEmbedding) (X.ofRestrict V.isOpenEmbedding) ≫ f =
      pullback.snd _ _ ≫ g := by
  rw [← cancel_epi (X.restrictInfIsoPullback U V).hom,
    restrictInfIsoPullback_hom_fst_assoc, restrictInfIsoPullback_hom_snd_assoc]
  exact h

end RestrictHomOfLE

section Glue

variable {X Y : LocallyRingedSpace.{u}} {ι : Type w} (U : ι → Opens X) (hU : ⨆ i, U i = ⊤)
  (f : ∀ i, X.restrict (U i).isOpenEmbedding ⟶ Y)
  (hf : ∀ i j, pullback.fst (X.ofRestrict (U i).isOpenEmbedding)
    (X.ofRestrict (U j).isOpenEmbedding) ≫ f i = pullback.snd _ _ ≫ f j)

include hf in
/-- The overlap condition descends to the underlying morphisms of presheafed spaces, because the
forgetful functor preserves pullbacks along open immersions. -/
private theorem toHom_pullback_condition (i j : ι) :
    pullback.fst (X.toPresheafedSpace.ofRestrict (U i).isOpenEmbedding)
        (X.toPresheafedSpace.ofRestrict (U j).isOpenEmbedding) ≫ (f i).toHom =
      pullback.snd _ _ ≫ (f j).toHom := by
  let F := forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace
  have h := congrArg (fun k ↦ (PreservesPullback.iso F
    (X.ofRestrict (U i).isOpenEmbedding) (X.ofRestrict (U j).isOpenEmbedding)).inv ≫ F.map k)
    (hf i j)
  simp only [Functor.map_comp, PreservesPullback.iso_inv_fst_assoc,
    PreservesPullback.iso_inv_snd_assoc] at h
  exact h

/-- **Gluing morphisms out of a locally ringed space.** If the opens `U i` cover `X` and the
morphisms `f i : X|_{U i} ⟶ Y` agree on the overlaps, then they glue to a morphism `X ⟶ Y`
(`ofRestrict_glueMorphisms`), which is unique (`hom_ext_of_ofRestrict`). -/
noncomputable def glueMorphisms : X ⟶ Y where
  toHom := PresheafedSpace.glueMorphisms X.IsSheaf U hU (fun i ↦ (f i).toHom)
    (toHom_pullback_condition U f hf)
  prop x := by
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hU.symm ▸ trivial : x ∈ ⨆ i, U i)
    let x' : X.toPresheafedSpace.restrict (U i).isOpenEmbedding := ⟨x, hi⟩
    let g := PresheafedSpace.glueMorphisms X.IsSheaf U hU (fun i ↦ (f i).toHom)
      (toHom_pullback_condition U f hf)
    let fi : X.toPresheafedSpace.restrict (U i).isOpenEmbedding ⟶ Y.toPresheafedSpace := (f i).toHom
    have hfac : X.toPresheafedSpace.ofRestrict (U i).isOpenEmbedding ≫ g = fi :=
      PresheafedSpace.ofRestrict_glueMorphisms X.IsSheaf U hU _ _ i
    have hloc : IsLocalHom ((X.toPresheafedSpace.ofRestrict (U i).isOpenEmbedding ≫ g).stalkMap
        x').hom := by
      rw [PresheafedSpace.stalkMap.congr_hom _ _ hfac x', CommRingCat.hom_comp]
      have := isLocalHom_of_isIso (eqToHom (hfac ▸ rfl :
        Y.presheaf.stalk ((X.toPresheafedSpace.ofRestrict (U i).isOpenEmbedding ≫ g).base x') =
          Y.presheaf.stalk (fi.base x')))
      have : IsLocalHom (fi.stalkMap x').hom := (f i).prop ⟨x, hi⟩
      exact CommRingCat.isLocalHom_comp _ _
    rw [PresheafedSpace.stalkMap.comp] at hloc
    have : IsLocalHom (((X.toPresheafedSpace.ofRestrict (U i).isOpenEmbedding).stalkMap x').hom.comp
        (g.stalkMap x).hom) := hloc
    exact isLocalHom_of_comp _
      ((X.toPresheafedSpace.ofRestrict (U i).isOpenEmbedding).stalkMap x').hom

/-- The glued morphism restricts to `f i` on `U i`. -/
@[reassoc (attr := simp)]
theorem ofRestrict_glueMorphisms (i : ι) :
    X.ofRestrict (U i).isOpenEmbedding ≫ glueMorphisms U hU f hf = f i :=
  Hom.ext' (PresheafedSpace.ofRestrict_glueMorphisms X.IsSheaf U hU _ _ i)

include hU in
/-- **Morphisms out of a locally ringed space are determined locally.** Two morphisms `X ⟶ Y`
agreeing on every member of an open cover of `X` are equal. -/
theorem hom_ext_of_ofRestrict {g g' : X ⟶ Y}
    (h : ∀ i, X.ofRestrict (U i).isOpenEmbedding ≫ g = X.ofRestrict (U i).isOpenEmbedding ≫ g') :
    g = g' :=
  Hom.ext' (PresheafedSpace.hom_ext_of_ofRestrict X.IsSheaf U hU fun i ↦ congrArg Hom.toHom (h i))

end Glue

end AlgebraicGeometry.LocallyRingedSpace
