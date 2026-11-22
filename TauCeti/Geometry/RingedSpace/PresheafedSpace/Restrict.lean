/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.RingedSpace.OpenImmersion
public import TauCeti.Topology.Category.TopCat.Opens

/-!
# Inclusions between restrictions of a presheafed space to nested opens

For opens `V ≤ W` of a presheafed space `X`, the restriction of `X` to `V` includes into its
restriction to `W`, compatibly with the inclusions into `X`. This is the presheafed-space analogue
of Mathlib's `AlgebraicGeometry.Scheme.homOfLE`, together with `pullbackRestrictIso`.

## Main definitions

* `AlgebraicGeometry.PresheafedSpace.restrictHomOfLE`: the inclusion `X|_V ⟶ X|_W` for `V ≤ W`.
* `AlgebraicGeometry.PresheafedSpace.pullbackRestrictIso`:
  `pullback (X.ofRestrict U) (X.ofRestrict V) ≅ X|_{U ⊓ V}`.

## Main results

* `AlgebraicGeometry.PresheafedSpace.restrictHomOfLE_ofRestrict`: composing with the inclusion
  `X|_W ⟶ X` gives the inclusion `X|_V ⟶ X`.
* `AlgebraicGeometry.PresheafedSpace.restrictHomOfLE_refl`,
  `AlgebraicGeometry.PresheafedSpace.restrictHomOfLE_comp`: the inclusions are functorial.
* `AlgebraicGeometry.PresheafedSpace.pullbackRestrictIso_hom_restrictHomOfLE_left`,
  `pullbackRestrictIso_hom_restrictHomOfLE_right`, `pullbackRestrictIso_inv_fst`,
  `pullbackRestrictIso_inv_snd`: projection identities for `pullbackRestrictIso`.
-/

public section

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.PresheafedSpace

universe v u

variable {C : Type u} [Category.{v} C] (X : PresheafedSpace C)

/- The presheaf of the restriction `X.restrict h` is `h.functor.op ⋙ X.presheaf` only after
unfolding Mathlib's `AlgebraicGeometry.PresheafedSpace.restrict`, which `rw` does not do. In the
proofs below, restriction maps of `X.restrict h` are therefore merged with those of `X` by
`erw [← X.presheaf.map_comp]`, after which the remaining equalities of morphisms of `Opens X` hold
by `rfl`, `Opens X` being a preorder. -/

/-- For opens `V ≤ W` of `X`, the inclusion of the restriction of `X` to `V` into its restriction
to `W`. Its components are restriction maps of the presheaf of `X`. -/
@[expose, simps]
def restrictHomOfLE {V W : Opens X} (h : V ≤ W) :
    X.restrict V.isOpenEmbedding ⟶ X.restrict W.isOpenEmbedding where
  base := (Opens.toTopCat X).map (homOfLE h)
  c :=
    { app Q := X.presheaf.map (homOfLE (Opens.functor_obj_map_homOfLE_obj_le h Q.unop)).op
      -- `erw`: see the comment above
      naturality _ _ _ := by
        erw [← X.presheaf.map_comp, ← X.presheaf.map_comp]
        rfl }

/-- The inclusion `X|_V ⟶ X|_W` followed by the inclusion `X|_W ⟶ X` is the inclusion
`X|_V ⟶ X`. -/
@[reassoc (attr := simp)]
theorem restrictHomOfLE_ofRestrict {V W : Opens X} (h : V ≤ W) :
    X.restrictHomOfLE h ≫ X.ofRestrict W.isOpenEmbedding = X.ofRestrict V.isOpenEmbedding := by
  have hbase : (X.restrictHomOfLE h ≫ X.ofRestrict W.isOpenEmbedding).base =
      (X.ofRestrict V.isOpenEmbedding).base := by
    rw [comp_base, ofRestrict_base, ofRestrict_base, restrictHomOfLE_base]
    rfl
  refine PresheafedSpace.ext _ _ hbase ?_
  ext Q
  rw [NatTrans.comp_app, comp_c_app, Functor.whiskerRight_app, eqToHom_app,
    ofRestrict_c_app, ofRestrict_c_app, restrictHomOfLE_c_app]
  erw [← X.presheaf.map_comp, ← X.presheaf.map_comp]
  rfl

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

private theorem range_pullback_fst_subset (U V : Opens X) :
    Set.range (pullback.fst (X.ofRestrict U.isOpenEmbedding)
        (X.ofRestrict V.isOpenEmbedding) ≫ X.ofRestrict U.isOpenEmbedding).base ⊆
      Set.range (X.ofRestrict (U ⊓ V).isOpenEmbedding).base := by
  rintro _ ⟨p, rfl⟩
  let ιU := X.ofRestrict U.isOpenEmbedding; let ιV := X.ofRestrict V.isOpenEmbedding
  exact ⟨⟨(pullback.fst ιU ιV ≫ ιU).base p, ((pullback.fst ιU ιV).base p).2,
    congrArg (fun k ↦ k.base p) (pullback.condition : pullback.fst ιU ιV ≫ ιU =
      pullback.snd ιU ιV ≫ ιV) ▸ ((pullback.snd ιU ιV).base p).2⟩, rfl⟩

/-- The pullback of two open inclusions `X|_U ⟶ X` and `X|_V ⟶ X` is canonically isomorphic to
the restriction `X|_{U ⊓ V}`. -/
noncomputable def pullbackRestrictIso (U V : Opens X) :
    pullback (X.ofRestrict U.isOpenEmbedding) (X.ofRestrict V.isOpenEmbedding) ≅
      X.restrict (U ⊓ V).isOpenEmbedding where
  hom := IsOpenImmersion.lift (X.ofRestrict (U ⊓ V).isOpenEmbedding)
    (pullback.fst _ _ ≫ X.ofRestrict U.isOpenEmbedding) (range_pullback_fst_subset X U V)
  inv := pullback.lift (X.restrictHomOfLE inf_le_left) (X.restrictHomOfLE inf_le_right) (by simp)
  hom_inv_id := pullback.hom_ext
    (by rw [Category.assoc, pullback.lift_fst, Category.id_comp, ← cancel_mono (X.ofRestrict _),
      Category.assoc, restrictHomOfLE_ofRestrict, IsOpenImmersion.lift_fac])
    (by rw [Category.assoc, pullback.lift_snd, Category.id_comp, ← cancel_mono (X.ofRestrict _),
      Category.assoc, restrictHomOfLE_ofRestrict, IsOpenImmersion.lift_fac, pullback.condition])
  inv_hom_id := (cancel_mono (X.ofRestrict (U ⊓ V).isOpenEmbedding)).mp <| by
    rw [Category.assoc, IsOpenImmersion.lift_fac, Category.id_comp, pullback.lift_fst_assoc,
      restrictHomOfLE_ofRestrict]

/-- Composing `pullbackRestrictIso.hom` with the left inclusion gives `pullback.fst`. -/
@[reassoc (attr := simp)] theorem pullbackRestrictIso_hom_restrictHomOfLE_left (U V : Opens X) :
    (X.pullbackRestrictIso U V).hom ≫ X.restrictHomOfLE inf_le_left =
      pullback.fst (X.ofRestrict U.isOpenEmbedding) (X.ofRestrict V.isOpenEmbedding) :=
  (cancel_mono (X.ofRestrict U.isOpenEmbedding)).mp <| by
    rw [Category.assoc, restrictHomOfLE_ofRestrict]
    dsimp [pullbackRestrictIso]; rw [IsOpenImmersion.lift_fac]

/-- Composing `pullbackRestrictIso.hom` with the right inclusion gives `pullback.snd`. -/
@[reassoc (attr := simp)] theorem pullbackRestrictIso_hom_restrictHomOfLE_right (U V : Opens X) :
    (X.pullbackRestrictIso U V).hom ≫ X.restrictHomOfLE inf_le_right =
      pullback.snd (X.ofRestrict U.isOpenEmbedding) (X.ofRestrict V.isOpenEmbedding) :=
  (cancel_mono (X.ofRestrict V.isOpenEmbedding)).mp <| by
    rw [Category.assoc, restrictHomOfLE_ofRestrict]
    dsimp [pullbackRestrictIso]; rw [IsOpenImmersion.lift_fac, pullback.condition]

/-- Composing `pullbackRestrictIso.inv` with `pullback.fst` gives the left inclusion. -/
@[reassoc (attr := simp)] theorem pullbackRestrictIso_inv_fst (U V : Opens X) :
    (X.pullbackRestrictIso U V).inv ≫ pullback.fst (X.ofRestrict U.isOpenEmbedding)
        (X.ofRestrict V.isOpenEmbedding) = X.restrictHomOfLE inf_le_left := pullback.lift_fst _ _ _

/-- Composing `pullbackRestrictIso.inv` with `pullback.snd` gives the right inclusion. -/
@[reassoc (attr := simp)] theorem pullbackRestrictIso_inv_snd (U V : Opens X) :
    (X.pullbackRestrictIso U V).inv ≫ pullback.snd (X.ofRestrict U.isOpenEmbedding)
        (X.ofRestrict V.isOpenEmbedding) = X.restrictHomOfLE inf_le_right := pullback.lift_snd _ _ _

end AlgebraicGeometry.PresheafedSpace
