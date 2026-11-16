/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace.ResidueField

/-!
# Residue-field evaluation on open restrictions of locally ringed spaces

On an open restriction `L.restrict U.isOpenEmbedding` of a locally ringed space `L` to
`U : Opens L`, evaluating a section `s ∈ Γ(U, O_L)` at `x ∈ U` and applying the canonical
residue-field map of `L.ofRestrict U.isOpenEmbedding` agrees with global evaluation `Γevaluation`
on `L.restrict U.isOpenEmbedding` after transporting `s` along `Opens.isOpenEmbedding_obj_top U`.
In particular, the restricted global section vanishes in the residue field at `x` if and only if
`s` vanishes in the residue field of `L` at `x`.

## Main results

* `AlgebraicGeometry.LocallyRingedSpace.residueFieldMap_injective` and
  `AlgebraicGeometry.LocallyRingedSpace.residueFieldMap_eq_zero_iff`: `residueFieldMap f x` is
  injective and reflects zero.
* `AlgebraicGeometry.LocallyRingedSpace.residueFieldMap_ofRestrict_evaluation`: compatibility of
  `LocallyRingedSpace.evaluation` on `U` with `LocallyRingedSpace.Γevaluation` on
  `L.restrict U.isOpenEmbedding`.
* `AlgebraicGeometry.LocallyRingedSpace.Γevaluation_restrict_eq_zero_iff`: vanishing of the
  restricted global section at `x` is equivalent to `L.evaluation ⟨x.1, x.2⟩ s = 0`.
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
under the canonical identification `Opens.isOpenEmbedding_obj_top U`. -/
theorem residueFieldMap_ofRestrict_evaluation (L : LocallyRingedSpace.{u}) (U : Opens L)
    (x : L.restrict U.isOpenEmbedding) (s : L.presheaf.obj (op U)) :
    have hx : x ∈ (Opens.map (L.ofRestrict U.isOpenEmbedding).base).obj U :=
      (Opens.inclusion'_map_eq_top U).symm ▸ Opens.mem_top x
    residueFieldMap (L.ofRestrict U.isOpenEmbedding) x
        (L.evaluation ⟨(L.ofRestrict U.isOpenEmbedding).base x, hx⟩ s) =
      (L.restrict U.isOpenEmbedding).Γevaluation x
        (L.presheaf.map (eqToHom (congrArg op (Opens.isOpenEmbedding_obj_top U)).symm) s) := by
  let j : L.restrict U.isOpenEmbedding ⟶ L := L.ofRestrict U.isOpenEmbedding
  have hU : (Opens.map j.base).obj U = (⊤ : Opens (L.restrict U.isOpenEmbedding)) :=
    Opens.inclusion'_map_eq_top U
  have hxU : x ∈ (Opens.map j.base).obj U := hU.symm ▸ Opens.mem_top x
  let sTop : (L.restrict U.isOpenEmbedding).presheaf.obj (op ⊤) :=
    L.presheaf.map (eqToHom (congrArg op (Opens.isOpenEmbedding_obj_top U)).symm) s
  have hmap : L.presheaf.map (eqToHom (congrArg op (Opens.isOpenEmbedding_obj_top U)).symm) ≫
      (L.restrict U.isOpenEmbedding).presheaf.map (homOfLE hU.le).op = j.c.app (op U) := by
    have hjc : j.c.app (op U) = (L.toPresheafedSpace.ofRestrict U.isOpenEmbedding).c.app (op U) :=
      rfl
    rw [hjc, PresheafedSpace.ofRestrict_c_app]
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

/-- The restricted global section corresponding to `s ∈ Γ(U, O_L)` vanishes in the residue field
at `x ∈ L.restrict U.isOpenEmbedding` if and only if `s` vanishes in the residue field of `L` at
`x`. -/
@[simp]
theorem Γevaluation_restrict_eq_zero_iff (L : LocallyRingedSpace.{u}) (U : Opens L)
    (x : L.restrict U.isOpenEmbedding) (s : L.presheaf.obj (op U)) :
    (L.restrict U.isOpenEmbedding).Γevaluation x
        (L.presheaf.map (eqToHom (congrArg op (Opens.isOpenEmbedding_obj_top U)).symm) s) = 0 ↔
      L.evaluation ⟨x.1, x.2⟩ s = 0 := by
  rw [← residueFieldMap_ofRestrict_evaluation, residueFieldMap_eq_zero_iff]
  rfl

end AlgebraicGeometry.LocallyRingedSpace
