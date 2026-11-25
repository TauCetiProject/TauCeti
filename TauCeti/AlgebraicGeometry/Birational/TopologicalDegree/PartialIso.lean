/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Birational.TopologicalDegree.Birationality
public import TauCeti.AlgebraicGeometry.Birational.FunctionField.Determination
public import Mathlib.AlgebraicGeometry.Birational.Birational

/-!
# Partial isomorphisms and rational maps of topological degree one

A partial isomorphism `φ` of integral schemes, an isomorphism between dense opens of `X` and `Y`
(Mathlib's `AlgebraicGeometry.Scheme.PartialIso`), has rational map `φ.toRationalMap` with inverse
`φ.symm.toRationalMap` on both sides
(`AlgebraicGeometry.Scheme.PartialIso.toRationalMap_comp_symm`). So the rational map of a partial
isomorphism has topological degree `1`, and its pullback of rational functions is an isomorphism:
a birational map has topological degree `1`.

Conversely, over a ring `k`, a dominant `k`-rational map `f : X ⤏ Y` of integral `k`-schemes, with
`X` locally of finite type over `k`, has topological degree `1` exactly when it has a two-sided
inverse among dominant `k`-rational maps
(`AlgebraicGeometry.Scheme.RationalMap.topologicalDegree_eq_one_iff_exists_comp_eq_id`): the
inverse is the rational map whose pullback is `(f^*)^{-1}`, which exists because a dominant
`k`-rational map into `X` is determined by, and can be built from, its pullback.

## Main results

* `AlgebraicGeometry.Scheme.PartialIso.toRationalMap_comp_symm` and
  `AlgebraicGeometry.Scheme.PartialIso.toRationalMap_symm_comp`: `φ⁻¹ ∘ φ = id` and
  `φ ∘ φ⁻¹ = id` as rational maps.
* `AlgebraicGeometry.Scheme.PartialIso.topologicalDegree_toRationalMap`: the rational map of a
  partial isomorphism has topological degree `1`.
* `AlgebraicGeometry.Scheme.RationalMap.topologicalDegree_eq_one_iff_exists_comp_eq_id`: a
  dominant `k`-rational map has topological degree `1` exactly when it has a two-sided dominant
  `k`-rational inverse.

## References

* The Stacks Project, Tag 0BXN (the degree of a dominant generically finite morphism of integral
  schemes as the degree of the extension of function fields).
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}}

/-- The partial map of a partial isomorphism is dominant: its image is a dense open. -/
instance PartialIso.isDominant_toPartialMap_hom (φ : X.PartialIso Y) :
    IsDominant φ.toPartialMap.hom := by
  have := Opens.isDominant_ι φ.dense_target
  exact inferInstanceAs (IsDominant (φ.iso.hom ≫ φ.target.ι))

/-- The partial map `e.hom` on `U`, followed by the partial map `e.inv` on `V`, for an isomorphism
`e` of dense opens `U` of `X` and `V` of `Y`, is equivalent to the identity of `X`. -/
theorem PartialMap.mk_comp_mk_equiv [IsIntegral X] [IsIntegral Y] (U : X.Opens)
    (hU : Dense (U : Set X)) (V : Y.Opens) (hV : Dense (V : Set Y)) (e : U.toScheme ≅ V.toScheme)
    [IsDominant (e.hom ≫ V.ι)] :
    ((⟨U, hU, e.hom ≫ V.ι⟩ : X.PartialMap Y).comp ⟨V, hV, e.inv ≫ U.ι⟩).equiv
      (PartialMap.id X) := by
  have key : (e.hom ≫ V.ι) ∣_ V ≫ e.inv = ((e.hom ≫ V.ι) ⁻¹ᵁ V).ι := by
    rw [← cancel_mono (e.hom ≫ V.ι), Category.assoc, Iso.inv_hom_id_assoc, morphismRestrict_ι]
  refine ⟨_, (PartialMap.comp _ _).dense_domain, le_rfl,
    le_top.trans_eq (Hom.toPartialMap_domain _).symm, ?_⟩
  rw [PartialMap.restrict_hom, PartialMap.restrict_hom, homOfLE_rfl, Category.id_comp,
    PartialMap.comp_hom]
  dsimp only
  rw [reassoc_of% key, Hom.isoImage_inv_ι, Hom.toPartialMap_hom, Category.comp_id, topIso_hom]
  exact (X.homOfLE_ι _).symm

/-- The partial map of a partial isomorphism followed by that of its inverse is equivalent to the
identity. -/
theorem PartialIso.toPartialMap_comp_symm_equiv [IsIntegral X] [IsIntegral Y]
    (φ : X.PartialIso Y) :
    (φ.toPartialMap.comp φ.symm.toPartialMap).equiv (PartialMap.id X) := by
  have := Opens.isDominant_ι φ.dense_target
  exact PartialMap.mk_comp_mk_equiv φ.source φ.dense_source φ.target φ.dense_target φ.iso

/-- **A partial isomorphism is invertible as a rational map**: `φ⁻¹ ∘ φ = id`. -/
theorem PartialIso.toRationalMap_comp_symm [IsIntegral X] [IsIntegral Y] (φ : X.PartialIso Y) :
    φ.toRationalMap.comp φ.symm.toRationalMap = RationalMap.id X := by
  rw [RationalMap.comp_def, PartialMap.toRationalMap_eq_iff]
  refine PartialMap.equivalence_rel.trans (PartialMap.comp_equiv_of_equiv_left ?_ _)
    φ.toPartialMap_comp_symm_equiv
  exact PartialMap.toRationalMap_eq_iff.mp φ.toRationalMap.toRationalMap_representative

/-- **A partial isomorphism is invertible as a rational map**: `φ ∘ φ⁻¹ = id`. -/
theorem PartialIso.toRationalMap_symm_comp [IsIntegral X] [IsIntegral Y] (φ : X.PartialIso Y) :
    φ.symm.toRationalMap.comp φ.toRationalMap = RationalMap.id Y :=
  RationalMap.comp_eq_id_of_comp_eq_id _ _ φ.toRationalMap_comp_symm

/-- **A birational map has topological degree one**: the rational map of a partial isomorphism
of integral schemes has topological degree `1`. -/
theorem PartialIso.topologicalDegree_toRationalMap [IsIntegral X] [IsIntegral Y]
    (φ : X.PartialIso Y) : φ.toRationalMap.topologicalDegree = 1 :=
  (RationalMap.topologicalDegree_eq_one_of_comp_eq_id _ _ φ.toRationalMap_comp_symm).1

/-- The pullback of rational functions along the rational map of a partial isomorphism of
integral schemes is an isomorphism of function fields. -/
theorem PartialIso.isIso_functionFieldMap_toRationalMap [IsIntegral X] [IsIntegral Y]
    (φ : X.PartialIso Y) : IsIso φ.toRationalMap.functionFieldMap :=
  (RationalMap.topologicalDegree_eq_one_iff_isIso _).1 φ.topologicalDegree_toRationalMap

section Inverse

variable (k : Type u) [CommRing k] [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [IsIntegral X]
  [IsIntegral Y] [LocallyOfFiniteType (X ↘ Spec (.of k))]

/-- A dominant `k`-rational map `f : X ⤏ Y` of integral `k`-schemes of topological degree `1`,
with `X` locally of finite type over `k`, has a two-sided inverse among dominant `k`-rational
maps: the rational map whose pullback of rational functions is `(f^*)^{-1}`. -/
theorem RationalMap.exists_comp_eq_id_of_topologicalDegree_eq_one (f : X ⤏ Y) [f.IsDominant]
    [f.IsOver (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))] (h : f.topologicalDegree = 1) :
    ∃ (g : Y ⤏ X) (_ : g.IsDominant), g.IsOver (Y ↘ Spec (.of k)) (X ↘ Spec (.of k)) ∧
      f.comp g = RationalMap.id X ∧ g.comp f = RationalMap.id Y := by
  have hb : Function.Bijective (f.functionFieldAlgHom k) := by
    have := (topologicalDegree_eq_one_iff_bijective f).1 h
    convert this using 1
    ext a
    exact functionFieldAlgHom_apply k f a
  let e := AlgEquiv.ofBijective (f.functionFieldAlgHom k) hb
  let g := ofFunctionFieldAlgHom k e.symm.toAlgHom
  have hcomp : f.comp g = RationalMap.id X := by
    have := isOver_comp (sX := X ↘ Spec (.of k)) (sY := Y ↘ Spec (.of k))
      (sZ := X ↘ Spec (.of k)) f inferInstance g inferInstance
    refine eq_of_functionFieldAlgHom_eq k ?_
    rw [functionFieldAlgHom_comp, functionFieldAlgHom_id,
      functionFieldAlgHom_ofFunctionFieldAlgHom]
    ext a
    exact e.apply_symm_apply a
  exact ⟨g, inferInstance, inferInstance, hcomp, comp_eq_id_of_comp_eq_id f g hcomp⟩

/-- **Topological degree one and inverses.** A dominant `k`-rational map `f : X ⤏ Y` of integral
`k`-schemes, with `X` locally of finite type over `k`, has topological degree `1` exactly when it
has a two-sided inverse among dominant `k`-rational maps. -/
theorem RationalMap.topologicalDegree_eq_one_iff_exists_comp_eq_id (f : X ⤏ Y) [f.IsDominant]
    [f.IsOver (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))] :
    f.topologicalDegree = 1 ↔ ∃ (g : Y ⤏ X) (_ : g.IsDominant),
      g.IsOver (Y ↘ Spec (.of k)) (X ↘ Spec (.of k)) ∧
        f.comp g = RationalMap.id X ∧ g.comp f = RationalMap.id Y :=
  ⟨exists_comp_eq_id_of_topologicalDegree_eq_one k f, fun ⟨_, _, _, h, _⟩ =>
    (topologicalDegree_eq_one_of_comp_eq_id f _ h).1⟩

end Inverse

end AlgebraicGeometry.Scheme
