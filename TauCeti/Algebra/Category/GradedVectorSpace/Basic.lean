/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import TauCeti.CategoryTheory.Equivalence.Pow
public import TauCeti.CategoryTheory.GradedObject

/-!
# Graded vector spaces

Let `k` be a field. We use Mathlib's canonical category
`GradedObjectWithShift (-1) (ModuleCat k)` of `ℤ`-graded vector spaces. Its canonical shift
`shiftEquiv _ 1` moves every piece up by one degree, `(V{1})ᵢ = V_{i-1}`, and is a `k`-linear
autoequivalence; the pointwise abelian and linear structures come from
`TauCeti.CategoryTheory.GradedObject`.

The one-dimensional space `M = k` placed in degree `0` is projective, its morphisms into `V` are
the degree-zero piece `V₀`, and it is not isomorphic to any of its shifts `M{j}` with `j ≠ 0`.
Forgetting the grading is Mathlib's `GradedObject.total`, the functor `U` taking the direct sum
`⨁ᵢ Vᵢ` of the pieces; it is invariant under the shift, `{1} ⋙ U ≅ U`, and `U M ≅ k`.

## Main definitions

* `TauCeti.GradedVectorSpace k` and `TauCeti.GradedVectorSpace.shift k`: the category of
  `ℤ`-graded vector spaces and its grading shift, abbreviations for Mathlib's canonical
  `GradedObjectWithShift (-1) (ModuleCat k)` and `shiftEquiv _ 1`.
* `TauCeti.GradedVectorSpace.unit k`: the field `k` placed in degree `0`, given by Mathlib's
  canonical `GradedObject.single₀` applied to `k`.
* `TauCeti.GradedVectorSpace.homUnitLinearEquiv`: morphisms out of `unit k` are the degree-zero
  piece of the target.
* `TauCeti.GradedVectorSpace.shiftCompTotalIso` (`{1} ⋙ U ≅ U`) and
  `TauCeti.GradedVectorSpace.totalObjUnitIso` (`U M ≅ k`), for `U = GradedObject.total ℤ _`.

## Main results

* `TauCeti.GradedVectorSpace.nonempty_iso_shift_pow_obj`: `(V{j})ᵢ ≅ V_{i-j}`.
* `TauCeti.GradedVectorSpace.finrank_hom_unit_shift_pow`: `dim_k Hom(M, M{j})` is `1` for
  `j = 0` and `0` otherwise; consequently `M{j} ≇ M` for `j ≠ 0`
  (`TauCeti.GradedVectorSpace.isEmpty_iso_unit_shift_pow`).

## References

* Zsuzsanna Dancso and Anthony Licata, "Koszul algebras and flow lattices", *Journal of
  Combinatorial Theory, Series A* **185** (2022), Section 2.2, for the shift convention.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u

variable (k : Type u) [Field k]

/-- The category of **`ℤ`-graded vector spaces** over `k`: Mathlib's canonical category of graded
objects `GradedObjectWithShift (-1) (ModuleCat k)`, whose shift raises every degree by one. -/
abbrev GradedVectorSpace : Type (u + 1) :=
  GradedObjectWithShift (-1 : ℤ) (ModuleCat.{u} k)

namespace GradedVectorSpace

/-- The **grading shift** `V ↦ V{1}` on graded vector spaces, `(V{1})ᵢ = V_{i-1}`: Mathlib's
canonical shift by `1`, a `k`-linear autoequivalence. -/
abbrev shift : GradedVectorSpace k ≌ GradedVectorSpace k :=
  shiftEquiv (GradedVectorSpace k) (1 : ℤ)

/-- **The iterated shift reindexes the grading**: the piece of `V{j}` in degree `i` is isomorphic
to the piece of `V` in degree `i - j`. -/
theorem nonempty_iso_shift_pow_obj (j : ℤ) (V : GradedVectorSpace k) (i : ℤ) :
    Nonempty ((((shift k) ^ j).functor.obj V) i ≅ V (i - j)) := by
  induction j using Int.induction_on generalizing V with
  | zero => exact ⟨eqToIso (by simp)⟩
  | succ j ih =>
    obtain ⟨φ⟩ := ih ((shift k).functor.obj V)
    refine ⟨Pi.isoApp (((shift k).powSuccIso j).app V) i ≪≫ φ ≪≫ eqToIso ?_⟩
    simp only [shiftEquiv'_functor, GradedObject.shiftFunctor_obj_apply, one_smul]
    congr 1
    omega
  | pred j ih =>
    obtain ⟨φ⟩ := ih ((shift k).inverse.obj V)
    refine ⟨(Pi.isoApp (((shift k).powPredIso (-j)).app V) i).symm ≪≫ φ ≪≫
      eqToIso ?_⟩
    simp only [shiftEquiv'_inverse, GradedObject.shiftFunctor_obj_apply, neg_smul, one_smul,
      neg_neg]
    congr 1
    omega

/-- The **graded vector space `k` placed in degree `0`**, defined as Mathlib's canonical
single-degree graded object. It is characterized by `unitObjZeroIso` and `isZero_unit_obj`. -/
noncomputable def unit : GradedVectorSpace k :=
  (GradedObject.single₀ ℤ).obj (ModuleCat.of k k)

/-- The piece of `unit k` in degree `0` is the field `k`, as an object of `ModuleCat k`. -/
noncomputable def unitObjZeroIso : unit k 0 ≅ ModuleCat.of k k :=
  GradedObject.singleObjApplyIso (0 : ℤ) (ModuleCat.of k k)

/-- The piece of `unit k` in degree `0` is the field `k`. -/
noncomputable def unitObjZeroLinearEquiv : (unit k 0 : Type u) ≃ₗ[k] k :=
  (unitObjZeroIso k).toLinearEquiv

/-- The pieces of `unit k` away from degree `0` vanish. -/
theorem isZero_unit_obj {i : ℤ} (hi : i ≠ 0) : IsZero (unit k i) :=
  (GradedObject.isInitialSingleObjApply 0 (ModuleCat.of k k) i hi).isZero

private noncomputable def homUnitHomLinearEquiv (V : GradedVectorSpace k) :
    (unit k ⟶ V) ≃ₗ[k] (ModuleCat.of k k ⟶ V 0) where
  toFun f := (unitObjZeroIso k).inv ≫ f 0
  invFun f i :=
    if hi : i = 0 then
      eqToHom (congrArg (unit k) hi) ≫ (unitObjZeroIso k).hom ≫ f ≫
        eqToHom (congrArg V hi.symm)
    else 0
  left_inv f := by
    funext i
    by_cases hi : i = 0
    · subst i
      simp
    · exact (isZero_unit_obj k hi).eq_of_src _ _
  right_inv f := by simp
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

private theorem homUnitHomLinearEquiv_apply {V : GradedVectorSpace k} (f : unit k ⟶ V) :
    homUnitHomLinearEquiv k V f = (unitObjZeroIso k).inv ≫ f 0 :=
  rfl

private theorem homUnitHomLinearEquiv_symm_apply_zero
    {V : GradedVectorSpace k} (f : ModuleCat.of k k ⟶ V 0) :
    (homUnitHomLinearEquiv k V).symm f 0 = (unitObjZeroIso k).hom ≫ f := by
  simp [homUnitHomLinearEquiv]

/-- **Morphisms out of `unit k` are the degree-zero piece** of the target: a morphism is
determined by the image of `1` in degree `0`. -/
noncomputable def homUnitLinearEquiv (V : GradedVectorSpace k) :
    (unit k ⟶ V) ≃ₗ[k] V 0 :=
  (homUnitHomLinearEquiv k V).trans
    (ModuleCat.homLinearEquiv.trans (LinearMap.ringLmapEquivSelf k k _))

/-- `homUnitLinearEquiv` evaluates the degree-zero component of a morphism at `1 ∈ k`. -/
@[simp]
theorem homUnitLinearEquiv_apply {V : GradedVectorSpace k} (f : unit k ⟶ V) :
    homUnitLinearEquiv k V f = (f 0).hom ((unitObjZeroLinearEquiv k).symm 1) := by
  simp [homUnitLinearEquiv, homUnitHomLinearEquiv_apply, unitObjZeroLinearEquiv]
  -- Mathlib has no simp lemma for `ModuleCat.homLinearEquiv`, which is `ModuleCat.Hom.hom` by
  -- definition.
  rfl

/-- The degree-zero component of the morphism out of `unit k` corresponding to `v ∈ V₀` is the
identification `unit k 0 ≅ k` followed by `c ↦ c • v`. -/
@[simp]
theorem homUnitLinearEquiv_symm_apply_zero {V : GradedVectorSpace k} (v : V 0) :
    (homUnitLinearEquiv k V).symm v 0 =
      (unitObjZeroIso k).hom ≫ ModuleCat.ofHom (LinearMap.toSpanSingleton k (V 0) v) := by
  simp [homUnitLinearEquiv, homUnitHomLinearEquiv_symm_apply_zero]
  -- Mathlib has no simp lemma for `ModuleCat.homLinearEquiv.symm`, which is `ModuleCat.ofHom` by
  -- definition; `LinearMap.toSpanSingleton k _ v` is `LinearMap.smulRight 1 v` by definition.
  rfl

/-- `unit k` is projective because epimorphisms of graded objects are componentwise epimorphisms
and the one-dimensional module `k` is projective. -/
instance : Projective (unit k) where
  factors {E X} f e _ := by
    let _ : Epi ((piEquivalenceFunctorDiscrete ℤ (ModuleCat.{u} k)).functor.map e) :=
      inferInstance
    let _ : Epi (e 0) := by
      -- The component `e 0` is by definition the component at `⟨0⟩` of the natural
      -- transformation corresponding to `e` under `piEquivalenceFunctorDiscrete`.
      change Epi (((piEquivalenceFunctorDiscrete ℤ (ModuleCat.{u} k)).functor.map e).app ⟨0⟩)
      infer_instance
    have : Projective (ModuleCat.of k k) :=
      ModuleCat.projective_of_free (Module.Basis.singleton Unit k)
    obtain ⟨g, hg⟩ := Projective.factors (homUnitHomLinearEquiv k X f) (e 0)
    refine ⟨(homUnitHomLinearEquiv k E).symm g, ?_⟩
    apply (homUnitHomLinearEquiv k X).injective
    rw [homUnitHomLinearEquiv_apply, homUnitHomLinearEquiv_apply, Pi.comp_apply,
      homUnitHomLinearEquiv_symm_apply_zero, Category.assoc, Iso.inv_hom_id_assoc, hg,
      homUnitHomLinearEquiv_apply]

/-- Every piece of `unit k` is finite-dimensional. -/
theorem finiteDimensional_unit_obj (i : ℤ) : FiniteDimensional k (unit k i) := by
  by_cases hi : i = 0
  · subst hi
    exact Module.Finite.equiv (unitObjZeroLinearEquiv k).symm
  · have := ModuleCat.subsingleton_of_isZero (isZero_unit_obj k hi)
    infer_instance

/-- The piece of `unit k` in degree `i` has dimension `1` if `i = 0` and `0` otherwise. -/
@[simp]
theorem finrank_unit_obj (i : ℤ) :
    Module.finrank k (unit k i) = if i = 0 then 1 else 0 := by
  split_ifs with hi
  · subst hi
    rw [(unitObjZeroLinearEquiv k).finrank_eq, Module.finrank_self]
  · have := ModuleCat.subsingleton_of_isZero (isZero_unit_obj k hi)
    exact Module.finrank_zero_of_subsingleton

/-- The morphisms from `M = unit k` to its shift `M{j}` are the piece of `M` in degree `-j`. -/
theorem nonempty_linearEquiv_hom_unit_shift_pow (j : ℤ) :
    Nonempty ((unit k ⟶ ((shift k) ^ j).functor.obj (unit k)) ≃ₗ[k] unit k (-j)) := by
  obtain ⟨φ⟩ := nonempty_iso_shift_pow_obj k j (unit k) 0
  rw [zero_sub] at φ
  exact ⟨(homUnitLinearEquiv k _).trans φ.toLinearEquiv⟩

/-- **The degree-zero morphisms `Hom(M, M{j})`** between `M = unit k` and its shifts: they form a
one-dimensional space for `j = 0` and vanish otherwise. -/
@[simp]
theorem finrank_hom_unit_shift_pow (j : ℤ) :
    Module.finrank k (unit k ⟶ ((shift k) ^ j).functor.obj (unit k)) =
      if j = 0 then 1 else 0 := by
  obtain ⟨φ⟩ := nonempty_linearEquiv_hom_unit_shift_pow k j
  rw [φ.finrank_eq, finrank_unit_obj]
  simp only [neg_eq_zero]

/-- **The shifts of `M = unit k` are genuinely different**: `M{j}` is not isomorphic to `M` for
`j ≠ 0`, since there are no nonzero morphisms `M ⟶ M{j}` while `M` has nonzero endomorphisms. -/
theorem isEmpty_iso_unit_shift_pow {j : ℤ} (hj : j ≠ 0) :
    IsEmpty (unit k ≅ ((shift k) ^ j).functor.obj (unit k)) := by
  refine ⟨fun f ↦ ?_⟩
  have : Subsingleton (unit k ⟶ ((shift k) ^ j).functor.obj (unit k)) := by
    obtain ⟨φ⟩ := nonempty_linearEquiv_hom_unit_shift_pow k j
    have := ModuleCat.subsingleton_of_isZero (isZero_unit_obj k (neg_ne_zero.2 hj))
    exact φ.toEquiv.subsingleton
  have hid : 𝟙 (unit k) = 0 := by
    rw [← f.hom_inv_id, Subsingleton.elim f.hom 0, zero_comp]
  have : Subsingleton (unit k ⟶ ((shift k) ^ (0 : ℤ)).functor.obj (unit k)) :=
    ⟨fun a b ↦ by rw [← Category.id_comp a, ← Category.id_comp b, hid, zero_comp, zero_comp]⟩
  have hone := finrank_hom_unit_shift_pow k 0
  rw [Module.finrank_zero_of_subsingleton] at hone
  simp at hone

/-! ### Totalizing the grading -/

/-- **Totalizing the grading is invariant under the shift**: `{1} ⋙ U ≅ U`. Both functors are left
adjoint to the constant functor. -/
noncomputable def shiftCompTotalIso :
    (shift k).functor ⋙ GradedObject.total ℤ (ModuleCat.{u} k) ≅
      GradedObject.total ℤ (ModuleCat.{u} k) :=
  Adjunction.leftAdjointUniq
    ((shift k).toAdjunction.comp (gradedObjectTotalAdjunction ℤ (ModuleCat.{u} k)))
    ((gradedObjectTotalAdjunction ℤ (ModuleCat.{u} k)).ofNatIsoRight (Iso.refl _))

private noncomputable def coproductUnitIso :
    (∐ fun i : ℤ ↦ unit k i) ≅ ModuleCat.of k k where
  hom := Sigma.desc fun i ↦
    if hi : i = 0 then eqToHom (congrArg (unit k) hi) ≫ (unitObjZeroIso k).hom else 0
  inv := (unitObjZeroIso k).inv ≫ Sigma.ι (unit k) 0
  hom_inv_id := by
    apply Sigma.hom_ext
    intro i
    by_cases hi : i = 0
    · subst i
      simp only [colimit.ι_desc_assoc, Discrete.functor_obj_eq_as, Cofan.mk_pt, Cofan.mk_ι_app,
        ↓reduceDIte, eqToHom_refl, Category.id_comp, Iso.hom_inv_id_assoc, Category.comp_id]
    · exact (isZero_unit_obj k hi).eq_of_src _ _
  inv_hom_id := by
    rw [Category.assoc, Sigma.ι_comp_desc]
    simp

/-- **The total space underlying `M = unit k` is `k`**. -/
noncomputable def totalObjUnitIso :
    (GradedObject.total ℤ (ModuleCat.{u} k)).obj (unit k) ≅ ModuleCat.of k k :=
  coproductUnitIso k

end GradedVectorSpace

end TauCeti
