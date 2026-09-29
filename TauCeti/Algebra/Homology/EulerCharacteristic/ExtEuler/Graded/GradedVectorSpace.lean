/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.GradedObject.Single
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.ForgetGrading
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.Shift
public import TauCeti.CategoryTheory.GradedObject

/-!
# The q-Euler form of graded vector spaces

Let `k` be a field. We use Mathlib's canonical category
`GradedObjectWithShift (-1) (ModuleCat k)` of `ℤ`-graded vector spaces. Its canonical shift
`shiftEquiv _ 1` moves every piece up by one degree, `(V{1})ᵢ = V_{i-1}`, and is a `k`-linear
autoequivalence.

The one-dimensional space `M = k` placed in degree `0` is the smallest nontrivial test of the
q-Euler formalism: it is projective, it is not isomorphic to any of its shifts `M{j}` with
`j ≠ 0`, its degree-zero endomorphisms are one-dimensional, and it has no higher `Ext`. Hence

```text
χ_q(M, M) = 1,    χ_q(M, M{1}) = q = q χ_q(M, M),    χ_q(M{1}, M) = q⁻¹ = q⁻¹ χ_q(M, M).
```

At `q = 1` the three values agree, while at `q = -1` a single shift changes the sign.

Forgetting the grading is the functor `U` taking the direct sum `⨁ᵢ Vᵢ` of the pieces; it is
invariant under the shift, `{1} ⋙ U ≅ U`, and `U M ≅ k`. In every cohomological degree the
bigraded `Ext` groups of `(M, M)` assemble into the ungraded `Ext` groups of `(U M, U M)` in
`ModuleCat k`; this is checked directly, by computing both sides, and it identifies the value of
`χ_q(M, M)` at `q = 1` with the ordinary Ext-Euler characteristic `χ(U M, U M) = 1`.

## Main definitions

* `TauCeti.GradedVectorSpace.unit k`: the field `k` placed in degree `0`, given by Mathlib's
  canonical `GradedObject.single₀` applied to `k`.
* `TauCeti.GradedVectorSpace.homUnitLinearEquiv`: morphisms out of `unit k` are the degree-zero
  piece of the target.
* `GradedObject.total ℤ (ModuleCat k)`: forgetting the grading, `V ↦ ⨁ᵢ Vᵢ`, with
  `TauCeti.GradedVectorSpace.shiftCompTotalIso` (`{1} ⋙ U ≅ U`) and
  `TauCeti.GradedVectorSpace.totalObjUnitIso` (`U M ≅ k`).

## Main results

* `TauCeti.GradedVectorSpace.nonempty_iso_shift_pow_obj`: `(V{j})ᵢ ≅ V_{i-j}`.
* `TauCeti.GradedVectorSpace.finrank_hom_unit_shift_pow`: `dim_k Hom(M, M{j})` is `1` for
  `j = 0` and `0` otherwise; consequently `M{j} ≇ M` for `j ≠ 0`
  (`TauCeti.GradedVectorSpace.isEmpty_iso_unit_shift_pow`).
* `TauCeti.GradedVectorSpace.gradedExtEuler_unit`: `χ_q(M, M) = 1`.
* `TauCeti.GradedVectorSpace.gradedExtEuler_unit_shiftTarget` and
  `TauCeti.GradedVectorSpace.gradedExtEuler_unit_shiftSource`: `χ_q(M, M{1}) = q` and
  `χ_q(M{1}, M) = q⁻¹`.
* `TauCeti.GradedVectorSpace.laurentEval_gradedExtEuler_unit_shiftTarget` and
  `TauCeti.GradedVectorSpace.laurentEval_gradedExtEuler_unit_shiftSource`: their values at
  `q = ε` for `ε = ±1`; in particular
  `TauCeti.GradedVectorSpace.laurentEval_neg_one_gradedExtEuler_unit_shiftTarget`: at `q = -1`,
  `χ_q(M, M{1})` is the negative of `χ_q(M, M)`.
* `TauCeti.GradedVectorSpace.isGradedExtComparison_unit`: the bigraded `Ext` groups of `(M, M)`
  assemble into the `Ext` groups of the underlying ungraded pair `(U M, U M)` in `ModuleCat k`.
* `TauCeti.GradedVectorSpace.laurentEval_one_gradedExtEuler_unit`: `χ_q(M, M)` at `q = 1` is the
  ordinary Ext-Euler characteristic of `(U M, U M)`.
* `TauCeti.GradedVectorSpace.extEuler_moduleCat_self`: the ordinary Ext-Euler characteristic
  `χ(k, k)` in `ModuleCat k` is `1`.

## Implementation notes

Graded vector spaces use Mathlib's `GradedObjectWithShift`, `GradedObject.single₀`,
`GradedObject.total`, and `shiftFunctor`. The pointwise abelian and linear instances missing from
Mathlib are supplied generically in `TauCeti.CategoryTheory.GradedObject`.

The results hold for every choice of `HasExt` instances on the two categories: `Ext` groups are
only used through their dimensions.

## References

* Zsuzsanna Dancso and Anthony Licata, "Koszul algebras and flow lattices", *Journal of
  Combinatorial Theory, Series A* **185** (2022), Section 2.2, for graded Grothendieck groups, the
  q-Euler form and its shift conventions.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian LaurentPolynomial

universe w w' u

variable (k : Type u) [Field k]

namespace GradedVectorSpace

local notation "GVS" k => GradedObjectWithShift (-1 : ℤ) (ModuleCat k)

local notation "σ" k => shiftEquiv (GVS k) (1 : ℤ)

/-- **The iterated shift reindexes the grading**: the piece of `V{j}` in degree `i` is isomorphic
to the piece of `V` in degree `i - j`. -/
theorem nonempty_iso_shift_pow_obj (j : ℤ) (V : GVS k) (i : ℤ) :
    Nonempty ((((σ k) ^ j).functor.obj V) i ≅ V (i - j)) := by
  induction j using Int.induction_on generalizing V with
  | zero => exact ⟨eqToIso (by simp)⟩
  | succ j ih =>
    obtain ⟨φ⟩ := ih ((σ k).functor.obj V)
    refine ⟨Pi.isoApp (((σ k).powSuccIso j).app V) i ≪≫ φ ≪≫ eqToIso ?_⟩
    change V (i - j - 1) = V (i - (j + 1))
    congr 1
    omega
  | pred j ih =>
    obtain ⟨φ⟩ := ih ((σ k).inverse.obj V)
    refine ⟨(Pi.isoApp (((σ k).powPredIso (-j)).app V) i).symm ≪≫ φ ≪≫
      eqToIso ?_⟩
    change V (i - -(j : ℤ) + 1) = V (i - (-(j : ℤ) - 1))
    congr 1
    omega

/-- The **graded vector space `k` placed in degree `0`**, using Mathlib's canonical single-degree
graded object. -/
noncomputable abbrev unit : GVS k :=
  (GradedObject.single₀ ℤ).obj (ModuleCat.of k k)

/-- The piece of `unit k` in degree `0` is the field `k`. -/
noncomputable def unitObjZeroLinearEquiv : (unit k 0 : Type u) ≃ₗ[k] k :=
  (GradedObject.singleObjApplyIso (0 : ℤ) (ModuleCat.of k k)).toLinearEquiv

/-- The pieces of `unit k` away from degree `0` vanish. -/
theorem isZero_unit_obj {i : ℤ} (hi : i ≠ 0) : IsZero (unit k i) :=
  (GradedObject.isInitialSingleObjApply 0 (ModuleCat.of k k) i hi).isZero

private noncomputable def homUnitHomLinearEquiv (V : GVS k) :
    (unit k ⟶ V) ≃ₗ[k] (ModuleCat.of k k ⟶ V 0) where
  toFun f := f 0
  invFun f i :=
    if hi : i = 0 then
      (GradedObject.singleObjApplyIsoOfEq 0 (ModuleCat.of k k) i hi).hom ≫ f ≫
        eqToHom (congrArg V hi.symm)
    else 0
  left_inv f := by
    funext i
    by_cases hi : i = 0
    · subst i
      simp only [↓reduceDIte, eqToHom_refl]
      cat_disch
    · exact (isZero_unit_obj k hi).eq_of_src _ _
  right_inv f := by
    simp only [↓reduceDIte, eqToHom_refl, Category.comp_id]
    change (𝟙 (ModuleCat.of k k)) ≫ f = f
    cat_disch
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem homUnitHomLinearEquiv_symm_apply_zero
    {V : GVS k} (f : ModuleCat.of k k ⟶ V 0) :
    (homUnitHomLinearEquiv k V).symm f 0 = f := by
  simp only [Int.reduceNeg]
  cat_disch

/-- **Morphisms out of `unit k` are the degree-zero piece** of the target: a morphism is
determined by the image of `1` in degree `0`. -/
noncomputable def homUnitLinearEquiv (V : GVS k) :
    (unit k ⟶ V) ≃ₗ[k] V 0 :=
  (homUnitHomLinearEquiv k V).trans
    (ModuleCat.homLinearEquiv.trans (LinearMap.ringLmapEquivSelf k k _))

/-- `unit k` is projective because epimorphisms of graded objects are componentwise epimorphisms
and the one-dimensional module `k` is projective. -/
instance : Projective (unit k) where
  factors {E X} f e _ := by
    let _ : Epi ((piEquivalenceFunctorDiscrete ℤ (ModuleCat.{u} k)).functor.map e) :=
      inferInstance
    let _ : Epi (e 0) := by
      change Epi (((piEquivalenceFunctorDiscrete ℤ (ModuleCat.{u} k)).functor.map e).app ⟨0⟩)
      infer_instance
    have : Projective (ModuleCat.of k k) :=
      ModuleCat.projective_of_free (Module.Basis.singleton Unit k)
    obtain ⟨g, hg⟩ := Projective.factors (homUnitHomLinearEquiv k X f) (e 0)
    refine ⟨(homUnitHomLinearEquiv k E).symm g, ?_⟩
    apply (homUnitHomLinearEquiv k X).injective
    change (homUnitHomLinearEquiv k E).symm g 0 ≫ e 0 = f 0
    rw [homUnitHomLinearEquiv_symm_apply_zero]
    exact hg

/-- Every piece of `unit k` is finite-dimensional. -/
theorem finiteDimensional_unit_obj (i : ℤ) : FiniteDimensional k (unit k i) := by
  by_cases hi : i = 0
  · subst hi
    exact Module.Finite.equiv (unitObjZeroLinearEquiv k).symm
  · have := ModuleCat.subsingleton_of_isZero (isZero_unit_obj k hi)
    infer_instance

/-- The piece of `unit k` in degree `i` has dimension `1` if `i = 0` and `0` otherwise. -/
theorem finrank_unit_obj (i : ℤ) :
    Module.finrank k (unit k i) = if i = 0 then 1 else 0 := by
  split_ifs with hi
  · subst hi
    rw [(unitObjZeroLinearEquiv k).finrank_eq, Module.finrank_self]
  · have := ModuleCat.subsingleton_of_isZero (isZero_unit_obj k hi)
    exact Module.finrank_zero_of_subsingleton

/-- The morphisms from `M = unit k` to its shift `M{j}` are the piece of `M` in degree `-j`. -/
theorem nonempty_linearEquiv_hom_unit_shift_pow (j : ℤ) :
    Nonempty ((unit k ⟶ ((σ k) ^ j).functor.obj (unit k)) ≃ₗ[k] unit k (-j)) := by
  obtain ⟨φ⟩ := nonempty_iso_shift_pow_obj k j (unit k) 0
  rw [zero_sub] at φ
  exact ⟨(homUnitLinearEquiv k _).trans φ.toLinearEquiv⟩

/-- **The degree-zero morphisms `Hom(M, M{j})`** between `M = unit k` and its shifts: they form a
one-dimensional space for `j = 0` and vanish otherwise. -/
theorem finrank_hom_unit_shift_pow (j : ℤ) :
    Module.finrank k (unit k ⟶ ((σ k) ^ j).functor.obj (unit k)) =
      if j = 0 then 1 else 0 := by
  obtain ⟨φ⟩ := nonempty_linearEquiv_hom_unit_shift_pow k j
  rw [φ.finrank_eq, finrank_unit_obj]
  simp only [neg_eq_zero]

/-- The graded morphism spaces `Hom(M, M{j})` have finite Laurent support. -/
theorem hasFiniteLaurentSupport_hom_unit :
    HasFiniteLaurentSupport k fun j ↦ unit k ⟶ ((σ k) ^ j).functor.obj (unit k) := by
  refine HasFiniteLaurentSupport.of_finset (fun j ↦ ?_) {0} fun j hj ↦ ?_
  · obtain ⟨φ⟩ := nonempty_linearEquiv_hom_unit_shift_pow k j
    have := finiteDimensional_unit_obj k (-j)
    exact Module.Finite.equiv φ.symm
  · obtain ⟨φ⟩ := nonempty_linearEquiv_hom_unit_shift_pow k j
    have := ModuleCat.subsingleton_of_isZero (isZero_unit_obj k (neg_ne_zero.2
      (Finset.notMem_singleton.1 hj)))
    exact φ.toEquiv.subsingleton

/-- **The shifts of `M = unit k` are genuinely different**: `M{j}` is not isomorphic to `M` for
`j ≠ 0`, since there are no nonzero morphisms `M ⟶ M{j}` while `M` has nonzero endomorphisms. -/
theorem isEmpty_iso_unit_shift_pow {j : ℤ} (hj : j ≠ 0) :
    IsEmpty (unit k ≅ ((σ k) ^ j).functor.obj (unit k)) := by
  refine ⟨fun f ↦ ?_⟩
  have : Subsingleton (unit k ⟶ ((σ k) ^ j).functor.obj (unit k)) := by
    have := (hasFiniteLaurentSupport_hom_unit k).finiteDimensional j
    rw [← Module.finrank_zero_iff (R := k), finrank_hom_unit_shift_pow]
    simp only [hj, ↓reduceIte]
  have hid : 𝟙 (unit k) = 0 := by
    rw [← f.hom_inv_id, Subsingleton.elim f.hom 0, zero_comp]
  have : Subsingleton (unit k ⟶ ((σ k) ^ (0 : ℤ)).functor.obj (unit k)) :=
    ⟨fun a b ↦ by rw [← Category.id_comp a, ← Category.id_comp b, hid, zero_comp, zero_comp]⟩
  have hone := finrank_hom_unit_shift_pow k 0
  rw [Module.finrank_zero_of_subsingleton] at hone
  simp at hone

/-! ### Totalizing the grading -/

private noncomputable abbrev gradedConst : ModuleCat.{u} k ⥤ GVS k :=
  Functor.const (Discrete ℤ) ⋙ (piEquivalenceFunctorDiscrete ℤ (ModuleCat.{u} k)).inverse

private noncomputable def totalGradedConstAdj :
    GradedObject.total ℤ (ModuleCat.{u} k) ⊣ gradedConst k := by
  change ((piEquivalenceFunctorDiscrete ℤ (ModuleCat.{u} k)).functor ⋙ colim) ⊣ _
  exact (piEquivalenceFunctorDiscrete ℤ (ModuleCat.{u} k)).toAdjunction.comp colimConstAdj

/-- **Totalizing the grading is invariant under the shift**: `{1} ⋙ U ≅ U`. Both functors are left
adjoint to the constant functor. -/
noncomputable def shiftCompTotalIso :
    (σ k).functor ⋙ GradedObject.total ℤ (ModuleCat.{u} k) ≅
      GradedObject.total ℤ (ModuleCat.{u} k) :=
  Adjunction.leftAdjointUniq
    ((σ k).toAdjunction.comp (totalGradedConstAdj k))
    ((totalGradedConstAdj k).ofNatIsoRight (Iso.refl _))

private noncomputable def coproductUnitIso :
    (∐ fun i : ℤ ↦ unit k i) ≅ ModuleCat.of k k where
  hom := Sigma.desc fun i ↦
    if hi : i = 0 then
      (GradedObject.singleObjApplyIsoOfEq 0 (ModuleCat.of k k) i hi).hom
    else 0
  inv := (GradedObject.singleObjApplyIso 0 (ModuleCat.of k k)).inv ≫ Sigma.ι (unit k) 0
  hom_inv_id := by
    apply Sigma.hom_ext
    intro i
    by_cases hi : i = 0
    · subst i
      simp only [colimit.ι_desc_assoc, Discrete.functor_obj_eq_as, Cofan.mk_pt, Cofan.mk_ι_app,
        ↓reduceDIte, Iso.hom_inv_id_assoc, Category.comp_id]
    · exact (isZero_unit_obj k hi).eq_of_src _ _
  inv_hom_id := by
    rw [Category.assoc, Sigma.ι_comp_desc]
    simp [GradedObject.singleObjApplyIsoOfEq, GradedObject.single]

/-- **The total space underlying `M = unit k` is `k`**. -/
noncomputable def totalObjUnitIso :
    (GradedObject.total ℤ (ModuleCat.{u} k)).obj (unit k) ≅ ModuleCat.of k k :=
  coproductUnitIso k

/-! ### The q-Euler characteristic of `M = unit k` -/

section GradedExtEuler

variable [HasExt.{w} (GVS k)]

/-- The pair `(M, M)` is graded Euler-admissible: `M` is projective and its graded morphism spaces
have finite Laurent support. -/
theorem isGradedEulerAdmissible_unit :
    IsGradedEulerAdmissible.{w} k (σ k) (unit k) (unit k) :=
  isGradedEulerAdmissible_of_projective k (σ k) _ _ (hasFiniteLaurentSupport_hom_unit k)

/-- **`χ_q(M, M) = 1`**: the only surviving bigraded `Ext` group of `(M, M)` is the
one-dimensional space of degree-zero endomorphisms. -/
theorem gradedExtEuler_unit :
    gradedExtEuler k (σ k) (isGradedEulerAdmissible_unit.{w} k) = 1 := by
  rw [gradedExtEuler_projective k (σ k) (hasFiniteLaurentSupport_hom_unit k), ← T_zero]
  ext j
  rw [coeff_targetShiftGradedDimension, finrank_hom_unit_shift_pow, T_apply]
  simp [eq_comm (a := (0 : ℤ))]

/-- **`χ_q(M, M{1}) = q`**, that is, `q · χ_q(M, M)`: the q-Euler form is q-linear in its second
argument. -/
theorem gradedExtEuler_unit_shiftTarget :
    gradedExtEuler k (σ k) (isGradedEulerAdmissible_unit.{w} k).shiftTarget = T 1 := by
  rw [gradedExtEuler_shiftTarget (isGradedEulerAdmissible_unit.{w} k), gradedExtEuler_unit,
    mul_one]

/-- **`χ_q(M{1}, M) = q⁻¹`**, that is, `q⁻¹ · χ_q(M, M)`: the q-Euler form is q-antilinear in its
first argument. -/
theorem gradedExtEuler_unit_shiftSource :
    gradedExtEuler k (σ k) (isGradedEulerAdmissible_unit.{w} k).shiftSource = T (-1) := by
  rw [gradedExtEuler_shiftSource (isGradedEulerAdmissible_unit.{w} k), gradedExtEuler_unit,
    mul_one]

/-- At `q = ε` for a unit `ε : ℤˣ`, the value `χ_q(M, M{1})` becomes `ε`. -/
theorem laurentEval_gradedExtEuler_unit_shiftTarget (ε : ℤˣ) :
    laurentEval ε (gradedExtEuler k (σ k) (isGradedEulerAdmissible_unit.{w} k).shiftTarget) =
      ε := by
  rw [gradedExtEuler_unit_shiftTarget, laurentEval_T_one]

/-- At `q = ε` for a unit `ε : ℤˣ`, the value `χ_q(M{1}, M)` becomes `ε⁻¹`. -/
theorem laurentEval_gradedExtEuler_unit_shiftSource (ε : ℤˣ) :
    laurentEval ε (gradedExtEuler k (σ k) (isGradedEulerAdmissible_unit.{w} k).shiftSource) =
      ((ε⁻¹ : ℤˣ) : ℤ) := by
  rw [gradedExtEuler_unit_shiftSource, laurentEval_T, zpow_neg_one]

/-- **At `q = -1` a single shift changes the sign**: `χ_q(M, M{1})` specializes to the negative of
the specialization of `χ_q(M, M)`. -/
theorem laurentEval_neg_one_gradedExtEuler_unit_shiftTarget :
    laurentEval (-1 : ℤˣ)
        (gradedExtEuler k (σ k) (isGradedEulerAdmissible_unit.{w} k).shiftTarget) =
      -laurentEval (-1 : ℤˣ) (gradedExtEuler k (σ k) (isGradedEulerAdmissible_unit.{w} k)) := by
  rw [laurentEval_gradedExtEuler_unit_shiftTarget, gradedExtEuler_unit, map_one, Units.val_neg,
    Units.val_one]

end GradedExtEuler

/-! ### Comparison with the underlying ungraded pair `(U M, U M)` -/

section Comparison

variable [HasExt.{w'} (ModuleCat.{u} k)]

/-- **The ungraded Ext-Euler characteristic `χ(k, k) = 1`** in `ModuleCat k`, for any
admissibility witness: `k` is projective with one-dimensional endomorphisms. -/
theorem extEuler_moduleCat_self
    (h : IsEulerAdmissible.{w'} k (ModuleCat.of k k) (ModuleCat.of k k)) :
    extEuler.{w'} k h = 1 := by
  have : Projective (ModuleCat.of k k) :=
    ModuleCat.projective_of_free (Module.Basis.singleton Unit k)
  rw [extEuler_projective, ModuleCat.homLinearEquiv.finrank_eq,
    (LinearMap.ringLmapEquivSelf k k k).finrank_eq, Module.finrank_self, Nat.cast_one]

variable [HasExt.{w} (GVS k)]

/-- **The graded `Ext` groups of `(M, M)` assemble into the ungraded ones of `(U M, U M)`**: in
each cohomological degree `n`, `⨁ j, Extⁿ(M, M{j}) ≅ Extⁿ_k(U M, U M)`. Both sides are computed:
they are one-dimensional for `n = 0` and zero otherwise. -/
theorem isGradedExtComparison_unit :
    IsGradedExtComparison.{w, w'} k (σ k) (unit k) (unit k)
      ((GradedObject.total ℤ (ModuleCat.{u} k)).obj (unit k))
      ((GradedObject.total ℤ (ModuleCat.{u} k)).obj (unit k)) := by
  have : Projective ((GradedObject.total ℤ (ModuleCat.{u} k)).obj (unit k)) :=
    have := ModuleCat.projective_of_free (Module.Basis.singleton Unit k)
    Projective.of_iso (totalObjUnitIso k).symm this
  have hhom := Linear.homCongr k (totalObjUnitIso k) (totalObjUnitIso k)
  have : FiniteDimensional k
      ((GradedObject.total ℤ (ModuleCat.{u} k)).obj (unit k) ⟶
        (GradedObject.total ℤ (ModuleCat.{u} k)).obj (unit k)) :=
    Module.Finite.equiv (hhom.trans (ModuleCat.homLinearEquiv (S := k))).symm
  have hadm := isEulerAdmissible_of_projective.{w'} k
    ((GradedObject.total ℤ (ModuleCat.{u} k)).obj (unit k))
    ((GradedObject.total ℤ (ModuleCat.{u} k)).obj (unit k))
  refine ⟨fun n ↦ ?_⟩
  have hfin := (isGradedEulerAdmissible_unit.{w} k).internallyFinite.finiteLaurentSupport n
  have := hfin.finiteDimensional 0
  have := hadm.isExtFinite.finiteDimensional n
  -- In internal degree `j ≠ 0` there are no morphisms and no higher `Ext`.
  have hsub (j : ℤ) (hj : j ≠ 0) :
      Subsingleton (GradedExt.{w} (σ k) (unit k) (unit k) n j) := by
    have := hfin.finiteDimensional j
    rw [← Module.finrank_zero_iff (R := k)]
    cases n with
    | zero =>
      rw [(Ext.linearEquiv₀ (R := k)).finrank_eq, finrank_hom_unit_shift_pow]
      simp only [hj, ↓reduceIte]
    | succ m =>
      have := (isExtBoundedBy_one_of_projective.{w} (unit k)
        (((σ k) ^ j).functor.obj (unit k))).subsingleton (Nat.le_add_left 1 m)
      exact Module.finrank_zero_of_subsingleton
  -- In internal degree `0` both sides have the same dimension.
  refine ⟨(DirectSum.componentLinearEquiv _ 0 hsub).trans (LinearEquiv.ofFinrankEq _ _ ?_)⟩
  cases n with
  | zero =>
    rw [(Ext.linearEquiv₀ (R := k)).finrank_eq, finrank_hom_unit_shift_pow,
      (Ext.linearEquiv₀ (R := k)).finrank_eq, hhom.finrank_eq,
      ModuleCat.homLinearEquiv.finrank_eq,
      (LinearMap.ringLmapEquivSelf k k k).finrank_eq, Module.finrank_self]
    simp only [↓reduceIte]
  | succ m =>
    have := (isExtBoundedBy_one_of_projective.{w} (unit k)
      (((σ k) ^ (0 : ℤ)).functor.obj (unit k))).subsingleton (Nat.le_add_left 1 m)
    have := (isExtBoundedBy_one_of_projective.{w'}
      ((GradedObject.total ℤ (ModuleCat.{u} k)).obj (unit k))
      ((GradedObject.total ℤ (ModuleCat.{u} k)).obj (unit k))).subsingleton
        (Nat.le_add_left 1 m)
    rw [Module.finrank_zero_of_subsingleton, Module.finrank_zero_of_subsingleton]

/-- **At `q = 1` the q-Euler characteristic of `(M, M)` is the ordinary Ext-Euler characteristic of
the underlying ungraded pair `(U M, U M)`**, as it must be after forgetting the grading. -/
theorem laurentEval_one_gradedExtEuler_unit :
    laurentEval (1 : ℤˣ) (gradedExtEuler k (σ k) (isGradedEulerAdmissible_unit.{w} k)) =
      extEuler.{w'} k ((isGradedExtComparison_unit.{w, w'} k).isEulerAdmissible
        (isGradedEulerAdmissible_unit.{w} k)) :=
  (isGradedExtComparison_unit.{w, w'} k).laurentEval_one_gradedExtEuler _

end Comparison

end GradedVectorSpace

end TauCeti
