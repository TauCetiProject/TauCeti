/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.ForgetGrading
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.Shift
public import TauCeti.CategoryTheory.Adjunction.Linear
public import TauCeti.CategoryTheory.Linear.FunctorCategory

/-!
# The q-Euler form of graded vector spaces

Let `k` be a field. A `ℤ`-graded `k`-vector space is a functor `Discrete ℤ ⥤ ModuleCat k`, that
is, a family `(Vᵢ)` of vector spaces indexed by the internal degree; these form a `k`-linear
abelian category `TauCeti.GradedVectorSpace k`. Its grading shift `V ↦ V{1}` moves every piece up
by one degree, `(V{1})ᵢ = V_{i-1}`, and is a `k`-linear autoequivalence.

The one-dimensional space `M = k` placed in degree `0` is the smallest nontrivial test of the
q-Euler formalism: it is projective, it is not isomorphic to any of its shifts `M{j}` with
`j ≠ 0`, its degree-zero endomorphisms are one-dimensional, and it has no higher `Ext`. Hence

```text
χ_q(M, M) = 1,    χ_q(M, M{1}) = q = q χ_q(M, M),    χ_q(M{1}, M) = q⁻¹ = q⁻¹ χ_q(M, M).
```

At `q = 1` the three values agree, while at `q = -1` a single shift changes the sign.

The ungraded vector space underlying `M` is the one-dimensional space `k`. In every cohomological
degree the bigraded `Ext` groups of `(M, M)` assemble into the ungraded `Ext` groups of `(k, k)` in
`ModuleCat k`; this is checked directly, by computing both sides, and it identifies the value of
`χ_q(M, M)` at `q = 1` with the ordinary Ext-Euler characteristic `χ(k, k) = 1`.

## Main definitions

* `TauCeti.GradedVectorSpace k`: `ℤ`-graded `k`-vector spaces.
* `TauCeti.GradedVectorSpace.shift k`: the grading shift, with `(V{1})ᵢ = V_{i-1}`.
* `TauCeti.GradedVectorSpace.unit k`: the field `k` placed in degree `0`, the left adjoint of
  evaluation in degree `0` applied to `k`.
* `TauCeti.GradedVectorSpace.homUnitLinearEquiv`: morphisms out of `unit k` are the degree-zero
  piece of the target.

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
  assemble into the `Ext` groups of `(k, k)` in `ModuleCat k`.
* `TauCeti.GradedVectorSpace.laurentEval_one_gradedExtEuler_unit`: `χ_q(M, M)` at `q = 1` is the
  ordinary Ext-Euler characteristic of `(k, k)`, which is `1` by
  `TauCeti.GradedVectorSpace.extEuler_moduleCat_self`.

## Implementation notes

Graded vector spaces are modelled as the functor category `Discrete ℤ ⥤ ModuleCat k` rather than
as Mathlib's `CategoryTheory.GradedObject ℤ (ModuleCat k)`, because the functor category already
carries Mathlib's abelian and linear structures. The object `M` is the left adjoint of evaluation
in degree `0` applied to `k`, so that its projectivity and the identification
`Hom(M, V) ≃ₗ[k] V₀` are instances of general adjunction facts.

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

/-- **`ℤ`-graded `k`-vector spaces**: families `(Vᵢ)_{i ∈ ℤ}` of `k`-vector spaces, as functors from
the discrete category on `ℤ`. Morphisms are degree-preserving families of linear maps. -/
abbrev GradedVectorSpace : Type (u + 1) :=
  Discrete ℤ ⥤ ModuleCat.{u} k

namespace GradedVectorSpace

/-- The **grading shift** `V ↦ V{1}` of graded vector spaces, moving each piece up by one degree:
`(V{1})ᵢ = V_{i-1}`. It is reindexing along the translation `i ↦ i + 1` of `ℤ`. -/
noncomputable def shift : GradedVectorSpace k ≌ GradedVectorSpace k :=
  (Discrete.equivalence (Equiv.addRight (1 : ℤ))).congrLeft

/-- The grading shift is additive, being precomposition with a functor. -/
instance : (shift k).functor.Additive :=
  inferInstanceAs ((Functor.whiskeringLeft _ _ (ModuleCat.{u} k)).obj
    (Discrete.equivalence (Equiv.addRight (1 : ℤ))).inverse).Additive

/-- The grading shift is `k`-linear, being precomposition with a functor. -/
instance : (shift k).functor.Linear k :=
  inferInstanceAs (((Functor.whiskeringLeft _ _ (ModuleCat.{u} k)).obj
    (Discrete.equivalence (Equiv.addRight (1 : ℤ))).inverse).Linear k)

/-- The piece of `V{1}` in degree `i` is the piece of `V` in degree `i - 1`. -/
@[simp]
theorem shift_functor_obj_obj (V : GradedVectorSpace k) (i : ℤ) :
    ((shift k).functor.obj V).obj ⟨i⟩ = V.obj ⟨i - 1⟩ :=
  (rfl)

/-- The piece of `V{-1}` in degree `i` is the piece of `V` in degree `i + 1`. -/
@[simp]
theorem shift_inverse_obj_obj (V : GradedVectorSpace k) (i : ℤ) :
    ((shift k).inverse.obj V).obj ⟨i⟩ = V.obj ⟨i + 1⟩ :=
  (rfl)

/-- **The iterated shift reindexes the grading**: the piece of `V{j}` in degree `i` is isomorphic
to the piece of `V` in degree `i - j`. -/
theorem nonempty_iso_shift_pow_obj (j : ℤ) (V : GradedVectorSpace k) (i : ℤ) :
    Nonempty ((((shift k) ^ j).functor.obj V).obj ⟨i⟩ ≅ V.obj ⟨i - j⟩) := by
  induction j using Int.induction_on generalizing V with
  | zero => exact ⟨eqToIso (by simp)⟩
  | succ j ih =>
    obtain ⟨φ⟩ := ih ((shift k).functor.obj V)
    refine ⟨(((shift k).powSuccIso j).app V).app ⟨i⟩ ≪≫ φ ≪≫ eqToIso ?_⟩
    rw [shift_functor_obj_obj, sub_sub]
  | pred j ih =>
    obtain ⟨φ⟩ := ih ((shift k).inverse.obj V)
    refine ⟨((((shift k).powPredIso (-j)).app V).app ⟨i⟩).symm ≪≫ φ ≪≫ eqToIso ?_⟩
    rw [shift_inverse_obj_obj]
    congr 2
    ring

/-- The **graded vector space `k` placed in degree `0`**: the left adjoint of evaluation in
degree `0`, applied to the one-dimensional space `k`. -/
noncomputable def unit : GradedVectorSpace k :=
  (evaluationLeftAdjoint (ModuleCat.{u} k) (⟨0⟩ : Discrete ℤ)).obj (ModuleCat.of k k)

/-- `unit k` is projective: it is the image of the projective module `k` under a left adjoint whose
right adjoint, evaluation in degree `0`, preserves epimorphisms. -/
instance : Projective (unit k) :=
  (evaluationAdjunctionRight (ModuleCat.{u} k) (⟨0⟩ : Discrete ℤ)).map_projective _
    (ModuleCat.projective_of_free (Module.Basis.singleton Unit k))

/-- **Morphisms out of `unit k` are the degree-zero piece** of the target: a morphism is
determined by the image of `1` in degree `0`. -/
noncomputable def homUnitLinearEquiv (V : GradedVectorSpace k) :
    (unit k ⟶ V) ≃ₗ[k] V.obj ⟨0⟩ :=
  ((evaluationAdjunctionRight (ModuleCat.{u} k) (⟨0⟩ : Discrete ℤ)).homLinearEquiv k _ V).trans
    (ModuleCat.homLinearEquiv.trans (LinearMap.ringLmapEquivSelf k k _))

/-- The piece of `unit k` in degree `0` is the field `k`. -/
noncomputable def unitObjZeroLinearEquiv : ((unit k).obj ⟨0⟩ : Type u) ≃ₗ[k] k :=
  letI : Unique ((⟨0⟩ : Discrete ℤ) ⟶ ⟨0⟩) := uniqueOfSubsingleton (𝟙 _)
  (coproductUniqueIso fun _ : (⟨0⟩ : Discrete ℤ) ⟶ ⟨0⟩ ↦ ModuleCat.of k k).toLinearEquiv

/-- The pieces of `unit k` away from degree `0` vanish. -/
theorem isZero_unit_obj {i : ℤ} (hi : i ≠ 0) : IsZero ((unit k).obj ⟨i⟩) := by
  have : IsEmpty ((⟨0⟩ : Discrete ℤ) ⟶ ⟨i⟩) := ⟨fun f ↦ hi (Discrete.eq_of_hom f).symm⟩
  rw [IsZero.iff_id_eq_zero]
  exact Sigma.hom_ext _ _ fun b ↦ isEmptyElim b

/-- Every piece of `unit k` is finite-dimensional. -/
theorem finiteDimensional_unit_obj (i : ℤ) : FiniteDimensional k ((unit k).obj ⟨i⟩) := by
  by_cases hi : i = 0
  · subst hi
    exact Module.Finite.equiv (unitObjZeroLinearEquiv k).symm
  · have := ModuleCat.subsingleton_of_isZero (isZero_unit_obj k hi)
    infer_instance

/-- The piece of `unit k` in degree `i` has dimension `1` if `i = 0` and `0` otherwise. -/
theorem finrank_unit_obj (i : ℤ) :
    Module.finrank k ((unit k).obj ⟨i⟩) = if i = 0 then 1 else 0 := by
  split_ifs with hi
  · subst hi
    rw [(unitObjZeroLinearEquiv k).finrank_eq, Module.finrank_self]
  · have := ModuleCat.subsingleton_of_isZero (isZero_unit_obj k hi)
    exact Module.finrank_zero_of_subsingleton

/-- The morphisms from `M = unit k` to its shift `M{j}` are the piece of `M` in degree `-j`. -/
theorem nonempty_linearEquiv_hom_unit_shift_pow (j : ℤ) :
    Nonempty ((unit k ⟶ ((shift k) ^ j).functor.obj (unit k)) ≃ₗ[k] (unit k).obj ⟨-j⟩) := by
  obtain ⟨φ⟩ := nonempty_iso_shift_pow_obj k j (unit k) 0
  rw [zero_sub] at φ
  exact ⟨(homUnitLinearEquiv k _).trans φ.toLinearEquiv⟩

/-- **The degree-zero morphisms `Hom(M, M{j})`** between `M = unit k` and its shifts: they form a
one-dimensional space for `j = 0` and vanish otherwise. -/
theorem finrank_hom_unit_shift_pow (j : ℤ) :
    Module.finrank k (unit k ⟶ ((shift k) ^ j).functor.obj (unit k)) =
      if j = 0 then 1 else 0 := by
  obtain ⟨φ⟩ := nonempty_linearEquiv_hom_unit_shift_pow k j
  rw [φ.finrank_eq, finrank_unit_obj]
  simp only [neg_eq_zero]

/-- The graded morphism spaces `Hom(M, M{j})` have finite Laurent support. -/
theorem hasFiniteLaurentSupport_hom_unit :
    HasFiniteLaurentSupport k fun j ↦ unit k ⟶ ((shift k) ^ j).functor.obj (unit k) := by
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
    IsEmpty (unit k ≅ ((shift k) ^ j).functor.obj (unit k)) := by
  refine ⟨fun f ↦ ?_⟩
  have : Subsingleton (unit k ⟶ ((shift k) ^ j).functor.obj (unit k)) := by
    have := (hasFiniteLaurentSupport_hom_unit k).finiteDimensional j
    rw [← Module.finrank_zero_iff (R := k), finrank_hom_unit_shift_pow]
    simp only [hj, ↓reduceIte]
  have hid : 𝟙 (unit k) = 0 := by
    rw [← f.hom_inv_id, Subsingleton.elim f.hom 0, zero_comp]
  have : Subsingleton (unit k ⟶ ((shift k) ^ (0 : ℤ)).functor.obj (unit k)) :=
    ⟨fun a b ↦ by rw [← Category.id_comp a, ← Category.id_comp b, hid, zero_comp, zero_comp]⟩
  have hone := finrank_hom_unit_shift_pow k 0
  rw [Module.finrank_zero_of_subsingleton] at hone
  simp at hone

/-! ### The q-Euler characteristic of `M = unit k` -/

section GradedExtEuler

variable [HasExt.{w} (GradedVectorSpace k)]

/-- The pair `(M, M)` is graded Euler-admissible: `M` is projective and its graded morphism spaces
have finite Laurent support. -/
theorem isGradedEulerAdmissible_unit :
    IsGradedEulerAdmissible.{w} k (shift k) (unit k) (unit k) :=
  isGradedEulerAdmissible_of_projective k (shift k) _ _ (hasFiniteLaurentSupport_hom_unit k)

/-- **`χ_q(M, M) = 1`**: the only surviving bigraded `Ext` group of `(M, M)` is the
one-dimensional space of degree-zero endomorphisms. -/
theorem gradedExtEuler_unit :
    gradedExtEuler k (shift k) (isGradedEulerAdmissible_unit.{w} k) = 1 := by
  rw [gradedExtEuler_projective k (shift k) (hasFiniteLaurentSupport_hom_unit k), ← T_zero]
  ext j
  rw [coeff_targetShiftGradedDimension, finrank_hom_unit_shift_pow, T_apply]
  simp [eq_comm (a := (0 : ℤ))]

/-- **`χ_q(M, M{1}) = q`**, that is, `q · χ_q(M, M)`: the q-Euler form is q-linear in its second
argument. -/
theorem gradedExtEuler_unit_shiftTarget :
    gradedExtEuler k (shift k) (isGradedEulerAdmissible_unit.{w} k).shiftTarget = T 1 := by
  rw [gradedExtEuler_shiftTarget (isGradedEulerAdmissible_unit.{w} k), gradedExtEuler_unit,
    mul_one]

/-- **`χ_q(M{1}, M) = q⁻¹`**, that is, `q⁻¹ · χ_q(M, M)`: the q-Euler form is q-antilinear in its
first argument. -/
theorem gradedExtEuler_unit_shiftSource :
    gradedExtEuler k (shift k) (isGradedEulerAdmissible_unit.{w} k).shiftSource = T (-1) := by
  rw [gradedExtEuler_shiftSource (isGradedEulerAdmissible_unit.{w} k), gradedExtEuler_unit,
    mul_one]

/-- At `q = ε` for a unit `ε : ℤˣ`, the value `χ_q(M, M{1})` becomes `ε`. -/
theorem laurentEval_gradedExtEuler_unit_shiftTarget (ε : ℤˣ) :
    laurentEval ε (gradedExtEuler k (shift k) (isGradedEulerAdmissible_unit.{w} k).shiftTarget) =
      ε := by
  rw [gradedExtEuler_unit_shiftTarget, laurentEval_T_one]

/-- At `q = ε` for a unit `ε : ℤˣ`, the value `χ_q(M{1}, M)` becomes `ε⁻¹`. -/
theorem laurentEval_gradedExtEuler_unit_shiftSource (ε : ℤˣ) :
    laurentEval ε (gradedExtEuler k (shift k) (isGradedEulerAdmissible_unit.{w} k).shiftSource) =
      ((ε⁻¹ : ℤˣ) : ℤ) := by
  rw [gradedExtEuler_unit_shiftSource, laurentEval_T, zpow_neg_one]

/-- **At `q = -1` a single shift changes the sign**: `χ_q(M, M{1})` specializes to the negative of
the specialization of `χ_q(M, M)`. -/
theorem laurentEval_neg_one_gradedExtEuler_unit_shiftTarget :
    laurentEval (-1 : ℤˣ)
        (gradedExtEuler k (shift k) (isGradedEulerAdmissible_unit.{w} k).shiftTarget) =
      -laurentEval (-1 : ℤˣ) (gradedExtEuler k (shift k) (isGradedEulerAdmissible_unit.{w} k)) := by
  rw [laurentEval_gradedExtEuler_unit_shiftTarget, gradedExtEuler_unit, map_one, Units.val_neg,
    Units.val_one]

end GradedExtEuler

/-! ### Comparison with the ungraded pair `(k, k)` -/

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

variable [HasExt.{w} (GradedVectorSpace k)]

/-- **The graded `Ext` groups of `(M, M)` assemble into the ungraded ones of `(k, k)`**: in each
cohomological degree `n`, `⨁ j, Extⁿ(M, M{j}) ≅ Extⁿ_k(k, k)`. Both sides are computed: they are
one-dimensional for `n = 0` and zero otherwise. -/
theorem isGradedExtComparison_unit :
    IsGradedExtComparison.{w, w'} k (shift k) (unit k) (unit k)
      (ModuleCat.of k k) (ModuleCat.of k k) := by
  have : Projective (ModuleCat.of k k) :=
    ModuleCat.projective_of_free (Module.Basis.singleton Unit k)
  have : FiniteDimensional k (ModuleCat.of k k ⟶ ModuleCat.of k k) :=
    Module.Finite.equiv (ModuleCat.homLinearEquiv (S := k)).symm
  have hadm := isEulerAdmissible_of_projective.{w'} k (ModuleCat.of k k) (ModuleCat.of k k)
  refine ⟨fun n ↦ ?_⟩
  have hfin := (isGradedEulerAdmissible_unit.{w} k).internallyFinite.finiteLaurentSupport n
  have := hfin.finiteDimensional 0
  have := hadm.isExtFinite.finiteDimensional n
  -- In internal degree `j ≠ 0` there are no morphisms and no higher `Ext`.
  have hsub (j : ℤ) (hj : j ≠ 0) :
      Subsingleton (GradedExt.{w} (shift k) (unit k) (unit k) n j) := by
    have := hfin.finiteDimensional j
    rw [← Module.finrank_zero_iff (R := k)]
    cases n with
    | zero =>
      rw [(Ext.linearEquiv₀ (R := k)).finrank_eq, finrank_hom_unit_shift_pow]
      simp only [hj, ↓reduceIte]
    | succ m =>
      have := (isExtBoundedBy_one_of_projective.{w} (unit k)
        (((shift k) ^ j).functor.obj (unit k))).subsingleton (Nat.le_add_left 1 m)
      exact Module.finrank_zero_of_subsingleton
  -- In internal degree `0` both sides have the same dimension.
  refine ⟨(DirectSum.componentLinearEquiv _ 0 hsub).trans (LinearEquiv.ofFinrankEq _ _ ?_)⟩
  cases n with
  | zero =>
    rw [(Ext.linearEquiv₀ (R := k)).finrank_eq, finrank_hom_unit_shift_pow,
      (Ext.linearEquiv₀ (R := k)).finrank_eq, ModuleCat.homLinearEquiv.finrank_eq,
      (LinearMap.ringLmapEquivSelf k k k).finrank_eq, Module.finrank_self]
    simp only [↓reduceIte]
  | succ m =>
    have := (isExtBoundedBy_one_of_projective.{w} (unit k)
      (((shift k) ^ (0 : ℤ)).functor.obj (unit k))).subsingleton (Nat.le_add_left 1 m)
    have := (isExtBoundedBy_one_of_projective.{w'} (ModuleCat.of k k)
      (ModuleCat.of k k)).subsingleton (Nat.le_add_left 1 m)
    rw [Module.finrank_zero_of_subsingleton, Module.finrank_zero_of_subsingleton]

/-- **At `q = 1` the q-Euler characteristic of `(M, M)` is the ordinary Ext-Euler characteristic of
`(k, k)`**, as it must be after forgetting the grading. -/
theorem laurentEval_one_gradedExtEuler_unit :
    laurentEval (1 : ℤˣ) (gradedExtEuler k (shift k) (isGradedEulerAdmissible_unit.{w} k)) =
      extEuler.{w'} k ((isGradedExtComparison_unit.{w, w'} k).isEulerAdmissible
        (isGradedEulerAdmissible_unit.{w} k)) :=
  (isGradedExtComparison_unit.{w, w'} k).laurentEval_one_gradedExtEuler _

end Comparison

end GradedVectorSpace

end TauCeti
