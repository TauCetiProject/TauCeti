/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Belyi.BaseChange
public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Fibre
public import TauCeti.FieldTheory.FunctionField.Place.Extension.LocalData
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Place
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Ramification
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Regular
import TauCeti.FieldTheory.RatFunc.Transcendental
import TauCeti.RingTheory.TensorProduct.Reduced

/-!
# Geometric ramification partitions

For a function field with perfect, exact constants, extending the constants (algebraically or
transcendentally) to an algebraically closed field splits a place of degree `f` into `f` rational
places, without changing its ramification index. Consequently the unweighted ramification indices
in each geometric marked fibre are exactly the weighted ramification partition over the original
constants. Multiplicities, not just the sets of indices, are preserved.

When the base constant field `k` is already algebraically closed, extending further to ANY field
`k' / k` (algebraically closed or not) induces a ramification-preserving bijection on each marked
fibre (`TauCeti.Place.map_fst_localData_markedPlace_eq_of_isAlgClosed_base`). Factoring an
arbitrary extension `k → k'` to an algebraically closed `k'` through the relative algebraic closure
of `k` in `k'` combines this invariance with the algebraic splitting case to yield
`TauCeti.Place.map_fst_localData_markedPlace_eq_parts_weightedRamificationPartition`.

The comparison is stated for a compositum of function fields with compatible rational parameters.
It does not require the map to be unramified away from the marked fibres.

## Main results

* `TauCeti.Place.map_fst_localData_markedPlace_eq_of_isAlgClosed_base`: over an algebraically
  closed constant field `k`, extending constants to any field `k' / k` preserves the multiset of
  ramification indices over each marked place.
* `TauCeti.Place.map_fst_localData_markedPlace_eq_parts_weightedRamificationPartition`: over a
  perfect exact constant field `k`, extending constants to any algebraically closed field `k' / k`
  identifies the geometric ramification indices over each marked place with the parts of the
  weighted ramification partition over `k`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Section III.6,
  especially Theorem 3.6.3.
-/

public section

namespace TauCeti.Place

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [Algebra (RatFunc k') F'] [IsScalarTower k' (RatFunc k') F']
  [PerfectField k] [IsAlgClosed k']
  [FiniteDimensional (RatFunc k) F] [FiniteDimensional (RatFunc k') F']

private theorem map_fst_localData_eq_sum {k₀ F₀ : Type*} [Field k₀] [Field F₀] [Algebra k₀ F₀]
    [Algebra (RatFunc k₀) F₀] [IsScalarTower k₀ (RatFunc k₀) F₀] [FiniteDimensional (RatFunc k₀) F₀]
    (i : Fin 3) :
    (localData (k' := k₀) (F' := F₀) k₀ (RatFunc k₀) (markedPlace k₀ i)).map Prod.fst =
      ∑ Q ∈ (finite_setOf_restrict_eq (k' := k₀) (F' := F₀) k₀ (RatFunc k₀)
        (markedPlace k₀ i)).toFinset, ({ramificationIdx (RatFunc k₀) Q} : Multiset ℕ) := by
  let s := (finite_setOf_restrict_eq (k' := k₀) (F' := F₀) k₀ (RatFunc k₀)
    (markedPlace k₀ i)).toFinset
  simpa only [localData_def, Multiset.map_map, Function.comp_def,
    Finset.sum_eq_multiset_sum, s] using
    (Multiset.sum_map_singleton (s.val.map (ramificationIdx (RatFunc k₀)))).symm

private theorem map_fst_localData_markedPlace_eq_of_isAlgebraic [Algebra.IsAlgebraic k k']
    (hex : IsIntegrallyClosedIn k F) (hcomp : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) (i : Fin 3) :
    (localData (k' := k') (F' := F') k' (RatFunc k') (markedPlace k' i)).map Prod.fst =
      (weightedRamificationPartition (k' := k) (F' := F) k (RatFunc k)
        (IsFunctionField.ratFunc k) (markedPlace k i)).parts := by
  classical
  let := isAlgebraic_of_constantCompositum_eq_top (k := k) hcomp
  have hF : IsFunctionField k F := (IsFunctionField.ratFunc k).finite_extension
  let s := (finite_setOf_restrict_eq (k' := k) (F' := F) k (RatFunc k) (markedPlace k i)).toFinset
  let s' :=
    (finite_setOf_restrict_eq (k' := k') (F' := F') k' (RatFunc k') (markedPlace k' i)).toFinset
  have hmem (Q' : Place k' F') : Q' ∈ s' ↔ Q'.restrict k F ∈ s := by
    simpa only [s, s', Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using
      (restrict_restrict_eq_markedPlace_iff hX Q' i).symm
  have hdeg (Q : Place k F) (hQ : Q ∈ s) : relativeDegree k (RatFunc k) Q = Q.degree := by
    have hQ' : Q.restrict k (RatFunc k) = markedPlace k i := by
      simpa only [s, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hQ
    have hmark : (markedPlace k i).degree = 1 := by
      fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, markedPlace_zero,
        markedPlace_one, markedPlace_two, degree_adicOfIrreducible_X_sub_C,
        degree_adicOfIrreducible, Polynomial.natDegree_X, degree_infty]
    simpa only [hQ', hmark, one_mul] using
      (degree_eq_degree_restrict_mul_relativeDegree k (RatFunc k) Q).symm
  have hcard (Q : Place k F) (hQ : Q ∈ s) :
      (s'.filter fun Q' => Q'.restrict k F = Q).card = relativeDegree k (RatFunc k) Q := by
    have hf := finite_setOf_restrict_eq_of_constantCompositum_eq_top hF hcomp Q
    have hs : s'.filter (fun Q' => Q'.restrict k F = Q) = hf.toFinset := by
      ext Q'; simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, hmem]
      exact and_iff_right_of_imp fun h => h ▸ hQ
    let := Q.finiteDimensional_residueField hF
    let : IsAlgClosure k k' := ⟨inferInstance, inferInstance⟩
    rw [hs, hdeg Q hQ, ← Set.ncard_eq_toFinset_card _ hf]
    exact ncard_setOf_restrict_eq_eq_degree_of_constantCompositum_eq_top hF hex hcomp Q
      (IsAlgClosed.lift : Q.ResidueField →ₐ[k] k')
  have hdown : (weightedRamificationPartition (k' := k) (F' := F) k (RatFunc k)
        (IsFunctionField.ratFunc k) (markedPlace k i)).parts =
      ∑ Q ∈ s, Multiset.replicate (relativeDegree k (RatFunc k) Q)
        (ramificationIdx (RatFunc k) Q) := by
    rw [parts_weightedRamificationPartition, localData_def, Multiset.bind_map]; rfl
  rw [map_fst_localData_eq_sum (k₀ := k') (F₀ := F'), hdown,
    ← Finset.sum_fiberwise_of_maps_to (fun Q' hQ' => (hmem Q').mp hQ')]
  refine Finset.sum_congr rfl fun Q hQ => ?_
  rw [← hcard Q hQ, ← Multiset.nsmul_singleton, ← Finset.sum_const]
  exact Finset.sum_congr rfl fun Q' hQ' => by
    rw [ramificationIdx_ratFunc_eq_of_constantCompositum_eq_top hcomp hX Q',
      (Finset.mem_filter.mp hQ').2]

omit [PerfectField k] [IsAlgClosed k'] in
/-- **Over an algebraically closed base field, extending constants to any field `k' / k` preserves
the multiset of ramification indices over each marked place**, because every place over `k` has
residue degree `1` and extends uniquely to a place of `F'` nontrivial on `F`, while places of `F'`
trivial on `F` never lie over `{0, 1, ∞}`. -/
theorem map_fst_localData_markedPlace_eq_of_isAlgClosed_base [IsAlgClosed k]
    (hex : IsIntegrallyClosedIn k F) (hcomp : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) (i : Fin 3) :
    (localData (k' := k') (F' := F') k' (RatFunc k') (markedPlace k' i)).map Prod.fst =
      (localData (k' := k) (F' := F) k (RatFunc k) (markedPlace k i)).map Prod.fst := by
  classical
  have hF : IsFunctionField k F := (IsFunctionField.ratFunc k).finite_extension
  have H := linearDisjoint_of_isGeometricallyReduced_ratFunc hex hX
  have hexU (Q : Place k F) : ∃! Q' : Place k' F',
      Q'.integers.comap (algebraMap F F') = Q.integers :=
    existsUnique_integers_comap_eq_of_degree_eq_one hF H hcomp
      (Q.degree_eq_one_of_isAlgClosed_of_isFunctionField hF)
  let liftPlace (Q : Place k F) : Place k' F' := (hexU Q).choose
  have hlift (Q : Place k F) : (liftPlace Q).integers.comap (algebraMap F F') = Q.integers :=
    (hexU Q).choose_spec.1
  rw [map_fst_localData_eq_sum (k₀ := k') (F₀ := F'), map_fst_localData_eq_sum (k₀ := k) (F₀ := F)]
  refine (Finset.sum_nbij liftPlace ?_ ?_ ?_ ?_).symm
  · intro Q hQ
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hQ ⊢
    exact (restrict_eq_markedPlace_iff_of_integers_comap_eq hX (hlift Q) i).mp hQ
  · exact fun Q₁ _ Q₂ _ hEq ↦ integers_injective (by rw [← hlift Q₁, hEq, hlift Q₂])
  · intro Q' hQ'
    simp only [Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hQ'
    rcases isTrivialOn_or_existsUnique_integers_comap_eq hF Q' with htriv | ⟨Q, hQ, -⟩
    · exact (restrict_notMem_zeroOneInfty_of_isTrivialOn hX htriv
        (hQ' ▸ range_markedPlace k' ▸ ⟨i, rfl⟩)).elim
    · refine ⟨Q, ?_, ((hexU Q).choose_spec.2 Q' hQ).symm⟩
      simp only [Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      exact (restrict_eq_markedPlace_iff_of_integers_comap_eq hX hQ i).mpr hQ'
  · exact fun Q _ ↦ by rw [ramificationIdx_ratFunc_eq_of_integers_comap_eq hex hcomp hX (hlift Q)]

/-- After extending constants to an algebraically closed field, each marked fibre has
one ramification index for each weighted part of the original fibre. A residue degree `f`
over the original constants contributes `f` geometric points. -/
theorem map_fst_localData_markedPlace_eq_parts_weightedRamificationPartition
    (hex : IsIntegrallyClosedIn k F) (hcomp : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) (i : Fin 3) :
    (localData (k' := k') (F' := F') k' (RatFunc k') (markedPlace k' i)).map Prod.fst =
      (weightedRamificationPartition (k' := k) (F' := F) k (RatFunc k)
        (IsFunctionField.ratFunc k) (markedPlace k i)).parts := by
  let kbar := algebraicClosure k k'
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  let F₁ := constantCompositum F kbar F'
  let _ : Algebra kbar F₁ := constantCompositumAlgebra F kbar F'
  have : IsScalarTower kbar F₁ F' := isScalarTower_constantCompositum F kbar F'
  have : IsScalarTower k kbar F₁ := isScalarTower_base_constantCompositum k F kbar F'
  have hcomp₁ : constantCompositum F kbar F₁ = ⊤ :=
    (constantCompositum_eq_top_iff F kbar F' F₁).2 rfl
  have hcomp₂ : constantCompositum F₁ k' F' = ⊤ :=
    constantCompositum_eq_top_of_eq_top F k' F' F₁ hcomp
  have hx₁ : Transcendental kbar (algebraMap F F₁ (algebraMap (RatFunc k) F RatFunc.X)) :=
    (linearDisjoint_fieldRange_of_isIntegrallyClosedIn hex).transcendental_algebraMap <|
      (transcendental_algebraMap_iff (FaithfulSMul.algebraMap_injective (RatFunc k) F)).mpr
        RatFunc.transcendental_X
  let _ := ratFuncAlgebraOfTranscendental hx₁
  have := isScalarTower_ratFuncAlgebraOfTranscendental hx₁
  have hX₁ : algebraMap F F₁ (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc kbar) F₁ RatFunc.X :=
    (algebraMap_ratFuncAlgebraOfTranscendental_X hx₁).symm
  have hX₂ : algebraMap F₁ F' (algebraMap (RatFunc kbar) F₁ RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X := by
    rw [← hX₁, ← IsScalarTower.algebraMap_apply F F₁ F', hX]
  have : FiniteDimensional (RatFunc kbar) F₁ :=
    finiteDimensional_ratFunc_of_constantCompositum_eq_top hcomp₁ hX₁
  exact (map_fst_localData_markedPlace_eq_of_isAlgClosed_base
    (hex.of_constantCompositum_eq_top hcomp₁) hcomp₂ hX₂ i).trans
    (map_fst_localData_markedPlace_eq_of_isAlgebraic hex hcomp₁ hX₁ i)

end TauCeti.Place
