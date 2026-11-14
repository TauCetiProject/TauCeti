/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Belyi.BaseChange
public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Fibre
public import TauCeti.FieldTheory.FunctionField.Place.Extension.LocalData
import TauCeti.FieldTheory.AlgebraicClosure
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Algebraic
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Degree
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Place
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Ramification
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Regular
import TauCeti.FieldTheory.FunctionField.ConstantExtension.TensorProduct
import TauCeti.FieldTheory.FunctionField.SeparablyGenerated
import TauCeti.FieldTheory.RatFunc.Transcendental

/-!
# Geometric ramification partitions

For a function field with perfect, exact constants, extending the constants (algebraically or
transcendently)
to an algebraically closed field splits a place of degree `f` into `f` rational places,
without changing its ramification index. Consequently the
unweighted ramification indices in each geometric marked fibre are exactly the weighted
ramification partition over the original constants. Multiplicities, not just the sets of
indices, are preserved.

The comparison is stated for a compositum of function fields with compatible rational
parameters. It does not require the map to be unramified away from the marked fibres.

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
  [PerfectField k] [IsAlgClosed k'] [Algebra.IsAlgebraic k k']
  [FiniteDimensional (RatFunc k) F] [FiniteDimensional (RatFunc k') F']

private theorem map_fst_localData_markedPlace_eq_of_isAlgebraic
    (hex : IsIntegrallyClosedIn k F) (hcomp : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) (i : Fin 3) :
    (localData (k' := k') (F' := F') k' (RatFunc k') (markedPlace k' i)).map Prod.fst =
      (weightedRamificationPartition (k' := k) (F' := F) k (RatFunc k)
        (IsFunctionField.ratFunc k) (markedPlace k i)).parts := by
  classical
  let := isAlgebraic_of_constantCompositum_eq_top (k := k) hcomp
  have hF : IsFunctionField k F := (IsFunctionField.ratFunc k).finite_extension
  let s := (finite_setOf_restrict_eq (k' := k) (F' := F) k (RatFunc k)
    (markedPlace k i)).toFinset
  let s' := (finite_setOf_restrict_eq (k' := k') (F' := F') k' (RatFunc k')
    (markedPlace k' i)).toFinset
  have hmem (Q' : Place k' F') :
      Q' ∈ s' ↔ Q'.restrict k F ∈ s := by
    simpa only [s, s', Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using
      (restrict_restrict_eq_markedPlace_iff hX Q' i).symm
  have hdeg (Q : Place k F) (hQ : Q ∈ s) :
      relativeDegree k (RatFunc k) Q = Q.degree := by
    have hQ' : Q.restrict k (RatFunc k) = markedPlace k i := by
      simpa only [s, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hQ
    have h := degree_eq_degree_restrict_mul_relativeDegree k (RatFunc k) Q
    have hmark : (markedPlace k i).degree = 1 := by
      fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
        markedPlace_zero, markedPlace_one, markedPlace_two,
        degree_adicOfIrreducible_X_sub_C, degree_adicOfIrreducible,
        Polynomial.natDegree_X, degree_infty]
    simpa only [hQ', hmark, one_mul] using h.symm
  -- Use the constant-extension splitting theorem to count points over each original place.
  -- Since the marked base place is rational, that count is the relative residue degree.
  have hcard (Q : Place k F) (hQ : Q ∈ s) :
      (s'.filter fun Q' => Q'.restrict k F = Q).card = relativeDegree k (RatFunc k) Q := by
    have hf := finite_setOf_restrict_eq_of_constantCompositum_eq_top hF hcomp Q
    have hs : s'.filter (fun Q' => Q'.restrict k F = Q) = hf.toFinset := by
      ext Q'
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      rw [hmem]
      exact and_iff_right_of_imp fun h => h ▸ hQ
    rw [hs, hdeg Q hQ]
    let := Q.finiteDimensional_residueField hF
    let : IsAlgClosure k k' := ⟨inferInstance, inferInstance⟩
    simpa only [Set.ncard_eq_toFinset_card _ hf] using
      ncard_setOf_restrict_eq_eq_degree_of_constantCompositum_eq_top hF hex hcomp Q
        (IsAlgClosed.lift : Q.ResidueField →ₐ[k] k')
  have he (Q' : Place k' F') :
      ramificationIdx (RatFunc k') Q' = ramificationIdx (RatFunc k) (Q'.restrict k F) :=
    ramificationIdx_ratFunc_eq_of_constantCompositum_eq_top hcomp hX Q'
  have hup :
      (localData (k' := k') (F' := F') k' (RatFunc k') (markedPlace k' i)).map Prod.fst =
        ∑ Q' ∈ s', ({ramificationIdx (RatFunc k') Q'} : Multiset ℕ) := by
    -- A multiset of indices is the sum of its singleton entries, indexed by the fibre.
    simpa only [localData_def, Multiset.map_map, Function.comp_def,
      Finset.sum_eq_multiset_sum, s'] using
      (Multiset.sum_map_singleton (s'.val.map (ramificationIdx (RatFunc k')))).symm
  have hdown :
      (weightedRamificationPartition (k' := k) (F' := F) k (RatFunc k)
        (IsFunctionField.ratFunc k) (markedPlace k i)).parts =
        ∑ Q ∈ s, Multiset.replicate (relativeDegree k (RatFunc k) Q)
          (ramificationIdx (RatFunc k) Q) := by
    rw [parts_weightedRamificationPartition, localData_def, Multiset.bind_map]
    -- Binding the local pairs to replicated indices is the indexed sum of those multisets.
    rfl
  -- Regroup the geometric indices by restriction; the index is constant on each fibre.
  rw [hup, hdown, ← Finset.sum_fiberwise_of_maps_to (fun Q' hQ' => (hmem Q').mp hQ')]
  apply Finset.sum_congr rfl
  intro Q hQ
  simp only [he]
  calc
    _ = ∑ _ ∈ s'.filter (fun Q' => Q'.restrict k F = Q),
        ({ramificationIdx (RatFunc k) Q} : Multiset ℕ) := by
      apply Finset.sum_congr rfl
      intro Q' hQ'
      rw [(Finset.mem_filter.mp hQ').2]
    _ = _ := by rw [Finset.sum_const, hcard Q hQ, Multiset.nsmul_singleton]

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

omit [IsAlgClosed k'] [Algebra.IsAlgebraic k k'] in
private theorem map_fst_localData_markedPlace_eq_of_isAlgClosed_base [IsAlgClosed k]
    (hex : IsIntegrallyClosedIn k F) (hcomp : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) (i : Fin 3) :
    (localData (k' := k') (F' := F') k' (RatFunc k') (markedPlace k' i)).map Prod.fst =
      (localData (k' := k) (F' := F) k (RatFunc k) (markedPlace k i)).map Prod.fst := by
  classical
  have hF : IsFunctionField k F := (IsFunctionField.ratFunc k).finite_extension
  obtain ⟨x₀, hx₀, _⟩ := hF.exists_transcendental_and_isSeparable_adjoin_of_perfectField
  have : Algebra.IsGeometricallyReduced k F := isGeometricallyReduced_of_separating hx₀
  have H := linearDisjoint_of_isGeometricallyReduced_ratFunc hex hX
  have hexU (Q : Place k F) : ∃! Q' : Place k' F',
      Q'.integers.comap (algebraMap F F') = Q.integers := by
    have := Q.finiteDimensional_residueField hF
    exact existsUnique_integers_comap_eq_of_degree_eq_one hF H hcomp
      Q.degree_eq_one_of_isAlgClosed_of_isIntegral
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

omit [Algebra.IsAlgebraic k k'] in
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
