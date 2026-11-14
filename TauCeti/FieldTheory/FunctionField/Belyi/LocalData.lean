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

For a function field `F / k(t)` with perfect, exact constants `k`, extending the constants along an
arbitrary field extension `k → k'` to an algebraically closed field `k'` (algebraic or
transcendental, such as `ℚ ⊂ AlgebraicClosure ℚ` or a number field `K ⊂ ℂ`) splits each place of
degree `f` over a marked point into `f` rational places, without changing its ramification index.
Consequently the unweighted ramification indices in each geometric marked fibre over `k'` are
exactly the weighted ramification partition over the original constants `k`. Multiplicities, not
just the sets of indices, are preserved.

When `k' / k` is transcendental, the proof factors `k → k'` through the algebraic closure of `k`
inside `k'`: the algebraic step splits residue degrees into geometric points, while the purely
transcendental step between algebraically closed fields induces a ramification-preserving bijection
on each marked fibre because vertical places never lie over `{0, 1, ∞}` and rational places extend
uniquely.

## Main results

* `TauCeti.Place.map_fst_localData_markedPlace_eq_parts_weightedRamificationPartition`: the
  geometric ramification multiset at each marked place over an algebraically closed extension `k'`
  equals the parts of the weighted ramification partition over `k`, without any algebraicity
  assumption on `k' / k`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Section III.6,
  especially Theorem 3.6.3.
-/

public section

namespace TauCeti.Place

section AlgebraicStep

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [Algebra (RatFunc k') F'] [IsScalarTower k' (RatFunc k') F']
  [PerfectField k] [IsAlgClosed k'] [Algebra.IsAlgebraic k k']
  [FiniteDimensional (RatFunc k) F] [FiniteDimensional (RatFunc k') F']

/-- Each place `Q` in a marked fibre over `k` splits into `relativeDegree k (RatFunc k) Q`
geometric places in the corresponding marked fibre over an algebraic closure `k'`. -/
private theorem card_filter_restrict_eq_relativeDegree [Algebra.IsIntegral F F']
    [DecidableEq (Place k F)]
    (hex : IsIntegrallyClosedIn k F) (hcomp : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) (i : Fin 3) {Q : Place k F}
    (hQ : Q.restrict k (RatFunc k) = markedPlace k i) :
    (((finite_setOf_restrict_eq (k' := k') (F' := F') k' (RatFunc k')
        (markedPlace k' i)).toFinset).filter fun (Q' : Place k' F') => Q'.restrict k F = Q).card =
      relativeDegree k (RatFunc k) Q := by
  have hF : IsFunctionField k F := (IsFunctionField.ratFunc k).finite_extension
  have hdeg : relativeDegree k (RatFunc k) Q = Q.degree := by
    have h := degree_eq_degree_restrict_mul_relativeDegree k (RatFunc k) Q
    have hmark : (markedPlace k i).degree = 1 := by
      fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
        markedPlace_zero, markedPlace_one, markedPlace_two,
        degree_adicOfIrreducible_X_sub_C, degree_adicOfIrreducible,
        Polynomial.natDegree_X, degree_infty]
    simpa only [hQ, hmark, one_mul] using h.symm
  have hf := finite_setOf_restrict_eq_of_constantCompositum_eq_top hF hcomp Q
  have hs : ((finite_setOf_restrict_eq (k' := k') (F' := F') k' (RatFunc k')
      (markedPlace k' i)).toFinset).filter (fun (Q' : Place k' F') => Q'.restrict k F = Q) =
      hf.toFinset := by
    ext Q'
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq,
      ← restrict_restrict_eq_markedPlace_iff hX Q' i]
    exact and_iff_right_of_imp fun h => h ▸ hQ
  rw [hs, hdeg]
  let := Q.finiteDimensional_residueField hF
  let : IsAlgClosure k k' := ⟨inferInstance, inferInstance⟩
  simpa only [Set.ncard_eq_toFinset_card _ hf] using
    ncard_setOf_restrict_eq_eq_degree_of_constantCompositum_eq_top hF hex hcomp Q
      (IsAlgClosed.lift : Q.ResidueField →ₐ[k] k')

/-- Algebraic-extension case of
`map_fst_localData_markedPlace_eq_parts_weightedRamificationPartition`. -/
private theorem map_fst_localData_markedPlace_eq_of_isAlgebraic
    (hex : IsIntegrallyClosedIn k F) (hcomp : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) (i : Fin 3) :
    (localData (k' := k') (F' := F') k' (RatFunc k') (markedPlace k' i)).map Prod.fst =
      (weightedRamificationPartition (k' := k) (F' := F) k (RatFunc k)
        (IsFunctionField.ratFunc k) (markedPlace k i)).parts := by
  classical
  let := isAlgebraic_of_constantCompositum_eq_top (k := k) hcomp
  let s := (finite_setOf_restrict_eq (k' := k) (F' := F) k (RatFunc k)
    (markedPlace k i)).toFinset
  let s' := (finite_setOf_restrict_eq (k' := k') (F' := F') k' (RatFunc k')
    (markedPlace k' i)).toFinset
  have hmem (Q' : Place k' F') : Q' ∈ s' ↔ Q'.restrict k F ∈ s := by
    simpa only [s, s', Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using
      (restrict_restrict_eq_markedPlace_iff hX Q' i).symm
  have he (Q' : Place k' F') :
      ramificationIdx (RatFunc k') Q' = ramificationIdx (RatFunc k) (Q'.restrict k F) :=
    ramificationIdx_ratFunc_eq_of_constantCompositum_eq_top hcomp hX Q'
  have hup :
      (localData (k' := k') (F' := F') k' (RatFunc k') (markedPlace k' i)).map Prod.fst =
        ∑ Q' ∈ s', ({ramificationIdx (RatFunc k') Q'} : Multiset ℕ) := by
    simpa only [localData_def, Multiset.map_map, Function.comp_def,
      Finset.sum_eq_multiset_sum, s'] using
      (Multiset.sum_map_singleton (s'.val.map (ramificationIdx (RatFunc k')))).symm
  have hdown :
      (weightedRamificationPartition (k' := k) (F' := F) k (RatFunc k)
        (IsFunctionField.ratFunc k) (markedPlace k i)).parts =
        ∑ Q ∈ s, Multiset.replicate (relativeDegree k (RatFunc k) Q)
          (ramificationIdx (RatFunc k) Q) := by
    rw [parts_weightedRamificationPartition, localData_def, Multiset.bind_map]
    rfl
  rw [hup, hdown, ← Finset.sum_fiberwise_of_maps_to (fun Q' hQ' => (hmem Q').mp hQ')]
  refine Finset.sum_congr rfl fun Q hQ => ?_
  have hQi : Q.restrict k (RatFunc k) = markedPlace k i := by
    simpa only [s, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hQ
  simp only [he]
  calc
    _ = ∑ _ ∈ s'.filter (fun Q' => Q'.restrict k F = Q),
        ({ramificationIdx (RatFunc k) Q} : Multiset ℕ) :=
      Finset.sum_congr rfl fun _ hQ' => by rw [(Finset.mem_filter.mp hQ').2]
    _ = _ := by
      rw [Finset.sum_const, card_filter_restrict_eq_relativeDegree hex hcomp hX i hQi,
        Multiset.nsmul_singleton]

end AlgebraicStep

section AlgClosedStep

/-- Over an algebraically closed constant field `k`, every place of `F` has degree `1` and extends
uniquely to `F' = F · k'` for any extension `k' / k`, while places of `F'` trivial on `F` avoid
the marked set; hence each marked fibre and its ramification multiset are preserved verbatim. -/
private theorem map_fst_localData_markedPlace_eq_of_isAlgClosed_base
    {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
    [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
    [IsScalarTower k k' F'] [IsScalarTower k F F']
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
    [Algebra (RatFunc k') F'] [IsScalarTower k' (RatFunc k') F']
    [IsAlgClosed k]
    [FiniteDimensional (RatFunc k) F] [FiniteDimensional (RatFunc k') F']
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
  let s := (finite_setOf_restrict_eq (k' := k) (F' := F) k (RatFunc k) (markedPlace k i)).toFinset
  let s' := (finite_setOf_restrict_eq (k' := k') (F' := F') k' (RatFunc k')
    (markedPlace k' i)).toFinset
  have hexU (Q : Place k F) : ∃! Q' : Place k' F',
      Q'.integers.comap (algebraMap F F') = Q.integers := by
    have := Q.finiteDimensional_residueField hF
    exact existsUnique_integers_comap_eq_of_degree_eq_one hF H hcomp
      Q.degree_eq_one_of_isAlgClosed_of_isIntegral
  let liftPlace (Q : Place k F) : Place k' F' := (hexU Q).choose
  have hlift (Q : Place k F) : (liftPlace Q).integers.comap (algebraMap F F') = Q.integers :=
    (hexU Q).choose_spec.1
  have hup : (localData (k' := k') (F' := F') k' (RatFunc k') (markedPlace k' i)).map Prod.fst =
      ∑ Q' ∈ s', ({ramificationIdx (RatFunc k') Q'} : Multiset ℕ) := by
    simpa only [localData_def, Multiset.map_map, Function.comp_def,
      Finset.sum_eq_multiset_sum, s'] using
      (Multiset.sum_map_singleton (s'.val.map (ramificationIdx (RatFunc k')))).symm
  have hdown : (localData (k' := k) (F' := F) k (RatFunc k) (markedPlace k i)).map Prod.fst =
      ∑ Q ∈ s, ({ramificationIdx (RatFunc k) Q} : Multiset ℕ) := by
    simpa only [localData_def, Multiset.map_map, Function.comp_def,
      Finset.sum_eq_multiset_sum, s] using
      (Multiset.sum_map_singleton (s.val.map (ramificationIdx (RatFunc k)))).symm
  rw [hup, hdown]
  refine (Finset.sum_nbij liftPlace ?_ ?_ ?_ ?_).symm
  · intro Q hQ
    simp only [s, s', Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hQ ⊢
    exact (restrict_eq_markedPlace_iff_of_integers_comap_eq hX (hlift Q) i).mp hQ
  · intro Q₁ _ Q₂ _ hEq
    exact integers_injective (by rw [← hlift Q₁, hEq, hlift Q₂])
  · intro Q' hQ'
    simp only [s', Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hQ'
    rcases isTrivialOn_or_existsUnique_integers_comap_eq hF Q' with htriv | ⟨Q, hQ, -⟩
    · refine False.elim (restrict_notMem_zeroOneInfty_of_isTrivialOn hX htriv ?_)
      rw [hQ', ← range_markedPlace]
      exact ⟨i, rfl⟩
    · refine ⟨Q, ?_, ((hexU Q).choose_spec.2 Q' hQ).symm⟩
      simp only [s, Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      exact (restrict_eq_markedPlace_iff_of_integers_comap_eq hX hQ i).mpr hQ'
  · intro Q _
    rw [ramificationIdx_ratFunc_eq_of_integers_comap_eq hex hcomp hX (hlift Q)]

end AlgClosedStep

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [Algebra (RatFunc k') F'] [IsScalarTower k' (RatFunc k') F']
  [PerfectField k] [IsAlgClosed k']
  [FiniteDimensional (RatFunc k) F] [FiniteDimensional (RatFunc k') F']

/-- **After extending constants to any algebraically closed field (algebraic or transcendental),
each marked fibre has one ramification index for each weighted part of the original fibre**: a
place of residue degree `f` over `k` contributes `f` geometric points over `k'`. -/
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
  have H₁ : (IsScalarTower.toAlgHom k kbar F₁).fieldRange.LinearDisjoint F :=
    linearDisjoint_fieldRange_of_isIntegrallyClosedIn hex
  have hxF : Transcendental k (algebraMap (RatFunc k) F RatFunc.X) :=
    (transcendental_algebraMap_iff (FaithfulSMul.algebraMap_injective (RatFunc k) F)).mpr
      RatFunc.transcendental_X
  have hx₁ : Transcendental kbar (algebraMap F F₁ (algebraMap (RatFunc k) F RatFunc.X)) :=
    H₁.transcendental_algebraMap hxF
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
  have hex₁ : IsIntegrallyClosedIn kbar F₁ := hex.of_constantCompositum_eq_top hcomp₁
  exact (map_fst_localData_markedPlace_eq_of_isAlgClosed_base hex₁ hcomp₂ hX₂ i).trans
    (map_fst_localData_markedPlace_eq_of_isAlgebraic hex hcomp₁ hX₁ i)

end TauCeti.Place
