/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Belyi.BaseChange
public import TauCeti.FieldTheory.FunctionField.Place.Extension.LocalData
import TauCeti.FieldTheory.FunctionField.SeparablyGenerated
import TauCeti.FieldTheory.RatFunc.Transcendental
import TauCeti.FieldTheory.Separable.Regular

/-!
# Geometric ramification partitions

For a function field with perfect, exact constants, extending the constants to any algebraically
closed field `k'` (algebraic or transcendental over `k`, such as `ℂ` over a number field) splits a
place of degree `f` into `f` places nontrivial on `F`, without changing its ramification index at
the marked fibres, while places trivial on `F` avoid the marked fibres altogether. Consequently the
unweighted ramification indices in each geometric marked fibre are exactly the weighted
ramification partition over the original constants. Multiplicities, not just the sets of indices,
are preserved.

The comparison is stated for a compositum of function fields with compatible rational
parameters. It does not require the map to be unramified away from the marked fibres, nor `k' / k`
to be algebraic.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Section III.6,
  especially Theorem 3.6.3.
-/

public section

open scoped IntermediateField TensorProduct

namespace TauCeti.Place

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [Algebra (RatFunc k') F'] [IsScalarTower k' (RatFunc k') F']
  [PerfectField k] [IsAlgClosed k']
  [FiniteDimensional (RatFunc k) F] [FiniteDimensional (RatFunc k') F']

/-- After extending constants to any algebraically closed field (algebraic or transcendental over
`k`), each marked fibre has one ramification index for each weighted part of the original fibre. A
residue degree `f` over the original constants contributes `f` geometric points. -/
theorem map_fst_localData_markedPlace_eq_parts_weightedRamificationPartition
    (hex : IsIntegrallyClosedIn k F) (hcomp : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) (i : Fin 3) :
    (localData (k' := k') (F' := F') k' (RatFunc k') (markedPlace k' i)).map Prod.fst =
      (weightedRamificationPartition (k' := k) (F' := F) k (RatFunc k)
        (IsFunctionField.ratFunc k) (markedPlace k i)).parts := by
  classical
  have hF : IsFunctionField k F := (IsFunctionField.ratFunc k).finite_extension
  obtain ⟨u, hu, _⟩ := hF.exists_transcendental_and_isSeparable_adjoin_of_perfectField
  have : Algebra.IsGeometricallyReduced k F := isGeometricallyReduced_of_separating hu
  let t : F := algebraMap (RatFunc k) F RatFunc.X
  have ht : Transcendental k t :=
    (transcendental_algebraMap_iff (algebraMap (RatFunc k) F).injective).mpr
      RatFunc.transcendental_X
  have ht' : Transcendental k' (algebraMap F F' t) := by
    change Transcendental k' (algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X))
    rw [hX]
    exact (transcendental_algebraMap_iff (algebraMap (RatFunc k') F').injective).mpr
      RatFunc.transcendental_X
  have : FiniteDimensional k⟮t⟯ F := hF.finiteDimensional_adjoin ht
  have : IsDomain (F ⊗[k] k') := isDomain_tensorProduct_of_isGeometricallyReduced hex k'
  have hld : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F :=
    linearDisjoint_of_constantCompositum_eq_top_of_transcendental ht' hcomp
  let s := (finite_setOf_restrict_eq (k' := k) (F' := F) k (RatFunc k)
    (markedPlace k i)).toFinset
  let s' := (finite_setOf_restrict_eq (k' := k') (F' := F') k' (RatFunc k')
    (markedPlace k' i)).toFinset
  have hs'_eq {Q' : Place k' F'} (hQ' : Q' ∈ s') :
      Q'.restrict k' (RatFunc k') = markedPlace k' i := by
    simpa only [s', Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hQ'
  have hne (Q' : Place k' F') (hQ' : Q' ∈ s') : ramificationIdx F Q' ≠ 0 := fun h0 ↦
    restrict_notMem_zeroOneInfty_of_ramificationIdx_eq_zero hX h0
      ((hs'_eq hQ') ▸ range_markedPlace k' ▸ ⟨i, rfl⟩)
  let π : {Q' // Q' ∈ s'} → Place k F :=
    fun Q' ↦ Q'.1.restrictOfRamificationIdxNeZero k (hne Q'.1 Q'.2)
  have hmaps : ∀ Q' ∈ s'.attach, π Q' ∈ s := by
    intro Q' _
    simp only [s, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, π]
    exact (restrictOfRamificationIdxNeZero_restrict_eq_markedPlace_iff hX Q'.1
      (hne Q'.1 Q'.2) i).mpr (hs'_eq Q'.2)
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
  have hcard (Q : Place k F) (hQ : Q ∈ s) :
      (s'.attach.filter fun Q' => π Q' = Q).card = relativeDegree k (RatFunc k) Q := by
    have hf := finite_setOf_restrictOfRamificationIdxNeZero_eq hF hld hcomp Q
    have hmap : (s'.attach.filter fun Q' => π Q' = Q).map ⟨Subtype.val, Subtype.val_injective⟩ =
        hf.toFinset := by
      ext P'
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_attach, true_and,
        Function.Embedding.coeFn_mk, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Subtype.exists]
      refine ⟨fun ⟨a, hP's, hπ, ha⟩ ↦ ha ▸ ⟨hne a hP's, hπ⟩, fun ⟨hP', hres⟩ ↦ ?_⟩
      have hQi : Q.restrict k (RatFunc k) = markedPlace k i := by
        simpa only [s, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hQ
      have hP's : P' ∈ s' := by
        simp only [s', Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
        exact (restrictOfRamificationIdxNeZero_restrict_eq_markedPlace_iff hX P' hP' i).mp
          (hres ▸ hQi)
      exact ⟨P', hP's, hres, rfl⟩
    rw [← Finset.card_map ⟨Subtype.val, Subtype.val_injective⟩, hmap, hdeg Q hQ]
    simpa only [Set.ncard_eq_toFinset_card _ hf] using
      ncard_setOf_restrictOfRamificationIdxNeZero_eq_of_isAlgClosed hF hld hcomp Q
  have hup :
      (localData (k' := k') (F' := F') k' (RatFunc k') (markedPlace k' i)).map Prod.fst =
        ∑ Q' ∈ s'.attach, ({ramificationIdx (RatFunc k') Q'.1} : Multiset ℕ) := by
    rw [Finset.sum_attach s' (fun Q' ↦ ({ramificationIdx (RatFunc k') Q'} : Multiset ℕ))]
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
  rw [hup, hdown, ← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl
  intro Q hQ
  calc
    _ = ∑ _ ∈ s'.attach.filter (fun Q' => π Q' = Q),
        ({ramificationIdx (RatFunc k) Q} : Multiset ℕ) := by
      apply Finset.sum_congr rfl
      intro Q' hQ'
      have hπQ : π Q' = Q := (Finset.mem_filter.mp hQ').2
      rw [ramificationIdx_ratFunc_eq_of_restrict_eq_markedPlace hF hcomp hX (hs'_eq Q'.2),
        ← hπQ]
    _ = _ := by rw [Finset.sum_const, hcard Q hQ, Multiset.nsmul_singleton]

end TauCeti.Place
