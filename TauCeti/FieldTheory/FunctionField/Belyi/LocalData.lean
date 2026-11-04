/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Belyi.BaseChange
public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Fibre
public import TauCeti.FieldTheory.FunctionField.Place.Extension.LocalData
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Ramification

/-!
# Geometric ramification partitions

For a function field with perfect, exact constants, extending the constants algebraically
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
      have hlinear : (Polynomial.X - 1 : Polynomial k).natDegree = 1 := by
        simpa only [Polynomial.C_1] using Polynomial.natDegree_X_sub_C (1 : k)
      fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
        markedPlace_zero, markedPlace_one, markedPlace_two, degree_adicOfIrreducible,
        Polynomial.natDegree_X, Polynomial.C_1, hlinear, degree_infty]
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
    _ = ∑ Q' ∈ s'.filter (fun Q' => Q'.restrict k F = Q),
        ({ramificationIdx (RatFunc k) Q} : Multiset ℕ) := by
      apply Finset.sum_congr rfl
      intro Q' hQ'
      rw [(Finset.mem_filter.mp hQ').2]
    _ = _ := by rw [Finset.sum_const, hcard Q hQ, Multiset.nsmul_singleton]

end TauCeti.Place
