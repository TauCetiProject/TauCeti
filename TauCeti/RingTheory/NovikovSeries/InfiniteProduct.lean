/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovSeries.TopologicalRing
public import Mathlib.Topology.Algebra.InfiniteSum.Group

/-!
# Filtered infinite products of Novikov series

A family of Novikov series has a convergent unordered product if,
below each period cutoff, only finitely many factors differ from one. The product
agrees below that cutoff with any finite product containing those exceptional
factors, provided all factors have nonnegative support. This makes infinite Euler
products computable by finite period windows, without discreteness or injectivity of the period map.

The factors need not be units. Only finitely many can have negative support; these
are separated off for the convergence theorem. Nonnegative support prevents
multiplication from lowering the period of an error in the cutoff formulas. The result
applies to principal units used in dynamical zeta products.

## References

* M. Hutchings and Y.-J. Lee, *Circle-valued Morse theory and Reidemeister torsion*,
  Geom. Topol. 3 (1999), Section 2.
-/

public section

noncomputable section

open Filter Topology

namespace TauCeti.NovikovSeries

variable {R H ι : Type*} [CommRing R] [AddCommMonoid H] {N : H →+ ℝ}
  {f : ι → nonnegSubring R N} {C : ℝ}

/-- A finite product of nonnegative series congruent to one modulo `U_C` is
itself congruent to one modulo `U_C`. -/
theorem prod_sub_one_mem_periodFiltration (s : Finset ι)
    (hf : ∀ i ∈ s, (f i : NovikovSeries R H N) - 1 ∈ periodFiltration R N C) :
    (∏ i ∈ s, (f i : NovikovSeries R H N)) - 1 ∈ periodFiltration R N C := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    have heq : (f i : NovikovSeries R H N) * (∏ j ∈ s, (f j : NovikovSeries R H N)) - 1 =
        (f i : NovikovSeries R H N) * ((∏ j ∈ s, (f j : NovikovSeries R H N)) - 1) +
          ((f i : NovikovSeries R H N) - 1) := by ring
    rw [heq]
    have hi0 := mem_periodFiltration.2 (mem_nonnegSubring.1 (f i).2)
    have hmul := mul_mem_periodFiltration hi0
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
    exact add_mem (by simpa only [zero_add] using hmul) (hf i (Finset.mem_insert_self _ _))

/-- Adding factors congruent to one modulo `U_C` does not change a finite product
modulo `U_C`. -/
theorem prod_sub_prod_mem_periodFiltration {s t : Finset ι} (hst : s ⊆ t)
    (hf : ∀ i ∈ t, i ∉ s → (f i : NovikovSeries R H N) - 1 ∈ periodFiltration R N C) :
    (∏ i ∈ t, (f i : NovikovSeries R H N)) - (∏ i ∈ s, (f i : NovikovSeries R H N)) ∈
      periodFiltration R N C := by
  classical
  have hs : (∏ i ∈ s, (f i : NovikovSeries R H N)) ∈ periodFiltration R N 0 :=
    mem_periodFiltration.2 (mem_nonnegSubring.1
      ((nonnegSubring R N).prod_mem fun i _ => (f i).2))
  have h := mul_mem_periodFiltration (prod_sub_one_mem_periodFiltration (t \ s)
    fun i hi => hf i (Finset.mem_sdiff.1 hi).1 (Finset.mem_sdiff.1 hi).2) hs
  simpa only [add_zero, sub_mul, one_mul, Finset.prod_sdiff hst] using h

/-- Nonnegative factors whose deviations from one escape each cutoff form a
multipliable family. The index type may be uncountable. -/
theorem multipliable_of_nonneg_finite_cutoffs
    (hf : ∀ C : ℝ, {i | (f i : NovikovSeries R H N) - 1 ∉ periodFiltration R N C}.Finite) :
    Multipliable (fun i => (f i : NovikovSeries R H N)) := by
  classical
  apply multipliable_iff_cauchySeq_finset.2
  refine hasBasis_uniformity.cauchySeq_iff.2 fun C _ => ?_
  let s := (hf C).toFinset
  have hs (t : Finset ι) (hst : s ⊆ t) :
      (∏ i ∈ t, (f i : NovikovSeries R H N)) - (∏ i ∈ s, (f i : NovikovSeries R H N)) ∈
        periodFiltration R N C := by
    apply prod_sub_prod_mem_periodFiltration hst
    intro i _ hi
    simpa only [s, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using hi
  refine ⟨s, fun t ht u hu => ?_⟩
  have h := sub_mem (hs u hu) (hs t ht)
  simpa using h

/-- An infinite filtered product agrees modulo `U_C` with any finite product
containing all factors that differ from one below `C`. -/
theorem tprod_sub_prod_mem_periodFiltration
    (hf : ∀ D : ℝ, {i | (f i : NovikovSeries R H N) - 1 ∉ periodFiltration R N D}.Finite)
    (s : Finset ι)
    (hs : ∀ i, i ∉ s → (f i : NovikovSeries R H N) - 1 ∈ periodFiltration R N C) :
    (∏' i, (f i : NovikovSeries R H N)) - (∏ i ∈ s, (f i : NovikovSeries R H N)) ∈
      periodFiltration R N C := by
  classical
  apply (isClosed_periodFiltration C).mem_of_tendsto
    ((multipliable_of_nonneg_finite_cutoffs hf).hasProd.sub_const _)
  filter_upwards [eventually_ge_atTop s] with t ht
  exact prod_sub_prod_mem_periodFiltration ht fun i _ hi => hs i hi

/-- Each coefficient of a filtered product can be computed from any finite cutoff
containing all factors that can affect that coefficient. -/
theorem coeff_tprod_eq_coeff_prod
    (hf : ∀ D : ℝ, {i | (f i : NovikovSeries R H N) - 1 ∉ periodFiltration R N D}.Finite)
    (s : Finset ι)
    (hs : ∀ i, i ∉ s → (f i : NovikovSeries R H N) - 1 ∈ periodFiltration R N C)
    {h : H} (hh : N h < C) :
    (∏' i, (f i : NovikovSeries R H N)).coeff h =
      (∏ i ∈ s, (f i : NovikovSeries R H N)).coeff h := by
  have heq := mem_periodFiltration.1 (tprod_sub_prod_mem_periodFiltration hf s hs) h hh
  simpa only [coeff_sub, sub_eq_zero] using heq

/-- A family of arbitrary Novikov series has an unordered product if only finitely
many factors differ from one below each cutoff. No uniform lower bound on the
supports of all finite partial products is assumed. -/
theorem multipliable_of_finite_cutoffs {g : ι → NovikovSeries R H N}
    (hg : ∀ C : ℝ, {i | g i - 1 ∉ periodFiltration R N C}.Finite) : Multipliable g := by
  classical
  -- Separate the finitely many factors that can have negative support.
  let s := (hg 0).toFinset
  have hnonneg (i : ι) (hi : i ∉ s) : g i ∈ nonnegSubring R N := by
    have hdiff : g i - 1 ∈ periodFiltration R N 0 := by
      simpa only [s, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using hi
    have hsum := add_mem hdiff (one_mem_periodFiltration_zero (R := R) (N := N))
    exact mem_nonnegSubring.2 (mem_periodFiltration.1 (by simpa using hsum))
  let a : ι → nonnegSubring R N := fun i =>
    if hi : i ∉ s then ⟨g i, hnonneg i hi⟩ else 1
  let b : ι → NovikovSeries R H N := fun i => if i ∈ s then g i else 1
  have ha : Multipliable (fun i => (a i : NovikovSeries R H N)) := by
    apply multipliable_of_nonneg_finite_cutoffs
    intro C
    apply (hg C).subset
    intro i hi
    by_cases his : i ∈ s
    · simp [a, his] at hi
    · simpa [a, his] using hi
  have hb : Multipliable b := by
    apply multipliable_of_hasFiniteMulSupport
    exact s.finite_toSet.subset fun i hi => by
      by_contra his
      have his' : i ∉ s := his
      exact hi (by simp [b, his'])
  exact (ha.mul hb).congr fun i => by
    by_cases hi : i ∈ s <;> simp [a, b, hi]

end TauCeti.NovikovSeries
