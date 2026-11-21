/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SacksSplitting.Code
public import TauCeti.Computability.SacksSplitting.Degree
public import TauCeti.Computability.Simple.Lowness

/-!
# Concrete instances and cross-construction consequences of Sacks splitting

This module instantiates Sacks's splitting machine and its degree corollaries across boundary cases
and across the low-simple-set construction of `TauCeti.Computability.Simple.Lowness`:

* **Empty and singleton inputs:** on empty batches `fun _ => ∅` the stage machine stays at `(∅, ∅)`
  at every stage; on `{0}` against `(∅ : Set ℕ).jump` one half equals `{0}` and the other equals
  `∅`, illustrating why no infinitude hypothesis on `B` is needed.
* **Infinite computable input:** splitting `{n : ℕ | Even n}` against `(∅ : Set ℕ).jump` yields
  disjoint computable (and low) halves whose union is `{n : ℕ | Even n}`, at least one of which is
  infinite; unlike the noncomputable case, the split reductions `A_i ≤_T B` force both halves to be
  computable.
* **Self-splitting `TauCeti.lowSimpleSet`:** Soare's low simple set splits into two disjoint,
  infinite, noncomputable, low, Turing incomparable c.e. subsets strictly below `lowSimpleSet`
  whose degrees join to `deg(lowSimpleSet)`, **neither of which is simple** (each lies in the
  complement of the other).
* **Splitting with distinct input and target (`B ≠ C`):** splitting `lowSimpleSet` against the
  distinct complete target `(∅ : Set ℕ).jump`, and conversely splitting `(∅ : Set ℕ).jump` against
  the incomplete target `lowSimpleSet` to obtain a low c.e. degree Turing incomparable with
  `lowSimpleSet`.
* **Numerical index-level split of `(∅ : Set ℕ).jump`:** running `splitIndex` on an index `e` of
  `(∅ : Set ℕ).jump` produces two numerical c.e. indices whose domains partition
  `(∅ : Set ℕ).jump` into low incomparable halves whose join has degree `0'` and is not low.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Theorems VII.1.1 and
  VII.3.2, Corollaries VII.3.4–VII.3.7.
-/

public section

open TauCeti.Enumeration TauCeti.SacksSplitting

namespace TauCeti.Examples

/-! ### Empty, singleton, and infinite computable inputs -/

/-- Splitting `(∅ : Set ℕ)` against `(∅ : Set ℕ).jump` produces two empty low c.e. halves neither
of which computes `(∅ : Set ℕ).jump`. -/
theorem exists_split_empty_avoiding_jump_empty :
    ∃ A₀ A₁ : Set ℕ, REPred (· ∈ A₀) ∧ REPred (· ∈ A₁) ∧ A₀ = ∅ ∧ A₁ = ∅ ∧
      A₀.Low ∧ A₁.Low ∧ ¬TuringReducible (∅ : Set ℕ).jump.oracle A₀.oracle ∧
      ¬TuringReducible (∅ : Set ℕ).jump.oracle A₁.oracle := by
  obtain ⟨A₀, A₁, hA₀, hA₁, -, hunion, hL₀, hL₁, hnc₀, hnc₁⟩ :=
    exists_split_low_not_turingReducible Set.finite_empty.computablePred.to_re
      Set.rePred_mem_jump_empty (Set.not_computablePred_mem_jump ∅)
  obtain ⟨rfl, rfl⟩ := Set.union_empty_iff.1 hunion
  exact ⟨∅, ∅, hA₀, hA₁, rfl, rfl, hL₀, hL₁, hnc₀, hnc₁⟩

/-- Splitting the singleton `{0}` against `(∅ : Set ℕ).jump` yields disjoint low c.e. halves with
union `{0}` (so one half is `{0}` and the other is `∅`), neither computing `(∅ : Set ℕ).jump`. -/
theorem exists_split_singleton_zero_avoiding_jump_empty :
    ∃ A₀ A₁ : Set ℕ, REPred (· ∈ A₀) ∧ REPred (· ∈ A₁) ∧ Disjoint A₀ A₁ ∧ A₀ ∪ A₁ = {0} ∧
      ((A₀ = {0} ∧ A₁ = ∅) ∨ (A₀ = ∅ ∧ A₁ = {0})) ∧
      A₀.Low ∧ A₁.Low ∧ ¬TuringReducible (∅ : Set ℕ).jump.oracle A₀.oracle ∧
      ¬TuringReducible (∅ : Set ℕ).jump.oracle A₁.oracle := by
  obtain ⟨A₀, A₁, hA₀, hA₁, hd, hunion, hL₀, hL₁, hnc₀, hnc₁⟩ :=
    exists_split_low_not_turingReducible (Set.finite_singleton 0).computablePred.to_re
      Set.rePred_mem_jump_empty (Set.not_computablePred_mem_jump ∅)
  have hcases : (A₀ = {0} ∧ A₁ = ∅) ∨ (A₀ = ∅ ∧ A₁ = {0}) := by
    have h0 : 0 ∈ A₀ ∪ A₁ := hunion ▸ Set.mem_singleton 0
    rcases h0 with h0₀ | h0₁
    · refine Or.inl ⟨Set.Subset.antisymm (Set.subset_union_left.trans hunion.le)
        (Set.singleton_subset_iff.2 h0₀), Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_⟩
      obtain rfl : x = 0 := Set.mem_singleton_iff.1 (hunion.le (Or.inr hx))
      exact Set.disjoint_left.1 hd h0₀ hx
    · refine Or.inr ⟨Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_,
        Set.Subset.antisymm (Set.subset_union_right.trans hunion.le)
          (Set.singleton_subset_iff.2 h0₁)⟩
      obtain rfl : x = 0 := Set.mem_singleton_iff.1 (hunion.le (Or.inl hx))
      exact Set.disjoint_left.1 hd hx h0₁
  exact ⟨A₀, A₁, hA₀, hA₁, hd, hunion, hcases, hL₀, hL₁, hnc₀, hnc₁⟩

/-- Splitting the infinite computable set `{n : ℕ | Even n}` against `(∅ : Set ℕ).jump` produces
disjoint low **computable** halves whose union is `{n : ℕ | Even n}`, at least one of which is
infinite, with neither half computing `(∅ : Set ℕ).jump`. -/
theorem exists_split_even_avoiding_jump_empty :
    ∃ A₀ A₁ : Set ℕ, ComputablePred (· ∈ A₀) ∧ ComputablePred (· ∈ A₁) ∧
      Disjoint A₀ A₁ ∧ A₀ ∪ A₁ = {n : ℕ | Even n} ∧ (A₀.Infinite ∨ A₁.Infinite) ∧
      A₀.Low ∧ A₁.Low ∧ ¬TuringReducible (∅ : Set ℕ).jump.oracle A₀.oracle ∧
      ¬TuringReducible (∅ : Set ℕ).jump.oracle A₁.oracle := by
  have hc_even : ComputablePred (· ∈ {n : ℕ | Even n}) :=
    (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2))
      (Primrec.const 0)).computablePred.of_eq fun _ => by simp [Nat.even_iff]
  have hinf_even : {n : ℕ | Even n}.Infinite :=
    Set.infinite_of_injective_forall_mem (f := (2 * ·))
      (fun _ _ (h : 2 * _ = 2 * _) => by omega) fun k => ⟨k, by omega⟩
  obtain ⟨A₀, A₁, hA₀, hA₁, hd, hunion, hL₀, hL₁, hnc₀, hnc₁⟩ :=
    exists_split_low_not_turingReducible hc_even.to_re
      Set.rePred_mem_jump_empty (Set.not_computablePred_mem_jump ∅)
  have heven : TuringReducible {n : ℕ | Even n}.oracle (∅ : Set ℕ).oracle :=
    (Set.turingReducible_empty_iff _).2 hc_even
  have hc₀ : ComputablePred (· ∈ A₀) :=
    (Set.turingReducible_empty_iff A₀).1 <|
      (hunion ▸ hd.turingReducible_union_left hA₀ hA₁).trans heven
  have hc₁ : ComputablePred (· ∈ A₁) :=
    (Set.turingReducible_empty_iff A₁).1 <|
      (hunion ▸ hd.turingReducible_union_right hA₀ hA₁).trans heven
  have hinf : A₀.Infinite ∨ A₁.Infinite := by
    by_contra! hfin
    exact hinf_even (hunion ▸ hfin.1.union hfin.2)
  exact ⟨A₀, A₁, hc₀, hc₁, hd, hunion, hinf, hL₀, hL₁, hnc₀, hnc₁⟩

/-! ### Splitting Soare's low simple set -/

private theorem not_simple_splitHalf_self {B : ℕ → Finset ℕ} (hBm : Monotone B)
    (hB : Computable fun s => Finset.equivBitIndices.symm (B s))
    (hnc : ¬ComputablePred (· ∈ stageLimit B)) (b : Bool) :
    ¬(splitHalf B B b).Simple := fun hS => by
  have hinf : (splitHalf B B (!b)).Infinite :=
    .of_not_computablePred (not_computablePred_mem_splitHalf_self hBm hB hnc (!b))
  obtain ⟨x, hx', hx⟩ := hS.inter_nonempty (rePred_mem_splitHalf hB hB (!b)) hinf
  have hd : Disjoint (splitHalf B B (!b)) (splitHalf B B b) := by
    cases b
    · exact (disjoint_splitHalf B B).symm
    · exact disjoint_splitHalf B B
  exact Set.disjoint_left.1 hd hx' hx

/-- **Self-splitting `lowSimpleSet`:** Soare's low simple set is the disjoint union of two low,
infinite, noncomputable, Turing incomparable c.e. sets `A₀` and `A₁` strictly between `0` and
`deg(lowSimpleSet)` whose degrees join to `deg(lowSimpleSet)`, **neither of which is simple**. -/
theorem exists_split_lowSimpleSet_not_simple :
    ∃ A₀ A₁ : Set ℕ, REPred (· ∈ A₀) ∧ REPred (· ∈ A₁) ∧
      A₀.Low ∧ A₁.Low ∧ Disjoint A₀ A₁ ∧ A₀ ∪ A₁ = lowSimpleSet ∧
      A₀.Infinite ∧ A₁.Infinite ∧ ¬A₀.Simple ∧ ¬A₁.Simple ∧
      IncompRel TuringReducible A₀.oracle A₁.oracle ∧
      toAntisymmetrization TuringReducible A₀.oracle ∈
        Set.Ioo (toAntisymmetrization TuringReducible (∅ : Set ℕ).oracle)
          (toAntisymmetrization TuringReducible lowSimpleSet.oracle) ∧
      toAntisymmetrization TuringReducible A₁.oracle ∈
        Set.Ioo (toAntisymmetrization TuringReducible (∅ : Set ℕ).oracle)
          (toAntisymmetrization TuringReducible lowSimpleSet.oracle) ∧
      toAntisymmetrization TuringReducible A₀.oracle ⊔
        toAntisymmetrization TuringReducible A₁.oracle =
          toAntisymmetrization TuringReducible lowSimpleSet.oracle := by
  let bs := RestrainedSimple.stage LowSimple.diagUse
  have hbs : Computable fun s => Finset.equivBitIndices.symm (bs s) :=
    (RestrainedSimple.primrec_stage LowSimple.primrec_diagUse).to_comp
  have hbm : Monotone bs := RestrainedSimple.monotone_stage LowSimple.diagUse
  have hnc : ¬ComputablePred (· ∈ stageLimit bs) := by
    rw [← lowSimpleSet_eq_stageLimit]
    exact simple_lowSimpleSet.not_computablePred
  have hinf (b : Bool) : (splitHalf bs bs b).Infinite :=
    .of_not_computablePred (not_computablePred_mem_splitHalf_self hbm hbs hnc b)
  rw [lowSimpleSet_eq_stageLimit]
  exact ⟨splitHalf bs bs false, splitHalf bs bs true,
    rePred_mem_splitHalf hbs hbs false, rePred_mem_splitHalf hbs hbs true,
    low_splitHalf hbs hbm hbs hnc false, low_splitHalf hbs hbm hbs hnc true,
    disjoint_splitHalf bs bs, splitHalf_false_union_splitHalf_true bs bs,
    hinf false, hinf true,
    not_simple_splitHalf_self hbm hbs hnc false,
    not_simple_splitHalf_self hbm hbs hnc true,
    incompRel_splitHalf_self hbm hbs hnc,
    degree_splitHalf_self_mem_Ioo hbm hbs hnc false,
    degree_splitHalf_self_mem_Ioo hbm hbs hnc true,
    (degree_stageLimit_eq_sup_splitHalf hbs hbs).symm⟩

/-- **Splitting `lowSimpleSet` against the distinct complete target `(∅ : Set ℕ).jump`:**
`lowSimpleSet` splits into two disjoint low c.e. sets whose join is Turing equivalent to
`lowSimpleSet` and neither of which computes `(∅ : Set ℕ).jump`. -/
theorem exists_split_lowSimpleSet_avoiding_jump_empty :
    ∃ A₀ A₁ : Set ℕ, REPred (· ∈ A₀) ∧ REPred (· ∈ A₁) ∧
      A₀.Low ∧ A₁.Low ∧ Disjoint A₀ A₁ ∧ A₀ ∪ A₁ = lowSimpleSet ∧
      TuringEquivalent lowSimpleSet.oracle (A₀.join A₁).oracle ∧
      ¬TuringReducible (∅ : Set ℕ).jump.oracle A₀.oracle ∧
      ¬TuringReducible (∅ : Set ℕ).jump.oracle A₁.oracle := by
  obtain ⟨A₀, A₁, hA₀, hA₁, hd, hunion, hL₀, hL₁, hnc₀, hnc₁⟩ :=
    exists_split_low_not_turingReducible rePred_mem_lowSimpleSet Set.rePred_mem_jump_empty
      (Set.not_computablePred_mem_jump ∅)
  exact ⟨A₀, A₁, hA₀, hA₁, hL₀, hL₁, hd, hunion,
    hunion ▸ hd.turingEquivalent_union_join hA₀ hA₁, hnc₀, hnc₁⟩

/-- **Incomparable low c.e. partner for `lowSimpleSet`:** splitting `(∅ : Set ℕ).jump` against the
incomplete target `lowSimpleSet` yields a low c.e. set strictly between `0` and `0'` whose Turing
degree is incomparable with `deg(lowSimpleSet)`. -/
theorem exists_low_ce_degree_incompRel_lowSimpleSet :
    ∃ A : Set ℕ, REPred (· ∈ A) ∧ A.Low ∧
      toAntisymmetrization TuringReducible A.oracle ∈
        Set.Ioo (toAntisymmetrization TuringReducible (∅ : Set ℕ).oracle)
          (toAntisymmetrization TuringReducible (∅ : Set ℕ).jump.oracle) ∧
      IncompRel (· ≤ ·) (toAntisymmetrization TuringReducible A.oracle)
        (toAntisymmetrization TuringReducible lowSimpleSet.oracle) := by
  have hK : ¬TuringReducible (∅ : Set ℕ).jump.oracle lowSimpleSet.oracle := fun h =>
    degree_lowSimpleSet_mem_Ioo.2.not_ge (turingDegree_le_iff.2 h)
  obtain ⟨A, hA, hlow, h₁, h₂⟩ :=
    exists_low_incomparable_degree rePred_mem_lowSimpleSet simple_lowSimpleSet.not_computablePred hK
  exact ⟨A, hA, hlow,
    Set.degree_mem_Ioo_of_incomparable hlow.turingReducible_jump_empty
      (Set.turingReducible_jump_of_rePred ∅ rePred_mem_lowSimpleSet)
      (mt turingDegree_le_iff.2 h₁) (mt turingDegree_le_iff.2 h₂),
    h₁, h₂⟩

/-! ### Index-level splitting of the halting set -/

/-- Running the numerical splitting operator `splitIndex` on an index `e` of `(∅ : Set ℕ).jump`
produces two c.e. indices `splitIndex false e e` and `splitIndex true e e` whose domains partition
`(∅ : Set ℕ).jump` into low, Turing incomparable halves whose parity join has degree `0'` and is
not low. -/
theorem exists_splitIndex_jump_empty :
    ∃ e : ℕ, {x | ((Denumerable.ofNat Nat.Partrec.Code e).eval x).Dom} = (∅ : Set ℕ).jump ∧
      let A₀ := {x | ((Denumerable.ofNat Nat.Partrec.Code (splitIndex false e e)).eval x).Dom}
      let A₁ := {x | ((Denumerable.ofNat Nat.Partrec.Code (splitIndex true e e)).eval x).Dom}
      Disjoint A₀ A₁ ∧ A₀ ∪ A₁ = (∅ : Set ℕ).jump ∧ A₀.Low ∧ A₁.Low ∧
        IncompRel TuringReducible A₀.oracle A₁.oracle ∧
        toAntisymmetrization TuringReducible (A₀.join A₁).oracle =
          toAntisymmetrization TuringReducible (∅ : Set ℕ).jump.oracle ∧
        ¬(A₀.join A₁).Low := by
  obtain ⟨k₀, hk₀⟩ := rePred_iff_exists_code.1 Set.rePred_mem_jump_empty
  have hk₀' : {x | (k₀.eval x).Dom} = (∅ : Set ℕ).jump := Set.ext fun x => (hk₀ x).symm
  have hnc : ¬ComputablePred fun x => (k₀.eval x).Dom := fun h =>
    Set.not_computablePred_mem_jump ∅ (h.of_eq fun x => (hk₀ x).symm)
  have hnl : ¬{x | (k₀.eval x).Dom}.Low := hk₀' ▸ Set.not_low_jump ∅
  refine ⟨Encodable.encode k₀, ?_⟩
  simp only [Denumerable.ofNat_encode, ofNat_splitIndex]
  refine ⟨hk₀', disjoint_dom_eval_splitCode k₀ k₀,
    (dom_eval_splitCode_false_union_true k₀ k₀).trans hk₀',
    low_dom_eval_splitCode hnc false k₀, low_dom_eval_splitCode hnc true k₀,
    incompRel_dom_eval_splitCode_self hnc, ?_, not_low_join_dom_eval_splitCode k₀ hnl⟩
  rw [← hk₀', toAntisymmetrization_eq]
  exact (turingEquivalent_dom_eval_join_splitCode k₀ k₀).symm

end TauCeti.Examples
