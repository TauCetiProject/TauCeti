/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SacksSplitting.Code
public import Mathlib.Order.Comparable

/-!
# Degree and set corollaries of Sacks splitting

Combining Sacks's low splitting theorem with the disjoint-splitting reductions of
`TauCeti.Computability.Split` yields Soare's structural consequences for the c.e. Turing degrees
[S, VII.3.3–7]:

* **Split reductions and join equivalence** [S, VII.3.3]: when `B` and `C` have computable stage
  codes, each half `splitHalf B C b` reduces to `stageLimit B` via the two disjoint enumerations
  (rather than subset inclusion), and `stageLimit B` is Turing equivalent to the parity join of
  the two halves, so its degree is the supremum of their degrees.
* **Self-splitting** [S, VII.3.4]: every noncomputable c.e. set `B` is the disjoint union of two
  low, Turing incomparable c.e. sets strictly below `B` whose join is Turing equivalent to `B`.
* **Join of low degrees** [S, VII.3.5]: splitting an arbitrary c.e. set `B` (including computable
  or finite `B`) against `(∅ : Set ℕ).jump` expresses `B` as a disjoint union of two low c.e. sets
  whose degrees have supremum `deg(B)`.
* **Non-minimality** [S, VII.3.6]: every nonzero c.e. degree bounds a strictly smaller nonzero low
  c.e. degree, so no c.e. degree covers the computable degree in `TuringDegree`.
* **Incomparability below `0'`** [S, VII.3.7]: splitting `(∅ : Set ℕ).jump` against a nonzero
  incomplete c.e. set `C` produces two low c.e. halves at least one of which cannot reduce to `C`
  (else their join `(∅ : Set ℕ).jump` would reduce to `C`), giving a low c.e. set Turing
  incomparable with `C`. Following [S, p. 125], `exists_primrec_code_pair_incompRel_of_incomplete`
  exhibits a primitive recursive pair `(f₀ c, f₁ c)` of codes at least one of whose domains is
  incomparable with `W_c` when `0 <_T W_c <_T 0'`, without asserting a computable selector between
  the two halves.
* **Failure of lowness and jump distribution under join**: splitting `(∅ : Set ℕ).jump` yields two
  low c.e. sets whose join is complete (hence not low), so `deg(A₀') ⊔ deg(A₁') < deg((A₀ ⊕ A₁)')`.

## Main results

* `TauCeti.SacksSplitting.turingEquivalent_dom_eval_join_splitCode`,
  `TauCeti.SacksSplitting.incompRel_dom_eval_splitCode_self`: code-level join equivalence and
  self-splitting incomparability.
* `TauCeti.SacksSplitting.exists_low_incomparable_split`,
  `TauCeti.SacksSplitting.exists_low_incomparable_ce_degrees_sup_eq`: [S, VII.3.4].
* `TauCeti.SacksSplitting.exists_split_low`,
  `TauCeti.SacksSplitting.exists_low_ce_degrees_sup_eq`: [S, VII.3.5].
* `TauCeti.SacksSplitting.exists_low_ce_degree_mem_Ioo`,
  `TauCeti.SacksSplitting.not_covBy_degree_of_rePred`: [S, VII.3.6].
* `TauCeti.SacksSplitting.exists_primrec_code_pair_incompRel_of_incomplete`,
  `TauCeti.SacksSplitting.exists_low_rePred_incompRel_of_incomplete`,
  `TauCeti.SacksSplitting.exists_low_ce_degree_incompRel`: [S, VII.3.7].
* `TauCeti.SacksSplitting.exists_split_jump_empty_low_not_low_join`,
  `TauCeti.SacksSplitting.not_forall_jump_join_turingReducible`: low c.e. halves of
  `(∅ : Set ℕ).jump` have non-low join and refute unrestricted jump distribution over join.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Remark VII.3.3 and
  Corollaries VII.3.4–VII.3.7, pp. 125–126.
-/

public section

open TauCeti.Enumeration

namespace TauCeti.SacksSplitting

/-! ### Split reductions and join equivalence -/

section SplitJoin

variable {B C : ℕ → Finset ℕ}
  (hB : Computable fun s => Finset.equivBitIndices.symm (B s))
  (hC : Computable fun s => Finset.equivBitIndices.symm (C s))
include hB hC

/-- Each half of Sacks's splitting is Turing reducible to `stageLimit B` [S, VII.3.3]. -/
theorem turingReducible_splitHalf_stageLimit (b : Bool) :
    TuringReducible (splitHalf B C b).oracle (stageLimit B).oracle := by
  rw [← splitHalf_false_union_splitHalf_true B C]
  cases b
  · exact (disjoint_splitHalf B C).turingReducible_union_left
      (rePred_mem_splitHalf hB hC false) (rePred_mem_splitHalf hB hC true)
  · exact (disjoint_splitHalf B C).turingReducible_union_right
      (rePred_mem_splitHalf hB hC false) (rePred_mem_splitHalf hB hC true)

/-- `stageLimit B` is Turing equivalent to the parity join of its two Sacks-splitting halves
[S, VII.3.3]. -/
theorem turingEquivalent_stageLimit_join_splitHalf :
    TuringEquivalent (stageLimit B).oracle
      ((splitHalf B C false).join (splitHalf B C true)).oracle := by
  rw [← splitHalf_false_union_splitHalf_true B C]
  exact (disjoint_splitHalf B C).turingEquivalent_union_join
    (rePred_mem_splitHalf hB hC false) (rePred_mem_splitHalf hB hC true)

/-- The Turing degree of `stageLimit B` is the supremum of the degrees of its two Sacks-splitting
halves. -/
theorem degree_stageLimit_eq_sup_splitHalf :
    toAntisymmetrization TuringReducible (stageLimit B).oracle =
      toAntisymmetrization TuringReducible (splitHalf B C false).oracle ⊔
        toAntisymmetrization TuringReducible (splitHalf B C true).oracle := by
  rw [← (Set.isLUB_degree_join _ _).unique isLUB_pair, toAntisymmetrization_eq]
  exact turingEquivalent_stageLimit_join_splitHalf hB hC

end SplitJoin

/-- For **all** codes `c₀` and `c₁`, `W_{c₀}` is Turing equivalent to the parity join of the two
output domains `W_{splitCode false c₀ c₁}` and `W_{splitCode true c₀ c₁}` [S, VII.3.3]. -/
theorem turingEquivalent_dom_eval_join_splitCode (c₀ c₁ : Nat.Partrec.Code) :
    TuringEquivalent {x | (c₀.eval x).Dom}.oracle
      ({x | ((splitCode false c₀ c₁).eval x).Dom}.join
        {x | ((splitCode true c₀ c₁).eval x).Dom}).oracle := by
  rw [← dom_eval_splitCode_false_union_true c₀ c₁]
  exact (disjoint_dom_eval_splitCode c₀ c₁).turingEquivalent_union_join
    (splitCode false c₀ c₁).rePred_dom_eval (splitCode true c₀ c₁).rePred_dom_eval

/-- When `W_{c₀}` is not low, the parity join of `W_{splitCode false c₀ c₁}` and
`W_{splitCode true c₀ c₁}` is not low, for any target code `c₁`. -/
theorem not_low_join_dom_eval_splitCode {c₀ : Nat.Partrec.Code} (c₁ : Nat.Partrec.Code)
    (hnl : ¬{x | (c₀.eval x).Dom}.Low) :
    ¬({x | ((splitCode false c₀ c₁).eval x).Dom}.join
      {x | ((splitCode true c₀ c₁).eval x).Dom}).Low := fun h =>
  hnl ((Set.low_congr (turingEquivalent_dom_eval_join_splitCode c₀ c₁)).2 h)

/-! ### Self-splitting into incomparable low halves -/

section SelfSplit

variable {B : ℕ → Finset ℕ} (hBm : Monotone B)
  (hB : Computable fun s => Finset.equivBitIndices.symm (B s))
  (hnc : ¬ComputablePred (· ∈ stageLimit B))
include hBm hB hnc

/-- When `B` has computable monotone stages and a noncomputable limit, neither half of
`splitHalf B B` is Turing reducible to the opposite half. -/
theorem not_turingReducible_splitHalf_self (b : Bool) :
    ¬TuringReducible (splitHalf B B b).oracle (splitHalf B B (!b)).oracle := fun h => by
  -- otherwise `stageLimit B` would reduce to `splitHalf B B (!b)` via the parity join
  have hjoin : TuringReducible ((splitHalf B B false).join (splitHalf B B true)).oracle
      (splitHalf B B (!b)).oracle := by
    cases b
    · exact Set.join_turingReducible h .rfl
    · exact Set.join_turingReducible .rfl h
  exact not_turingReducible_splitHalf hB hBm hB hnc (!b)
    ((turingEquivalent_stageLimit_join_splitHalf hB hB).1.trans hjoin)

/-- The two halves of `splitHalf B B` are Turing incomparable. -/
theorem incompRel_splitHalf_self :
    IncompRel TuringReducible (splitHalf B B false).oracle (splitHalf B B true).oracle :=
  ⟨not_turingReducible_splitHalf_self hBm hB hnc false,
    not_turingReducible_splitHalf_self hBm hB hnc true⟩

/-- Neither half of `splitHalf B B` is computable. -/
theorem not_computablePred_mem_splitHalf_self (b : Bool) :
    ¬ComputablePred (· ∈ splitHalf B B b) := fun h =>
  not_turingReducible_splitHalf_self hBm hB hnc b
    (((Set.turingReducible_empty_iff _).2 h).trans (Set.empty_turingReducible _))

/-- Each half of `splitHalf B B` has Turing degree strictly between `0` and `deg(stageLimit B)`. -/
theorem degree_splitHalf_self_mem_Ioo (b : Bool) :
    toAntisymmetrization TuringReducible (splitHalf B B b).oracle ∈
      Set.Ioo (toAntisymmetrization TuringReducible (∅ : Set ℕ).oracle)
        (toAntisymmetrization TuringReducible (stageLimit B).oracle) := by
  simp only [Set.mem_Ioo, lt_iff_le_not_ge, turingDegree_le_iff]
  refine ⟨⟨Set.empty_turingReducible _, fun h =>
      not_computablePred_mem_splitHalf_self hBm hB hnc b ((Set.turingReducible_empty_iff _).1 h)⟩,
    ⟨turingReducible_splitHalf_stageLimit hB hB b,
      not_turingReducible_splitHalf hB hBm hB hnc b⟩⟩

end SelfSplit

/-- When `W_c` is noncomputable, the domains of `splitCode false c c` and `splitCode true c c` are
Turing incomparable [S, VII.3.4]. -/
theorem incompRel_dom_eval_splitCode_self {c : Nat.Partrec.Code}
    (hnc : ¬ComputablePred fun x => (c.eval x).Dom) :
    IncompRel TuringReducible {x | ((splitCode false c c).eval x).Dom}.oracle
      {x | ((splitCode true c c).eval x).Dom}.oracle := by
  rw [setOf_dom_eval_splitCode, setOf_dom_eval_splitCode]
  have hnclim : ¬ComputablePred (· ∈ stageLimit c.domStage) := by
    rwa [Nat.Partrec.Code.stageLimit_domStage]
  exact incompRel_splitHalf_self c.monotone_domStage c.computable_domStage hnclim

/-- **Incomparable low c.e. splitting** [S, VII.3.4]: every noncomputable c.e. set `B` is the
disjoint union of two low, Turing incomparable c.e. sets strictly Turing below `B`, whose parity
join is Turing equivalent to `B`. -/
theorem exists_low_incomparable_split {B : Set ℕ} (hB : REPred (· ∈ B))
    (hnc : ¬ComputablePred (· ∈ B)) :
    ∃ A₀ A₁ : Set ℕ, REPred (· ∈ A₀) ∧ REPred (· ∈ A₁) ∧
      A₀.Low ∧ A₁.Low ∧ Disjoint A₀ A₁ ∧ A₀ ∪ A₁ = B ∧
      TuringReducible A₀.oracle B.oracle ∧ TuringReducible A₁.oracle B.oracle ∧
      ¬TuringReducible B.oracle A₀.oracle ∧ ¬TuringReducible B.oracle A₁.oracle ∧
      IncompRel TuringReducible A₀.oracle A₁.oracle ∧
      TuringEquivalent B.oracle (A₀.join A₁).oracle := by
  obtain ⟨bs, hbm, -, hbs, hBlim⟩ := rePred_iff_exists_stages.1 hB
  simp only [Set.ofPred_mem_eq] at hBlim
  rw [← hBlim] at hnc ⊢
  exact ⟨splitHalf bs bs false, splitHalf bs bs true,
    rePred_mem_splitHalf hbs hbs false, rePred_mem_splitHalf hbs hbs true,
    low_splitHalf hbs hbm hbs hnc false, low_splitHalf hbs hbm hbs hnc true,
    disjoint_splitHalf bs bs, splitHalf_false_union_splitHalf_true bs bs,
    turingReducible_splitHalf_stageLimit hbs hbs false,
    turingReducible_splitHalf_stageLimit hbs hbs true,
    not_turingReducible_splitHalf hbs hbm hbs hnc false,
    not_turingReducible_splitHalf hbs hbm hbs hnc true,
    incompRel_splitHalf_self hbm hbs hnc,
    turingEquivalent_stageLimit_join_splitHalf hbs hbs⟩

/-- **Degree form of Sacks's self-splitting** [S, VII.3.4]: for every noncomputable c.e. set `B`,
there are two low c.e. sets with incomparable Turing degrees strictly between `0` and `deg(B)`
whose supremum is `deg(B)`. -/
theorem exists_low_incomparable_ce_degrees_sup_eq {B : Set ℕ} (hB : REPred (· ∈ B))
    (hnc : ¬ComputablePred (· ∈ B)) :
    ∃ A₀ A₁ : Set ℕ, REPred (· ∈ A₀) ∧ REPred (· ∈ A₁) ∧ A₀.Low ∧ A₁.Low ∧
      toAntisymmetrization TuringReducible A₀.oracle ∈
        Set.Ioo (toAntisymmetrization TuringReducible (∅ : Set ℕ).oracle)
          (toAntisymmetrization TuringReducible B.oracle) ∧
      toAntisymmetrization TuringReducible A₁.oracle ∈
        Set.Ioo (toAntisymmetrization TuringReducible (∅ : Set ℕ).oracle)
          (toAntisymmetrization TuringReducible B.oracle) ∧
      IncompRel (· ≤ ·) (toAntisymmetrization TuringReducible A₀.oracle)
        (toAntisymmetrization TuringReducible A₁.oracle) ∧
      toAntisymmetrization TuringReducible A₀.oracle ⊔
        toAntisymmetrization TuringReducible A₁.oracle =
          toAntisymmetrization TuringReducible B.oracle := by
  obtain ⟨bs, hbm, -, hbs, hBlim⟩ := rePred_iff_exists_stages.1 hB
  simp only [Set.ofPred_mem_eq] at hBlim
  rw [← hBlim] at hnc ⊢
  refine ⟨splitHalf bs bs false, splitHalf bs bs true,
    rePred_mem_splitHalf hbs hbs false, rePred_mem_splitHalf hbs hbs true,
    low_splitHalf hbs hbm hbs hnc false, low_splitHalf hbs hbm hbs hnc true,
    degree_splitHalf_self_mem_Ioo hbm hbs hnc false,
    degree_splitHalf_self_mem_Ioo hbm hbs hnc true, ?_,
    (degree_stageLimit_eq_sup_splitHalf hbs hbs).symm⟩
  simpa only [IncompRel, turingDegree_le_iff] using incompRel_splitHalf_self hbm hbs hnc

/-! ### Every c.e. degree is a join of two low c.e. degrees -/

/-- **Low splitting of an arbitrary c.e. set** [S, VII.3.5]: every c.e. set `B` (including
computable, finite, or empty sets) is the disjoint union of two low c.e. sets whose parity join is
Turing equivalent to `B`. -/
theorem exists_split_low {B : Set ℕ} (hB : REPred (· ∈ B)) :
    ∃ A₀ A₁ : Set ℕ, REPred (· ∈ A₀) ∧ REPred (· ∈ A₁) ∧
      A₀.Low ∧ A₁.Low ∧ Disjoint A₀ A₁ ∧ A₀ ∪ A₁ = B ∧
      TuringEquivalent B.oracle (A₀.join A₁).oracle := by
  obtain ⟨A₀, A₁, hA₀, hA₁, hd, hunion, hL₀, hL₁, -, -⟩ :=
    exists_split_low_not_turingReducible hB Set.rePred_mem_jump_empty
      (Set.not_computablePred_mem_jump ∅)
  exact ⟨A₀, A₁, hA₀, hA₁, hL₀, hL₁, hd, hunion,
    hunion ▸ hd.turingEquivalent_union_join hA₀ hA₁⟩

/-- **Every c.e. degree is the supremum of two low c.e. degrees** [S, VII.3.5]. -/
theorem exists_low_ce_degrees_sup_eq {B : Set ℕ} (hB : REPred (· ∈ B)) :
    ∃ A₀ A₁ : Set ℕ, REPred (· ∈ A₀) ∧ REPred (· ∈ A₁) ∧ A₀.Low ∧ A₁.Low ∧
      toAntisymmetrization TuringReducible A₀.oracle ⊔
        toAntisymmetrization TuringReducible A₁.oracle =
          toAntisymmetrization TuringReducible B.oracle := by
  obtain ⟨A₀, A₁, hA₀, hA₁, hL₀, hL₁, -, -, heq⟩ := exists_split_low hB
  refine ⟨A₀, A₁, hA₀, hA₁, hL₀, hL₁, ?_⟩
  rw [← (Set.isLUB_degree_join A₀ A₁).unique isLUB_pair, toAntisymmetrization_eq]
  exact heq.symm

/-! ### Non-minimality of nonzero c.e. degrees -/

/-- Below every nonzero c.e. degree there is a strictly intermediate low c.e. degree
[S, VII.3.6]. -/
theorem exists_low_ce_degree_mem_Ioo {B : Set ℕ} (hB : REPred (· ∈ B))
    (hpos : toAntisymmetrization TuringReducible (∅ : Set ℕ).oracle <
      toAntisymmetrization TuringReducible B.oracle) :
    ∃ A : Set ℕ, REPred (· ∈ A) ∧ A.Low ∧
      toAntisymmetrization TuringReducible A.oracle ∈
        Set.Ioo (toAntisymmetrization TuringReducible (∅ : Set ℕ).oracle)
          (toAntisymmetrization TuringReducible B.oracle) := by
  have hnc : ¬ComputablePred (· ∈ B) := fun hc =>
    hpos.not_ge (turingDegree_le_iff.2 ((Set.turingReducible_empty_iff B).2 hc))
  obtain ⟨A₀, -, hA₀, -, hL₀, -, hmem, -, -, -⟩ := exists_low_incomparable_ce_degrees_sup_eq hB hnc
  exact ⟨A₀, hA₀, hL₀, hmem⟩

/-- **No c.e. degree is minimal** [S, VII.3.6]: no c.e. set has degree covering the computable
degree in `TuringDegree`. -/
theorem not_covBy_degree_of_rePred {B : Set ℕ} (hB : REPred (· ∈ B)) :
    ¬(toAntisymmetrization TuringReducible (∅ : Set ℕ).oracle ⋖
      toAntisymmetrization TuringReducible B.oracle) := fun hcov => by
  obtain ⟨A, -, -, h₀A, hAB⟩ := exists_low_ce_degree_mem_Ioo hB hcov.lt
  exact hcov.2 h₀A hAB

/-! ### Incomparable low c.e. degrees for nonzero incomplete c.e. degrees -/

/-- Given a code `k₀` for `(∅ : Set ℕ).jump` and a code `c` whose domain `W_c` is noncomputable
and incomplete, at least one side `b` of `splitCode b k₀ c` has a low domain Turing incomparable
with `W_c` [S, VII.3.7]. -/
theorem exists_side_incompRel_splitCode_of_incomplete {k₀ c : Nat.Partrec.Code}
    (hk₀ : {x | (k₀.eval x).Dom} = (∅ : Set ℕ).jump)
    (hnc : ¬ComputablePred fun x => (c.eval x).Dom)
    (hinc : ¬TuringReducible (∅ : Set ℕ).jump.oracle {x | (c.eval x).Dom}.oracle) :
    ∃ b : Bool, {x | ((splitCode b k₀ c).eval x).Dom}.Low ∧
      IncompRel TuringReducible {x | ((splitCode b k₀ c).eval x).Dom}.oracle
        {x | (c.eval x).Dom}.oracle := by
  by_contra! hall
  have hred (b : Bool) :
      TuringReducible {x | ((splitCode b k₀ c).eval x).Dom}.oracle {x | (c.eval x).Dom}.oracle := by
    by_contra hnr
    exact hall b (low_dom_eval_splitCode hnc b k₀)
      ⟨hnr, not_turingReducible_dom_eval_splitCode hnc b k₀⟩
  have heq := turingEquivalent_dom_eval_join_splitCode k₀ c
  rw [hk₀] at heq
  exact hinc (heq.1.trans (Set.join_turingReducible (hred false) (hred true)))

/-- **Uniform code-pair form of [S, VII.3.7 and p. 125].** There is a pair of primitive recursive
code transformations `(f₀, f₁)` whose domains partition `(∅ : Set ℕ).jump` for **every** code `c`,
such that whenever `W_c` is noncomputable and incomplete, both domains are low and **at least one**
of them is Turing incomparable with `W_c`. Following Soare's remark on p. 125, the pair
`(f₀ c, f₁ c)` is uniform in `c`, whereas no computable selector choosing a single successful half
is claimed. -/
theorem exists_primrec_code_pair_incompRel_of_incomplete :
    ∃ f₀ f₁ : Nat.Partrec.Code → Nat.Partrec.Code, Primrec f₀ ∧ Primrec f₁ ∧
      (∀ c, Disjoint {x | ((f₀ c).eval x).Dom} {x | ((f₁ c).eval x).Dom} ∧
        {x | ((f₀ c).eval x).Dom} ∪ {x | ((f₁ c).eval x).Dom} = (∅ : Set ℕ).jump) ∧
      ∀ c, (¬ComputablePred fun x => (c.eval x).Dom) →
        ¬TuringReducible (∅ : Set ℕ).jump.oracle {x | (c.eval x).Dom}.oracle →
        {x | ((f₀ c).eval x).Dom}.Low ∧ {x | ((f₁ c).eval x).Dom}.Low ∧
          (IncompRel TuringReducible {x | ((f₀ c).eval x).Dom}.oracle {x | (c.eval x).Dom}.oracle ∨
            IncompRel TuringReducible {x | ((f₁ c).eval x).Dom}.oracle
              {x | (c.eval x).Dom}.oracle) := by
  obtain ⟨k₀, hk₀⟩ := rePred_iff_exists_code.1 Set.rePred_mem_jump_empty
  have hk₀' : {x | (k₀.eval x).Dom} = (∅ : Set ℕ).jump := Set.ext fun x => (hk₀ x).symm
  refine ⟨fun c => splitCode false k₀ c, fun c => splitCode true k₀ c,
    (primrec₂_splitCode false).comp (Primrec.const k₀) Primrec.id,
    (primrec₂_splitCode true).comp (Primrec.const k₀) Primrec.id,
    fun c => ⟨disjoint_dom_eval_splitCode k₀ c,
      (dom_eval_splitCode_false_union_true k₀ c).trans hk₀'⟩,
    fun c hnc hinc => ⟨low_dom_eval_splitCode hnc false k₀, low_dom_eval_splitCode hnc true k₀, ?_⟩⟩
  obtain ⟨b, -, hincb⟩ := exists_side_incompRel_splitCode_of_incomplete hk₀' hnc hinc
  cases b
  · exact Or.inl hincb
  · exact Or.inr hincb

/-- **Every noncomputable incomplete c.e. set has an incomparable low c.e. set** [S, VII.3.7]. -/
theorem exists_low_rePred_incompRel_of_incomplete {C : Set ℕ} (hC : REPred (· ∈ C))
    (hnc : ¬ComputablePred (· ∈ C))
    (hinc : ¬TuringReducible (∅ : Set ℕ).jump.oracle C.oracle) :
    ∃ A : Set ℕ, REPred (· ∈ A) ∧ A.Low ∧ IncompRel TuringReducible A.oracle C.oracle := by
  obtain ⟨k₀, hk₀⟩ := rePred_iff_exists_code.1 Set.rePred_mem_jump_empty
  obtain ⟨c, hc⟩ := rePred_iff_exists_code.1 hC
  have hk₀' : {x | (k₀.eval x).Dom} = (∅ : Set ℕ).jump := Set.ext fun x => (hk₀ x).symm
  have hc' : {x | (c.eval x).Dom} = C := Set.ext fun x => (hc x).symm
  rw [← hc'] at hnc hinc ⊢
  obtain ⟨b, hlow, hincomp⟩ := exists_side_incompRel_splitCode_of_incomplete hk₀' hnc hinc
  exact ⟨{x | ((splitCode b k₀ c).eval x).Dom}, (splitCode b k₀ c).rePred_dom_eval, hlow, hincomp⟩

/-- **Degree form of [S, VII.3.7]:** every c.e. degree strictly between `0` and `0'` has an
incomparable low c.e. degree, which likewise lies strictly between `0` and `0'`. -/
theorem exists_low_ce_degree_incompRel {C : Set ℕ} (hC : REPred (· ∈ C))
    (hIoo : toAntisymmetrization TuringReducible C.oracle ∈
      Set.Ioo (toAntisymmetrization TuringReducible (∅ : Set ℕ).oracle)
        (toAntisymmetrization TuringReducible (∅ : Set ℕ).jump.oracle)) :
    ∃ A : Set ℕ, REPred (· ∈ A) ∧ A.Low ∧
      toAntisymmetrization TuringReducible A.oracle ∈
        Set.Ioo (toAntisymmetrization TuringReducible (∅ : Set ℕ).oracle)
          (toAntisymmetrization TuringReducible (∅ : Set ℕ).jump.oracle) ∧
      IncompRel (· ≤ ·) (toAntisymmetrization TuringReducible A.oracle)
        (toAntisymmetrization TuringReducible C.oracle) := by
  have hnc : ¬ComputablePred (· ∈ C) := fun hc =>
    hIoo.1.not_ge (turingDegree_le_iff.2 ((Set.turingReducible_empty_iff C).2 hc))
  have hinc : ¬TuringReducible (∅ : Set ℕ).jump.oracle C.oracle := fun h =>
    hIoo.2.not_ge (turingDegree_le_iff.2 h)
  obtain ⟨A, hA, hlow, hincomp⟩ := exists_low_rePred_incompRel_of_incomplete hC hnc hinc
  refine ⟨A, hA, hlow,
    Set.degree_mem_Ioo_of_incomparable hlow.turingReducible_jump_empty
      (Set.turingReducible_jump_of_rePred ∅ hC) hincomp.1 hincomp.2, ?_⟩
  simpa only [IncompRel, turingDegree_le_iff] using hincomp

/-! ### Splitting the halting set: low sets with non-low join -/

/-- **Splitting `(∅ : Set ℕ).jump` into low halves:** the halting set is the disjoint union of two
low, Turing incomparable c.e. sets `A₀` and `A₁` whose parity join `A₀ ⊕ A₁` is not low, and whose
jumps satisfy `deg(A₀') ⊔ deg(A₁') < deg((A₀ ⊕ A₁)')`. -/
theorem exists_split_jump_empty_low_not_low_join :
    ∃ A₀ A₁ : Set ℕ, REPred (· ∈ A₀) ∧ REPred (· ∈ A₁) ∧
      A₀.Low ∧ A₁.Low ∧ Disjoint A₀ A₁ ∧ A₀ ∪ A₁ = (∅ : Set ℕ).jump ∧
      IncompRel TuringReducible A₀.oracle A₁.oracle ∧
      ¬(A₀.join A₁).Low ∧
      ¬TuringReducible (A₀.join A₁).jump.oracle (A₀.jump.join A₁.jump).oracle ∧
      toAntisymmetrization TuringReducible A₀.jump.oracle ⊔
        toAntisymmetrization TuringReducible A₁.jump.oracle <
          toAntisymmetrization TuringReducible (A₀.join A₁).jump.oracle := by
  obtain ⟨A₀, A₁, hA₀, hA₁, hL₀, hL₁, hd, hunion, -, -, -, -, hincomp, heq⟩ :=
    exists_low_incomparable_split Set.rePred_mem_jump_empty (Set.not_computablePred_mem_jump ∅)
  have hnotlow : ¬(A₀.join A₁).Low := fun h =>
    Set.not_low_jump ∅ ((Set.low_congr heq).2 h)
  have hjjoin : TuringReducible (A₀.jump.join A₁.jump).oracle (∅ : Set ℕ).jump.oracle :=
    Set.join_turingReducible (Set.low_iff_jump_turingReducible.1 hL₀)
      (Set.low_iff_jump_turingReducible.1 hL₁)
  have hnotred : ¬TuringReducible (A₀.join A₁).jump.oracle (A₀.jump.join A₁.jump).oracle :=
    fun h => Set.not_jump_turingReducible (∅ : Set ℕ).jump <|
      (Set.turingReducible_jump_jump heq.1).trans (h.trans hjjoin)
  have hsup : toAntisymmetrization TuringReducible A₀.jump.oracle ⊔
      toAntisymmetrization TuringReducible A₁.jump.oracle =
        toAntisymmetrization TuringReducible (A₀.jump.join A₁.jump).oracle :=
    ((Set.isLUB_degree_join A₀.jump A₁.jump).unique isLUB_pair).symm
  have hle : toAntisymmetrization TuringReducible (A₀.jump.join A₁.jump).oracle ≤
      toAntisymmetrization TuringReducible (A₀.join A₁).jump.oracle := by
    rw [← hsup, sup_le_iff, turingDegree_le_iff, turingDegree_le_iff]
    exact ⟨Set.turingReducible_jump_jump Set.turingReducible_join_left,
      Set.turingReducible_jump_jump Set.turingReducible_join_right⟩
  have hlt : toAntisymmetrization TuringReducible A₀.jump.oracle ⊔
      toAntisymmetrization TuringReducible A₁.jump.oracle <
        toAntisymmetrization TuringReducible (A₀.join A₁).jump.oracle := by
    rw [hsup, lt_iff_le_not_ge]
    exact ⟨hle, by rwa [turingDegree_le_iff]⟩
  exact ⟨A₀, A₁, hA₀, hA₁, hL₀, hL₁, hd, hunion, hincomp, hnotlow, hnotred, hlt⟩

/-- **The Turing jump does not distribute over the parity join:** `(A₀ ⊕ A₁)'` need not Turing
reduce to `A₀' ⊕ A₁'`, even when `A₀` and `A₁` are disjoint low c.e. sets. -/
theorem not_forall_jump_join_turingReducible :
    ¬∀ A₀ A₁ : Set ℕ, TuringReducible (A₀.join A₁).jump.oracle (A₀.jump.join A₁.jump).oracle := by
  intro hall
  obtain ⟨A₀, A₁, -, -, -, -, -, -, -, -, hnotred, -⟩ := exists_split_jump_empty_low_not_low_join
  exact hnotred (hall A₀ A₁)

end TauCeti.SacksSplitting
