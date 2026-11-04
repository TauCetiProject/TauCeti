/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Join
public import TauCeti.Computability.SingleOracle.Code
import TauCeti.Computability.Enumeration.Code
import TauCeti.Computability.Enumeration.Domain

/-!
# Disjoint c.e. splittings

Let `B = A₀ ∪ A₁` with `A₀` and `A₁` disjoint c.e. sets. Although `A₀ ⊆ B` alone gives no
reduction, the two enumerations together do: to decide whether `x ∈ A₀` relative to `B`, first
ask whether `x ∈ B`; if not, `x ∉ A₀`, and if so, wait until `x` is enumerated into one of the
two halves, which says which half it lies in. Hence `A₀ ≤_T B`, `A₁ ≤_T B` and
`B ≡_T A₀ ⊕ A₁`.

The reduction is uniform in the enumerations. For ordinary codes `c₀` and `c₁`,
`Nat.Partrec.Code.splitProgram c₀ c₁` is an oracle program, primitive recursive in `c₀` and `c₁`,
which relative to the oracle `W_{c₀} ∪ W_{c₁}` computes `W_{c₀}` whenever the domains `W_{c₀}`
and `W_{c₁}` are disjoint. The program `splitProgram c₁ c₀` computes the other half.

## Main definitions

* `Nat.Partrec.Code.splitProgram`: the oracle program computing one half of a disjoint c.e.
  splitting from the whole.

## Main results

* `Nat.Partrec.Code.primrec₂_splitProgram`: the program is primitive recursive in the codes.
* `Nat.Partrec.Code.eval_splitProgram`: relative to `W_{c₀} ∪ W_{c₁}` it computes `W_{c₀}`
  when `W_{c₀}` and `W_{c₁}` are disjoint.
* `Disjoint.turingReducible_union_left`, `Disjoint.turingReducible_union_right`: each half of a
  disjoint c.e. splitting is Turing reducible to the whole.
* `Disjoint.turingEquivalent_union_join`: the whole is Turing equivalent to the join of the
  halves.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter VII, 3.3.
-/

public section

open Encodable Denumerable TauCeti.Enumeration

namespace TauCeti

open Nat.Partrec

/-- The search behind a splitting: on `x` with the oracle answer `b` for `x ∈ W_{c₀} ∪ W_{c₁}`,
look for a stage at which `b = 0` or `x` has been enumerated into `W_{c₀}` or `W_{c₁}`, and
answer `1` exactly when `b ≠ 0` and `x` was found in `W_{c₀}`. -/
private def splitSearch (c₀ c₁ : Code) (x b : ℕ) : Part ℕ :=
  (Nat.rfind fun s => Part.some (decide (b = 0 ∨ x ∈ c₀.domStage s ∨ x ∈ c₁.domStage s))).map
    fun s => if b ≠ 0 ∧ x ∈ c₀.domStage s then 1 else 0

/-- The splitting search is partial computable, with all of its arguments coded in one number. -/
private theorem partrec_splitSearch : Nat.Partrec fun n =>
    splitSearch (ofNat Code n.unpair.1.unpair.1) (ofNat Code n.unpair.1.unpair.2)
      n.unpair.2.unpair.1 n.unpair.2.unpair.2 := by
  classical
  -- the codes, the input and the oracle answer, read off from `n`
  have hc₀ : Primrec fun n : ℕ => ofNat Code n.unpair.1.unpair.1 :=
    (Primrec.ofNat Code).comp <| Primrec.fst.comp <| Primrec.unpair.comp <|
      Primrec.fst.comp Primrec.unpair
  have hc₁ : Primrec fun n : ℕ => ofNat Code n.unpair.1.unpair.2 :=
    (Primrec.ofNat Code).comp <| Primrec.snd.comp <| Primrec.unpair.comp <|
      Primrec.fst.comp Primrec.unpair
  have hx : Primrec fun n : ℕ => n.unpair.2.unpair.1 :=
    Primrec.fst.comp <| Primrec.unpair.comp <| Primrec.snd.comp Primrec.unpair
  have hb : Primrec fun n : ℕ => n.unpair.2.unpair.2 :=
    Primrec.snd.comp <| Primrec.unpair.comp <| Primrec.snd.comp Primrec.unpair
  -- membership of the input in the stage `s` of a domain
  have hmem {c : ℕ → Code} (hc : Primrec c) :
      Primrec₂ fun (n s : ℕ) => decide (n.unpair.2.unpair.1 ∈ (c n).domStage s) :=
    Code.primrecRel_mem_domStage.decide.comp ((hc.comp Primrec.fst).pair Primrec.snd)
      (hx.comp Primrec.fst)
  have hb0 : PrimrecRel fun (n _ : ℕ) => n.unpair.2.unpair.2 = 0 :=
    Primrec.eq.comp (hb.comp Primrec.fst) (Primrec.const 0)
  have hstop : Primrec₂ fun (n s : ℕ) => decide (n.unpair.2.unpair.2 = 0 ∨
      n.unpair.2.unpair.1 ∈ (ofNat Code n.unpair.1.unpair.1).domStage s ∨
      n.unpair.2.unpair.1 ∈ (ofNat Code n.unpair.1.unpair.2).domStage s) :=
    (Primrec.or.comp hb0.decide (Primrec.or.comp (hmem hc₀) (hmem hc₁))).of_eq fun p => by
      simp only [Bool.decide_or]
  have hout : Primrec₂ fun (n s : ℕ) =>
      if n.unpair.2.unpair.2 ≠ 0 ∧
        n.unpair.2.unpair.1 ∈ (ofNat Code n.unpair.1.unpair.1).domStage s then 1 else 0 :=
    (Primrec.ite (hb0.not.and (Primrec.eq.comp (hmem hc₀) (Primrec.const true)))
      (Primrec.const 1) (Primrec.const 0)).of_eq fun p => by simp only [decide_eq_true_eq, ne_eq]
  exact Partrec.nat_iff.1 <| (Partrec.rfind hstop.to_comp.partrec₂).map hout.to_comp

/-- A fixed ordinary code of the splitting search. -/
private noncomputable def splitSearchCode : Code :=
  (Code.exists_code.1 partrec_splitSearch).choose

private theorem eval_splitSearchCode (n : ℕ) :
    splitSearchCode.eval n = splitSearch (ofNat Code n.unpair.1.unpair.1)
      (ofNat Code n.unpair.1.unpair.2) n.unpair.2.unpair.1 n.unpair.2.unpair.2 :=
  congrFun (Code.exists_code.1 partrec_splitSearch).choose_spec n

/-- **Correctness of the splitting search.** Given the answer to whether `x ∈ W_{c₀} ∪ W_{c₁}`,
the search answers whether `x ∈ W_{c₀}`, provided the two domains are disjoint. -/
private theorem splitSearch_indicator {c₀ c₁ : Code}
    (hd : Disjoint {x | (c₀.eval x).Dom} {x | (c₁.eval x).Dom}) (x : ℕ) :
    splitSearch c₀ c₁ x (({x | (c₀.eval x).Dom} ∪ {x | (c₁.eval x).Dom}).indicator 1 x) =
      Part.some ({x | (c₀.eval x).Dom}.indicator 1 x) := by
  classical
  by_cases hx : (c₀.eval x).Dom ∨ (c₁.eval x).Dom
  · -- `x` is enumerated into one of the halves at some stage; the search finds the first one
    have hex : ∃ s, x ∈ c₀.domStage s ∨ x ∈ c₁.domStage s := by
      rcases hx with h | h
      · obtain ⟨s, hs⟩ := Code.exists_mem_domStage_iff.2 h
        exact ⟨s, Or.inl hs⟩
      · obtain ⟨s, hs⟩ := Code.exists_mem_domStage_iff.2 h
        exact ⟨s, Or.inr hs⟩
    have hmem : Nat.find hex ∈ Nat.rfind fun s =>
        Part.some (decide (1 = 0 ∨ x ∈ c₀.domStage s ∨ x ∈ c₁.domStage s)) :=
      Nat.mem_rfind.2 ⟨by simpa using Nat.find_spec hex,
        fun hm => by simpa using Nat.find_min hex hm⟩
    have hval : (x ∈ c₀.domStage (Nat.find hex)) ↔ (c₀.eval x).Dom := by
      refine ⟨fun h => Code.exists_mem_domStage_iff.1 ⟨_, h⟩, fun h₀ => ?_⟩
      refine (Nat.find_spec hex).resolve_right fun h₁ => ?_
      exact Set.disjoint_left.1 hd h₀ (Code.exists_mem_domStage_iff.1 ⟨_, h₁⟩)
    rw [Set.indicator_of_mem ((Set.mem_union _ _ _).2 hx), Pi.one_apply, splitSearch,
      Part.eq_some_iff.2 hmem, Part.map_some]
    by_cases h₀ : (c₀.eval x).Dom
    · rw [Set.indicator_of_mem h₀, ite_eq_left ⟨one_ne_zero, hval.2 h₀⟩, Pi.one_apply]
    · rw [Set.indicator_of_notMem h₀, ite_eq_right fun h => h₀ (hval.1 h.2)]
  · -- the oracle says `x ∉ W_{c₀} ∪ W_{c₁}`, and the search stops at once
    have hmem : 0 ∈ Nat.rfind fun s =>
        Part.some (decide (0 = 0 ∨ x ∈ c₀.domStage s ∨ x ∈ c₁.domStage s)) :=
      Nat.mem_rfind.2 ⟨by simp, fun hm => absurd hm (Nat.not_lt_zero _)⟩
    rw [Set.indicator_of_notMem fun h => hx ((Set.mem_union _ _ _).1 h),
      Set.indicator_of_notMem (not_or.1 hx).1, splitSearch, Part.eq_some_iff.2 hmem, Part.map_some,
      ite_eq_right fun h => h.1 rfl]

end TauCeti

namespace Nat.Partrec.Code

/-- The **splitting program** for ordinary codes `c₀` and `c₁`: relative to an oracle for
`W_{c₀} ∪ W_{c₁}`, on input `x` it asks the oracle whether `x ∈ W_{c₀} ∪ W_{c₁}`; if not it
answers `0`, and if so it waits until `x` is enumerated into `W_{c₀}` or `W_{c₁}` and answers `1`
or `0` accordingly. -/
noncomputable def splitProgram (c₀ c₁ : Code) : TauCeti.Oracle.Single.Code :=
  .comp (curry TauCeti.splitSearchCode (Nat.pair (encode c₀) (encode c₁))).toSingleOracleCode
    (.pair Code.id.toSingleOracleCode .oracle)

/-- The splitting program is primitive recursive in the two codes. -/
theorem primrec₂_splitProgram : Primrec₂ splitProgram :=
  TauCeti.Oracle.Single.Code.primrec₂_comp.comp
    (primrec_toSingleOracleCode.comp <| primrec₂_curry.comp
      (_root_.Primrec.const TauCeti.splitSearchCode)
      (Primrec₂.natPair.comp (_root_.Primrec.encode.comp _root_.Primrec.fst)
        (_root_.Primrec.encode.comp _root_.Primrec.snd)))
    (_root_.Primrec.const _)

/-- **Uniform split reduction.** If the domains `W_{c₀}` and `W_{c₁}` of two codes are disjoint,
then relative to `W_{c₀} ∪ W_{c₁}` the splitting program computes `W_{c₀}`. -/
theorem eval_splitProgram {c₀ c₁ : Code}
    (hd : Disjoint {x | (c₀.eval x).Dom} {x | (c₁.eval x).Dom}) :
    TauCeti.Oracle.Single.Code.eval ({x | (c₀.eval x).Dom} ∪ {x | (c₁.eval x).Dom}).oracle
      (splitProgram c₀ c₁) = {x | (c₀.eval x).Dom}.oracle := by
  funext x
  simp only [splitProgram, TauCeti.Oracle.Single.Code.eval_comp,
    TauCeti.Oracle.Single.Code.eval_pair, TauCeti.Oracle.Single.Code.eval_toSingleOracleCode,
    TauCeti.Oracle.Single.Code.eval_oracle, Set.oracle_apply, eval_id, Seq.seq, Part.map_eq_map,
    Part.map_some, Part.bind_some]
  -- `Code.eval` is valued in `ℕ →. ℕ`, which `rw` cannot see through, so chain the equations
  refine (Part.bind_some _ _).trans <| (eval_curry _ _ _).trans <|
    (TauCeti.eval_splitSearchCode _).trans ?_
  simpa only [Nat.unpair_pair, ofNat_encode] using TauCeti.splitSearch_indicator hd x


end Nat.Partrec.Code

namespace Disjoint

open TauCeti.Enumeration

variable {A₀ A₁ : Set ℕ}

/-- **Splitting, first half.** If `A₀` and `A₁` are disjoint c.e. sets, then `A₀` is Turing
reducible to `A₀ ∪ A₁`. -/
theorem turingReducible_union_left (hd : Disjoint A₀ A₁) (h₀ : REPred (· ∈ A₀))
    (h₁ : REPred (· ∈ A₁)) : TuringReducible A₀.oracle (A₀ ∪ A₁).oracle := by
  obtain ⟨c₀, hc₀⟩ := rePred_iff_exists_code.1 h₀
  obtain ⟨c₁, hc₁⟩ := rePred_iff_exists_code.1 h₁
  obtain rfl : A₀ = {x | (c₀.eval x).Dom} := Set.ext hc₀
  obtain rfl : A₁ = {x | (c₁.eval x).Dom} := Set.ext hc₁
  exact TauCeti.Oracle.Single.Code.turingReducible_iff_exists_code.2
    ⟨_, Nat.Partrec.Code.eval_splitProgram hd⟩

/-- **Splitting, second half.** If `A₀` and `A₁` are disjoint c.e. sets, then `A₁` is Turing
reducible to `A₀ ∪ A₁`. -/
theorem turingReducible_union_right (hd : Disjoint A₀ A₁) (h₀ : REPred (· ∈ A₀))
    (h₁ : REPred (· ∈ A₁)) : TuringReducible A₁.oracle (A₀ ∪ A₁).oracle := by
  rw [Set.union_comm]
  exact hd.symm.turingReducible_union_left h₁ h₀

/-- **Splitting and join.** If `A₀` and `A₁` are disjoint c.e. sets, then `A₀ ∪ A₁` is Turing
equivalent to the join `A₀ ⊕ A₁`. -/
theorem turingEquivalent_union_join (hd : Disjoint A₀ A₁) (h₀ : REPred (· ∈ A₀))
    (h₁ : REPred (· ∈ A₁)) : TuringEquivalent (A₀ ∪ A₁).oracle (A₀.join A₁).oracle :=
  ⟨Set.union_turingReducible_join, Set.join_turingReducible
    (hd.turingReducible_union_left h₀ h₁) (hd.turingReducible_union_right h₀ h₁)⟩

end Disjoint
