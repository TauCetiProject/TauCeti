/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Simple.Basic
public import TauCeti.Computability.Enumeration.Code
public import TauCeti.Computability.SingleOracle.Primrec
public import TauCeti.Computability.Priority.Injury.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
import TauCeti.Computability.Priority.Injury.Causes
import TauCeti.Computability.Primrec.Bitwise
import TauCeti.Computability.Primrec.List
import TauCeti.Data.Set.Card
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Finite

/-!
# The finite-injury construction of a low simple set

This file carries out Soare's finite-injury construction of a simple set `A` [S, VII.1.1] and
proves that it is simple. The construction has two families of requirements, in the priority
order `N_0, P_0, N_1, P_1, …`:

* the positive requirement `P_i`: if `W_i` is infinite then `A` meets `W_i`;
* the negative requirement `N_e`: if `Φ_{e,s}^{A_s}(e)` converges at infinitely many stages `s`,
  then `Φ_e^A(e)` converges.

Here `W_i` is the domain of the code `Denumerable.ofNat Nat.Partrec.Code i`, with stages
`W_{i,s}` given by `Nat.Partrec.Code.domStage`, and `Φ_{e,s}^{A_s}(e)` is the run `diagRun` of the
oracle program numbered `e` on the input `e` with fuel `s` against the finite set `A_s`, answering
`1` on `A_s` and `0` outside it.

The stages `A_s = stage s` start empty. At the transition to stage `s + 1`, the restraint of
`N_e` is the use `r(e, s)` of `Φ_{e,s}^{A_s}(e)`, or `0` when this run fails. The requirement `P_i`
**requires attention** with the witness `x` when `W_{i,s}` is still disjoint from `A_s`, and `x`
is an element of `W_{i,s}` with `x > 2i` and `x > r(e, s)` for every `e ≤ i`. The least `i` that
requires attention enumerates its least witness. So at most one number enters per stage, and
the entries of `P_i` never injure `N_e` for `e ≤ i`.

The main results, in the order in which the verification uses them:

* the stages and their limit are effective: the binary codes of the stages are primitive
  recursive, so `A` is c.e. (`TauCeti.rePred_mem_lowSimpleSet`);
* each positive requirement acts at most once (`TauCeti.LowSimple.eq_of_attention_eq_some`), so
  the entries below `2n` come from the requirements `P_i` with `i < n`, which gives the counting
  invariant `|A ∩ [0, 2n]| ≤ n` and coinfiniteness;
* every injury to `N_e`, a number entering at or below the restraint `r(e, s)`, is caused by
  some `P_i` with `i < e`, so `N_e` is injured by at most `e` numbers
  (`TauCeti.LowSimple.finite_injurySet_and_ncard_le`);
* after the last injury a convergent computation `Φ_{e,s}^{A_s}(e)` is preserved forever, so the
  diagonal stage computations and the restraints are eventually constant
  (`TauCeti.LowSimple.exists_eventually_diagRun_eq`);
* once the restraints of `N_0, …, N_i` and the actions of `P_0, …, P_{i-1}` have settled, `P_i`
  acts if `W_i` is infinite and still disjoint from `A`, so every positive requirement is met
  and `A` is simple (`TauCeti.simple_lowSimpleSet`).

Lowness of `A`, which the negative requirements are designed for, is not proved in this file.

## Main definitions

* `TauCeti.LowSimple.diagRun`, `TauCeti.LowSimple.diagUse`: the diagonal stage computation
  `Φ_{e,s}^D(e)` against a finite set `D`, and its use. Both are primitive recursive in the binary
  code of `D` (`TauCeti.LowSimple.primrec_diagRun`).
* `TauCeti.LowSimple.RequiresAttention`, `TauCeti.LowSimple.attention`: when a positive
  requirement requires attention, and the action selected at a stage.
* `TauCeti.LowSimple.stage`: the finite stages `A_s`.
* `TauCeti.LowSimple.restraint`: the restraint `r(e, s)` of `N_e`, always active.
* `TauCeti.LowSimple.enumeratedBy`: the numbers enumerated by `P_i`.
* `TauCeti.lowSimpleSet`: the constructed set, the limit of the stages.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Theorem VII.1.1.
-/

public section

open Filter TauCeti.Enumeration TauCeti.Priority

namespace TauCeti

namespace LowSimple

/-- The **diagonal stage computation** `Φ_{e,s}^D(e)`: the run of the oracle program numbered `e`
on the input `e` with fuel `s`, against the finite set `D` answering `1` on `D` and `0` outside
it. A run with fuel `s` only succeeds on inputs below `s`, so it fails for `e ≥ s`, and its use is
at most `s`. -/
def diagRun (D : Finset ℕ) (s e : ℕ) : Option Oracle.Single.Code.Halt :=
  Oracle.Single.Code.evaln (fun z => some (if z ∈ D then 1 else 0)) s
    (Denumerable.ofNat Oracle.Single.Code e) e

/-- Unfolding `diagRun`. -/
theorem diagRun_def (D : Finset ℕ) (s e : ℕ) :
    diagRun D s e = Oracle.Single.Code.evaln (fun z => some (if z ∈ D then 1 else 0)) s
      (Denumerable.ofNat Oracle.Single.Code e) e :=
  (rfl)

/-- The use of the diagonal stage computation `Φ_{e,s}^D(e)`, or `0` when it fails. -/
def diagUse (D : Finset ℕ) (s e : ℕ) : ℕ :=
  ((diagRun D s e).map Oracle.Single.Code.Halt.use).getD 0

/-- The use of a convergent diagonal stage computation is the use of its run. -/
theorem diagUse_eq_of_diagRun_eq_some {D : Finset ℕ} {s e : ℕ} {d : Oracle.Single.Code.Halt}
    (h : diagRun D s e = some d) : diagUse D s e = d.use := by
  simp [diagUse, h]

/-- The use of a failed diagonal stage computation is `0`. -/
theorem diagUse_eq_zero_of_diagRun_eq_none {D : Finset ℕ} {s e : ℕ} (h : diagRun D s e = none) :
    diagUse D s e = 0 := by
  simp [diagUse, h]

/-- The positive requirement `P_i` **requires attention** at stage `s` with the witness `x`, when
the current finite set is `D`: the stage `W_{i,s}` of the domain of the code
`Denumerable.ofNat Nat.Partrec.Code i` is disjoint from `D`, and `x` is an element of `W_{i,s}`
with `2 * i < x` and `diagUse D s e < x` for every `e ≤ i`. -/
structure RequiresAttention (D : Finset ℕ) (s i x : ℕ) : Prop where
  /-- The stage `W_{i,s}` is disjoint from the current set. -/
  disjoint : Disjoint ((Denumerable.ofNat Nat.Partrec.Code i).domStage s) D
  /-- The witness lies in the stage `W_{i,s}`. -/
  mem_domStage : x ∈ (Denumerable.ofNat Nat.Partrec.Code i).domStage s
  /-- The witness exceeds `2 * i`. -/
  two_mul_lt : 2 * i < x
  /-- The witness exceeds the use of every diagonal stage computation of priority at most `i`. -/
  diagUse_lt : ∀ e ≤ i, diagUse D s e < x

/-- Unfolding `RequiresAttention` into its four clauses. -/
theorem requiresAttention_iff {D : Finset ℕ} {s i x : ℕ} :
    RequiresAttention D s i x ↔
      Disjoint ((Denumerable.ofNat Nat.Partrec.Code i).domStage s) D ∧
        x ∈ (Denumerable.ofNat Nat.Partrec.Code i).domStage s ∧ 2 * i < x ∧
          ∀ e ≤ i, diagUse D s e < x :=
  ⟨fun h => ⟨h.disjoint, h.mem_domStage, h.two_mul_lt, h.diagUse_lt⟩,
    fun ⟨h₁, h₂, h₃, h₄⟩ => ⟨h₁, h₂, h₃, h₄⟩⟩

instance (D : Finset ℕ) (s i x : ℕ) : Decidable (RequiresAttention D s i x) :=
  decidable_of_iff' _ requiresAttention_iff

/-- A witness lies below the stage, since `W_{i,s}` only contains numbers below `s`. -/
theorem RequiresAttention.lt {D : Finset ℕ} {s i x : ℕ} (h : RequiresAttention D s i x) : x < s :=
  Finset.mem_range.1 (Nat.Partrec.Code.domStage_subset_range _ _ h.mem_domStage)

/-- The **action** at stage `s` when the current set is `D`: the least `i` such that `P_i`
requires attention, together with its least witness, or `none` when no positive requirement
requires attention. Both searches are bounded by `s`, since witnesses lie below `s` and exceed
`2 * i`. -/
def attention (D : Finset ℕ) (s : ℕ) : Option (ℕ × ℕ) :=
  ((List.range s).find? fun i => decide (∃ x < s, RequiresAttention D s i x)).bind fun i =>
    ((List.range s).find? fun x => decide (RequiresAttention D s i x)).map (i, ·)

/-- The action at a stage is the least requirement requiring attention, with its least
witness. -/
theorem attention_eq_some_iff {D : Finset ℕ} {s i x : ℕ} :
    attention D s = some (i, x) ↔ RequiresAttention D s i x ∧
      (∀ j < i, ∀ y, ¬RequiresAttention D s j y) ∧ ∀ y < x, ¬RequiresAttention D s i y := by
  simp only [attention, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq,
    List.find?_range_eq_some, List.mem_range, decide_eq_true_eq, Bool.not_eq_eq_eq_not,
    Bool.not_true, decide_eq_false_iff_not, not_exists, not_and]
  constructor
  · rintro ⟨i, ⟨-, -, hmin⟩, x, ⟨hx, -, hxmin⟩, rfl, rfl⟩
    exact ⟨hx, fun j hj y hy => hmin j hj y hy.lt hy, hxmin⟩
  · rintro ⟨hx, hmin, hxmin⟩
    have hxs := hx.lt
    have hix := hx.two_mul_lt
    exact ⟨i, ⟨⟨x, hxs, hx⟩, by omega, fun j hj y _ => hmin j hj y⟩, x, ⟨hx, hxs, hxmin⟩,
      rfl, rfl⟩

/-- No action is selected exactly when no positive requirement requires attention. -/
theorem attention_eq_none_iff {D : Finset ℕ} {s : ℕ} :
    attention D s = none ↔ ∀ i x, ¬RequiresAttention D s i x := by
  refine ⟨fun h i x hx => ?_, fun h => ?_⟩
  · -- some requirement requires attention, so the search for the least one succeeds
    have hi : ((List.range s).find? fun i => decide (∃ x < s, RequiresAttention D s i x)).isSome :=
      List.find?_isSome.2 ⟨i, List.mem_range.2 (by have := hx.lt; have := hx.two_mul_lt; omega),
        decide_eq_true ⟨x, hx.lt, hx⟩⟩
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.1 hi
    obtain ⟨⟨y, -, hy⟩, -⟩ := List.find?_range_eq_some.1 hj |>.imp_left of_decide_eq_true
    have hy' : ((List.range s).find? fun x => decide (RequiresAttention D s j x)).isSome :=
      List.find?_isSome.2 ⟨y, List.mem_range.2 hy.lt, decide_eq_true hy⟩
    obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 hy'
    simp [attention, hj, hz] at h
  · rw [attention, Option.bind_eq_none_iff]
    intro i hi
    obtain ⟨⟨x, -, hx⟩, -⟩ := List.find?_range_eq_some.1 hi |>.imp_left of_decide_eq_true
    exact absurd hx (h i x)

/-- The **stages** `A_s` of the construction: `A_0 = ∅`, and `A_{s+1}` adds to `A_s` the witness
of the action at stage `s`, if any. -/
def stage : ℕ → Finset ℕ
  | 0 => ∅
  | s + 1 => (attention (stage s) s).elim (stage s) fun p => insert p.2 (stage s)

@[simp]
theorem stage_zero : stage 0 = ∅ := by
  rw [stage]

theorem stage_succ_of_attention_eq_none {s : ℕ} (h : attention (stage s) s = none) :
    stage (s + 1) = stage s := by
  rw [stage, h, Option.elim_none]

theorem stage_succ_of_attention_eq_some {s i x : ℕ} (h : attention (stage s) s = some (i, x)) :
    stage (s + 1) = insert x (stage s) := by
  rw [stage, h, Option.elim_some]

/-- The stages increase. -/
theorem monotone_stage : Monotone stage := by
  refine monotone_nat_of_le_succ fun s => ?_
  rcases h : attention (stage s) s with _ | ⟨i, x⟩
  · rw [stage_succ_of_attention_eq_none h]
  · rw [stage_succ_of_attention_eq_some h]
    exact Finset.subset_insert _ _

/-- **The fresh entries.** A number enters at stage `s + 1` exactly when it is the witness of the
action at stage `s`. In particular at most one number enters at each stage. -/
theorem mem_fresh_stage {s x : ℕ} :
    x ∈ fresh stage s ↔ ∃ i, attention (stage s) s = some (i, x) := by
  rw [mem_fresh]
  constructor
  · rintro ⟨hx, hxs⟩
    rcases h : attention (stage s) s with _ | ⟨i, y⟩
    · rw [stage_succ_of_attention_eq_none h] at hx
      exact absurd hx hxs
    · rw [stage_succ_of_attention_eq_some h, Finset.mem_insert] at hx
      exact ⟨i, by rw [hx.resolve_right hxs]⟩
  · rintro ⟨i, h⟩
    obtain ⟨hx, -⟩ := attention_eq_some_iff.1 h
    rw [stage_succ_of_attention_eq_some h]
    exact ⟨Finset.mem_insert_self _ _, Finset.disjoint_left.1 hx.disjoint hx.mem_domStage⟩

/-- The restraint `r(e, s)` of the negative requirement `N_e` at stage `s`: the use of the
diagonal stage computation `Φ_{e,s}^{A_s}(e)`, or `0` when it fails. It is always active, and
`some 0` still protects the number `0`. -/
def restraint (e s : ℕ) : Option ℕ :=
  some (diagUse (stage s) s e)

/-- The restraint of `N_e` at stage `s` is the use of `Φ_{e,s}^{A_s}(e)`. -/
@[simp]
theorem restraint_eq (e s : ℕ) : restraint e s = some (diagUse (stage s) s e) :=
  (rfl)

/-- The restraint `r(e, s)` is `b` exactly when `b` is the use of `Φ_{e,s}^{A_s}(e)`. -/
theorem restraint_eq_some_iff {e s b : ℕ} : restraint e s = some b ↔ diagUse (stage s) s e = b :=
  by rw [restraint_eq, Option.some.injEq]

/-- The numbers enumerated by the positive requirement `P_i`. -/
def enumeratedBy (i : ℕ) : Set ℕ :=
  {x | ∃ s, attention (stage s) s = some (i, x)}

/-- A number is enumerated by `P_i` exactly when it is the witness of an action of `P_i`. -/
@[simp]
theorem mem_enumeratedBy {i x : ℕ} :
    x ∈ enumeratedBy i ↔ ∃ s, attention (stage s) s = some (i, x) :=
  Iff.rfl

/-- An action at stage `s` is never repeated at a later stage by the same requirement, since its
witness keeps `W_i` from being disjoint from the later stages. -/
private theorem not_lt_of_attention_eq_some {s t i x y : ℕ}
    (hs : attention (stage s) s = some (i, x)) (ht : attention (stage t) t = some (i, y)) :
    ¬s < t := by
  intro hst
  have hxs := (attention_eq_some_iff.1 hs).1.mem_domStage
  have hxt : x ∈ stage t :=
    monotone_stage hst (stage_succ_of_attention_eq_some hs ▸ Finset.mem_insert_self _ _)
  exact Finset.disjoint_left.1 (attention_eq_some_iff.1 ht).1.disjoint
    (Nat.Partrec.Code.monotone_domStage _ hst.le hxs) hxt

/-- **Each positive requirement acts at most once.** -/
theorem eq_of_attention_eq_some {s t i x y : ℕ} (hs : attention (stage s) s = some (i, x))
    (ht : attention (stage t) t = some (i, y)) : s = t ∧ x = y := by
  obtain rfl : s = t := le_antisymm (not_lt.1 (not_lt_of_attention_eq_some ht hs))
    (not_lt.1 (not_lt_of_attention_eq_some hs ht))
  simp_all

/-- Each positive requirement enumerates at most one number. -/
theorem subsingleton_enumeratedBy (i : ℕ) : (enumeratedBy i).Subsingleton :=
  fun _ ⟨_, hs⟩ _ ⟨_, ht⟩ => (eq_of_attention_eq_some hs ht).2

/-- An entry of `P_i` exceeds `2 * i`. -/
theorem lt_of_mem_enumeratedBy {i x : ℕ} (hx : x ∈ enumeratedBy i) : 2 * i < x :=
  let ⟨_, hs⟩ := hx
  (attention_eq_some_iff.1 hs).1.two_mul_lt

end LowSimple

open LowSimple

/-- **Soare's low simple set**: the limit of the stages `LowSimple.stage`. It is simple
(`TauCeti.simple_lowSimpleSet`); its lowness is not proved in this file. -/
def lowSimpleSet : Set ℕ :=
  stageLimit stage

/-- The constructed set is the limit of the stages. -/
theorem lowSimpleSet_eq_stageLimit : lowSimpleSet = stageLimit stage :=
  (rfl)

/-- A number is in the constructed set exactly when it appears at some stage. -/
theorem mem_lowSimpleSet_iff_exists_stage {x : ℕ} : x ∈ lowSimpleSet ↔ ∃ s, x ∈ stage s := by
  rw [lowSimpleSet_eq_stageLimit, mem_stageLimit]

/-- Every element of the constructed set was enumerated by a positive requirement. -/
@[simp]
theorem mem_lowSimpleSet {x : ℕ} : x ∈ lowSimpleSet ↔ ∃ i, x ∈ enumeratedBy i := by
  constructor
  · intro hx
    obtain ⟨s, hs⟩ := exists_mem_fresh_of_mem_stageLimit hx (by simp)
    obtain ⟨i, h⟩ := mem_fresh_stage.1 hs
    exact ⟨i, s, h⟩
  · rintro ⟨i, s, h⟩
    exact mem_stageLimit_of_mem_fresh (mem_fresh_stage.2 ⟨i, h⟩)

/-! ### Effectivity -/

namespace LowSimple

open Primrec

/-- The diagonal stage computation `Φ_{e,s}^D(e)`, its output and use or its failure, is primitive
recursive in the binary code of `D`, the stage `s` and the index `e`. -/
theorem primrec_diagRun :
    Primrec fun q : ℕ × ℕ × ℕ => diagRun (Finset.equivBitIndices q.1) q.2.1 q.2.2 := by
  have hargs : Primrec fun q : ℕ × ℕ × ℕ =>
      (q.1, q.2.1, Denumerable.ofNat Oracle.Single.Code q.2.2, q.2.2) :=
    fst.pair ((fst.comp snd).pair (((Primrec.ofNat Oracle.Single.Code).comp (snd.comp snd)).pair
      (snd.comp snd)))
  exact (Oracle.Single.Code.primrec_evaln_equivBitIndices.comp hargs).of_eq fun q => by
    rw [diagRun]

/-- The use of the diagonal stage computation is primitive recursive in the binary code of the
finite set, the stage and the index. -/
theorem primrec_diagUse :
    Primrec fun q : ℕ × ℕ × ℕ => diagUse (Finset.equivBitIndices q.1) q.2.1 q.2.2 := by
  have huse : Primrec fun q : ℕ × ℕ × ℕ =>
      (diagRun (Finset.equivBitIndices q.1) q.2.1 q.2.2).map Oracle.Single.Code.Halt.use :=
    option_map primrec_diagRun (Oracle.Single.Code.Halt.primrec_use.comp snd).to₂
  exact option_getD.comp huse (const 0)

/-- Requiring attention is primitive recursive in the binary code of the current set, the stage,
the requirement and the witness. -/
private theorem primrecPred_requiresAttention :
    PrimrecPred fun q : ℕ × ℕ × ℕ × ℕ =>
      RequiresAttention (Finset.equivBitIndices q.1) q.2.1 q.2.2.1 q.2.2.2 := by
  -- disjointness, as a zero binary intersection
  have hdisj : PrimrecPred fun q : ℕ × ℕ × ℕ × ℕ =>
      Finset.equivBitIndices.symm
        ((Denumerable.ofNat Nat.Partrec.Code q.2.2.1).domStage q.2.1) &&& q.1 = 0 :=
    Primrec.eq.comp (nat_land.comp (Nat.Partrec.Code.primrec_domStage.comp
      (((Primrec.ofNat _).comp (fst.comp (snd.comp snd))).pair (fst.comp snd))) fst) (const 0)
  -- the bound on the diagonal uses
  have hg : Primrec fun a : ℕ × ℕ × ℕ × ℕ × ℕ => (a.2.1, a.2.2.1, a.1) :=
    (fst.comp snd).pair ((fst.comp (snd.comp snd)).pair fst)
  have hd := primrec_diagUse.comp hg
  have hU : PrimrecRel fun (e : ℕ) (q : ℕ × ℕ × ℕ × ℕ) =>
      diagUse (Finset.equivBitIndices q.1) q.2.1 e < q.2.2.2 :=
    nat_lt.comp hd (snd.comp (snd.comp (snd.comp snd)))
  have huse : PrimrecPred fun q : ℕ × ℕ × ℕ × ℕ => ∀ e < q.2.2.1 + 1,
      diagUse (Finset.equivBitIndices q.1) q.2.1 e < q.2.2.2 :=
    (hU.forall_mem_list.comp (list_range.comp (succ.comp (fst.comp (snd.comp snd))))
      Primrec.id).of_eq fun q => by simp
  have hmem : PrimrecPred fun q : ℕ × ℕ × ℕ × ℕ =>
      q.2.2.2 ∈ (Denumerable.ofNat Nat.Partrec.Code q.2.2.1).domStage q.2.1 :=
    Nat.Partrec.Code.primrecRel_mem_domStage_ofNat.comp
      ((fst.comp (snd.comp snd)).pair (fst.comp snd))
      (snd.comp (snd.comp snd))
  have hlt : PrimrecPred fun q : ℕ × ℕ × ℕ × ℕ => 2 * q.2.2.1 < q.2.2.2 :=
    nat_lt.comp (nat_mul.comp (const 2) (fst.comp (snd.comp snd))) (snd.comp (snd.comp snd))
  refine (hdisj.and (hmem.and (hlt.and huse))).of_eq fun q => ?_
  have hzero (m : ℕ) : m = 0 ↔ Finset.equivBitIndices m = ∅ := by
    rw [← Equiv.eq_symm_apply]
    simp
  rw [requiresAttention_iff, Finset.disjoint_iff_inter_eq_empty, hzero (_ &&& _),
    Finset.equivBitIndices_land, Equiv.apply_symm_apply]
  simp only [Nat.lt_succ_iff]

/-- The action is primitive recursive in the binary code of the current set and the stage. -/
private theorem primrec_attention :
    Primrec fun q : ℕ × ℕ => attention (Finset.equivBitIndices q.1) q.2 := by
  have hg : Primrec fun a : ℕ × (ℕ × ℕ) × ℕ => (a.2.1.1, a.2.1.2, a.2.2, a.1) :=
    (fst.comp (fst.comp snd)).pair ((snd.comp (fst.comp snd)).pair ((snd.comp snd).pair fst))
  have hR : PrimrecRel fun (x : ℕ) (q : (ℕ × ℕ) × ℕ) =>
      RequiresAttention (Finset.equivBitIndices q.1.1) q.1.2 q.2 x :=
    (primrecPred_requiresAttention.comp hg).of_eq fun _ => Iff.rfl
  have hex : PrimrecRel fun (q : ℕ × ℕ) (i : ℕ) =>
      ∃ x < q.2, RequiresAttention (Finset.equivBitIndices q.1) q.2 i x :=
    (hR.exists_mem_list.comp (list_range.comp (snd.comp fst)) Primrec.id).of_eq fun q => by
      simp
  have hR' : PrimrecRel fun (p : (ℕ × ℕ) × ℕ) (x : ℕ) =>
      RequiresAttention (Finset.equivBitIndices p.1.1) p.1.2 p.2 x :=
    hR.comp snd fst
  have hpair : Primrec₂ fun (p : (ℕ × ℕ) × ℕ) (x : ℕ) => (p.2, x) :=
    (snd.comp fst).pair snd
  exact option_bind (list_find? (list_range.comp snd) hex.decide)
    (option_map (list_find? (list_range.comp (snd.comp fst)) hR'.decide) hpair)

/-- The binary codes `∑ x ∈ A_s, 2 ^ x` of the stages are primitive recursive. -/
theorem primrec_stage : Primrec fun s => Finset.equivBitIndices.symm (stage s) := by
  have hstep : Primrec₂ fun (s m : ℕ) =>
      (attention (Finset.equivBitIndices m) s).elim m fun p => m ||| 2 ^ p.2 :=
    (option_casesOn (primrec_attention.comp (snd.pair fst)) snd
      (nat_lor.comp (snd.comp fst) (nat_pow.comp (const 2) (snd.comp snd))).to₂).of_eq
      fun p => by dsimp only; cases attention (Finset.equivBitIndices p.2) p.1 <;> rfl
  refine (nat_rec₁ 0 hstep).of_eq fun s => ?_
  induction s with
  | zero => simp
  | succ s ih =>
    simp only [ih, Equiv.apply_symm_apply]
    rcases h : attention (stage s) s with _ | ⟨i, x⟩
    · simp [stage_succ_of_attention_eq_none h]
    · simp only [Option.elim_some, stage_succ_of_attention_eq_some h,
        Finset.equivBitIndices_symm_insert]

end LowSimple

/-- The constructed set is c.e. -/
theorem rePred_mem_lowSimpleSet : REPred (· ∈ lowSimpleSet) :=
  rePred_iff_exists_stages.2 ⟨stage, monotone_stage, stage_zero, primrec_stage.to_comp, rfl⟩

/-! ### Coinfiniteness -/

/-- **The counting invariant.** The constructed set has at most `n` elements up to `2 * n`: such an
element is enumerated by some `P_i` with `i < n`, and each `P_i` enumerates at most one number. -/
theorem ncard_lowSimpleSet_inter_Iic_le (n : ℕ) : (lowSimpleSet ∩ Set.Iic (2 * n)).ncard ≤ n := by
  have hsub : lowSimpleSet ∩ Set.Iic (2 * n) ⊆ ⋃ i ∈ Finset.range n, enumeratedBy i := by
    rintro x ⟨hx, hxn⟩
    obtain ⟨i, hi⟩ := mem_lowSimpleSet.1 hx
    have := lt_of_mem_enumeratedBy hi
    simp only [Set.mem_Iic] at hxn
    exact Set.mem_iUnion₂.2 ⟨i, Finset.mem_range.2 (by omega), hi⟩
  simpa using (Set.finite_and_ncard_le_sum_of_subset_biUnion (b := fun _ => 1) hsub fun i _ =>
    ⟨(subsingleton_enumeratedBy i).finite,
      (Set.ncard_le_one (subsingleton_enumeratedBy i).finite).2 (subsingleton_enumeratedBy i)⟩).2

/-- The complement of the constructed set is infinite. -/
theorem infinite_compl_lowSimpleSet : lowSimpleSetᶜ.Infinite :=
  Set.infinite_compl_of_ncard_inter_Iic_le ncard_lowSimpleSet_inter_Iic_le

/-! ### Finite injury and preservation -/

namespace LowSimple

/-- **Injury attribution.** A number injuring `N_e`, one entering at stage `s + 1` at or below the
restraint `r(e, s)`, is the witness of an action of some `P_i` with `i < e`. -/
theorem exists_lt_of_mem_injuriesAt {e s x : ℕ} (hx : x ∈ injuriesAt stage restraint e s) :
    ∃ i < e, attention (stage s) s = some (i, x) := by
  obtain ⟨i, h⟩ := mem_fresh_stage.1 (injuriesAt_subset_fresh hx)
  refine ⟨i, ?_, h⟩
  obtain ⟨-, -, b, hb, hxb⟩ := mem_injuriesAt.1 hx
  obtain rfl : diagUse (stage s) s e = b := restraint_eq_some_iff.1 hb
  by_contra hie
  exact absurd hxb (not_le.2 ((attention_eq_some_iff.1 h).1.diagUse_lt e (not_lt.1 hie)))

/-- **Finite injury.** At most `e` numbers ever injure the negative requirement `N_e`. -/
theorem finite_injurySet_and_ncard_le (e : ℕ) :
    (injurySet stage restraint e).Finite ∧ (injurySet stage restraint e).ncard ≤ e :=
  finite_injurySet_and_ncard_le_of_subsingleton_causes enumeratedBy
    (fun i _ => subsingleton_enumeratedBy i) fun s _ hx =>
      let ⟨i, hi, h⟩ := exists_lt_of_mem_injuriesAt hx
      ⟨i, hi, s, h⟩

/-- **Preservation.** If `N_e` is not injured at stage `s + 1`, a convergent diagonal stage
computation `Φ_{e,s}^{A_s}(e)` is still convergent at stage `s + 1`, with the same output and
use. -/
theorem diagRun_succ_eq_some {e s : ℕ} {d : Oracle.Single.Code.Halt}
    (hd : diagRun (stage s) s e = some d) (hinj : injuriesAt stage restraint e s = ∅) :
    diagRun (stage (s + 1)) (s + 1) e = some d := by
  rw [diagRun_def] at hd ⊢
  refine Oracle.Single.Code.evaln_eq_some_of_eqOn
    (Oracle.Single.Code.evaln_mono s.le_succ hd) fun z hz => ?_
  -- a number below the use that entered would injure `N_e`
  have hzs : z ∈ stage (s + 1) ↔ z ∈ stage s := by
    refine ⟨fun hz' => by_contra fun hzs => ?_, fun hzs => monotone_stage s.le_succ hzs⟩
    have : z ∈ injuriesAt stage restraint e s := mem_injuriesAt.2
      ⟨hz', hzs, _, restraint_eq_some_iff.2 rfl, by
        rw [diagUse_eq_of_diagRun_eq_some ((diagRun_def _ _ _).trans hd)]
        exact (Set.mem_Iio.1 hz).le⟩
    simp [hinj] at this
  simp [hzs]

/-- **The diagonal stage computations stabilize.** For each `e`, the run `Φ_{e,s}^{A_s}(e)` is
eventually constant: either it eventually fails forever, or from some stage on it converges
with a fixed output and use. -/
theorem exists_eventually_diagRun_eq (e : ℕ) :
    ∃ o, ∀ᶠ s in atTop, diagRun (stage s) s e = o := by
  obtain ⟨s₀, hs₀⟩ := (finite_injurySet_iff_eventually_eq_empty monotone_stage).1
    (finite_injurySet_and_ncard_le e).1
  by_cases h : ∃ s ≥ s₀, (diagRun (stage s) s e).isSome
  · obtain ⟨s₁, hs₁, hsome⟩ := h
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 hsome
    refine ⟨some d, eventually_atTop.2 ⟨s₁, fun t ht => ?_⟩⟩
    induction t, ht using Nat.le_induction with
    | base => exact hd
    | succ t ht ih => exact diagRun_succ_eq_some ih (hs₀ t (hs₁.trans ht))
  · push Not at h
    exact ⟨none, eventually_atTop.2 ⟨s₀, fun s hs => Option.not_isSome_iff_eq_none.1 (h s hs)⟩⟩

/-- **The restraints stabilize.** For each `e`, the restraint `r(e, s)` is eventually constant. -/
theorem exists_eventually_restraint_eq (e : ℕ) :
    ∃ b, ∀ᶠ s in atTop, restraint e s = some b := by
  obtain ⟨o, ho⟩ := exists_eventually_diagRun_eq e
  exact ⟨(o.map Oracle.Single.Code.Halt.use).getD 0, ho.mono fun s hs => by
    simp [diagUse, hs]⟩

/-- Each positive requirement eventually stops acting. -/
private theorem eventually_attention_ne (i : ℕ) :
    ∀ᶠ s in atTop, ∀ y, attention (stage s) s ≠ some (i, y) := by
  by_cases h : ∃ s y, attention (stage s) s = some (i, y)
  · obtain ⟨s, y, hs⟩ := h
    exact eventually_atTop.2 ⟨s + 1, fun t ht z htz => by
      have := (eq_of_attention_eq_some hs htz).1
      omega⟩
  · push Not at h
    exact Eventually.of_forall h

end LowSimple

/-! ### Simplicity -/

/-- **The positive requirements are met**: the constructed set meets the domain of every code
whose domain is infinite. -/
theorem inter_lowSimpleSet_nonempty {c : Nat.Partrec.Code} (hc : {x | (c.eval x).Dom}.Infinite) :
    ({x | (c.eval x).Dom} ∩ lowSimpleSet).Nonempty := by
  by_contra hdisj
  rw [Set.not_nonempty_iff_eq_empty, ← Set.disjoint_iff_inter_eq_empty] at hdisj
  set i := Encodable.encode c
  have hci : Denumerable.ofNat Nat.Partrec.Code i = c := Denumerable.ofNat_encode c
  -- the restraints of `N_0, …, N_i` settle, with eventual values bounded by `R`
  choose b hb using exists_eventually_restraint_eq
  set R := (Finset.range (i + 1)).sup b
  have hR : ∀ᶠ s in atTop, ∀ e ∈ Finset.range (i + 1), restraint e s = some (b e) :=
    (eventually_all_finset _).2 fun e _ => hb e
  -- the requirements `P_0, …, P_{i-1}` stop acting
  have hP : ∀ᶠ s in atTop, ∀ j ∈ Finset.range i, ∀ y, attention (stage s) s ≠ some (j, y) :=
    (eventually_all_finset _).2 fun j _ => eventually_attention_ne j
  -- a large enough element of the infinite set `W_i` appears in its stages
  obtain ⟨x, hxW, hx⟩ := hc.exists_gt (max (2 * i) R)
  have hxW' : ∀ᶠ s in atTop, x ∈ c.domStage s := by
    have : x ∈ stageLimit c.domStage := by simpa using hxW
    obtain ⟨s₀, hs₀⟩ := (mem_stageLimit_iff_eventually c.monotone_domStage).1 this
    exact eventually_atTop.2 ⟨s₀, hs₀⟩
  obtain ⟨s, hRs, hPs, hxs⟩ := (hR.and (hP.and hxW')).exists
  -- at stage `s`, the requirement `P_i` requires attention with the witness `x`
  have hreq : RequiresAttention (stage s) s i x := by
    refine ⟨?_, hci ▸ hxs, lt_of_le_of_lt (le_max_left _ _) hx, fun e he => ?_⟩
    · rw [hci, Finset.disjoint_left]
      intro y hyW hys
      have hyW' : y ∈ stageLimit c.domStage := subset_stageLimit _ s hyW
      rw [Nat.Partrec.Code.stageLimit_domStage] at hyW'
      exact Set.disjoint_left.1 hdisj hyW' (subset_stageLimit _ s hys)
    · have hre := hRs e (Finset.mem_range.2 (Nat.lt_succ_of_le he))
      rw [restraint_eq_some_iff] at hre
      rw [hre]
      exact lt_of_le_of_lt ((Finset.le_sup (Finset.mem_range.2 (Nat.lt_succ_of_le he))).trans
        (le_max_right _ _)) hx
  -- the action at stage `s` is then by `P_i`, whose witness lies in `W_i ∩ A`
  obtain ⟨⟨j, y⟩, hjy⟩ := Option.ne_none_iff_exists'.1 fun h =>
    attention_eq_none_iff.1 h i x hreq
  obtain ⟨hy, hmin, -⟩ := attention_eq_some_iff.1 hjy
  obtain rfl : j = i := by
    rcases lt_trichotomy j i with hji | rfl | hij
    · exact absurd hjy (hPs j (Finset.mem_range.2 hji) y)
    · rfl
    · exact absurd hreq (hmin i hij x)
  have hyW : y ∈ {x | (c.eval x).Dom} := by
    rw [← Nat.Partrec.Code.stageLimit_domStage]
    exact subset_stageLimit _ s (hci ▸ hy.mem_domStage)
  exact Set.disjoint_left.1 hdisj hyW (mem_lowSimpleSet.2 ⟨i, s, hjy⟩)

/-- **The constructed set is simple.** -/
theorem simple_lowSimpleSet : lowSimpleSet.Simple :=
  Set.simple_iff_forall_code.2
    ⟨rePred_mem_lowSimpleSet, infinite_compl_lowSimpleSet, fun _ => inter_lowSimpleSet_nonempty⟩

end TauCeti
