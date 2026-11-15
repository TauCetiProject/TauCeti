/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Simple.Basic
public import TauCeti.Computability.Enumeration.Code
public import TauCeti.Computability.Priority.Injury.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
import TauCeti.Computability.Priority.Injury.Causes
import TauCeti.Computability.Primrec.Bitwise
import TauCeti.Computability.Primrec.List
import TauCeti.Data.Set.Card
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Finite

/-!
# Simple sets built under negative restraints

Soare's finite-injury constructions of a low simple set [S, VII.1.1] and of a simple set avoiding
the cone above a noncomputable c.e. set [S, VII.3.1] share their positive requirements and their
enumeration rule; they differ only in the restraints held by the negative requirements. This file
carries out that common construction for an arbitrary restraint function and proves the facts it
supports on its own.

The restraint is a function `R D s e`: the restraint of the negative requirement `N_e` at stage `s`
when the current finite set is `D`. The positive requirement `P_i` is: if `W_i` is infinite then
the constructed set meets `W_i`, where `W_i` is the domain of the code
`Denumerable.ofNat Nat.Partrec.Code i`, with stages `W_{i,s}` given by
`Nat.Partrec.Code.domStage`.

The stages `A_s = stage R s` start empty. At the transition to stage `s + 1`, the requirement `P_i`
**requires attention** with the witness `x` when `W_{i,s}` is still disjoint from `A_s`, and `x` is
an element of `W_{i,s}` with `x > 2i` and `x > R A_s s e` for every `e ≤ i`. The least `i` that
requires attention enumerates its least witness. So at most one number enters per stage, and the
entries of `P_i` never injure `N_e` for `e ≤ i`.

The main results, valid for every restraint function:

* each positive requirement acts at most once (`TauCeti.RestrainedSimple.eq_of_attention_eq_some`),
  so the entries below `2n` come from the requirements `P_i` with `i < n`, which gives the counting
  invariant `|A ∩ [0, 2n]| ≤ n` and coinfiniteness
  (`TauCeti.RestrainedSimple.infinite_compl_stageLimit_stage`);
* every injury to `N_e`, a number entering at or below the restraint `r(e, s)`, is caused by some
  `P_i` with `i < e`, so `N_e` is injured by at most `e` numbers
  (`TauCeti.RestrainedSimple.finite_injurySet_and_ncard_le`);
* when the restraints are primitive recursive in the binary code of the current set, so are the
  binary codes of the stages, and the constructed set is c.e.
  (`TauCeti.RestrainedSimple.rePred_mem_stageLimit_stage`);
* when every restraint is eventually bounded along the construction, every positive requirement is
  met (`TauCeti.RestrainedSimple.inter_stageLimit_stage_nonempty`); if the restraints are moreover
  primitive recursive as above, the constructed set is simple
  (`TauCeti.RestrainedSimple.simple_stageLimit_stage`).

Bounding the restraints is the task of the negative requirements, and uses the particular
restraint function: for the low simple set it follows from preservation of the diagonal
computations (`TauCeti.LowSimple.exists_eventually_diagRun_eq`).

## Main definitions

* `TauCeti.RestrainedSimple.RequiresAttention`, `TauCeti.RestrainedSimple.attention`: when a
  positive requirement requires attention, and the action selected at a stage.
* `TauCeti.RestrainedSimple.stage`: the finite stages `A_s`.
* `TauCeti.RestrainedSimple.restraint`: the restraint `r(e, s)` of `N_e`, always active.
* `TauCeti.RestrainedSimple.enumeratedBy`: the numbers enumerated by `P_i`.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Theorems VII.1.1 and
  VII.3.1.
-/

public section

open Filter TauCeti.Enumeration TauCeti.Priority

namespace TauCeti.RestrainedSimple

variable {R : Finset ℕ → ℕ → ℕ → ℕ}

/-- The positive requirement `P_i` **requires attention** at stage `s` with the witness `x`, when
the current finite set is `D` and the negative requirements hold the restraints `R D s e`: the
stage `W_{i,s}` of the domain of the code `Denumerable.ofNat Nat.Partrec.Code i` is disjoint from
`D`, and `x` is an element of `W_{i,s}` with `2 * i < x` and `R D s e < x` for every `e ≤ i`. -/
structure RequiresAttention (R : Finset ℕ → ℕ → ℕ → ℕ) (D : Finset ℕ) (s i x : ℕ) : Prop where
  /-- The stage `W_{i,s}` is disjoint from the current set. -/
  disjoint : Disjoint ((Denumerable.ofNat Nat.Partrec.Code i).domStage s) D
  /-- The witness lies in the stage `W_{i,s}`. -/
  mem_domStage : x ∈ (Denumerable.ofNat Nat.Partrec.Code i).domStage s
  /-- The witness exceeds `2 * i`. -/
  two_mul_lt : 2 * i < x
  /-- The witness exceeds the restraint of every negative requirement of priority at most `i`. -/
  restraint_lt : ∀ e ≤ i, R D s e < x

/-- Unfolding `RequiresAttention` into its four clauses. -/
theorem requiresAttention_iff {D : Finset ℕ} {s i x : ℕ} :
    RequiresAttention R D s i x ↔
      Disjoint ((Denumerable.ofNat Nat.Partrec.Code i).domStage s) D ∧
        x ∈ (Denumerable.ofNat Nat.Partrec.Code i).domStage s ∧ 2 * i < x ∧
          ∀ e ≤ i, R D s e < x :=
  ⟨fun h => ⟨h.disjoint, h.mem_domStage, h.two_mul_lt, h.restraint_lt⟩,
    fun ⟨h₁, h₂, h₃, h₄⟩ => ⟨h₁, h₂, h₃, h₄⟩⟩

instance (R : Finset ℕ → ℕ → ℕ → ℕ) (D : Finset ℕ) (s i x : ℕ) :
    Decidable (RequiresAttention R D s i x) :=
  decidable_of_iff' _ requiresAttention_iff

/-- A witness lies below the stage, since `W_{i,s}` only contains numbers below `s`. -/
theorem RequiresAttention.lt {D : Finset ℕ} {s i x : ℕ} (h : RequiresAttention R D s i x) :
    x < s :=
  Finset.mem_range.1 (Nat.Partrec.Code.domStage_subset_range _ _ h.mem_domStage)

/-- The **action** at stage `s` when the current set is `D`: the least `i` such that `P_i`
requires attention, together with its least witness, or `none` when no positive requirement
requires attention. Both searches are bounded by `s`, since witnesses lie below `s` and exceed
`2 * i`. -/
def attention (R : Finset ℕ → ℕ → ℕ → ℕ) (D : Finset ℕ) (s : ℕ) : Option (ℕ × ℕ) :=
  ((List.range s).find? fun i => decide (∃ x < s, RequiresAttention R D s i x)).bind fun i =>
    ((List.range s).find? fun x => decide (RequiresAttention R D s i x)).map (i, ·)

/-- The action at a stage is the least requirement requiring attention, with its least
witness. -/
theorem attention_eq_some_iff {D : Finset ℕ} {s i x : ℕ} :
    attention R D s = some (i, x) ↔ RequiresAttention R D s i x ∧
      (∀ j < i, ∀ y, ¬RequiresAttention R D s j y) ∧ ∀ y < x, ¬RequiresAttention R D s i y := by
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
    attention R D s = none ↔ ∀ i x, ¬RequiresAttention R D s i x := by
  refine ⟨fun h i x hx => ?_, fun h => ?_⟩
  · -- some requirement requires attention, so the search for the least one succeeds
    have hi :
        ((List.range s).find? fun i => decide (∃ x < s, RequiresAttention R D s i x)).isSome :=
      List.find?_isSome.2 ⟨i, List.mem_range.2 (by have := hx.lt; have := hx.two_mul_lt; omega),
        decide_eq_true ⟨x, hx.lt, hx⟩⟩
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.1 hi
    obtain ⟨⟨y, -, hy⟩, -⟩ := List.find?_range_eq_some.1 hj |>.imp_left of_decide_eq_true
    have hy' : ((List.range s).find? fun x => decide (RequiresAttention R D s j x)).isSome :=
      List.find?_isSome.2 ⟨y, List.mem_range.2 hy.lt, decide_eq_true hy⟩
    obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 hy'
    simp [attention, hj, hz] at h
  · rw [attention, Option.bind_eq_none_iff]
    intro i hi
    obtain ⟨⟨x, -, hx⟩, -⟩ := List.find?_range_eq_some.1 hi |>.imp_left of_decide_eq_true
    exact absurd hx (h i x)

/-- The **stages** `A_s` of the construction: `A_0 = ∅`, and `A_{s+1}` adds to `A_s` the witness
of the action at stage `s`, if any. -/
def stage (R : Finset ℕ → ℕ → ℕ → ℕ) : ℕ → Finset ℕ
  | 0 => ∅
  | s + 1 => (attention R (stage R s) s).elim (stage R s) fun p => insert p.2 (stage R s)

@[simp]
theorem stage_zero : stage R 0 = ∅ := by
  rw [stage]

theorem stage_succ_of_attention_eq_none {s : ℕ} (h : attention R (stage R s) s = none) :
    stage R (s + 1) = stage R s := by
  rw [stage, h, Option.elim_none]

theorem stage_succ_of_attention_eq_some {s i x : ℕ}
    (h : attention R (stage R s) s = some (i, x)) : stage R (s + 1) = insert x (stage R s) := by
  rw [stage, h, Option.elim_some]

/-- The stages increase. -/
theorem monotone_stage (R : Finset ℕ → ℕ → ℕ → ℕ) : Monotone (stage R) := by
  refine monotone_nat_of_le_succ fun s => ?_
  rcases h : attention R (stage R s) s with _ | ⟨i, x⟩
  · rw [stage_succ_of_attention_eq_none h]
  · rw [stage_succ_of_attention_eq_some h]
    exact Finset.subset_insert _ _

/-- **The fresh entries.** A number enters at stage `s + 1` exactly when it is the witness of the
action at stage `s`. In particular at most one number enters at each stage. -/
theorem mem_fresh_stage {s x : ℕ} :
    x ∈ fresh (stage R) s ↔ ∃ i, attention R (stage R s) s = some (i, x) := by
  rw [mem_fresh]
  constructor
  · rintro ⟨hx, hxs⟩
    rcases h : attention R (stage R s) s with _ | ⟨i, y⟩
    · rw [stage_succ_of_attention_eq_none h] at hx
      exact absurd hx hxs
    · rw [stage_succ_of_attention_eq_some h, Finset.mem_insert] at hx
      exact ⟨i, by rw [hx.resolve_right hxs]⟩
  · rintro ⟨i, h⟩
    obtain ⟨hx, -⟩ := attention_eq_some_iff.1 h
    rw [stage_succ_of_attention_eq_some h]
    exact ⟨Finset.mem_insert_self _ _, Finset.disjoint_left.1 hx.disjoint hx.mem_domStage⟩

/-- The restraint `r(e, s)` of the negative requirement `N_e` at stage `s`: the value
`R A_s s e` at the current stage. It is always active, and `some 0` still protects the
number `0`. -/
def restraint (R : Finset ℕ → ℕ → ℕ → ℕ) (e s : ℕ) : Option ℕ :=
  some (R (stage R s) s e)

/-- The restraint of `N_e` at stage `s` is the value of the restraint function at the current
stage. -/
@[simp]
theorem restraint_eq (e s : ℕ) : restraint R e s = some (R (stage R s) s e) :=
  (rfl)

/-- The restraint `r(e, s)` is `b` exactly when `b` is the value of the restraint function at the
current stage. -/
theorem restraint_eq_some_iff {e s b : ℕ} : restraint R e s = some b ↔ R (stage R s) s e = b := by
  rw [restraint_eq, Option.some.injEq]

/-- The numbers enumerated by the positive requirement `P_i`. -/
def enumeratedBy (R : Finset ℕ → ℕ → ℕ → ℕ) (i : ℕ) : Set ℕ :=
  {x | ∃ s, attention R (stage R s) s = some (i, x)}

/-- A number is enumerated by `P_i` exactly when it is the witness of an action of `P_i`. -/
@[simp]
theorem mem_enumeratedBy {i x : ℕ} :
    x ∈ enumeratedBy R i ↔ ∃ s, attention R (stage R s) s = some (i, x) :=
  Iff.rfl

/-- An action at stage `s` is never repeated at a later stage by the same requirement, since its
witness keeps `W_i` from being disjoint from the later stages. -/
private theorem not_lt_of_attention_eq_some {s t i x y : ℕ}
    (hs : attention R (stage R s) s = some (i, x))
    (ht : attention R (stage R t) t = some (i, y)) : ¬s < t := by
  intro hst
  have hxs := (attention_eq_some_iff.1 hs).1.mem_domStage
  have hxt : x ∈ stage R t :=
    monotone_stage R hst (stage_succ_of_attention_eq_some hs ▸ Finset.mem_insert_self _ _)
  exact Finset.disjoint_left.1 (attention_eq_some_iff.1 ht).1.disjoint
    (Nat.Partrec.Code.monotone_domStage _ hst.le hxs) hxt

/-- **Each positive requirement acts at most once.** -/
theorem eq_of_attention_eq_some {s t i x y : ℕ} (hs : attention R (stage R s) s = some (i, x))
    (ht : attention R (stage R t) t = some (i, y)) : s = t ∧ x = y := by
  obtain rfl : s = t := le_antisymm (not_lt.1 (not_lt_of_attention_eq_some ht hs))
    (not_lt.1 (not_lt_of_attention_eq_some hs ht))
  simp_all

/-- Each positive requirement enumerates at most one number. -/
theorem subsingleton_enumeratedBy (i : ℕ) : (enumeratedBy R i).Subsingleton :=
  fun _ ⟨_, hs⟩ _ ⟨_, ht⟩ => (eq_of_attention_eq_some hs ht).2

/-- An entry of `P_i` exceeds `2 * i`. -/
theorem lt_of_mem_enumeratedBy {i x : ℕ} (hx : x ∈ enumeratedBy R i) : 2 * i < x :=
  let ⟨_, hs⟩ := hx
  (attention_eq_some_iff.1 hs).1.two_mul_lt

/-- Every element of the constructed set was enumerated by a positive requirement. -/
theorem mem_stageLimit_stage {x : ℕ} : x ∈ stageLimit (stage R) ↔ ∃ i, x ∈ enumeratedBy R i := by
  constructor
  · intro hx
    obtain ⟨s, hs⟩ := exists_mem_fresh_of_mem_stageLimit hx (by simp)
    obtain ⟨i, h⟩ := mem_fresh_stage.1 hs
    exact ⟨i, s, h⟩
  · rintro ⟨i, s, h⟩
    exact mem_stageLimit_of_mem_fresh (mem_fresh_stage.2 ⟨i, h⟩)

/-! ### Effectivity -/

section Effectivity

open Primrec

variable (hR : Primrec fun q : ℕ × ℕ × ℕ => R (Finset.equivBitIndices q.1) q.2.1 q.2.2)
include hR

/-- Requiring attention is primitive recursive in the binary code of the current set, the stage,
the requirement and the witness, when the restraints are. -/
private theorem primrecPred_requiresAttention :
    PrimrecPred fun q : ℕ × ℕ × ℕ × ℕ =>
      RequiresAttention R (Finset.equivBitIndices q.1) q.2.1 q.2.2.1 q.2.2.2 := by
  -- disjointness, as a zero binary intersection
  have hdisj : PrimrecPred fun q : ℕ × ℕ × ℕ × ℕ =>
      Finset.equivBitIndices.symm
        ((Denumerable.ofNat Nat.Partrec.Code q.2.2.1).domStage q.2.1) &&& q.1 = 0 :=
    Primrec.eq.comp (nat_land.comp (Nat.Partrec.Code.primrec_domStage.comp
      (((Primrec.ofNat _).comp (fst.comp (snd.comp snd))).pair (fst.comp snd))) fst) (const 0)
  -- the bound on the restraints
  have hg : Primrec fun a : ℕ × ℕ × ℕ × ℕ × ℕ => (a.2.1, a.2.2.1, a.1) :=
    (fst.comp snd).pair ((fst.comp (snd.comp snd)).pair fst)
  have hU : PrimrecRel fun (e : ℕ) (q : ℕ × ℕ × ℕ × ℕ) =>
      R (Finset.equivBitIndices q.1) q.2.1 e < q.2.2.2 :=
    nat_lt.comp (hR.comp hg) (snd.comp (snd.comp (snd.comp snd)))
  have huse : PrimrecPred fun q : ℕ × ℕ × ℕ × ℕ => ∀ e < q.2.2.1 + 1,
      R (Finset.equivBitIndices q.1) q.2.1 e < q.2.2.2 :=
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

/-- The action is primitive recursive in the binary code of the current set and the stage, when
the restraints are. -/
private theorem primrec_attention :
    Primrec fun q : ℕ × ℕ => attention R (Finset.equivBitIndices q.1) q.2 := by
  have hg : Primrec fun a : ℕ × (ℕ × ℕ) × ℕ => (a.2.1.1, a.2.1.2, a.2.2, a.1) :=
    (fst.comp (fst.comp snd)).pair ((snd.comp (fst.comp snd)).pair ((snd.comp snd).pair fst))
  have hR' : PrimrecRel fun (x : ℕ) (q : (ℕ × ℕ) × ℕ) =>
      RequiresAttention R (Finset.equivBitIndices q.1.1) q.1.2 q.2 x :=
    ((primrecPred_requiresAttention hR).comp hg).of_eq fun _ => Iff.rfl
  have hex : PrimrecRel fun (q : ℕ × ℕ) (i : ℕ) =>
      ∃ x < q.2, RequiresAttention R (Finset.equivBitIndices q.1) q.2 i x :=
    (hR'.exists_mem_list.comp (list_range.comp (snd.comp fst)) Primrec.id).of_eq fun q => by
      simp
  have hR'' : PrimrecRel fun (p : (ℕ × ℕ) × ℕ) (x : ℕ) =>
      RequiresAttention R (Finset.equivBitIndices p.1.1) p.1.2 p.2 x :=
    hR'.comp snd fst
  have hpair : Primrec₂ fun (p : (ℕ × ℕ) × ℕ) (x : ℕ) => (p.2, x) :=
    (snd.comp fst).pair snd
  exact option_bind (list_find? (list_range.comp snd) hex.decide)
    (option_map (list_find? (list_range.comp (snd.comp fst)) hR''.decide) hpair)

/-- The binary codes `∑ x ∈ A_s, 2 ^ x` of the stages are primitive recursive, when the restraints
are primitive recursive in the binary code of the current set, the stage and the index. -/
theorem primrec_stage : Primrec fun s => Finset.equivBitIndices.symm (stage R s) := by
  have hstep : Primrec₂ fun (s m : ℕ) =>
      (attention R (Finset.equivBitIndices m) s).elim m fun p => m ||| 2 ^ p.2 :=
    (option_casesOn ((primrec_attention hR).comp (snd.pair fst)) snd
      (nat_lor.comp (snd.comp fst) (nat_pow.comp (const 2) (snd.comp snd))).to₂).of_eq
      fun p => by dsimp only; cases attention R (Finset.equivBitIndices p.2) p.1 <;> rfl
  refine (nat_rec₁ 0 hstep).of_eq fun s => ?_
  induction s with
  | zero => simp
  | succ s ih =>
    simp only [ih, Equiv.apply_symm_apply]
    rcases h : attention R (stage R s) s with _ | ⟨i, x⟩
    · simp [stage_succ_of_attention_eq_none h]
    · simp only [Option.elim_some, stage_succ_of_attention_eq_some h,
        Finset.equivBitIndices_symm_insert]

/-- The constructed set is c.e. when the restraints are primitive recursive. -/
theorem rePred_mem_stageLimit_stage : REPred (· ∈ stageLimit (stage R)) :=
  rePred_iff_exists_stages.2
    ⟨stage R, monotone_stage R, stage_zero, (primrec_stage hR).to_comp, rfl⟩

end Effectivity

/-! ### Coinfiniteness -/

/-- **The counting invariant.** The constructed set has at most `n` elements up to `2 * n`: such an
element is enumerated by some `P_i` with `i < n`, and each `P_i` enumerates at most one number. -/
theorem ncard_stageLimit_stage_inter_Iic_le (n : ℕ) :
    (stageLimit (stage R) ∩ Set.Iic (2 * n)).ncard ≤ n := by
  have hsub : stageLimit (stage R) ∩ Set.Iic (2 * n) ⊆ ⋃ i ∈ Finset.range n, enumeratedBy R i := by
    rintro x ⟨hx, hxn⟩
    obtain ⟨i, hi⟩ := mem_stageLimit_stage.1 hx
    have := lt_of_mem_enumeratedBy hi
    simp only [Set.mem_Iic] at hxn
    exact Set.mem_iUnion₂.2 ⟨i, Finset.mem_range.2 (by omega), hi⟩
  simpa using (Set.finite_and_ncard_le_sum_of_subset_biUnion (b := fun _ => 1) hsub fun i _ =>
    ⟨(subsingleton_enumeratedBy i).finite,
      (Set.ncard_le_one (subsingleton_enumeratedBy i).finite).2 (subsingleton_enumeratedBy i)⟩).2

/-- The complement of the constructed set is infinite. -/
theorem infinite_compl_stageLimit_stage : (stageLimit (stage R))ᶜ.Infinite :=
  Set.infinite_compl_of_ncard_inter_Iic_le ncard_stageLimit_stage_inter_Iic_le

/-! ### Finite injury -/

/-- **Injury attribution.** A number injuring `N_e`, one entering at stage `s + 1` at or below the
restraint `r(e, s)`, is the witness of an action of some `P_i` with `i < e`. -/
theorem exists_lt_of_mem_injuriesAt {e s x : ℕ} (hx : x ∈ injuriesAt (stage R) (restraint R) e s) :
    ∃ i < e, attention R (stage R s) s = some (i, x) := by
  obtain ⟨i, h⟩ := mem_fresh_stage.1 (injuriesAt_subset_fresh hx)
  refine ⟨i, ?_, h⟩
  obtain ⟨-, -, b, hb, hxb⟩ := mem_injuriesAt.1 hx
  obtain rfl : R (stage R s) s e = b := restraint_eq_some_iff.1 hb
  by_contra hie
  exact absurd hxb (not_le.2 ((attention_eq_some_iff.1 h).1.restraint_lt e (not_lt.1 hie)))

/-- **Finite injury.** At most `e` numbers ever injure the negative requirement `N_e`. -/
theorem finite_injurySet_and_ncard_le (e : ℕ) :
    (injurySet (stage R) (restraint R) e).Finite ∧
      (injurySet (stage R) (restraint R) e).ncard ≤ e :=
  finite_injurySet_and_ncard_le_of_subsingleton_causes (enumeratedBy R)
    (fun i _ => subsingleton_enumeratedBy i) fun s _ hx =>
      let ⟨i, hi, h⟩ := exists_lt_of_mem_injuriesAt hx
      ⟨i, hi, s, h⟩

/-! ### Simplicity -/

/-- Each positive requirement eventually stops acting. -/
private theorem eventually_attention_ne (i : ℕ) :
    ∀ᶠ s in atTop, ∀ y, attention R (stage R s) s ≠ some (i, y) := by
  by_cases h : ∃ s y, attention R (stage R s) s = some (i, y)
  · obtain ⟨s, y, hs⟩ := h
    exact eventually_atTop.2 ⟨s + 1, fun t ht z htz => by
      have := (eq_of_attention_eq_some hs htz).1
      omega⟩
  · push Not at h
    exact Eventually.of_forall h

/-- **The positive requirements are met** once the restraints are bounded: if every restraint is
eventually bounded along the construction, the constructed set meets the domain of every code
whose domain is infinite. -/
theorem inter_stageLimit_stage_nonempty (hR : ∀ e, ∃ b, ∀ᶠ s in atTop, R (stage R s) s e ≤ b)
    {c : Nat.Partrec.Code} (hc : {x | (c.eval x).Dom}.Infinite) :
    ({x | (c.eval x).Dom} ∩ stageLimit (stage R)).Nonempty := by
  by_contra hdisj
  rw [Set.not_nonempty_iff_eq_empty, ← Set.disjoint_iff_inter_eq_empty] at hdisj
  set i := Encodable.encode c
  have hci : Denumerable.ofNat Nat.Partrec.Code i = c := Denumerable.ofNat_encode c
  -- the restraints of `N_0, …, N_i` are eventually bounded by `B`
  choose b hb using hR
  set B := (Finset.range (i + 1)).sup b
  have hB : ∀ᶠ s in atTop, ∀ e ∈ Finset.range (i + 1), R (stage R s) s e ≤ b e :=
    (eventually_all_finset _).2 fun e _ => hb e
  -- the requirements `P_0, …, P_{i-1}` stop acting
  have hP : ∀ᶠ s in atTop, ∀ j ∈ Finset.range i, ∀ y, attention R (stage R s) s ≠ some (j, y) :=
    (eventually_all_finset _).2 fun j _ => eventually_attention_ne j
  -- a large enough element of the infinite set `W_i` appears in its stages
  obtain ⟨x, hxW, hx⟩ := hc.exists_gt (max (2 * i) B)
  have hxW' : ∀ᶠ s in atTop, x ∈ c.domStage s := by
    have : x ∈ stageLimit c.domStage := by simpa using hxW
    obtain ⟨s₀, hs₀⟩ := (mem_stageLimit_iff_eventually c.monotone_domStage).1 this
    exact eventually_atTop.2 ⟨s₀, hs₀⟩
  obtain ⟨s, hBs, hPs, hxs⟩ := (hB.and (hP.and hxW')).exists
  -- at stage `s`, the requirement `P_i` requires attention with the witness `x`
  have hreq : RequiresAttention R (stage R s) s i x := by
    refine ⟨?_, hci ▸ hxs, lt_of_le_of_lt (le_max_left _ _) hx, fun e he => ?_⟩
    · rw [hci, Finset.disjoint_left]
      intro y hyW hys
      have hyW' : y ∈ stageLimit c.domStage := subset_stageLimit _ s hyW
      rw [Nat.Partrec.Code.stageLimit_domStage] at hyW'
      exact Set.disjoint_left.1 hdisj hyW' (subset_stageLimit _ s hys)
    · have he' := Finset.mem_range.2 (Nat.lt_succ_of_le he)
      exact lt_of_le_of_lt (((hBs e he').trans (Finset.le_sup he')).trans (le_max_right _ _)) hx
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
  exact Set.disjoint_left.1 hdisj hyW (mem_stageLimit_stage.2 ⟨i, s, hjy⟩)

/-- **The constructed set is simple** when the restraints are primitive recursive in the binary
code of the current set and every restraint is eventually bounded along the construction. -/
theorem simple_stageLimit_stage
    (hRp : Primrec fun q : ℕ × ℕ × ℕ => R (Finset.equivBitIndices q.1) q.2.1 q.2.2)
    (hR : ∀ e, ∃ b, ∀ᶠ s in atTop, R (stage R s) s e ≤ b) : (stageLimit (stage R)).Simple :=
  Set.simple_iff_forall_code.2 ⟨rePred_mem_stageLimit_stage hRp, infinite_compl_stageLimit_stage,
    fun _ => inter_stageLimit_stage_nonempty hR⟩

end TauCeti.RestrainedSimple
