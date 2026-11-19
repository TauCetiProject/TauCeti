/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SacksSplitting.Routing
public import TauCeti.Computability.Priority.Agreement.Stabilization
public import TauCeti.Computability.Enumeration.Domain
import Mathlib.Order.Filter.Finite

/-!
# Sacks splitting: the stage machine and non-reduction of both halves

Given finite stages `B s` and `C s`, this file builds Sacks's splitting of the limit of `B` into two
disjoint halves `A₀` and `A₁`, neither of which computes the limit of `C` when that limit is
noncomputable [S, VII.3.2]. The requirements are `N_(e,i) : C ≠ Φ_e^{A_i}`, ordered by
`k = 2 * e + i`: requirement `k` protects the half `k.bodd` and runs the oracle program numbered
`k.div2`.

At stage `s` requirement `k` holds Soare's restraint `r^i(e, s)`: the agreement restraint of its
program against the answers of the current half `A_{i,s}`, with fuel `s` and target the
characteristic function of `C s` (`TauCeti.SacksSplitting.agreementRestraint`). The restraints of
the requirements `k < 2 * s` are recorded in a list, and the transition to stage `s + 1` routes
every fresh element of the batch `B s` with `TauCeti.SacksSplitting.step`: to the side opposite the
least requirement it threatens, inclusively, and to side zero otherwise. The batch is arbitrary, so
no serialization of `B` is needed and empty or finite limits need no separate case.

The halves are disjoint at every stage and their union at stage `s` is the union of the batches
`B t` for `t < s`, so the limits split the limit of `B`, with no hypothesis on `B`. When the
binary codes of the stages of `B` and `C` are computable (respectively primitive recursive), so
are the codes of the stage pairs, and both halves are c.e.

The priority induction of [S, p.125] follows. Suppose `C` has monotone stages with computable
codes and a noncomputable limit. By strong induction on `k`:

* the higher-priority restraints are eventually bounded, so by the routing rule requirement `k` is
  injured only finitely often (`TauCeti.SacksSplitting.finite_injurySet`);
* Soare's Lemma 1 then gives `C ≠ Φ_e^{A_i}` (`TauCeti.SacksSplitting.eval_ne_oracle`);
* finite injury and the limiting disagreement make the length of agreement and the restraint of
  requirement `k` eventually constant
  (`TauCeti.SacksSplitting.exists_eventually_agreementLength_eq_and_agreementRestraint_eq`).

No computable bound on the number of injuries is used or claimed.

## Main definitions

* `TauCeti.SacksSplitting.agreementRestraint`: the restraint of requirement `k` at stage `s`.
* `TauCeti.SacksSplitting.stage`: the pair of finite halves at stage `s`.
* `TauCeti.SacksSplitting.splitHalf`: the limit of the half on side `b`.

## Main results

* `TauCeti.SacksSplitting.disjoint_splitHalf`,
  `TauCeti.SacksSplitting.splitHalf_false_union_splitHalf_true`: the halves split the limit of `B`.
* `TauCeti.SacksSplitting.rePred_mem_splitHalf`: both halves are c.e.
* `TauCeti.SacksSplitting.not_turingReducible_splitHalf`: neither half computes the limit of `C`.
* `TauCeti.SacksSplitting.exists_split_not_turingReducible`: **Sacks's splitting theorem without
  the lowness clause**. For c.e. sets `B` and `C` with `C` noncomputable, `B` is the disjoint union
  of two c.e. sets neither of which computes `C`.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Theorem VII.3.2 and its
  proof on pp. 124–126.
-/

public section

open Filter TauCeti.Enumeration TauCeti.Priority

namespace TauCeti.SacksSplitting

/-! ### Restraints -/

/-- The length of agreement `ℓ^i(e, s)` of requirement `k = 2 * e + i` at stage `s` when the
current halves are `A`: that of the oracle program numbered `k.div2` against the answers of the
half on side `k.bodd`, with fuel `s` and the characteristic function of `C s` as target. -/
noncomputable def agreementLength (C : ℕ → Finset ℕ) (A : Finset ℕ × Finset ℕ) (s k : ℕ) : ℕ :=
  Oracle.Single.Code.agreementLength
    (Oracle.Single.Code.setAnswers (bif k.bodd then A.2 else A.1)) s
    (Denumerable.ofNat Oracle.Single.Code k.div2) ((C s : Set ℕ).indicator 1)

/-- Unfolding `SacksSplitting.agreementLength`. -/
theorem agreementLength_def (C : ℕ → Finset ℕ) (A : Finset ℕ × Finset ℕ) (s k : ℕ) :
    agreementLength C A s k =
      Oracle.Single.Code.agreementLength
        (Oracle.Single.Code.setAnswers (bif k.bodd then A.2 else A.1)) s
        (Denumerable.ofNat Oracle.Single.Code k.div2) ((C s : Set ℕ).indicator 1) :=
  (rfl)

/-- The restraint `r^i(e, s)` of requirement `k = 2 * e + i` at stage `s` when the current halves
are `A`: the agreement restraint of the oracle program numbered `k.div2` against the answers of the
half on side `k.bodd`, with fuel `s` and the characteristic function of `C s` as target. -/
noncomputable def agreementRestraint (C : ℕ → Finset ℕ) (A : Finset ℕ × Finset ℕ) (s k : ℕ) : ℕ :=
  Oracle.Single.Code.agreementRestraint
    (Oracle.Single.Code.setAnswers (bif k.bodd then A.2 else A.1)) s
    (Denumerable.ofNat Oracle.Single.Code k.div2) ((C s : Set ℕ).indicator 1)

/-- Unfolding `SacksSplitting.agreementRestraint`. -/
theorem agreementRestraint_def (C : ℕ → Finset ℕ) (A : Finset ℕ × Finset ℕ) (s k : ℕ) :
    agreementRestraint C A s k =
      Oracle.Single.Code.agreementRestraint
        (Oracle.Single.Code.setAnswers (bif k.bodd then A.2 else A.1)) s
        (Denumerable.ofNat Oracle.Single.Code k.div2) ((C s : Set ℕ).indicator 1) :=
  (rfl)

/-- The list of the restraints of the requirements `k < 2 * s`, those with program index below `s`,
read by the routing transition at stage `s`. -/
noncomputable def restraints (C : ℕ → Finset ℕ) (A : Finset ℕ × Finset ℕ) (s : ℕ) : List ℕ :=
  (List.range (2 * s)).map (agreementRestraint C A s)

variable {B C : ℕ → Finset ℕ} {A : Finset ℕ × Finset ℕ} {s k : ℕ}

/-- A recorded restraint is the restraint of its requirement. -/
theorem getD_restraints_of_lt (h : k < 2 * s) :
    (restraints C A s)[k]?.getD 0 = agreementRestraint C A s k := by
  simp [restraints, h]

/-- The routing transition never reads a restraint larger than the actual one: an unrecorded
restraint is read as zero. -/
theorem getD_restraints_le : (restraints C A s)[k]?.getD 0 ≤ agreementRestraint C A s k := by
  by_cases h : k < 2 * s
  · exact (getD_restraints_of_lt h).le
  · simp [restraints, h]

/-! ### The stage machine -/

variable (B C) in
/-- **The stages of Sacks splitting.** Both halves start empty, and the transition to stage
`s + 1` routes the fresh elements of the batch `B s` against the restraints at stage `s`. -/
noncomputable def stage : ℕ → Finset ℕ × Finset ℕ
  | 0 => (∅, ∅)
  | s + 1 => step (restraints C (stage s) s) (stage s) (B s)

/-- Both halves start empty. -/
@[simp]
theorem stage_zero : stage B C 0 = (∅, ∅) := by
  rw [stage]

/-- The transition to stage `s + 1` routes the batch `B s` against the restraints at stage `s`. -/
theorem stage_succ (s : ℕ) :
    stage B C (s + 1) = step (restraints C (stage B C s) s) (stage B C s) (B s) := by
  rw [stage]

variable (B C) in
/-- The half on side `b` at stage `s`, Soare's `A_{i,s}`. -/
noncomputable def halfStage (b : Bool) (s : ℕ) : Finset ℕ :=
  bif b then (stage B C s).2 else (stage B C s).1

@[simp]
theorem halfStage_false (s : ℕ) : halfStage B C false s = (stage B C s).1 :=
  (rfl)

@[simp]
theorem halfStage_true (s : ℕ) : halfStage B C true s = (stage B C s).2 :=
  (rfl)

/-- The first half at stage `s + 1` is the first output of the routing transition. -/
theorem halfStage_false_succ (s : ℕ) :
    halfStage B C false (s + 1) = (step (restraints C (stage B C s) s) (stage B C s) (B s)).1 := by
  rw [halfStage_false, stage_succ]

/-- The second half at stage `s + 1` is the second output of the routing transition. -/
theorem halfStage_true_succ (s : ℕ) :
    halfStage B C true (s + 1) = (step (restraints C (stage B C s) s) (stage B C s) (B s)).2 := by
  rw [halfStage_true, stage_succ]

/-- The stage pair is the pair of its halves. -/
theorem halfStage_false_true (s : ℕ) :
    (halfStage B C false s, halfStage B C true s) = stage B C s := by
  simp

/-- The stages of the halves are related by the routing transition. -/
theorem step_halfStage (s : ℕ) :
    step (restraints C (stage B C s) s) (halfStage B C false s, halfStage B C true s) (B s) =
      (halfStage B C false (s + 1), halfStage B C true (s + 1)) := by
  rw [halfStage_false_true, halfStage_false_true, stage_succ]

/-- At stage `s` requirement `k` holds exactly the agreement restraint of its program against its
half. -/
theorem agreementRestraint_stage (s k : ℕ) :
    agreementRestraint C (stage B C s) s k =
      Oracle.Single.Code.agreementRestraint
        (Oracle.Single.Code.setAnswers (halfStage B C k.bodd s)) s
        (Denumerable.ofNat Oracle.Single.Code k.div2) ((C s : Set ℕ).indicator 1) := by
  rw [agreementRestraint_def]
  cases k.bodd <;> simp

/-- At stage `s` requirement `k` has exactly the length of agreement of its program against its
half. -/
theorem agreementLength_stage (s k : ℕ) :
    agreementLength C (stage B C s) s k =
      Oracle.Single.Code.agreementLength
        (Oracle.Single.Code.setAnswers (halfStage B C k.bodd s)) s
        (Denumerable.ofNat Oracle.Single.Code k.div2) ((C s : Set ℕ).indicator 1) := by
  rw [agreementLength_def]
  cases k.bodd <;> simp

variable (B C) in
/-- The halves never lose an entry. -/
theorem monotone_halfStage (b : Bool) : Monotone (halfStage B C b) := by
  refine monotone_nat_of_le_succ fun s => ?_
  cases b
  · rw [halfStage_false_succ, halfStage_false]
    exact subset_step_fst ..
  · rw [halfStage_true_succ, halfStage_true]
    exact subset_step_snd ..

variable (B C) in
/-- The halves are disjoint at every stage. -/
theorem disjoint_halfStage (s : ℕ) : Disjoint (halfStage B C false s) (halfStage B C true s) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [halfStage_false_succ, halfStage_true_succ]
    exact disjoint_step (by simpa using ih)

variable (B C) in
/-- The union of the halves at stage `s` is the union of the batches `B t` with `t < s`. -/
theorem halfStage_false_union_halfStage_true (s : ℕ) :
    halfStage B C false s ∪ halfStage B C true s = (Finset.range s).biUnion B := by
  induction s with
  | zero => simp
  | succ s ih =>
    simp only [halfStage_false, halfStage_true] at ih
    rw [halfStage_false_succ, halfStage_true_succ, step_union, ih, Finset.range_add_one,
      Finset.biUnion_insert, Finset.union_comm]

/-! ### The halves -/

variable (B C) in
/-- **The half on side `b` of Sacks's splitting** of the limit of `B`, protecting against
computations of the limit of `C`: the limit of the stages `halfStage B C b`. -/
noncomputable def splitHalf (b : Bool) : Set ℕ :=
  stageLimit (halfStage B C b)

theorem splitHalf_def (b : Bool) : splitHalf B C b = stageLimit (halfStage B C b) :=
  (rfl)

/-- A number is in the half on side `b` exactly when it enters that half at some stage. -/
@[simp]
theorem mem_splitHalf {b : Bool} {x : ℕ} : x ∈ splitHalf B C b ↔ ∃ s, x ∈ halfStage B C b s :=
  mem_stageLimit

variable (B C) in
/-- The two halves are disjoint. -/
theorem disjoint_splitHalf : Disjoint (splitHalf B C false) (splitHalf B C true) := by
  refine Set.disjoint_left.2 fun x hx₀ hx₁ => ?_
  obtain ⟨s, hs⟩ := mem_stageLimit.1 hx₀
  obtain ⟨t, ht⟩ := mem_stageLimit.1 hx₁
  exact Finset.disjoint_left.1 (disjoint_halfStage B C (max s t))
    (monotone_halfStage B C false (le_max_left s t) hs)
    (monotone_halfStage B C true (le_max_right s t) ht)

variable (B C) in
/-- The two halves together are exactly the limit of `B`. -/
theorem splitHalf_false_union_splitHalf_true :
    splitHalf B C false ∪ splitHalf B C true = stageLimit B := by
  ext x
  have hmem (s : ℕ) : x ∈ halfStage B C false s ∨ x ∈ halfStage B C true s ↔ ∃ t < s, x ∈ B t := by
    rw [← Finset.mem_union, halfStage_false_union_halfStage_true]
    simp
  simp only [Set.mem_union, splitHalf_def, mem_stageLimit, ← exists_or, hmem]
  exact ⟨fun ⟨_, t, _, ht⟩ => ⟨t, ht⟩, fun ⟨t, ht⟩ => ⟨t + 1, t, t.lt_succ_self, ht⟩⟩

/-! ### Effectivity -/

section Effectivity

open Primrec

/-- The list of recorded restraints at stage `s` reads `C` only through `C s`, and it is primitive
recursive in the stage, the binary codes of the halves, and the binary code of `C s`. -/
private theorem primrec_restraints_equivBitIndices :
    Primrec fun p : (ℕ × ℕ × ℕ) × ℕ =>
      restraints (fun _ => Finset.equivBitIndices p.2)
        (Finset.equivBitIndices p.1.2.1, Finset.equivBitIndices p.1.2.2) p.1.1 := by
  have hargs : Primrec₂ fun (p : (ℕ × ℕ × ℕ) × ℕ) (k : ℕ) =>
      (((bif k.bodd then p.1.2.2 else p.1.2.1), p.2),
        p.1.1, Denumerable.ofNat Oracle.Single.Code k.div2) :=
    ((Primrec.cond (nat_bodd.comp snd) (snd.comp (snd.comp (fst.comp fst)))
      (fst.comp (snd.comp (fst.comp fst)))).pair (snd.comp fst)).pair
      ((fst.comp (fst.comp fst)).pair ((Primrec.ofNat _).comp (nat_div2.comp snd)))
  refine (list_map (list_range.comp (nat_mul.comp (const 2) (fst.comp fst)))
    (Oracle.Single.Code.primrec_agreementRestraint_equivBitIndices.comp₂ hargs)).of_eq
    fun p => ?_
  simp only [restraints]
  refine List.map_congr_left fun k _ => ?_
  rw [agreementRestraint_def]
  cases k.bodd <;> simp

/-- The list of recorded restraints is primitive recursive in the stage and the binary codes of the
halves, when the binary codes of the stages of `C` are primitive recursive. -/
theorem primrec_restraints (hC : Primrec fun s => Finset.equivBitIndices.symm (C s)) :
    Primrec fun p : ℕ × ℕ × ℕ =>
      restraints C (Finset.equivBitIndices p.2.1, Finset.equivBitIndices p.2.2) p.1 :=
  (primrec_restraints_equivBitIndices.comp (Primrec.id.pair (hC.comp fst))).of_eq fun p => by
    simp only [Equiv.apply_symm_apply]
    rfl

/-- The list of recorded restraints is computable in the stage and the binary codes of the
halves, when the binary codes of the stages of `C` are computable. -/
theorem computable_restraints (hC : Computable fun s => Finset.equivBitIndices.symm (C s)) :
    Computable fun p : ℕ × ℕ × ℕ =>
      restraints C (Finset.equivBitIndices p.2.1, Finset.equivBitIndices p.2.2) p.1 :=
  (primrec_restraints_equivBitIndices.to_comp.comp
    (Computable.id.pair (hC.comp Computable.fst))).of_eq fun p => by
    simp only [Equiv.apply_symm_apply]
    rfl

section Primrec

variable (hB : Primrec fun s => Finset.equivBitIndices.symm (B s))
  (hC : Primrec fun s => Finset.equivBitIndices.symm (C s))
include hB hC

/-- The binary codes of the stage pairs are primitive recursive, when those of the stages of `B`
and `C` are. -/
theorem primrec_stage : Primrec fun s =>
    (Finset.equivBitIndices.symm (stage B C s).1, Finset.equivBitIndices.symm (stage B C s).2) := by
  have hf : Primrec₂ fun (s : ℕ) (m : ℕ × ℕ) =>
      let A := step (restraints C (Finset.equivBitIndices m.1, Finset.equivBitIndices m.2) s)
        (Finset.equivBitIndices m.1, Finset.equivBitIndices m.2) (B s)
      (Finset.equivBitIndices.symm A.1, Finset.equivBitIndices.symm A.2) :=
    (primrec_step.comp ((primrec_restraints hC).pair
      (snd.pair (hB.comp fst)))).of_eq fun p => by simp
  refine (nat_rec₁ (0, 0) hf).of_eq fun s => ?_
  induction s with
  | zero => simp
  | succ s ih =>
    simp only [ih, Equiv.apply_symm_apply, Prod.mk.eta, stage_succ]

/-- The binary codes of the stages of each half are primitive recursive. -/
theorem primrec_halfStage (b : Bool) :
    Primrec fun s => Finset.equivBitIndices.symm (halfStage B C b s) := by
  cases b
  · exact (fst.comp (primrec_stage hB hC)).of_eq fun s => by simp
  · exact (snd.comp (primrec_stage hB hC)).of_eq fun s => by simp

end Primrec

section Computable

variable (hB : Computable fun s => Finset.equivBitIndices.symm (B s))
  (hC : Computable fun s => Finset.equivBitIndices.symm (C s))
include hB hC

/-- The binary codes of the stage pairs are computable, when those of the stages of `B` and `C`
are. -/
theorem computable_stage : Computable fun s =>
    (Finset.equivBitIndices.symm (stage B C s).1, Finset.equivBitIndices.symm (stage B C s).2) := by
  have hf : Computable₂ fun (_ : ℕ) (q : ℕ × ℕ × ℕ) =>
      let A := step (restraints C (Finset.equivBitIndices q.2.1, Finset.equivBitIndices q.2.2) q.1)
        (Finset.equivBitIndices q.2.1, Finset.equivBitIndices q.2.2) (B q.1)
      (Finset.equivBitIndices.symm A.1, Finset.equivBitIndices.symm A.2) :=
    (primrec_step.to_comp.comp ((computable_restraints hC).comp Computable.snd |>.pair
      ((Computable.snd.comp Computable.snd).pair
        (hB.comp (Computable.fst.comp Computable.snd))))).of_eq fun p => by simp
  refine (Computable.nat_rec Computable.id (Computable.const (0, 0)) hf).of_eq fun s => ?_
  dsimp only [id]
  induction s with
  | zero => simp
  | succ s ih =>
    simp only [ih, Equiv.apply_symm_apply, Prod.mk.eta, stage_succ]

/-- The binary codes of the stages of each half are computable. -/
theorem computable_halfStage (b : Bool) :
    Computable fun s => Finset.equivBitIndices.symm (halfStage B C b s) := by
  cases b
  · exact (Computable.fst.comp (computable_stage hB hC)).of_eq fun s => by simp
  · exact (Computable.snd.comp (computable_stage hB hC)).of_eq fun s => by simp

/-- Both halves are c.e. when the binary codes of the stages of `B` and `C` are computable. -/
theorem rePred_mem_splitHalf (b : Bool) : REPred (· ∈ splitHalf B C b) :=
  rePred_mem_stageLimit (computablePred_mem_of_computable_equivBitIndices
    (computable_halfStage hB hC b))

end Computable

end Effectivity

/-! ### Finite injury -/

variable (B C) in
/-- The restraint of requirement `k` at stage `s`, as an always active restraint for the injury
API. It protects the numbers at and below `agreementRestraint C (stage B C s) s k`. -/
noncomputable def restraint (k s : ℕ) : Option ℕ :=
  some (agreementRestraint C (stage B C s) s k)

theorem restraint_def (k s : ℕ) :
    restraint B C k s = some (agreementRestraint C (stage B C s) s k) :=
  (rfl)

/-- **Finite injury from bounded higher-priority restraints.** If from some stage on the restraints
of all requirements `j < k` are at most `R`, then only finitely many numbers ever injure
requirement `k` in its half. No effectivity is assumed, and no bound on the number of injuries is
claimed. -/
theorem finite_injurySet_of_eventually_le {R : ℕ}
    (h : ∀ᶠ s in atTop, ∀ j < k, agreementRestraint C (stage B C s) s j ≤ R) :
    (injurySet (halfStage B C k.bodd) (restraint B C) k).Finite := by
  obtain ⟨s₀, hs₀⟩ := eventually_atTop.1 h
  have hlist := finite_injurySet_of_bounded_higher_priority (A := halfStage B C)
    (r := fun s => restraints C (stage B C s) s) (k := k) (s₀ := s₀) (R := R) step_halfStage
    fun s hs j hj => getD_restraints_le.trans (hs₀ s hs j hj)
  have hA := monotone_halfStage B C k.bodd
  obtain ⟨s₁, hs₁⟩ := (finite_injurySet_iff_eventually_eq_empty hA).1 hlist
  refine (finite_injurySet_iff_eventually_eq_empty hA).2 ⟨max s₁ (k + 1), fun s hs => ?_⟩
  have hr : restraint B C k s = some ((restraints C (stage B C s) s)[k]?.getD 0) := by
    rw [restraint_def, getD_restraints_of_lt (by omega)]
  rw [← hs₁ s (le_of_max_le_left hs)]
  ext x
  simp only [mem_injuriesAt, hr]

/-! ### The priority induction -/

/-- At every stage requirement `k` holds a restraint covering its agreement restraint. -/
private theorem exists_restraint_eq_some_and_le (s : ℕ) :
    ∃ b, restraint B C k s = some b ∧
      Oracle.Single.Code.agreementRestraint
        (Oracle.Single.Code.setAnswers (halfStage B C k.bodd s)) s
        (Denumerable.ofNat Oracle.Single.Code k.div2) ((C s : Set ℕ).indicator 1) ≤ b :=
  ⟨_, restraint_def k s, (agreementRestraint_stage s k).ge⟩

variable (hB : Computable fun s => Finset.equivBitIndices.symm (B s)) (hCm : Monotone C)
  (hC : Computable fun s => Finset.equivBitIndices.symm (C s))
  (hnc : ¬ComputablePred (· ∈ stageLimit C))
include hB hCm hC hnc

/-- A finitely injured requirement is met: by Soare's Lemma 1, a reduction of the noncomputable
limit of `C` to the half would make that limit computable. -/
private theorem eval_ne_oracle_of_finite_injurySet
    (hI : (injurySet (halfStage B C k.bodd) (restraint B C) k).Finite) :
    Oracle.Single.Code.eval (splitHalf B C k.bodd).oracle
      (Denumerable.ofNat Oracle.Single.Code k.div2) ≠ (stageLimit C).oracle := fun heval =>
  hnc <| Oracle.Single.Code.computablePred_mem_stageLimit_of_eval_eq
    (monotone_halfStage B C k.bodd) hCm (computable_halfStage hB hC k.bodd) hC
    (exists_restraint_eq_some_and_le (k := k)) hI heval

/-- The three statements of the priority induction for requirement `k`: finite injury, and
eventual constancy of the length of agreement and of the restraint. -/
private theorem finite_injurySet_and_exists_eventually_eq (k : ℕ) :
    (injurySet (halfStage B C k.bodd) (restraint B C) k).Finite ∧
      ∃ n b, ∀ᶠ s in atTop,
        agreementLength C (stage B C s) s k = n ∧ agreementRestraint C (stage B C s) s k = b := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  -- the higher-priority restraints are eventually bounded by the induction hypothesis
  have hI : (injurySet (halfStage B C k.bodd) (restraint B C) k).Finite := by
    have hlower : ∀ j < k, ∃ n b, ∀ᶠ s in atTop,
        agreementLength C (stage B C s) s j = n ∧ agreementRestraint C (stage B C s) s j = b :=
      fun j hj => (ih j hj).2
    choose! n b hb using hlower
    refine finite_injurySet_of_eventually_le (R := (Finset.range k).sup b) ?_
    filter_upwards [(eventually_all_finset (Finset.range k)).2 fun j hj =>
      hb j (Finset.mem_range.1 hj)] with s hs j hj
    exact (hs j (Finset.mem_range.2 hj)).2.le.trans (Finset.le_sup (Finset.mem_range.2 hj))
  -- finite injury and the limiting disagreement make both quantities settle
  refine ⟨hI, ?_⟩
  obtain ⟨n, b, hnb⟩ :=
    Oracle.Single.Code.exists_eventually_agreementLength_eq_and_agreementRestraint_eq
      (monotone_halfStage B C k.bodd) hCm
      (Eventually.of_forall (exists_restraint_eq_some_and_le (k := k))) hI
      (eval_ne_oracle_of_finite_injurySet hB hCm hC hnc hI)
  exact ⟨n, b, hnb.mono fun s hs => by rwa [agreementLength_stage, agreementRestraint_stage]⟩

/-- **Every requirement is injured only finitely often**, when `C` has monotone stages with
computable codes and a noncomputable limit, and the stages of `B` have computable codes. -/
theorem finite_injurySet (k : ℕ) : (injurySet (halfStage B C k.bodd) (restraint B C) k).Finite :=
  (finite_injurySet_and_exists_eventually_eq hB hCm hC hnc k).1

/-- **The length of agreement and the restraint of every requirement are eventually constant**,
under the hypotheses of `SacksSplitting.finite_injurySet`. -/
theorem exists_eventually_agreementLength_eq_and_agreementRestraint_eq (k : ℕ) :
    ∃ n b, ∀ᶠ s in atTop,
      agreementLength C (stage B C s) s k = n ∧ agreementRestraint C (stage B C s) s k = b :=
  (finite_injurySet_and_exists_eventually_eq hB hCm hC hnc k).2

/-- **Every requirement is met**: under the hypotheses of `SacksSplitting.finite_injurySet`, no
oracle program computes the limit of `C` relative to either half. -/
theorem eval_ne_oracle (e : ℕ) (b : Bool) :
    Oracle.Single.Code.eval (splitHalf B C b).oracle (Denumerable.ofNat Oracle.Single.Code e) ≠
      (stageLimit C).oracle := by
  have h := eval_ne_oracle_of_finite_injurySet hB hCm hC hnc
    (finite_injurySet hB hCm hC hnc (Nat.bit b e))
  rwa [Nat.bodd_bit, Nat.div2_bit] at h

/-- **Neither half computes the limit of `C`**, under the hypotheses of
`SacksSplitting.finite_injurySet`. -/
theorem not_turingReducible_splitHalf (b : Bool) :
    ¬TuringReducible (stageLimit C).oracle (splitHalf B C b).oracle := fun h => by
  obtain ⟨c, hc⟩ := Oracle.Single.Code.turingReducible_iff_exists_code.1 h
  exact eval_ne_oracle hB hCm hC hnc (Encodable.encode c) b (by rwa [Denumerable.ofNat_encode])

omit hB hCm hC hnc

/-! ### Main result -/

/-- **Sacks's splitting theorem without the lowness clause** [S, VII.3.2]: for c.e. sets `B` and `C`
with `C` noncomputable, `B` is the union of two disjoint c.e. sets neither of which computes `C`.
There is no infinitude hypothesis on `B`. -/
theorem exists_split_not_turingReducible {B C : Set ℕ} (hB : REPred (· ∈ B))
    (hC : REPred (· ∈ C)) (hnc : ¬ComputablePred (· ∈ C)) :
    ∃ A₀ A₁ : Set ℕ, REPred (· ∈ A₀) ∧ REPred (· ∈ A₁) ∧ Disjoint A₀ A₁ ∧ A₀ ∪ A₁ = B ∧
      ¬TuringReducible C.oracle A₀.oracle ∧ ¬TuringReducible C.oracle A₁.oracle := by
  obtain ⟨b, hb⟩ := rePred_iff_exists_code.1 hB
  obtain ⟨c, hc⟩ := rePred_iff_exists_code.1 hC
  have hBc : stageLimit b.domStage = B := by
    rw [Nat.Partrec.Code.stageLimit_domStage]
    exact Set.ext fun x => (hb x).symm
  have hCc : stageLimit c.domStage = C := by
    rw [Nat.Partrec.Code.stageLimit_domStage]
    exact Set.ext fun x => (hc x).symm
  have hBp : Computable fun s => Finset.equivBitIndices.symm (b.domStage s) :=
    (Nat.Partrec.Code.primrec_domStage.comp ((Primrec.const b).pair Primrec.id)).to_comp
  have hCp : Computable fun s => Finset.equivBitIndices.symm (c.domStage s) :=
    (Nat.Partrec.Code.primrec_domStage.comp ((Primrec.const c).pair Primrec.id)).to_comp
  rw [← hCc] at hnc ⊢
  rw [← hBc]
  exact ⟨_, _, rePred_mem_splitHalf hBp hCp false, rePred_mem_splitHalf hBp hCp true,
    disjoint_splitHalf _ _, splitHalf_false_union_splitHalf_true _ _,
    not_turingReducible_splitHalf hBp c.monotone_domStage hCp hnc false,
    not_turingReducible_splitHalf hBp c.monotone_domStage hCp hnc true⟩

end TauCeti.SacksSplitting
