/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Priority.Agreement.Basic
public import TauCeti.Computability.SingleOracle.Limit
import Mathlib.Order.Filter.Finite

/-!
# Stabilization of the length of agreement and its restraint

Suppose a requirement protects the agreement restraint of a program against a target enumeration,
and only finitely many numbers injure it. If the program on the limit oracle does not compute the
target, the length of agreement eventually equals the first limiting disagreement, and the
agreement restraint is eventually constant. Neither quantity is assumed to be monotone.

The divergent case matters: a computation at the first disagreement can appear transiently on
finite approximations of the oracle. Once the smaller computations have settled and injuries have
stopped, the inclusive agreement restraint would preserve such a computation forever. Consequently
it would converge on the limit oracle as well.

The theorems use monotone finite-stage enumerations, without effectivity assumptions or an
effective bound on the last injury. They apply to the restraint stabilization steps of simple-set
cone avoidance and Sacks splitting.

## Main results

* `TauCeti.Oracle.Single.Code.exists_eventually_evaln_eq_of_le_agreementLength`: at any argument
  eventually covered by the agreement length, the stage run stabilizes with its output and use.
* `TauCeti.Oracle.Single.Code.eventually_agreementLength_eq_of_first_disagreement`: the length
  eventually equals a specified first limiting disagreement, including when that computation
  diverges.
* `TauCeti.Oracle.Single.Code.exists_eventually_agreementLength_eq_and_agreementRestraint_eq`:
  limiting disagreement implies stabilization of both the length and the restraint.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter VII.3,
  the restraint convergence arguments in the proofs of Theorems VII.3.1 and VII.3.2.
-/

public section

open Filter Set TauCeti.Enumeration TauCeti.Priority

namespace TauCeti.Oracle.Single.Code

variable {A C : ℕ → Finset ℕ} {r : ℕ → ℕ → Option ℕ} {e n : ℕ} {c : Code}

/-- With finite injury and an eventually live restraint covering the agreement restraint, the
stage run at an argument eventually below or at the length of agreement stabilizes, including
its use. The target stages need not be monotone for this conclusion. -/
theorem exists_eventually_evaln_eq_of_le_agreementLength (hA : Monotone A)
    (hr : ∀ᶠ s in atTop, ∃ b, r e s = some b ∧
      agreementRestraint (setAnswers (A s)) s c ((C s : Set ℕ).indicator 1) ≤ b)
    (hI : (injurySet A r e).Finite)
    (hn : ∀ᶠ s in atTop,
      n ≤ agreementLength (setAnswers (A s)) s c ((C s : Set ℕ).indicator 1)) :
    ∃ o, ∀ᶠ s in atTop, evaln (setAnswers (A s)) s c n = o := by
  obtain ⟨s₀, hs₀⟩ := (finite_injurySet_iff_eventually_eq_empty hA).1 hI
  obtain ⟨s₁, hs₁⟩ := eventually_atTop.1 (hn.and hr)
  by_cases h : ∃ s ≥ max s₀ s₁, (evaln (setAnswers (A s)) s c n).isSome
  · obtain ⟨s, hs, hsome⟩ := h
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 hsome
    refine ⟨some d, eventually_atTop.2 ⟨s, fun t ht => ?_⟩⟩
    induction t, ht using Nat.le_induction with
    | base => exact hd
    | succ t ht ih =>
      obtain ⟨b, hb, hcover⟩ := (hs₁ t (by omega)).2
      exact evaln_succ_eq_some_of_injuriesAt_eq_empty (hA t.le_succ) hb hcover
        (hs₀ t (by omega)) (hs₁ t (by omega)).1 ih
  · push Not at h
    exact ⟨none, eventually_atTop.2 ⟨max s₀ s₁, fun s hs =>
      Option.not_isSome_iff_eq_none.1 (h s hs)⟩⟩

/-- Under finite injury, the length of agreement eventually equals the first argument where the
limit program fails to return the target value. Failure includes divergence as well as a wrong
output. No stabilization of the restraint is assumed. -/
theorem eventually_agreementLength_eq_of_first_disagreement (hA : Monotone A) (hC : Monotone C)
    (hr : ∀ᶠ s in atTop, ∃ b, r e s = some b ∧
      agreementRestraint (setAnswers (A s)) s c ((C s : Set ℕ).indicator 1) ≤ b)
    (hI : (injurySet A r e).Finite)
    (hbelow : ∀ x < n, (stageLimit C).indicator 1 x ∈ eval (stageLimit A).oracle c x)
    (hne : (stageLimit C).indicator 1 n ∉ eval (stageLimit A).oracle c n) :
    ∀ᶠ s in atTop,
      agreementLength (setAnswers (A s)) s c ((C s : Set ℕ).indicator 1) = n := by
  -- True computations and the finitely many target bits below the first disagreement settle.
  have hlower : ∀ᶠ s in atTop,
      n ≤ agreementLength (setAnswers (A s)) s c ((C s : Set ℕ).indicator 1) := by
    have hprefix : ∀ x ∈ Finset.range n, ∀ᶠ s in atTop,
        AgreesAt (setAnswers (A s)) s c ((C s : Set ℕ).indicator 1) x := by
      intro x hx
      obtain ⟨d, hd, hrun⟩ := exists_eventually_evaln_setAnswers_eq_some_of_mem_eval hA
        tendsto_id (hbelow x (Finset.mem_range.1 hx))
      have htarget := Approximation.converges_iff_eventually.1
        (converges_indicator_stageLimit hC (1 : ℕ → ℕ)) x
      exact (hrun.and htarget).mono fun s hs =>
        agreesAt_iff.2 ⟨d, hs.1, hd.trans hs.2.symm⟩
    exact ((eventually_all_finset _).2 hprefix).mono fun s hs =>
      le_agreementLength_iff.2 fun x hx => hs x (Finset.mem_range.2 hx)
  -- The inclusive restraint protects a successful run even at the first disagreement.
  obtain ⟨o, ho⟩ := exists_eventually_evaln_eq_of_le_agreementLength hA hr hI hlower
  have hnot : ∀ᶠ s in atTop,
      ¬AgreesAt (setAnswers (A s)) s c ((C s : Set ℕ).indicator 1) n := by
    cases o with
    | none => exact ho.mono fun s hs => not_agreesAt_of_evaln_eq_none hs
    | some d =>
      have hd := mem_eval_of_eventually_evaln_eq_some (O := (stageLimit A).oracle) (by simp)
        (converges_setAnswers_stageLimit hA) ho
      have hout : d.output ≠ (stageLimit C).indicator 1 n := fun h => hne (h ▸ hd)
      have htarget := Approximation.converges_iff_eventually.1
        (converges_indicator_stageLimit hC (1 : ℕ → ℕ)) n
      exact (ho.and htarget).mono fun s hs => by
        rw [agreesAt_iff_of_evaln_eq_some hs.1, hs.2]
        exact hout
  exact (hlower.and hnot).mono fun s hs => le_antisymm
    (by by_contra h; exact hs.2 (agreesAt_of_lt_agreementLength (by omega))) hs.1

/-- Finite injury and disagreement on the limit oracle imply that both the length of agreement
and its inclusive maximum of uses are eventually constant. The restraint held by the requirement
may be larger than that maximum; no stabilization of that larger restraint is asserted. -/
theorem exists_eventually_agreementLength_eq_and_agreementRestraint_eq
    (hA : Monotone A) (hC : Monotone C)
    (hr : ∀ᶠ s in atTop, ∃ b, r e s = some b ∧
      agreementRestraint (setAnswers (A s)) s c ((C s : Set ℕ).indicator 1) ≤ b)
    (hI : (injurySet A r e).Finite)
    (hne : eval (stageLimit A).oracle c ≠ (stageLimit C).oracle) :
    ∃ n b, ∀ᶠ s in atTop,
      agreementLength (setAnswers (A s)) s c ((C s : Set ℕ).indicator 1) = n ∧
      agreementRestraint (setAnswers (A s)) s c ((C s : Set ℕ).indicator 1) = b := by
  classical
  have hdis : ∃ x, (stageLimit C).indicator 1 x ∉ eval (stageLimit A).oracle c x := by
    by_contra h
    push Not at h
    exact hne (funext fun x => (Part.eq_some_iff.2 (h x)).trans (oracle_apply _ _).symm)
  let n := Nat.find hdis
  have hlength := eventually_agreementLength_eq_of_first_disagreement hA hC hr hI
    (fun x hx => not_not.1 (Nat.find_min hdis hx)) (Nat.find_spec hdis)
  -- Each of the finitely many runs contributing to the eventual maximum stabilizes.
  have hruns (x : Fin (n + 1)) :
      ∃ o, ∀ᶠ s in atTop, evaln (setAnswers (A s)) s c x = o :=
    exists_eventually_evaln_eq_of_le_agreementLength hA hr hI
      (hlength.mono fun s hs => by rw [hs]; exact Nat.le_of_lt_succ x.isLt)
  choose o ho using hruns
  have hall : ∀ᶠ s in atTop, ∀ x : Fin (n + 1), evaln (setAnswers (A s)) s c x = o x :=
    (eventually_all).2 ho
  obtain ⟨s₀, hs₀⟩ := (hlength.and hall).exists
  refine ⟨n, agreementRestraint (setAnswers (A s₀)) s₀ c ((C s₀ : Set ℕ).indicator 1),
    (hlength.and hall).mono fun s hs => ⟨hs.1, ?_⟩⟩
  apply agreementRestraint_eq_of_evaln_eq (hs.1.trans hs₀.1.symm)
  intro x hx
  let i : Fin (n + 1) := ⟨x, by omega⟩
  exact (hs.2 i).trans (hs₀.2 i).symm

end TauCeti.Oracle.Single.Code
