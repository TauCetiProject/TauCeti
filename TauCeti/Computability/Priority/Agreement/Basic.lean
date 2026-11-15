/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SingleOracle.Agreement
public import TauCeti.Computability.Priority.Injury.Basic
public import TauCeti.Computability.Enumeration.Code
public import TauCeti.Computability.RE

/-!
# Preservation of agreement along a stage enumeration

In Sacks's constructions a set is enumerated in finite stages `A s`, and the requirement
`C ≠ Φ_e^A` holds a restraint at least the agreement restraint of `Φ_e` against the answers of
`A s` (`TauCeti.Oracle.Single.Code.setAnswers`) with fuel `s` and the target `C s`, Soare's
`r(e, s)`.
This file specializes the preservation theorems of
`TauCeti.Computability.SingleOracle.Agreement` to that setting: a transition that does not injure
the requirement keeps the answers at and below the restraint, hence the computations up to and
including the length of agreement, and the agreements where the target bit does not change.

It then proves the key step of Sacks's constructions, Soare's Lemma 1 in the proof of Theorem
VII.3.1: when the requirement is injured only finitely often, `Φ_e^A = C` forces `C` to be
computable. If `Φ_e^A` computes `C`, the length of agreement eventually exceeds every bound. After
the last injury, the computation at `x` is never lost while `C` does not change below `x`, so its
output is the value of `Φ_e^A` at `x`; by induction on `x`, the stage `C s` is then already correct
at `x`. Hence membership in `C` is decided by searching for a stage after the last injury whose
length of agreement exceeds the argument. In a construction, this turns noncomputability of `C`
into the inequality `C ≠ Φ_e^A`.

## Main results

* `TauCeti.Oracle.Single.Code.eqOn_setAnswers_of_injuriesAt_eq_empty`: without injury, the answers
  of `A s` and `A (s + 1)` agree at and below the restraint.
* `TauCeti.Oracle.Single.Code.evaln_succ_eq_some_of_injuriesAt_eq_empty`: **one-step preservation
  of computations**, with no hypothesis on the target.
* `TauCeti.Oracle.Single.Code.agreesAt_succ_of_injuriesAt_eq_empty`: **one-step preservation of
  agreement** where the target bit does not change.
* `TauCeti.Oracle.Single.Code.mem_stageLimit_iff_of_lt_agreementLength`: after the last injury,
  the stage `C s` is correct below the length of agreement at stage `s`.
* `TauCeti.Oracle.Single.Code.computablePred_mem_stageLimit_of_eval_eq`: **Soare's Lemma 1**, a
  finitely injured requirement with `Φ_e^A = C` makes `C` computable.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter VII.3, in
  particular the Remark on p. 122 and Lemma 1 in the proof of Theorem VII.3.1.
-/

public section

open Set TauCeti.Priority

namespace TauCeti.Oracle.Single.Code

variable {A C : ℕ → Finset ℕ} {r : ℕ → ℕ → Option ℕ} {e s b x : ℕ} {c : Code} {d : Halt}

/-- If nothing injures requirement `e`, with active restraint `b`, in the transition to stage
`s + 1`, and `A s ⊆ A (s + 1)`, then the oracle answers of `A s` and `A (s + 1)` agree at and
below `b`. -/
theorem eqOn_setAnswers_of_injuriesAt_eq_empty (hA : A s ⊆ A (s + 1)) (hr : r e s = some b)
    (hI : injuriesAt A r e s = ∅) :
    EqOn (setAnswers (A s)) (setAnswers (A (s + 1))) (Iic b) :=
  eqOn_setAnswers_iff.2 fun _ hz => mem_iff_mem_succ_of_injuriesAt_eq_empty hA hr hI hz

/-- **One-step preservation of computations.** Let requirement `e` hold, at stage `s`, a restraint
`b` at least the agreement restraint of `c` against the answers of `A s` with fuel `s` and the
target `C s`. If no number injures `e` in the transition to stage `s + 1`, and
`A s ⊆ A (s + 1)`, then every successful stage-`s` run at an argument up to and including the
length of agreement is a successful stage-`s + 1` run, with the same output and use. The target
`C` may change. -/
theorem evaln_succ_eq_some_of_injuriesAt_eq_empty (hA : A s ⊆ A (s + 1))
    (hr : r e s = some b)
    (hb : agreementRestraint (setAnswers (A s)) s c ((C s : Set ℕ).indicator 1) ≤ b)
    (hI : injuriesAt A r e s = ∅)
    (hx : x ≤ agreementLength (setAnswers (A s)) s c ((C s : Set ℕ).indicator 1))
    (hd : evaln (setAnswers (A s)) s c x = some d) :
    evaln (setAnswers (A (s + 1))) (s + 1) c x = some d :=
  evaln_eq_some_of_eqOn_agreementRestraint s.le_succ
    ((eqOn_setAnswers_of_injuriesAt_eq_empty hA hr hI).mono (Iic_subset_Iic.2 hb)) hx hd

/-- **One-step preservation of agreement.** Under the hypotheses of
`evaln_succ_eq_some_of_injuriesAt_eq_empty`, agreement at an argument below the length of agreement
persists to stage `s + 1` when membership of that argument in `C` does not change. -/
theorem agreesAt_succ_of_injuriesAt_eq_empty (hA : A s ⊆ A (s + 1))
    (hr : r e s = some b)
    (hb : agreementRestraint (setAnswers (A s)) s c ((C s : Set ℕ).indicator 1) ≤ b)
    (hI : injuriesAt A r e s = ∅)
    (hx : x < agreementLength (setAnswers (A s)) s c ((C s : Set ℕ).indicator 1))
    (hC : x ∈ C (s + 1) ↔ x ∈ C s) :
    AgreesAt (setAnswers (A (s + 1))) (s + 1) c ((C (s + 1) : Set ℕ).indicator 1) x :=
  agreesAt_of_eqOn_agreementRestraint s.le_succ
    ((eqOn_setAnswers_of_injuriesAt_eq_empty hA hr hI).mono (Iic_subset_Iic.2 hb)) hx
    (by simp [indicator_apply, hC])

/-! ### Soare's Lemma 1: a limiting reduction makes the target computable -/

section Limit

open Filter TauCeti.Enumeration

variable {s₀ : ℕ}

/-- **Soare's Lemma 1, correctness of late agreement.** Let the program `c`, relative to the limit
of monotone stages `A`, compute the characteristic function of the limit of monotone stages `C` at
every argument up to and including `x`. Suppose that from stage `s₀` on, requirement `e` holds a
restraint at least the agreement restraint of `c` against `A s` with target `C s` and fuel `s`, and
is never injured. Then at every stage `s ≥ s₀` at which `x` is below the length of agreement,
membership of `x` in `C` is already decided by `C s`. -/
theorem mem_stageLimit_iff_of_lt_agreementLength (hA : Monotone A) (hC : Monotone C)
    (hr : ∀ s, s₀ ≤ s → ∃ b, r e s = some b ∧
      agreementRestraint (setAnswers (A s)) s c ((C s : Set ℕ).indicator 1) ≤ b)
    (hI : ∀ s, s₀ ≤ s → injuriesAt A r e s = ∅)
    (heval : ∀ y ≤ x, eval (stageLimit A).oracle c y = (stageLimit C).oracle y) (hs : s₀ ≤ s)
    (hx : x < agreementLength (setAnswers (A s)) s c ((C s : Set ℕ).indicator 1)) :
    x ∈ stageLimit C ↔ x ∈ C s := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
  -- below `x` the target does not change after stage `s`, by the induction hypothesis
  have hCx : ∀ u, s ≤ u → ∀ y < x, (y ∈ C u ↔ y ∈ C s) := fun u hu y hy =>
    ⟨fun h => (ih y hy (fun z hz => heval z (hz.trans hy.le)) (hy.trans hx)).1
      (subset_stageLimit C u h), fun h => hC hu h⟩
  -- so the agreeing run at `x` persists at every later stage
  obtain ⟨d, hd, hdx⟩ := agreesAt_iff.1 (agreesAt_of_lt_agreementLength hx)
  have hpres : ∀ t, s ≤ t → evaln (setAnswers (A t)) t c x = some d := fun t hst => by
    refine evaln_eq_some_of_forall_Ico_of_le (σ := fun u => setAnswers (A u))
      (g := fun u => (C u : Set ℕ).indicator 1) hst
      (fun u hu => ⟨?_, fun y hy => ?_⟩) hx.le le_rfl hd
    · obtain ⟨b, hb, hbr⟩ := hr u (hs.trans hu.1)
      exact (eqOn_setAnswers_of_injuriesAt_eq_empty (hA u.le_succ) hb
        (hI u (hs.trans hu.1))).mono (Iic_subset_Iic.2 hbr)
    · simp [indicator_apply, hCx (u + 1) (hu.1.trans u.le_succ) y hy, hCx u hu.1 y hy]
  -- and its output is the value of `c` relative to the limit of `A`
  obtain ⟨t, ht⟩ := finite_prefix_stabilizes hA d.use
  have hmem := evaln_sound (O := (stageLimit A).oracle) (hpres (max s t) (le_max_left s t))
    fun z hz y hy => by
      rw [setAnswers_apply, Option.some.injEq] at hy
      rw [Set.oracle_apply, Part.mem_some_iff, ← hy]
      exact indicator_eq_indicator (ht (max s t) (le_max_right s t) z hz) rfl
  rw [heval x le_rfl, Set.oracle_apply, Part.mem_some_iff, hdx] at hmem
  by_cases hxC : x ∈ stageLimit C <;> by_cases hxs : x ∈ C s <;>
    simp [hxC, hxs] at hmem ⊢

/-- **Soare's Lemma 1.** Let `A` and `C` be the limits of monotone stages whose binary codes are
computable, and let requirement `e` hold, at every stage `s`, a restraint at least the agreement
restraint of the program `c` against `A s` with target `C s` and fuel `s`. If only finitely many
numbers injure `e`, and `c` relative to the limit of `A` computes the characteristic function of
the limit of `C`, then the limit of `C` is computable. -/
theorem computablePred_mem_stageLimit_of_eval_eq (hA : Monotone A) (hC : Monotone C)
    (hAc : Computable fun s => Finset.equivBitIndices.symm (A s))
    (hCc : Computable fun s => Finset.equivBitIndices.symm (C s))
    (hr : ∀ s, ∃ b, r e s = some b ∧
      agreementRestraint (setAnswers (A s)) s c ((C s : Set ℕ).indicator 1) ≤ b)
    (hI : (injurySet A r e).Finite)
    (heval : eval (stageLimit A).oracle c = (stageLimit C).oracle) :
    ComputablePred (· ∈ stageLimit C) := by
  obtain ⟨s₀, hs₀⟩ := (finite_injurySet_iff_eventually_eq_empty hA).1 hI
  have hmemC := computablePred_mem_of_computable_equivBitIndices hCc
  have hlen : Computable fun s =>
      agreementLength (setAnswers (A s)) s c ((C s : Set ℕ).indicator 1) :=
    (primrec_agreementLength_equivBitIndices.to_comp.comp
      ((hAc.pair hCc).pair (Computable.id.pair (Computable.const c)))).of_eq fun s => by simp
  -- a late enough agreement with the stage of `C` that omits the argument
  have hlate : ComputablePred fun q : ℕ × ℕ => s₀ ≤ q.2 ∧
      q.1 < agreementLength (setAnswers (A q.2)) q.2 c ((C q.2 : Set ℕ).indicator 1) ∧
        q.1 ∉ C q.2 := by
    have hle : ComputablePred fun q : ℕ × ℕ => s₀ ≤ q.2 :=
      PrimrecPred.computablePred (Primrec.nat_le.comp (Primrec.const s₀) Primrec.snd)
    have hlt : ComputablePred fun q : ℕ × ℕ =>
        q.1 < agreementLength (setAnswers (A q.2)) q.2 c ((C q.2 : Set ℕ).indicator 1) :=
      Computable.computablePred
        (Primrec.nat_lt.decide.to_comp.comp Computable.fst (hlen.comp Computable.snd))
    have hnot : ComputablePred fun q : ℕ × ℕ => q.1 ∉ C q.2 :=
      (ComputablePred.computable_of_manyOneReducible
        ⟨fun q : ℕ × ℕ => (q.2, q.1), Computable.snd.pair Computable.fst, fun _ => Iff.rfl⟩
        hmemC).not
    exact hle.and (hlt.and hnot)
  refine ComputablePred.computable_iff_re_compl_re'.2
    ⟨rePred_mem_stageLimit hmemC, (ComputablePred.rePred_exists (p := fun x s => s₀ ≤ s ∧
      x < agreementLength (setAnswers (A s)) s c ((C s : Set ℕ).indicator 1) ∧ x ∉ C s)
      hlate).of_eq
      fun x => ⟨fun ⟨s, hs, hx, hxs⟩ => ?_, fun hx => ?_⟩⟩
  · exact (mem_stageLimit_iff_of_lt_agreementLength hA hC (fun s _ => hr s)
      (fun s hs => hs₀ s hs) (fun y _ => congrFun heval y) hs hx).not.2 hxs
  · obtain ⟨s, hs, hxs⟩ := ((eventually_ge_atTop s₀).and
      (eventually_le_agreementLength_of_eval_eq hA hC (n := x + 1)
        fun y _ => congrFun heval y)).exists
    exact ⟨s, hs, hxs, fun h => hx (subset_stageLimit C s h)⟩

end Limit

end TauCeti.Oracle.Single.Code
