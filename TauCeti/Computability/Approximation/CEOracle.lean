/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SingleOracle.Limit
public import TauCeti.Computability.Enumeration.Code
import TauCeti.Computability.Approximation.Limit
import TauCeti.Computability.SingleOracle.Relative

/-!
# The Modulus Lemma for c.e. oracles

A total function computable in a c.e. set has a computable approximation with a modulus
computable in that set. The approximation runs its oracle program for bounded time against
the current finite enumeration. The oracle can recognize a successful stage whose answers
below the recorded use are all correct. Monotonicity then protects that run at every later
stage, so the first such stage is a modulus.

The search checks only the prefix below the successful run's use, not the prefix below the
current stage: the latter prefix need never settle fast enough. The modulus is computed by
unbounded search using the oracle, not by choosing an unspecified stabilization stage.

## Main results

* `TauCeti.Approximation.exists_computable_isModulus_of_stages`: the presentation-level
  statement, for any increasing computable finite-stage enumeration.
* `TauCeti.Approximation.computableIn_iff_exists_isModulus_of_rePred`: the Modulus Lemma,
  including its converse, for total natural-valued functions.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987,
  Modulus Lemma III.3.2.
-/

public section

open Filter TauCeti.Enumeration TauCeti.Oracle.Single

namespace TauCeti.Approximation

variable {A : ℕ → Finset ℕ} {c : Code} {g : ℕ → ℕ}

/-- A successful stage is certified when its finite answers below its recorded use agree
with the limit oracle. This test is decidable relative to the limit oracle. -/
private noncomputable def certifiedStage (A : ℕ → Finset ℕ) (c : Code) (x s : ℕ) : Bool :=
  let run := Code.evaln (Code.setAnswers (A s)) s c x
  let u := Code.stageUse (Code.setAnswers (A s)) s c x
  run.isSome && decide ((List.range u).map ((A s : Set ℕ).indicator (1 : ℕ → ℕ)) =
    (List.range u).map ((stageLimit A).indicator (1 : ℕ → ℕ)))

private theorem certifiedStage_iff {x s : ℕ} : certifiedStage A c x s = true ↔
    ∃ d, Code.evaln (Code.setAnswers (A s)) s c x = some d ∧
      ∀ z < d.use, (A s : Set ℕ).indicator (1 : ℕ → ℕ) z =
        (stageLimit A).indicator (1 : ℕ → ℕ) z := by
  unfold certifiedStage
  cases h : Code.evaln (Code.setAnswers (A s)) s c x with
  | none => simp
  | some d => simp [Code.stageUse_eq_of_evaln_eq_some h, List.map_inj_left]

private theorem computableIn_certifiedStage
    (hA : Computable fun s => Finset.equivBitIndices.symm (A s)) :
    ComputableIn₂ {(stageLimit A).oracle} (certifiedStage A c) := by
  classical
  have hr := Computable.comp (Code.computable₂_evaln_setAnswers hA c)
    (Computable.snd.pair Computable.fst)
  have hu : Computable (fun p : ℕ × ℕ =>
      Code.stageUse (Code.setAnswers (A p.2)) p.2 c p.1) :=
    ((Code.primrec_stageUse Code.primrec₂_setAnswers_equivBitIndices).to_comp.comp
      ((hA.comp Computable.snd).pair
        (Computable.snd.pair ((Computable.const c).pair Computable.fst)))).of_eq
      fun p => by simp only [Finset.equivBitIndices.apply_symm_apply]
  have hbits : Computable₂ (fun s z => (A s : Set ℕ).indicator (1 : ℕ → ℕ) z) :=
    (Primrec.indicator_equivBitIndices.to_comp.comp (hA.comp Computable.fst)
      Computable.snd).of_eq fun p => by simp only [Finset.equivBitIndices.apply_symm_apply]
  have hb : ComputableIn₂ {(stageLimit A).oracle}
      (fun s z => (A s : Set ℕ).indicator (1 : ℕ → ℕ) z) := hbits.computableIn
  have hleft := (ComputableIn₂.list_range_map hb).comp
    (ComputableIn.snd.pair hu.computableIn)
  have ho : ComputableIn₂ {(stageLimit A).oracle}
      (fun (_ : ℕ) z => (stageLimit A).indicator (1 : ℕ → ℕ) z) :=
    (stageLimit A).computableIn_indicator.comp ComputableIn.snd
  have hright := ComputableIn₂.list_range_map ho
  have hright' := hright.comp ((ComputableIn.const 0).pair hu.computableIn)
  have heq := (Primrec.eq.decide.computableIn).comp (hleft.pair hright')
  have hsome := Primrec.option_isSome.to_comp.comp hr
  exact RecursiveIn.of_eq
    ((Primrec.cond Primrec.fst Primrec.snd (Primrec.const false)).computableIn.comp
      (hsome.computableIn.pair heq)) fun p => by
        simp only [certifiedStage]
        cases Code.evaln (Code.setAnswers (A p.2)) p.2 c p.1 <;> simp

private theorem exists_certifiedStage (hA : Monotone A)
    (hc : Code.eval (stageLimit A).oracle c = fun x => Part.some (g x)) (x : ℕ) :
    ∃ s, certifiedStage A c x s = true := by
  have hx : g x ∈ Code.eval (stageLimit A).oracle c x := by rw [hc]; simp
  obtain ⟨d, -, hrun⟩ := Code.exists_eventually_evaln_setAnswers_eq_some_of_mem_eval
    hA tendsto_id hx
  have hbits := (converges_indicator_stageLimit hA (1 : ℕ → ℕ)).eventually_forall_mem
    (Finset.range d.use)
  obtain ⟨s, hs, hb⟩ := (hrun.and hbits).exists
  exact ⟨s, certifiedStage_iff.2 ⟨d, hs, fun z hz => hb z (Finset.mem_range.2 hz)⟩⟩

private theorem evaln_eq_some_of_certifiedStage (hA : Monotone A)
    {x s t : ℕ} (hs : certifiedStage A c x s = true) (hst : s ≤ t) :
    ∃ d, Code.evaln (Code.setAnswers (A s)) s c x = some d ∧
      Code.evaln (Code.setAnswers (A t)) t c x = some d ∧
      d.output ∈ Code.eval (stageLimit A).oracle c x := by
  classical
  obtain ⟨d, hd, hbits⟩ := certifiedStage_iff.1 hs
  have hprefix : ∀ z < d.use, z ∈ A s ↔ z ∈ stageLimit A := by
    intro z hz
    have hb := hbits z hz
    by_cases hs : z ∈ A s <;> by_cases hl : z ∈ stageLimit A <;> simp_all
  have hrun := Code.evaln_eq_some_of_eqOn hd (Code.eqOn_setAnswers_iff.2 hprefix)
  refine ⟨d, hd, ?_, Code.evaln_sound hrun (by simp)⟩
  apply Code.evaln_mono hst
  apply Code.evaln_eq_some_of_eqOn hd
  apply Code.eqOn_setAnswers_iff.2
  intro z hz
  exact ⟨fun hz' => hA hst hz', fun hz' => (hprefix z hz).2 (subset_stageLimit A t hz')⟩

/-- **Modulus Lemma for a specified enumeration.** A total function computable in the limit of
increasing computable finite stages has a computable approximation with a modulus computable
in that limit set. The enumeration need not start empty or enumerate one element at a time. -/
theorem exists_computable_isModulus_of_stages (hA : Monotone A)
    (hAc : Computable fun s => Finset.equivBitIndices.symm (A s))
    (hg : ComputableIn {(stageLimit A).oracle} g) :
    ∃ (f : ℕ → ℕ → ℕ) (m : ℕ → ℕ), Computable₂ f ∧
      ComputableIn {(stageLimit A).oracle} m ∧ IsModulus f g m := by
  classical
  obtain ⟨c, hc⟩ := Code.exists_code.1 (RecursiveIn.iff_nat.1 hg)
  have hrun := Code.computable₂_evaln_setAnswers hAc c
  let f : ℕ → ℕ → ℕ := fun s x =>
    ((Code.evaln (Code.setAnswers (A s)) s c x).map Code.Halt.output).getD 0
  have hex := exists_certifiedStage hA hc
  let m : ℕ → ℕ := fun x => Nat.find (hex x)
  refine ⟨f, m, ?_, ?_, ?_⟩
  · exact (Primrec.option_getD.comp
      (Primrec.option_map Primrec.id (Code.Halt.primrec_output.comp Primrec.snd).to₂)
      (Primrec.const 0)).to_comp.comp hrun
  · -- The certificate is an oracle-decidable test; totality follows from visibility.
    have htest := computableIn_certifiedStage hAc (c := c)
    have hzero : ComputableIn₂ {(stageLimit A).oracle} (fun x s =>
        bif certifiedStage A c x s then 0 else 1) :=
      (Primrec.cond Primrec.id (Primrec.const 0) (Primrec.const 1)).computableIn.comp htest
    apply RecursiveIn.iff_nat.2
    refine (ComputableIn₂.iff_nat.1 hzero).rfind.of_eq_tot fun x => ?_
    apply Nat.mem_rfind.2
    constructor
    · simp [m, Nat.find_spec (hex x)]
    · intro s hs
      have hnot : certifiedStage A c x s ≠ true := Nat.find_min (hex x) hs
      simp [Bool.eq_false_iff.2 hnot]
  · apply isModulus_iff.2
    intro x s hs
    obtain ⟨d, -, hd, hout⟩ := evaln_eq_some_of_certifiedStage hA (Nat.find_spec (hex x)) hs
    have heq : d.output = g x := by simpa [hc] using hout
    simp [f, hd, heq]

/-- **Modulus Lemma.** For a c.e. oracle `Z`, a total natural-valued function is computable in
`Z` exactly when it has a computable approximation with a `Z`-computable modulus. In particular,
no computable modulus is asserted when `Z` itself is noncomputable. -/
theorem computableIn_iff_exists_isModulus_of_rePred {Z : Set ℕ}
    (hZ : REPred (· ∈ Z)) :
    ComputableIn {Z.oracle} g ↔
      ∃ (f : ℕ → ℕ → ℕ) (m : ℕ → ℕ), Computable₂ f ∧
        ComputableIn {Z.oracle} m ∧ IsModulus f g m := by
  constructor
  · intro hg
    obtain ⟨A, hA, -, hAc, hlim⟩ := rePred_iff_exists_stages.1 hZ
    have hlim' : stageLimit A = Z := by simpa using hlim
    subst Z
    exact exists_computable_isModulus_of_stages hA hAc hg
  · rintro ⟨f, m, hf, hm, hmod⟩
    exact hmod.computableIn hf.computableIn hm

end TauCeti.Approximation
