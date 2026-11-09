/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.MarkovChain.Visits
public import TauCeti.Probability.Process.Excursion.MarkovChain

/-!
# Independent return gaps of a Markov chain

At a state to which a chain returns with probability one, the successive return gaps
are independent and identically distributed. Their common law is the image of the
excursion law under word length plus one: the final return step is not part of the
excursion word. After inclusion into `WithTop ℕ`, this is exactly the law of
`hittingAfter` with starting index one, not the entrance time with starting index zero.

The joint product-law identity and the first-return-law identity are also given for
any process with the Markov-chain path law. Together with
`successiveVisit_eq_sum_returnGap`, these allow laws of large numbers for independent
return cycles to be applied to occupation counts. No finite-mean assumption is made.

These laws are derived from the i.i.d. excursion decomposition at a recurrent state.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press, 1997, §§1.5 and 1.10.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open TauCeti TauCeti.Probability

namespace ProbabilityTheory.Kernel

variable {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  (κ : Kernel α α) [IsMarkovKernel κ] {a : α}

omit [Countable α] in
/-- Every gap of a recurrent chain is an excursion length plus the final return step. -/
private theorem ae_returnGap_eq_length_excursion_add_one
    (ha : markovChainLaw (Measure.dirac a) κ
      {x | hittingAfter (fun n x => x n) {a} 1 x ≠ ⊤} = 1) :
    ∀ᵐ x ∂markovChainLaw (Measure.dirac a) κ, ∀ k,
      returnGap (fun n x => x n) a k x = (excursion x a k).length + 1 := by
  filter_upwards [κ.ae_infinite_setOf_eq_markovChainLaw_dirac ha] with x hx k
  exact returnGap_eq_length_excursion_add_one (exists_visitCount_of_infinite hx (k + 1))

/-- The successive return gaps of a recurrent chain are independent. -/
theorem iIndepFun_returnGap
    (ha : markovChainLaw (Measure.dirac a) κ
      {x | hittingAfter (fun n x => x n) {a} 1 x ≠ ⊤} = 1) :
    ProbabilityTheory.iIndepFun (returnGap (fun n (x : ℕ → α) => x n) a)
      (markovChainLaw (Measure.dirac a) κ) := by
  have hret := κ.ae_infinite_setOf_eq_markovChainLaw_dirac ha
  have hi := (iIndepFun_excursionProcess hret).comp
    (fun _ (e : List α) => e.length + 1) (fun _ => Measurable.of_discrete)
  apply hi.congr
  intro k
  filter_upwards [κ.ae_returnGap_eq_length_excursion_add_one ha] with x hx
  simpa only [Function.comp_apply, excursionProcess_apply] using (hx k).symm

/-- Every return gap has the law of an excursion length plus one. -/
theorem hasLaw_returnGap
    (ha : markovChainLaw (Measure.dirac a) κ
      {x | hittingAfter (fun n x => x n) {a} 1 x ≠ ⊤} = 1) (k : ℕ) :
    HasLaw (returnGap (fun n (x : ℕ → α) => x n) a k)
      ((excursionLaw κ a).map fun e => e.length + 1)
      (markovChainLaw (Measure.dirac a) κ) := by
  have hret := κ.ae_infinite_setOf_eq_markovChainLaw_dirac ha
  have he : HasLaw (excursionProcess (fun n (x : ℕ → α) => x n) a k)
      (excursionLaw κ a) (markovChainLaw (Measure.dirac a) κ) :=
    ⟨aemeasurable_excursionProcess (fun n => (measurable_pi_apply n).aemeasurable)
        a (measurableSet_singleton a) k,
      map_excursionProcess_eq_excursionLaw k
        (hret.mono fun x hx => exists_visitCount_of_infinite hx (k + 1))⟩
  apply ((hasLaw_map (Measurable.of_discrete :
    Measurable (fun e : List α => e.length + 1)).aemeasurable).comp he).congr
  filter_upwards [κ.ae_returnGap_eq_length_excursion_add_one ha] with x hx
  simpa only [Function.comp_apply, excursionProcess_apply] using hx k

end ProbabilityTheory.Kernel

namespace ProbabilityTheory.HasLaw

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  [Countable α] [MeasurableSingletonClass α]
  {P : Measure Ω} {X : ℕ → Ω → α} {κ : Kernel α α} [IsMarkovKernel κ] {a : α}

/-- For any realization of a recurrent chain, the sequence of return gaps has the
infinite product of the excursion-length-plus-one law. -/
theorem returnGap_infinitePi
    (hX : HasLaw (fun ω n => X n ω) (markovChainLaw (Measure.dirac a) κ) P)
    (ha : markovChainLaw (Measure.dirac a) κ
      {x | hittingAfter (fun n x => x n) {a} 1 x ≠ ⊤} = 1) :
    HasLaw (fun ω k => returnGap X a k ω)
      (Measure.infinitePi fun _ : ℕ => (excursionLaw κ a).map fun e => e.length + 1) P := by
  have hgap := (κ.iIndepFun_returnGap ha).hasLaw_infinitePi
    (κ.hasLaw_returnGap ha)
    (Measurable.of_eval fun k => (measurable_returnGap
      (fun n => measurable_pi_apply n) (measurableSet_singleton a) k)).aemeasurable
  simpa only [Function.comp_def, returnGap_def] using hgap.comp hX

/-- In any realization, the cast of each return gap has precisely the positive
first-return law, with infinity retained in that law's codomain. -/
theorem natCast_returnGap_map_hittingAfter
    (hX : HasLaw (fun ω n => X n ω) (markovChainLaw (Measure.dirac a) κ) P)
    (ha : markovChainLaw (Measure.dirac a) κ
      {x | hittingAfter (fun n x => x n) {a} 1 x ≠ ⊤} = 1) (k : ℕ) :
    HasLaw (fun ω => (returnGap X a k ω : WithTop ℕ))
      ((markovChainLaw (Measure.dirac a) κ).map
        (hittingAfter (fun n x => x n) {a} 1)) P := by
  have hret := κ.ae_infinite_setOf_eq_markovChainLaw_dirac ha
  have h0 : (fun x : ℕ → α => (returnGap (fun n x => x n) a 0 x : WithTop ℕ)) =ᵐ[
      markovChainLaw (Measure.dirac a) κ] hittingAfter (fun n x => x n) {a} 1 := by
    filter_upwards [hret, markovChainLaw_dirac_ae_apply_zero κ a] with x hx hx0
    rw [← successiveVisit_one_eq_hittingAfter_of_zero hx0,
      successiveVisit_eq_sum_returnGap (exists_visitCount_of_infinite hx 1) hx0]
    simp
  have heq : (markovChainLaw (Measure.dirac a) κ).map
      (fun x => (returnGap (fun n x => x n) a 0 x : WithTop ℕ)) =
      (markovChainLaw (Measure.dirac a) κ).map
        (hittingAfter (fun n x => x n) {a} 1) := Measure.map_congr h0
  have hcast : Measurable (fun n : ℕ => (n : WithTop ℕ)) := Measurable.of_discrete
  have hfirst := (hasLaw_map hcast.aemeasurable).comp (κ.hasLaw_returnGap ha 0)
  have hk := (hasLaw_map hcast.aemeasurable).comp (κ.hasLaw_returnGap ha k)
  rw [hfirst.map_eq.symm.trans heq] at hk
  simpa only [Function.comp_def, returnGap_def] using hk.comp hX

end ProbabilityTheory.HasLaw
