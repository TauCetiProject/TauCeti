/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Restart.Basic
public import TauCeti.Probability.Renewal.Excess.Memoryless
public import TauCeti.Probability.Renewal.UnusedTail
public import Mathlib.Probability.IdentDistribIndep

/-!
# Stationary future laws of exponential renewals

At a deterministic observation time, the residual exponential waiting time and the unused
increment sequence together have the original i.i.d. increment law. Thus restarting an
exponential renewal process preserves the law of the entire increment sequence, not just
each coordinate's marginal distribution. The corresponding future count process
`s ↦ N (t + s) - N t` has the original count-process law, and each increment over a time
interval of length `s` is Poisson with mean `r * s`.

The results apply to arbitrary measurable realizations. They include observation at zero
and intervals of length zero. They assert stationarity of future laws, not independence
from the observed history; that requires a separate history factorization.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II,
  second edition (1971), Chapter I, §4 and Chapter XI, §1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {T : ℕ → Ω → ℝ≥0} {r : ℝ≥0}

/-- The entire restarted waiting-time sequence has the original i.i.d. exponential law.
In particular the residual first gap is independent of all the unused gaps. -/
theorem identDistrib_renewalRestart_of_expMeasure
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P) (t : ℝ≥0) :
    IdentDistrib (fun ω n ↦ renewalRestart T t n ω) (fun ω n ↦ T n ω) P P := by
  have := hindep.isProbabilityMeasure
  have hid (n : ℕ) : IdentDistrib (T n) (T 0) P P := by
    simpa only [Function.comp_def, Real.toNNReal_coe] using
      ((hlaw n).identDistrib (hlaw 0)).comp measurable_real_toNNReal
  have hzero : P {ω | T 0 ω = 0} < 1 := by
    have hz := ae_iff.1 (ae_pos_of_hasLaw_expMeasure (hlaw 0))
    exact (measure_mono_null (fun ω hω ↦ by simp [hω]) hz).trans_lt zero_lt_one
  have hE : IdentDistrib (renewalExcess T t) (T 0) P P := by
    simpa only [Function.comp_def, Real.toNNReal_coe] using
      ((hasLaw_renewalExcess_expMeasure hT hindep hlaw t).identDistrib (hlaw 0)).comp
        measurable_real_toNNReal
  have htail : HasLaw (fun ω n ↦ T (n + 1) ω)
      (Measure.infinitePi (fun _ : ℕ ↦ P.map (T 0))) P := by
    refine ⟨(Measurable.of_eval fun n ↦ hT (n + 1)).aemeasurable, ?_⟩
    rw [(hindep.precomp (add_left_injective 1)).map_fun_eq_infinitePi_map
      (fun n ↦ hT (n + 1))]
    congr 1
    funext n
    exact (hid (n + 1)).map_eq
  have hU := (hasLaw_renewalUnusedTail hT hindep hid hzero t).identDistrib htail
  have hEU : IndepFun (renewalExcess T t) (renewalUnusedTail T t) P :=
    ((indepFun_renewalUnusedTail_renewalCountNat_renewalExcess hT hindep hid hzero t).comp
      measurable_id measurable_snd).symm
  have hhead : IndepFun (T 0) (fun ω n ↦ T (n + 1) ω) P := by
    have h := hindep.indepFun_set {0} (Ici 1) (by simp) hT
    exact h.comp
      (by fun_prop : Measurable (fun z : ({0} : Set ℕ) → ℝ≥0 ↦ z ⟨0, by simp⟩))
      (by fun_prop : Measurable (fun z : Ici (1 : ℕ) → ℝ≥0 ↦
        fun n ↦ z ⟨n + 1, Nat.le_add_left 1 n⟩))
  let join (p : ℝ≥0 × (ℕ → ℝ≥0)) : ℕ → ℝ≥0
    | 0 => p.1
    | n + 1 => p.2 n
  have hjoin : Measurable join := by
    apply Measurable.of_eval
    intro n
    cases n <;> fun_prop
  convert (hE.prodMk hU hEU hhead).comp hjoin using 1 <;>
    (funext ω n; cases n <;>
      simp [join, renewalRestart_succ, renewalUnusedTail_apply, Nat.add_right_comm])

/-- The whole future count process of an exponential renewal has its original law.
This is a process-law assertion over all nonnegative times, not just a marginal identity. -/
theorem identDistrib_renewalCountNat_sub_of_expMeasure
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P) (t : ℝ≥0) :
    IdentDistrib (fun ω s ↦ renewalCountNat T (t + s) ω - renewalCountNat T t ω)
      (fun ω s ↦ renewalCountNat T s ω) P P := by
  have hrestart := identDistrib_renewalRestart_of_expMeasure hT hindep hlaw t
  have hcounts : HasLaw (fun ω s ↦ renewalCountNat T (t + s) ω - renewalCountNat T t ω)
      ((P.map (fun ω n ↦ T n ω)).map
        (fun w s ↦ renewalCountNat (fun n w ↦ w n) s w)) P :=
    hasLaw_renewalCountNat_sub_of_hasLaw_renewalRestart
      (ae_tendsto_arrival_atTop_of_expMeasure hindep hlaw) t
      ⟨hrestart.aemeasurable_fst, hrestart.map_eq⟩
  have hc : Measurable (fun (w : ℕ → ℝ≥0) s ↦
      renewalCountNat (fun n w ↦ w n) s w) :=
    Measurable.of_eval fun s ↦ measurable_renewalCountNat (fun n ↦ measurable_pi_apply n) s
  have hmap : ((P.map (fun ω n ↦ T n ω)).map
      (fun w s ↦ renewalCountNat (fun n w ↦ w n) s w)) =
      P.map (fun ω s ↦ renewalCountNat T s ω) := by
    rw [Measure.map_map hc (Measurable.of_eval hT)]
    congr 1
    funext ω s
    exact (renewalCountNat_comp (fun n (w : ℕ → ℝ≥0) ↦ w n) (fun ω n ↦ T n ω) s ω).symm
  exact ⟨hcounts.aemeasurable,
    (Measurable.of_eval fun s ↦ measurable_renewalCountNat hT s).aemeasurable,
    hcounts.map_eq.trans hmap⟩

/-- Every count increment over an interval of length `s` has Poisson law with mean `r * s`,
independently of the deterministic starting time. -/
theorem hasLaw_renewalCountNat_sub_poissonMeasure
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P) (t s : ℝ≥0) :
    HasLaw (fun ω ↦ renewalCountNat T (t + s) ω - renewalCountNat T t ω)
      (poissonMeasure (r * s)) P := by
  have h := (identDistrib_renewalCountNat_sub_of_expMeasure hT hindep hlaw t).comp
    (measurable_pi_apply s)
  exact h.symm.hasLaw (hasLaw_renewalCountNat_poissonMeasure hT hindep hlaw s)

end TauCeti.Probability
