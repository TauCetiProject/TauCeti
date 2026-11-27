/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.Exp.Damped
import TauCeti.MeasureTheory.Integral.Bochner.Fatou

/-!
# Removing exponential damping from an integral with an integrable subtraction

`TauCeti.integrableOn_and_integral_sub_eq_of_tendsto_exp_neg_mul` recovers the integral of a
nonnegative function on the positive half-line from the finite limit of its exponentially damped
integrals after subtracting an integrable function. Fatou's lemma
(`TauCeti.integrable_of_tendsto_of_integral_le`) gives integrability of the nonnegative term.
Then `TauCeti.tendsto_setIntegral_exp_smul` removes the damping from both terms.

The time-side passage to the limit in Delange's smoothing argument is an application
of this principle. See H. Delange, *Généralisation du théorème de Ikehara* (1954), §3.3.4.
-/

public section

open Filter MeasureTheory Set
open scoped Topology

namespace TauCeti

/-- A finite limit of the exponentially damped integrals of `f - g` on `(0, ∞)` implies
integrability of `f` and identifies the limit with the undamped integral, provided `f` is
nonnegative almost everywhere, `g` is integrable, and the damped integrals exist near zero. -/
theorem integrableOn_and_integral_sub_eq_of_tendsto_exp_neg_mul
    {μ : Measure ℝ} {f g : ℝ → ℝ} {L : ℝ}
    (hf : 0 ≤ᵐ[μ.restrict (Ioi 0)] f) (hg : IntegrableOn g (Ioi 0) μ)
    (hd : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      IntegrableOn (fun t ↦ Real.exp (-ε * t) * (f t - g t)) (Ioi 0) μ)
    (hlim : Tendsto (fun ε : ℝ ↦ ∫ t in Ioi 0, Real.exp (-ε * t) * (f t - g t) ∂μ)
      (𝓝[>] 0) (𝓝 L)) :
    IntegrableOn f (Ioi 0) μ ∧ (∫ t in Ioi 0, (f t - g t) ∂μ) = L := by
  have hε : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
  have hmap : Tendsto (fun ε : ℝ ↦ ε + 1) (𝓝[>] 0) (𝓝[≥] (1 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (by simpa using (tendsto_id (x := 𝓝 (0 : ℝ)) |>.add_const 1).mono_left nhdsWithin_le_nhds)
      (hε.mono fun ε h ↦ by simpa using h.le)
  have hdamp {v : ℝ → ℝ} (hv : IntegrableOn v (Ioi 0) μ) :
      Tendsto (fun ε : ℝ ↦ ∫ t in Ioi 0, Real.exp (-ε * t) * v t ∂μ)
        (𝓝[>] 0) (𝓝 (∫ t in Ioi 0, v t ∂μ)) := by
    have hrestrict : (μ.restrict (Ioi 0)).restrict (Ici 0) = μ.restrict (Ioi 0) :=
      by rw [Measure.restrict_restrict measurableSet_Ici, inter_eq_right.mpr Ioi_subset_Ici_self]
    have hv' : IntegrableOn v (Ici 0) (μ.restrict (Ioi 0)) :=
      by simpa only [IntegrableOn, hrestrict] using hv
    simpa only [Function.comp_def, hrestrict, add_sub_cancel_right, smul_eq_mul, neg_mul, mul_neg,
      mul_comm] using (tendsto_setIntegral_exp_smul hv').comp hmap
  have hgi (ε : ℝ) (hε : 0 ≤ ε) :
      IntegrableOn (fun t ↦ Real.exp (-ε * t) * g t) (Ioi 0) μ := by
    refine integrable_exp_neg_mul_smul_of_le (σ := 0) ?_
      ((ae_restrict_mem measurableSet_Ioi).mono fun _ ht ↦ ht.le) hε
    simpa only [neg_zero, zero_mul, Real.exp_zero, one_smul, IntegrableOn] using hg
  have hdi : ∀ᶠ ε : ℝ in 𝓝[>] 0, IntegrableOn (fun t ↦ Real.exp (-ε * t) * f t) (Ioi 0) μ := by
    filter_upwards [hd, hε] with ε hsub hpos
    simpa only [mul_sub, Pi.add_def, sub_add_cancel] using hsub.add (hgi ε hpos.le)
  have hflim : Tendsto (fun ε : ℝ ↦ ∫ t in Ioi 0, Real.exp (-ε * t) * f t ∂μ)
      (𝓝[>] 0) (𝓝 (L + ∫ t in Ioi 0, g t ∂μ)) := by
    refine (hlim.add (hdamp hg)).congr' ?_
    filter_upwards [hdi, hε] with ε hfi hpos
    simp only [mul_sub, integral_sub hfi (hgi ε hpos.le), sub_add_cancel]
  have hfi : IntegrableOn f (Ioi 0) μ := by
    refine integrable_of_tendsto_of_integral_le hdi ?_ ?_
      ((hflim.eventually (gt_mem_nhds (lt_add_one _))).frequently.mono fun _ h ↦ h.le)
    · exact .of_forall fun ε ↦ hf.mono fun t ht ↦ mul_nonneg (Real.exp_pos _).le ht
    · refine .of_forall fun t ↦ ?_
      have hc : Continuous fun ε : ℝ ↦ Real.exp (-ε * t) * f t := by fun_prop
      simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  exact ⟨hfi, tendsto_nhds_unique (hdamp (hfi.sub hg)) hlim⟩

end TauCeti
