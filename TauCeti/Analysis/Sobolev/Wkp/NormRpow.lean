/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Basic
import TauCeti.Analysis.Calculus.IteratedGradient.Measurable
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Analysis.Sobolev.WeakDeriv.NormRpow
import TauCeti.Analysis.Sobolev.Wkp.Chain
import TauCeti.Analysis.Sobolev.Wkp.Classical
import TauCeti.Analysis.Sobolev.Wkp.Restriction
import TauCeti.MeasureTheory.Integral.NormRpow

/-!
# Second-order Sobolev regularity of a norm power

Let `E` be a finite-dimensional real inner product space of dimension `n` with an additive Haar
measure, and let `u(x) = ‖x‖ ^ γ`. Away from the origin its classical Hessian is
`D²u(x) v = γ ‖x‖ ^ (γ - 2) v + γ (γ - 2) ‖x‖ ^ (γ - 4) ⟪x, v⟫ x`
(`TauCeti.iteratedGradientChain_one_norm_rpow_apply`). Its operator norm is at most
`|γ| (|γ - 2| + 1) ‖x‖ ^ (γ - 2)` (`TauCeti.norm_iteratedGradientChain_one_norm_rpow_le`). Its
trace, the Laplacian `γ (n + γ - 2) ‖x‖ ^ (γ - 2)`, bounds it from below: its operator norm is at
least `|γ (n + γ - 2)| / n · ‖x‖ ^ (γ - 2)`
(`TauCeti.abs_mul_rpow_le_finrank_mul_norm_iteratedGradientChain_one_norm_rpow`). Thus for
`γ ≠ 0` and `n + γ > 2` the Hessian has size comparable to `‖x‖ ^ (γ - 2)`.

For `n + γ > 2` the Hessian is the weak derivative of the gradient across the origin
(`TauCeti.hasWeakFDerivOn_gradient_norm_rpow`). The weak Hessian of every `W^{2,p}` function equal
to `u` is therefore its classical Hessian
(`TauCeti.Wkp.iteratedGradient_ae_eq_iteratedGradientChain_norm_rpow`). By the lower bound, that
Hessian is `p`-integrable near the origin only for `p < n / (2 - γ)`
(`TauCeti.lt_ofReal_of_memLp_iteratedGradientChain_one_norm_rpow`). Consequently, for
`γ ≠ 0`, `γ < 2` and `n + γ > 2`, on a bounded open set containing the origin,

`u ∈ W^{2,p}` exactly when `p < n / (2 - γ)`

(`TauCeti.exists_wkp_two_value_ae_eq_norm_rpow_iff`), including `p = ∞`, which never qualifies.
For `n ≥ 2` and `0 < γ < 1` the threshold `n / (2 - γ)` lies strictly between `n / 2` and `n`:
`u` is then a `W^{2,p}` function for some `p > n / 2`, hence continuous, but it is not in
`W^{2,n}`. Such power singularities are the standard witnesses for the sharpness of `W^{2,p}`
regularity statements for elliptic equations with discontinuous coefficients.

## Main declarations

* `TauCeti.Wkp.iteratedGradient_ae_eq_iteratedGradientChain_norm_rpow`: the weak derivatives of a
  `W^{k+1,p}` function equal to `‖x‖ ^ γ` are its classical derivatives.
* `TauCeti.lt_ofReal_of_memLp_iteratedGradientChain_one_norm_rpow`: the Hessian is `p`-integrable
  near the origin only for `p < n / (2 - γ)`.
* `TauCeti.exists_wkp_two_value_ae_eq_norm_rpow`: on a bounded open set, `‖x‖ ^ γ` lies in
  `W^{2,p}` when `p < n / (2 - γ)`, and `TauCeti.exists_wkp_two_value_ae_eq_norm_rpow_iff`: on a
  bounded open set containing the origin, exactly then.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.2.3, Example 2, for the first-order
  analogue: `‖x‖ ^ (-α)` lies in `W^{1,p}` of the unit ball exactly when `α < (n - p) / p`.
-/

public section

noncomputable section

open MeasureTheory Metric Set Filter TopologicalSpace Module
open scoped ENNReal NNReal Topology InnerProductSpace Gradient

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {γ : ℝ}

variable [FiniteDimensional ℝ E]

/-! ### The weak Hessian -/

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- The weak derivatives of an element of `W^{k+1,p}(Ω)` equal to `‖x‖ ^ γ` are its classical
derivatives; for `k = 1` its weak Hessian is its classical Hessian. -/
theorem Wkp.iteratedGradient_ae_eq_iteratedGradientChain_norm_rpow (k : ℕ)
    {Ω : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)] (w : Wkp μ Ω p (k + 1))
    (hw : (Wkp.value (k + 1) w : E → ℝ) =ᵐ[μ.restrict Ω] fun y => ‖y‖ ^ γ) :
    (Wkp.iteratedGradient k w : E → IteratedGradient E k) =ᵐ[μ.restrict Ω]
      iteratedGradientChain (fun y : E => ‖y‖ ^ γ) k := by
  -- On the zero space both fields vanish.
  rcases subsingleton_or_nontrivial E with hE | hE
  · have hsub : ∀ j, Subsingleton (IteratedGradient E j) := fun j => by
      induction j with
      | zero => exact hE
      | succ j ih => exact (inferInstance : Subsingleton (E →L[ℝ] IteratedGradient E j))
    exact ae_of_all _ fun _ => (hsub k).elim _ _
  -- Away from the origin, a null set, the power is smooth.
  let Ω' : Opens E := ⟨(Ω : Set E) \ {0}, Ω.isOpen.sdiff isClosed_singleton⟩
  have hΩ' : Ω' ≤ Ω := fun _ hx => hx.1
  have hres : μ.restrict (Ω' : Set E) = μ.restrict Ω :=
    Measure.restrict_congr_set (sdiff_null_ae_eq_self (measure_singleton 0))
  have h := Wkp.iteratedGradient_ae_eq_of_contDiffOn k (Wkp.restrictL hΩ' (k + 1) w)
    (fun x hx => ((contDiffAt_norm ℝ hx.2).rpow_const_of_ne
      (norm_ne_zero_iff.2 hx.2)).contDiffWithinAt)
    ((Wkp.value_restrictL_ae hΩ' (k + 1) w).trans (by rw [hres]; exact hw))
  have hae : ae (μ.restrict (Ω' : Set E)) = ae (μ.restrict Ω) := by rw [hres]
  have h' := (Wkp.iteratedGradient_restrictL_ae hΩ' k w).symm.trans h
  rwa [EventuallyEq, hae] at h'

/-! ### Membership in `W^{2,p}` -/

/-- **The Hessian of a norm power is not `Lᵖ` near the origin for large `p`.** Let `γ ≠ 0`,
`γ < 2` and `n + γ > 2`, where `n` is the dimension. If the Hessian of `‖x‖ ^ γ` is `p`-integrable
on a neighbourhood of the origin, then `p < n / (2 - γ)`: its norm is at least a positive multiple
of `‖x‖ ^ (γ - 2)`. -/
theorem lt_ofReal_of_memLp_iteratedGradientChain_one_norm_rpow (hγ0 : γ ≠ 0)
    (hγ : γ < 2) (hn : 2 < finrank ℝ E + γ) {Ω : Set E} (hΩ : Ω ∈ 𝓝 0) {p : ℝ≥0∞}
    (hH : MemLp (iteratedGradientChain (fun y : E => ‖y‖ ^ γ) 1) p (μ.restrict Ω)) :
    p < ENNReal.ofReal (finrank ℝ E / (2 - γ)) := by
  have h2γ : 0 < 2 - γ := by linarith
  have hnpos : (0 : ℝ) < finrank ℝ E := by linarith
  have := Module.nontrivial_of_finrank_pos (R := ℝ) (M := E) (by exact_mod_cast hnpos)
  by_contra hq
  rw [not_lt] at hq
  set q := ENNReal.ofReal (finrank ℝ E / (2 - γ)) with hq_def
  have hqr : q.toReal = finrank ℝ E / (2 - γ) := ENNReal.toReal_ofReal (div_pos hnpos h2γ).le
  have hq0 : q ≠ 0 := by
    rw [hq_def, ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact div_pos hnpos h2γ
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hΩ
  have : IsFiniteMeasure (μ.restrict (ball (0 : E) r)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  -- The Hessian, of norm at least `c ‖x‖ ^ (γ - 2)`, would be `q`-integrable on a ball about the
  -- origin.
  have hc : 0 < |γ * (finrank ℝ E + γ - 2)| / finrank ℝ E :=
    div_pos (abs_pos.2 (mul_ne_zero hγ0 (by linarith))) hnpos
  have h := neg_finrank_lt_mul_toReal_of_memLp_restrict (s := γ - 2) hq0 ENNReal.ofReal_ne_top
    (ball_mem_nhds 0 hr) hc
    (ae_of_all _ fun x => by
      rcases eq_or_ne x 0 with rfl | hx
      · rw [norm_zero, Real.zero_rpow (by linarith), mul_zero]
        exact norm_nonneg _
      rw [div_mul_eq_mul_div, div_le_iff₀ hnpos, mul_comm _ (finrank ℝ E : ℝ)]
      exact abs_mul_rpow_le_finrank_mul_norm_iteratedGradientChain_one_norm_rpow γ hx)
    ((hH.mono_measure (Measure.restrict_mono hball le_rfl)).mono_exponent hq)
  rw [hqr, show (γ - 2) * (finrank ℝ E / (2 - γ)) = -finrank ℝ E by field_simp; ring] at h
  exact lt_irrefl _ h

/-- For `γ < 2`, `n + γ > 2` and `p < n / (2 - γ)`, where `n` is the dimension, `‖x‖ ^ γ` lies in
`W^{2,p}` of every bounded open set. -/
theorem exists_wkp_two_value_ae_eq_norm_rpow (hγ : γ < 2)
    (hn : 2 < finrank ℝ E + γ) {Ω : Opens E} (hb : Bornology.IsBounded (Ω : Set E))
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p < ENNReal.ofReal (finrank ℝ E / (2 - γ))) :
    ∃ w : Wkp μ Ω p 2, (Wkp.value 2 w : E → ℝ) =ᵐ[μ.restrict Ω] fun y => ‖y‖ ^ γ := by
  have h2γ : 0 < 2 - γ := by linarith
  have := Module.nontrivial_of_finrank_pos (R := ℝ) (M := E)
    (by exact_mod_cast (by linarith : (0 : ℝ) < finrank ℝ E))
  have hp1 : 1 ≤ p := Fact.out
  have hpt : p ≠ ∞ := ne_top_of_lt hp
  have hpr : p.toReal * (2 - γ) < finrank ℝ E := by
    have := (ENNReal.toReal_lt_toReal hpt ENNReal.ofReal_ne_top).2 hp
    rwa [ENNReal.toReal_ofReal (by positivity), lt_div_iff₀ h2γ] at this
  have hp1r : 1 ≤ p.toReal := by
    simpa using ENNReal.toReal_mono hpt hp1
  have hae : ∀ᵐ x ∂μ.restrict Ω, x ≠ 0 := ae_restrict_of_ae (μ.ae_ne 0)
  -- The function, its gradient and its Hessian are dominated by multiples of powers of the norm.
  have hu : MemLp (fun y : E => ‖y‖ ^ γ) p (μ.restrict Ω) :=
    memLp_restrict_of_norm_le_mul_norm_rpow (C := 1) hpt hb
      (by fun_prop : Measurable fun y : E => ‖y‖ ^ γ).aestronglyMeasurable
      (ae_of_all _ fun x => by rw [one_mul, Real.norm_of_nonneg (by positivity)])
      (by nlinarith)
  have hg : MemLp (∇ fun y : E => ‖y‖ ^ γ) p (μ.restrict Ω) :=
    memLp_restrict_of_norm_le_mul_norm_rpow hpt hb
      (measurable_gradient _).aestronglyMeasurable
      (hae.mono fun x hx => (norm_gradient_norm_rpow_of_ne hx).le)
      (by nlinarith)
  have hH : MemLp (iteratedGradientChain (fun y : E => ‖y‖ ^ γ) 1) p (μ.restrict Ω) :=
    memLp_restrict_of_norm_le_mul_norm_rpow hpt hb
      (aestronglyMeasurable_iteratedGradientChain _ 1)
      (hae.mono fun x hx => norm_iteratedGradientChain_one_norm_rpow_le γ hx)
      (by nlinarith)
  obtain ⟨w, hw, -⟩ := Wkp.exists_value_iteratedGradient_ae_eq_of_chain 1
    (G := iteratedGradientChain (fun y : E => ‖y‖ ^ γ)) hu
    (by simpa only [iteratedGradientChain_zero] using
      hasWeakFDerivOn_norm_rpow_innerSL_gradient (μ := μ) (by linarith) Ω)
    (fun i hi => by
      obtain rfl : i = 0 := by omega
      simpa only [iteratedGradientChain_zero] using hasWeakFDerivOn_gradient_norm_rpow hn Ω)
    (fun i hi => by
      interval_cases i
      · simpa only [iteratedGradientChain_zero] using hg
      · exact hH)
  exact ⟨w, hw⟩

/-- **`W^{2,p}` regularity of a norm power.** Let `γ ≠ 0` and `γ < 2` with `n + γ > 2`, where `n`
is the dimension, and let `Ω` be a bounded open set containing the origin. Then `‖x‖ ^ γ` lies in
`W^{2,p}(Ω)` exactly when `p < n / (2 - γ)`; the case `p = ∞` is included and never occurs. -/
theorem exists_wkp_two_value_ae_eq_norm_rpow_iff (hγ0 : γ ≠ 0) (hγ : γ < 2)
    (hn : 2 < finrank ℝ E + γ) {Ω : Opens E} (hb : Bornology.IsBounded (Ω : Set E))
    (h0 : (0 : E) ∈ Ω) {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    (∃ w : Wkp μ Ω p 2, (Wkp.value 2 w : E → ℝ) =ᵐ[μ.restrict Ω] fun y => ‖y‖ ^ γ) ↔
      p < ENNReal.ofReal (finrank ℝ E / (2 - γ)) :=
  ⟨fun ⟨w, hw⟩ => lt_ofReal_of_memLp_iteratedGradientChain_one_norm_rpow hγ0 hγ hn
      (Ω.isOpen.mem_nhds h0) ((Lp.memLp (Wkp.iteratedGradient 1 w)).ae_eq
        (Wkp.iteratedGradient_ae_eq_iteratedGradientChain_norm_rpow 1 w hw)),
    exists_wkp_two_value_ae_eq_norm_rpow hγ hn hb⟩

end TauCeti
