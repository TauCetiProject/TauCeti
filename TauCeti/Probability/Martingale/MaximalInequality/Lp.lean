/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Martingale.MaximalInequality.Event
public import Mathlib.Order.PartialSups
import TauCeti.MeasureTheory.Integral.Lebesgue.Superlevel
import TauCeti.MeasureTheory.Function.Lp.Order
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral
import Mathlib.Analysis.Normed.Order.Lattice

/-!
# Doob's positive-part, event-refined `Lᵖ`, and strong `Lᵖ` maximal inequalities

`TauCeti.Probability.Martingale.MaximalInequality.Basic` and
`TauCeti.Probability.Martingale.MaximalInequality.Event` establish Doob's weak and event-refined
`L¹` maximal inequalities for nonnegative submartingales. This file removes the sign restriction on
submartingales via the positive part `f⁺` and upgrades the theory to `Lᵖ`:

* **Positive-part maximal inequalities (`p = 1`)**: for any real submartingale `f` on a finite
  measure space and any `ε : ℝ≥0`, the crossing events `{∃ t ∈ F, ε ≤ f_t}`, `{∃ t ≤ T, ε < f_t}`,
  and `{ε ≤ ⨆ t ≤ T, ofReal (f_t)}` are controlled by the restricted and full terminal expectations
  of `(f⁺)_T`, with no global sign hypothesis on `f` and no positivity side condition on `ε`.
* **Almost sure finiteness of the running supremum**: for any right-continuous real submartingale
  `f` (or Banach-valued martingale `M`) on `[0, T]` over a finite measure space, the running
  supremum `⨆ t ≤ T, ofReal (f_t)` (or `⨆ t ≤ T, ‖M_t‖ₑ`) is finite almost everywhere, already
  under `L¹` integrability alone.
* **Event-refined `Lᵖ` maximal inequalities (`1 ≤ p < ∞`)**: on the closed crossing event
  `A_ε = {ε ≤ ⨆ t ≤ T, ofReal (f_t)}` (and on finite time sets),
  `ε ^ p μ(A_ε) ≤ ∫⁻_{A_ε} ofReal ((f⁺)_T) ^ p ∂μ` holds unconditionally, and
  `ε ^ p μ(A_ε) ≤ ofReal (∫_{A_ε} (f⁺)_T ^ p ∂μ)` holds assuming `Lᵖ` integrability only at the
  terminal time `T`. Specializing to `M.norm` gives the Banach-valued martingale inequality
  `ε ^ p μ({ε ≤ ⨆ t ≤ T, ‖M_t‖ₑ}) ≤ ∫⁻_{...} ‖M_T‖ₑ ^ p ∂μ` (and the Bochner `setIntegral` form
  under `MemLp (M T) (ofReal p) μ`).
* **Doob's strong `Lᵖ` maximal inequalities (`1 < p < ∞`)**: combining the `L¹` superlevel bound
  with `TauCeti.eLpNorm_le_of_mul_meas_ofReal_lt_le_setLIntegral` yields the sharp constant
  `p / (p - 1)` for discrete `partialSups`, countable time sets, and right-continuous processes
  before `T`, for both signed submartingales (against `(f⁺)_T`, or `f_T` when `0 ≤ᵐ[μ] f_T`) and
  Banach-valued martingales. In the `eLpNorm` and `lintegral` formulations no `MemLp` hypothesis is
  needed; when the terminal value lies in `Lᵖ`, the real running supremum belongs to `Lᵖ` and its
  `p`-th moment is bounded by `(p / (p - 1)) ^ p` times the terminal `p`-th moment.
* **Uniform `Lᵖ` path convergence**: terminal `Lᵖ` convergence (`1 < p < ∞`) of right-continuous
  Banach-valued martingales implies `Lᵖ` convergence of the uniform path error on `[0, T]`.

## Main declarations

In `MeasureTheory.Submartingale`:
* `mul_measure_le_iSup_le_setIntegral_posPart`, `mul_measure_le_iSup_le_posPart`: closed-level
  positive-part maximal inequalities for signed right-continuous submartingales.
* `ae_iSup_ofReal_lt_top`: almost sure finiteness of `⨆ t ≤ T, ofReal (f t ω)`.
* `rpow_mul_measure_le_iSup_le_setLIntegral_posPart`, `rpow_mul_measure_le_iSup_le_setLIntegral`,
  `rpow_mul_measure_le_iSup_le_setIntegral_posPart`, `rpow_mul_measure_le_iSup_le_setIntegral`:
  event-refined `Lᵖ` maximal inequalities (`1 ≤ p < ∞`).
* `eLpNorm_partialSups_posPart_le`, `eLpNorm_partialSups_le`, `integral_rpow_partialSups_le`:
  discrete-time Doob `Lᵖ` maximal inequalities (`1 < p < ∞`).
* `eLpNorm_biSup_ofReal_le_posPart`, `eLpNorm_biSup_ofReal_le`: countable-time Doob `Lᵖ` maximal
  inequalities (`1 < p < ∞`).
* `lintegral_iSup_ofReal_rpow_le_posPart`, `eLpNorm_iSup_ofReal_le_posPart`,
  `eLpNorm_iSup_ofReal_le`, `memLp_toReal_iSup_ofReal`,
  `integral_toReal_iSup_ofReal_rpow_le_posPart`, `integral_toReal_iSup_ofReal_rpow_le`:
  continuous-time Doob `Lᵖ` maximal inequalities (`1 < p < ∞`).

In `MeasureTheory.Martingale`:
* `ae_iSup_enorm_lt_top`: almost sure finiteness of `⨆ t ≤ T, ‖M t ω‖ₑ`.
* `rpow_mul_measure_le_iSup_enorm_le_setLIntegral`,
  `rpow_mul_measure_le_iSup_enorm_le_setIntegral`: event-refined `Lᵖ` maximal inequalities for
  Banach-valued martingales (`1 ≤ p < ∞`).
* `eLpNorm_partialSups_norm_le`, `integral_rpow_partialSups_norm_le`, `eLpNorm_biSup_enorm_le`,
  `lintegral_iSup_enorm_rpow_le`, `eLpNorm_iSup_enorm_le`, `memLp_toReal_iSup_enorm`,
  `integral_toReal_iSup_enorm_rpow_le`: Doob's `Lᵖ` maximal inequalities for Banach-valued
  martingales (`1 < p < ∞`).
* `tendsto_eLpNorm_iSup_enorm_sub`: terminal `Lᵖ` convergence implies `Lᵖ` running-supremum
  convergence on `[0, T]`.

## References

* J. L. Doob, *Stochastic Processes*, Wiley, 1953, Chapter VII, Theorem 3.4.
* D. Revuz, M. Yor, *Continuous Martingales and Brownian Motion*, third edition, Springer, 1999,
  Theorem II.1.7.
* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition, Springer,
  1991, Theorem 1.3.8.
-/

public section

noncomputable section

open Filter Set Topology
open scoped NNReal ENNReal

namespace MeasureTheory.Submartingale

variable {Ω ι : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

private lemma ofReal_posPart_eq (x : ℝ) : ENNReal.ofReal (x⁺) = ENNReal.ofReal x := by
  rw [posPart_def]
  rcases le_total 0 x with hx | hx
  · rw [max_eq_left hx]
  · rw [max_eq_right hx, ENNReal.ofReal_zero, ENNReal.ofReal_eq_zero.2 hx]

private lemma apply_posPart_nonneg (f : ι → Ω → ℝ) (t : ι) (ω : Ω) : 0 ≤ (f⁺) t ω :=
  posPart_nonneg (f t ω)

private lemma posPart_ae_eq_of_nonneg {g : Ω → ℝ} (hg : 0 ≤ᵐ[μ] g) : g⁺ =ᵐ[μ] g :=
  hg.mono fun ω hω ↦ by
    change 0 ≤ g ω at hω
    rw [Pi.posPart_apply, posPart_def, max_eq_left hω]

private lemma posPart_right_continuous [Preorder ι] [TopologicalSpace ι]
    {f : ι → Ω → ℝ} {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ f u ω) (Ioi t) t) :
    ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ (f⁺) u ω) (Ioi t) t := by
  filter_upwards [hcont] with ω hω t ht
  exact continuous_posPart.continuousAt.comp_continuousWithinAt (hω t ht)

private lemma integrable_rpow_of_memLp {g : Ω → ℝ} {p : ℝ} (hp : 0 < p)
    (hnn : 0 ≤ᵐ[μ] g) (hg : MemLp g (ENNReal.ofReal p) μ) :
    Integrable (fun ω ↦ g ω ^ p) μ := by
  have hp_ne0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.2 hp).ne'
  have h := hg.integrable_norm_rpow hp_ne0 ENNReal.ofReal_ne_top
  rw [ENNReal.toReal_ofReal hp.le] at h
  refine h.congr (hnn.mono fun ω hω ↦ ?_)
  change 0 ≤ g ω at hω
  dsimp only
  rw [Real.norm_eq_abs, abs_of_nonneg hω]

private lemma lintegral_ofReal_rpow_eq_ofReal_integral {g : Ω → ℝ} {p : ℝ} (hp : 0 < p)
    (hnn : 0 ≤ᵐ[μ] g) (hg : MemLp g (ENNReal.ofReal p) μ) :
    ∫⁻ ω, ENNReal.ofReal (g ω) ^ p ∂μ = ENNReal.ofReal (∫ ω, g ω ^ p ∂μ) := by
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_rpow_of_memLp hp hnn hg)
    (hnn.mono fun _ h ↦ Real.rpow_nonneg h _)]
  refine lintegral_congr_ae (hnn.mono fun ω hω ↦ ?_)
  change 0 ≤ g ω at hω
  exact ENNReal.ofReal_rpow_of_nonneg hω hp.le

/-! ### Positive-part maximal inequalities for signed real submartingales -/

section PosPart

variable [LinearOrder ι] [IsFiniteMeasure μ] {ℱ : Filtration ι m0} {f : ι → Ω → ℝ}

/-- **Event-refined positive-part Doob inequality on a finite set.** No sign assumption on `f` or
positivity side condition on `ε` is needed. -/
theorem mul_measure_exists_mem_le_le_setIntegral_posPart
    (hf : Submartingale f ℱ μ) (ε : ℝ≥0) {F : Finset ι} {T : ι} (hF : ∀ t ∈ F, t ≤ T) :
    ε * μ {ω | ∃ t ∈ F, (ε : ℝ) ≤ f t ω} ≤
      ENNReal.ofReal (∫ ω in {ω | ∃ t ∈ F, (ε : ℝ) ≤ f t ω}, (f⁺) T ω ∂μ) := by
  rcases eq_or_ne ε 0 with rfl | hε
  · simp
  have hε_pos : (0 : ℝ) < ε := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hε)
  have hset : {ω | ∃ t ∈ F, (ε : ℝ) ≤ f t ω} = {ω | ∃ t ∈ F, (ε : ℝ) ≤ (f⁺) t ω} := by
    ext ω
    simp only [mem_ofPred_eq, Pi.posPart_apply, posPart_def, le_max_iff]
    exact exists_congr fun t ↦ and_congr_right fun _ ↦
      ⟨Or.inl, fun h ↦ h.resolve_right hε_pos.not_ge⟩
  rw [hset]
  exact hf.pos.mul_measure_exists_mem_le_le_setIntegral (apply_posPart_nonneg f) ε hF

/-- **Positive-part Doob maximal inequality on a finite set.** -/
theorem mul_measure_exists_mem_le_le_posPart
    (hf : Submartingale f ℱ μ) (ε : ℝ≥0) {F : Finset ι} {T : ι} (hF : ∀ t ∈ F, t ≤ T) :
    ε * μ {ω | ∃ t ∈ F, (ε : ℝ) ≤ f t ω} ≤ ENNReal.ofReal (∫ ω, (f⁺) T ω ∂μ) :=
  (hf.mul_measure_exists_mem_le_le_setIntegral_posPart ε hF).trans
    (ENNReal.ofReal_le_ofReal (setIntegral_le_integral (hf.pos.integrable T)
      (Eventually.of_forall (apply_posPart_nonneg f T))))

/-- **Event-refined positive-part Doob inequality for strict crossings on a countable set.** -/
theorem mul_measure_exists_mem_lt_le_setIntegral_posPart_of_countable
    (hf : Submartingale f ℱ μ) (ε : ℝ≥0) {S : Set ι} (hS : S.Countable) {T : ι}
    (hST : ∀ t ∈ S, t ≤ T) :
    ε * μ {ω | ∃ t ∈ S, (ε : ℝ) < f t ω} ≤
      ENNReal.ofReal (∫ ω in {ω | ∃ t ∈ S, (ε : ℝ) < f t ω}, (f⁺) T ω ∂μ) := by
  have hset : {ω | ∃ t ∈ S, (ε : ℝ) < f t ω} = {ω | ∃ t ∈ S, (ε : ℝ) < (f⁺) t ω} := by
    ext ω
    simp only [mem_ofPred_eq, Pi.posPart_apply, posPart_def, lt_max_iff]
    exact exists_congr fun t ↦ and_congr_right fun _ ↦
      ⟨Or.inl, fun h ↦ h.resolve_right (not_lt_of_ge ε.coe_nonneg)⟩
  rw [hset]
  exact hf.pos.mul_measure_exists_mem_lt_le_setIntegral_of_countable
    (apply_posPart_nonneg f) ε hS hST

section ContinuousTimePosPart

variable [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι]

/-- **Event-refined positive-part Doob inequality for strict crossings in continuous time.** -/
theorem mul_measure_exists_le_lt_le_setIntegral_posPart
    (hf : Submartingale f ℱ μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ f u ω) (Ioi t) t) (ε : ℝ≥0) :
    ε * μ {ω | ∃ t ≤ T, (ε : ℝ) < f t ω} ≤
      ENNReal.ofReal (∫ ω in {ω | ∃ t ≤ T, (ε : ℝ) < f t ω}, (f⁺) T ω ∂μ) := by
  have hset : {ω | ∃ t ≤ T, (ε : ℝ) < f t ω} = {ω | ∃ t ≤ T, (ε : ℝ) < (f⁺) t ω} := by
    ext ω
    simp only [mem_ofPred_eq, Pi.posPart_apply, posPart_def, lt_max_iff]
    exact exists_congr fun t ↦ and_congr_right fun _ ↦
      ⟨Or.inl, fun h ↦ h.resolve_right (not_lt_of_ge ε.coe_nonneg)⟩
  rw [hset]
  exact hf.pos.mul_measure_exists_le_lt_le_setIntegral (apply_posPart_nonneg f)
    (posPart_right_continuous hcont) ε

/-- **Positive-part Doob maximal inequality for strict crossings in continuous time.** -/
theorem mul_measure_exists_le_lt_le_posPart
    (hf : Submartingale f ℱ μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ f u ω) (Ioi t) t) (ε : ℝ≥0) :
    ε * μ {ω | ∃ t ≤ T, (ε : ℝ) < f t ω} ≤ ENNReal.ofReal (∫ ω, (f⁺) T ω ∂μ) :=
  (hf.mul_measure_exists_le_lt_le_setIntegral_posPart hcont ε).trans
    (ENNReal.ofReal_le_ofReal (setIntegral_le_integral (hf.pos.integrable T)
      (Eventually.of_forall (apply_posPart_nonneg f T))))

/-- **Closed-level event-refined positive-part Doob inequality.** Because `ENNReal.ofReal` vanishes
on `(-∞, 0]`, `⨆ t ≤ T, ENNReal.ofReal (f t ω)` coincides pointwise with
`⨆ t ≤ T, ENNReal.ofReal ((f⁺) t ω)`. -/
theorem mul_measure_le_iSup_le_setIntegral_posPart
    (hf : Submartingale f ℱ μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ f u ω) (Ioi t) t) (ε : ℝ≥0) :
    ε * μ {ω | (ε : ℝ≥0∞) ≤ ⨆ t ≤ T, ENNReal.ofReal (f t ω)} ≤
      ENNReal.ofReal (∫ ω in {ω | (ε : ℝ≥0∞) ≤ ⨆ t ≤ T, ENNReal.ofReal (f t ω)},
        (f⁺) T ω ∂μ) := by
  have hsup (ω : Ω) : (⨆ t ≤ T, ENNReal.ofReal ((f⁺) t ω)) = ⨆ t ≤ T, ENNReal.ofReal (f t ω) := by
    simp_rw [Pi.posPart_apply, ofReal_posPart_eq]
  simpa only [hsup] using hf.pos.mul_measure_le_iSup_le_setIntegral
    (apply_posPart_nonneg f) (posPart_right_continuous hcont) ε

/-- **Closed-level positive-part Doob maximal inequality** (`ε P(sup_{t ≤ T} f_t ≥ ε) ≤ E[(f_T)⁺]`).
Holds for every real submartingale `f` with right-continuous paths before `T` and `ε : ℝ≥0`. -/
theorem mul_measure_le_iSup_le_posPart
    (hf : Submartingale f ℱ μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ f u ω) (Ioi t) t) (ε : ℝ≥0) :
    ε * μ {ω | (ε : ℝ≥0∞) ≤ ⨆ t ≤ T, ENNReal.ofReal (f t ω)} ≤
      ENNReal.ofReal (∫ ω, (f⁺) T ω ∂μ) :=
  (hf.mul_measure_le_iSup_le_setIntegral_posPart hcont ε).trans
    (ENNReal.ofReal_le_ofReal (setIntegral_le_integral (hf.pos.integrable T)
      (Eventually.of_forall (apply_posPart_nonneg f T))))

/-- **Almost sure finiteness of the running supremum of a submartingale.** Any real submartingale
with almost surely right-continuous paths before `T` on a finite measure space has almost everywhere
finite running supremum `⨆ t ≤ T, ENNReal.ofReal (f t ω) < ∞` (no higher `Lᵖ` moment is needed). -/
theorem ae_iSup_ofReal_lt_top
    (hf : Submartingale f ℱ μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ f u ω) (Ioi t) t) :
    ∀ᵐ ω ∂μ, (⨆ t ≤ T, ENNReal.ofReal (f t ω)) < ∞ := by
  rw [ae_iff]
  set A : Set Ω := {ω | ¬ (⨆ t ≤ T, ENNReal.ofReal (f t ω)) < ∞}
  by_contra hA
  set C : ℝ≥0∞ := ENNReal.ofReal (∫ ω, (f⁺) T ω ∂μ)
  have hle (n : ℕ) : (n : ℝ≥0∞) ≤ C / μ A := by
    refine (ENNReal.le_div_iff_mul_le (.inl hA) (.inl (measure_ne_top μ A))).2 ?_
    have hsub : A ⊆ {ω | ((n : ℝ≥0) : ℝ≥0∞) ≤ ⨆ t ≤ T, ENNReal.ofReal (f t ω)} := fun ω hω ↦ by
      rw [mem_ofPred_eq, not_lt, top_le_iff] at hω
      simp [hω]
    exact (mul_le_mul_of_nonneg_left (measure_mono hsub) zero_le).trans
      (hf.mul_measure_le_iSup_le_posPart hcont n)
  have htop : C / μ A = ∞ :=
    top_unique (le_of_tendsto' ENNReal.tendsto_nat_nhds_top hle)
  exact (ENNReal.div_lt_top ENNReal.ofReal_ne_top hA).ne htop

end ContinuousTimePosPart

end PosPart

/-! ### Event-refined `Lᵖ` maximal inequalities (`1 ≤ p < ∞`) -/

section EventRefinedLp

variable [LinearOrder ι] [IsFiniteMeasure μ] {ℱ : Filtration ι m0} {f : ι → Ω → ℝ}

omit [IsFiniteMeasure μ] in
/-- Stopping `(f⁺)` at `T` and raising to `p ≥ 1` produces a pointwise nonnegative submartingale on
the whole index type `ι`, requiring `MemLp` only at the terminal time `T`. -/
private lemma submartingale_posPart_min_rpow
    (hf : Submartingale f ℱ μ) {T : ι} {p : ℝ} (hp : 1 ≤ p)
    (hT : MemLp ((f⁺) T) (ENNReal.ofReal p) μ) :
    Submartingale (fun t ω ↦ ((f⁺) (min t T) ω) ^ p)
      (ℱ.comp (monotone_id.min (monotone_const : Monotone fun _ : ι ↦ T))) μ := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hp_enn : 1 ≤ ENNReal.ofReal p := by
    rwa [← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff hp0.le]
  let τ : ι → ι := fun t ↦ min t T
  have hτ : Monotone τ := monotone_id.min monotone_const
  have hg : Submartingale (fun t ↦ (f⁺) (τ t)) (ℱ.comp hτ) μ := hf.pos.comp hτ
  refine hg.rpow (fun t ↦ Eventually.of_forall (apply_posPart_nonneg f (τ t))) hp fun t ↦ ?_
  have ht_mem : MemLp ((f⁺) (τ t)) (ENNReal.ofReal p) μ := by
    have hmax : τ (max t T) = T := min_eq_right (le_max_right t T)
    exact hg.memLp_of_le (le_max_left t T)
      (Eventually.of_forall (apply_posPart_nonneg f (τ t)))
      hp_enn (by simpa only [hmax] using hT)
  exact integrable_rpow_of_memLp hp0 (Eventually.of_forall (apply_posPart_nonneg f (τ t))) ht_mem

/-- **Event-refined `Lᵖ` Doob inequality on a finite set (positive-part Bochner form).** For
`1 ≤ p < ∞`, terminal `Lᵖ` integrability of `(f⁺) T` suffices to control `ε ^ p` times the measure
of the finite crossing event by the restricted `p`-th moment of `(f⁺) T`. -/
theorem rpow_mul_measure_exists_mem_le_le_setIntegral_posPart
    (hf : Submartingale f ℱ μ) (ε : ℝ≥0) {F : Finset ι} {T : ι} (hF : ∀ t ∈ F, t ≤ T)
    {p : ℝ} (hp : 1 ≤ p) (hT : MemLp ((f⁺) T) (ENNReal.ofReal p) μ) :
    (ε : ℝ≥0∞) ^ p * μ {ω | ∃ t ∈ F, (ε : ℝ) ≤ f t ω} ≤
      ENNReal.ofReal (∫ ω in {ω | ∃ t ∈ F, (ε : ℝ) ≤ f t ω}, ((f⁺) T ω) ^ p ∂μ) := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  rcases eq_or_ne ε 0 with rfl | hε
  · simp [ENNReal.zero_rpow_of_pos hp0]
  have hε_pos : (0 : ℝ) < ε := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hε)
  have hg := submartingale_posPart_min_rpow hf hp hT
  have hmax := hg.mul_measure_exists_mem_le_le_setIntegral
    (fun t ω ↦ Real.rpow_nonneg (apply_posPart_nonneg f (min t T) ω) _) (ε ^ p) hF
  have hset : {ω | ∃ t ∈ F, ((ε ^ p : ℝ≥0) : ℝ) ≤ ((f⁺) (min t T) ω) ^ p} =
      {ω | ∃ t ∈ F, (ε : ℝ) ≤ f t ω} := by
    ext ω
    simp only [mem_ofPred_eq, NNReal.coe_rpow]
    refine exists_congr fun t ↦ and_congr_right fun ht ↦ ?_
    rw [min_eq_left (hF t ht), Real.rpow_le_rpow_iff ε.coe_nonneg (apply_posPart_nonneg f t ω) hp0,
      Pi.posPart_apply, Pi.posPart_apply, posPart_def, le_max_iff]
    exact ⟨fun h ↦ h.resolve_right hε_pos.not_ge, Or.inl⟩
  rw [hset, min_self] at hmax
  simpa only [ENNReal.coe_rpow_of_nonneg _ hp0.le] using hmax

/-- **Event-refined `Lᵖ` Doob inequality on a finite set.** Requires `0 ≤ᵐ[μ] f T` and `MemLp`
only at the terminal time `T`. -/
theorem rpow_mul_measure_exists_mem_le_le_setIntegral
    (hf : Submartingale f ℱ μ) (ε : ℝ≥0) {F : Finset ι} {T : ι} (hF : ∀ t ∈ F, t ≤ T)
    (hposT : 0 ≤ᵐ[μ] f T) {p : ℝ} (hp : 1 ≤ p) (hT : MemLp (f T) (ENNReal.ofReal p) μ) :
    (ε : ℝ≥0∞) ^ p * μ {ω | ∃ t ∈ F, (ε : ℝ) ≤ f t ω} ≤
      ENNReal.ofReal (∫ ω in {ω | ∃ t ∈ F, (ε : ℝ) ≤ f t ω}, f T ω ^ p ∂μ) := by
  have hae : (f⁺) T =ᵐ[μ] f T := posPart_ae_eq_of_nonneg hposT
  have hmeas : MeasurableSet {ω | ∃ t ∈ F, (ε : ℝ) ≤ f t ω} := by
    simp only [← exists_prop, ofPred_exists]
    exact F.measurableSet_biUnion fun t _ ↦
      measurableSet_le measurable_const ((hf.stronglyAdapted t).mono (ℱ.le t)).measurable
  have hcongr : ∫ ω in {ω | ∃ t ∈ F, (ε : ℝ) ≤ f t ω}, ((f⁺) T ω) ^ p ∂μ =
      ∫ ω in {ω | ∃ t ∈ F, (ε : ℝ) ≤ f t ω}, f T ω ^ p ∂μ :=
    setIntegral_congr_ae hmeas (hae.mono fun _ hω _ ↦ congrArg (· ^ p) hω)
  rw [← hcongr]
  exact hf.rpow_mul_measure_exists_mem_le_le_setIntegral_posPart ε hF hp (hT.ae_eq hae.symm)

section ContinuousTimeEventLp

variable [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι]

/-- **Closed-level event-refined `Lᵖ` Doob inequality (positive-part Bochner form).** Requires
`MemLp` only at the terminal time `T`. -/
theorem rpow_mul_measure_le_iSup_le_setIntegral_posPart
    (hf : Submartingale f ℱ μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ f u ω) (Ioi t) t)
    (ε : ℝ≥0) {p : ℝ} (hp : 1 ≤ p) (hT : MemLp ((f⁺) T) (ENNReal.ofReal p) μ) :
    (ε : ℝ≥0∞) ^ p * μ {ω | (ε : ℝ≥0∞) ≤ ⨆ t ≤ T, ENNReal.ofReal (f t ω)} ≤
      ENNReal.ofReal (∫ ω in {ω | (ε : ℝ≥0∞) ≤ ⨆ t ≤ T, ENNReal.ofReal (f t ω)},
        ((f⁺) T ω) ^ p ∂μ) := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hg := submartingale_posPart_min_rpow hf hp hT
  have hg_cont : ∀ᵐ ω ∂μ, ∀ t < T,
      ContinuousWithinAt (fun u ↦ ((f⁺) (min u T) ω) ^ p) (Ioi t) t := by
    filter_upwards [posPart_right_continuous hcont] with ω hω t ht
    have hcongr : (fun u ↦ ((f⁺) (min u T) ω) ^ p) =ᶠ[𝓝[>] t] (fun u ↦ ((f⁺) u ω) ^ p) := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht)] with u hu
      rw [min_eq_left hu.le]
    exact ((Real.continuous_rpow_const hp0.le).continuousAt.comp_continuousWithinAt
      (hω t ht)).congr_of_eventuallyEq hcongr (by simp [min_eq_left ht.le])
  have hmax := hg.mul_measure_le_iSup_le_setIntegral
    (fun t ω ↦ Real.rpow_nonneg (apply_posPart_nonneg f (min t T) ω) _) hg_cont (ε ^ p)
  have hset : {ω | ((ε ^ p : ℝ≥0) : ℝ≥0∞) ≤
      ⨆ t ≤ T, ENNReal.ofReal (((f⁺) (min t T) ω) ^ p)} =
      {ω | (ε : ℝ≥0∞) ≤ ⨆ t ≤ T, ENNReal.ofReal (f t ω)} := by
    ext ω
    simp only [mem_ofPred_eq, ENNReal.coe_rpow_of_nonneg _ hp0.le]
    have hsup : (⨆ t ≤ T, ENNReal.ofReal (((f⁺) (min t T) ω) ^ p)) =
        (⨆ t ≤ T, ENNReal.ofReal (f t ω)) ^ p := by
      rw [ENNReal.iSup_rpow_of_pos hp0]
      refine iSup_congr fun t ↦ ?_
      by_cases ht : t ≤ T
      · simp only [ht, iSup_pos, min_eq_left ht]
        rw [← ENNReal.ofReal_rpow_of_nonneg (apply_posPart_nonneg f t ω) hp0.le,
          Pi.posPart_apply, Pi.posPart_apply, ofReal_posPart_eq]
      · simp [ht, ENNReal.zero_rpow_of_pos hp0]
    rw [hsup, ENNReal.rpow_le_rpow_iff hp0]
  rw [hset, min_self] at hmax
  simpa only [ENNReal.coe_rpow_of_nonneg _ hp0.le] using hmax

/-- **Closed-level event-refined `Lᵖ` Doob inequality (Bochner form).** Requires nonnegativity and
`MemLp` only at the terminal time `T`. -/
theorem rpow_mul_measure_le_iSup_le_setIntegral
    (hf : Submartingale f ℱ μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ f u ω) (Ioi t) t)
    (hposT : 0 ≤ᵐ[μ] f T) (ε : ℝ≥0) {p : ℝ} (hp : 1 ≤ p)
    (hT : MemLp (f T) (ENNReal.ofReal p) μ) :
    (ε : ℝ≥0∞) ^ p * μ {ω | (ε : ℝ≥0∞) ≤ ⨆ t ≤ T, ENNReal.ofReal (f t ω)} ≤
      ENNReal.ofReal (∫ ω in {ω | (ε : ℝ≥0∞) ≤ ⨆ t ≤ T, ENNReal.ofReal (f t ω)},
        f T ω ^ p ∂μ) := by
  have hae : (f⁺) T =ᵐ[μ] f T := posPart_ae_eq_of_nonneg hposT
  have hY : AEMeasurable (fun ω ↦ ⨆ t ≤ T, ENNReal.ofReal (f t ω)) μ :=
    aemeasurable_iSup_le_ofReal
      (fun t ↦ ((hf.stronglyAdapted t).measurable.mono (ℱ.le t) le_rfl).aemeasurable) hcont
  have hA : NullMeasurableSet {ω | (ε : ℝ≥0∞) ≤ ⨆ t ≤ T, ENNReal.ofReal (f t ω)} μ :=
    nullMeasurableSet_le aemeasurable_const hY
  have hcongr : ∫ ω in {ω | (ε : ℝ≥0∞) ≤ ⨆ t ≤ T, ENNReal.ofReal (f t ω)},
      ((f⁺) T ω) ^ p ∂μ =
      ∫ ω in {ω | (ε : ℝ≥0∞) ≤ ⨆ t ≤ T, ENNReal.ofReal (f t ω)}, f T ω ^ p ∂μ :=
    setIntegral_congr_ae₀ hA (hae.mono fun _ hω _ ↦ congrArg (· ^ p) hω)
  rw [← hcongr]
  exact hf.rpow_mul_measure_le_iSup_le_setIntegral_posPart hcont ε hp (hT.ae_eq hae.symm)

/-- **Unconditional closed-level event-refined `Lᵖ` Doob inequality (lower-integral form).** For
`1 ≤ p < ∞`, no `MemLp` hypothesis is needed: if `(f⁺) T ∉ Lᵖ`, the complement of the crossing
event has bounded `(f⁺) T ≤ ε` on a finite measure space, forcing the lower integral on the
crossing event to be `∞`. -/
theorem rpow_mul_measure_le_iSup_le_setLIntegral_posPart
    (hf : Submartingale f ℱ μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ f u ω) (Ioi t) t)
    (ε : ℝ≥0) {p : ℝ} (hp : 1 ≤ p) :
    (ε : ℝ≥0∞) ^ p * μ {ω | (ε : ℝ≥0∞) ≤ ⨆ t ≤ T, ENNReal.ofReal (f t ω)} ≤
      ∫⁻ ω in {ω | (ε : ℝ≥0∞) ≤ ⨆ t ≤ T, ENNReal.ofReal (f t ω)},
        ENNReal.ofReal ((f⁺) T ω) ^ p ∂μ := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  set A : Set Ω := {ω | (ε : ℝ≥0∞) ≤ ⨆ t ≤ T, ENNReal.ofReal (f t ω)}
  have hp_enn : 1 ≤ ENNReal.ofReal p := by
    rwa [← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff hp0.le]
  have hp_ne0 : ENNReal.ofReal p ≠ 0 := (zero_lt_one.trans_le hp_enn).ne'
  have hfT_meas : AEStronglyMeasurable ((f⁺) T) μ :=
    ((hf.pos.stronglyAdapted T).mono (ℱ.le T)).aestronglyMeasurable
  by_cases hT : MemLp ((f⁺) T) (ENNReal.ofReal p) μ
  · refine (hf.rpow_mul_measure_le_iSup_le_setIntegral_posPart hcont ε hp hT).trans_eq ?_
    exact (lintegral_ofReal_rpow_eq_ofReal_integral hp0
      (Eventually.of_forall (apply_posPart_nonneg f T)) (hT.restrict A)).symm
  · -- When `(f⁺) T ∉ Lᵖ`, the integral on `Aᶜ` is finite while the full `Lᵖ` integral is `∞`.
    have hY : AEMeasurable (fun ω ↦ ⨆ t ≤ T, ENNReal.ofReal (f t ω)) μ :=
      aemeasurable_iSup_le_ofReal
        (fun t ↦ ((hf.stronglyAdapted t).measurable.mono (ℱ.le t) le_rfl).aemeasurable) hcont
    have hA : NullMeasurableSet A μ := nullMeasurableSet_le aemeasurable_const hY
    have hfull_top : ∫⁻ ω, ENNReal.ofReal ((f⁺) T ω) ^ p ∂μ = ∞ := by
      rw [memLp_iff, not_lt, top_le_iff] at hT
      have heq := lintegral_rpow_enorm_eq_eLpNorm_rpow hp_ne0 ENNReal.ofReal_ne_top hfT_meas
      rw [ENNReal.toReal_ofReal hp0.le, hT, ENNReal.top_rpow_of_pos hp0] at heq
      exact (lintegral_congr fun ω ↦ by
        rw [Real.eNorm_eq_ofReal (apply_posPart_nonneg f T ω)]).symm.trans heq
    have hcompl_lt : ∫⁻ ω in Aᶜ, ENNReal.ofReal ((f⁺) T ω) ^ p ∂μ < ∞ := by
      rw [← lintegral_indicator₀ hA.compl]
      refine lt_of_le_of_lt (lintegral_mono (g := fun _ ↦ (ε : ℝ≥0∞) ^ p) fun ω ↦ ?_) ?_
      · by_cases hω : ω ∈ Aᶜ
        · rw [indicator_of_mem hω]
          simp only [A, mem_compl_iff, mem_ofPred_eq, not_le] at hω
          have hle : ENNReal.ofReal ((f⁺) T ω) ≤ (ε : ℝ≥0∞) := by
            rw [Pi.posPart_apply, Pi.posPart_apply, ofReal_posPart_eq]
            exact (le_iSup₂ (f := fun t (_ : t ≤ T) ↦ ENNReal.ofReal (f t ω)) T le_rfl).trans hω.le
          exact ENNReal.rpow_le_rpow hle hp0.le
        · rw [indicator_of_notMem hω]
          exact zero_le
      · rw [lintegral_const]
        exact ENNReal.mul_lt_top
          (ENNReal.rpow_lt_top_of_nonneg hp0.le ENNReal.coe_ne_top) (measure_lt_top _ _)
    have hadd := lintegral_add_compl₀ (fun ω ↦ ENNReal.ofReal ((f⁺) T ω) ^ p) hA
    rw [hfull_top] at hadd
    have hA_top : ∫⁻ ω in A, ENNReal.ofReal ((f⁺) T ω) ^ p ∂μ = ∞ := by
      by_contra hne
      exact (ENNReal.add_lt_top.2 ⟨lt_top_iff_ne_top.2 hne, hcompl_lt⟩).ne hadd
    rw [hA_top]
    exact le_top

/-- **Unconditional closed-level event-refined `Lᵖ` Doob inequality (lower-integral form).**
Requires nonnegativity only at the terminal time `T` (`0 ≤ᵐ[μ] f T`), with no `MemLp`
hypothesis. -/
theorem rpow_mul_measure_le_iSup_le_setLIntegral
    (hf : Submartingale f ℱ μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ f u ω) (Ioi t) t)
    (hposT : 0 ≤ᵐ[μ] f T) (ε : ℝ≥0) {p : ℝ} (hp : 1 ≤ p) :
    (ε : ℝ≥0∞) ^ p * μ {ω | (ε : ℝ≥0∞) ≤ ⨆ t ≤ T, ENNReal.ofReal (f t ω)} ≤
      ∫⁻ ω in {ω | (ε : ℝ≥0∞) ≤ ⨆ t ≤ T, ENNReal.ofReal (f t ω)},
        ENNReal.ofReal (f T ω) ^ p ∂μ := by
  have hae : (f⁺) T =ᵐ[μ] f T := posPart_ae_eq_of_nonneg hposT
  have hcongr : ∫⁻ ω in {ω | (ε : ℝ≥0∞) ≤ ⨆ t ≤ T, ENNReal.ofReal (f t ω)},
      ENNReal.ofReal ((f⁺) T ω) ^ p ∂μ =
      ∫⁻ ω in {ω | (ε : ℝ≥0∞) ≤ ⨆ t ≤ T, ENNReal.ofReal (f t ω)},
        ENNReal.ofReal (f T ω) ^ p ∂μ :=
    lintegral_congr_ae (ae_restrict_of_ae (hae.mono fun _ hω ↦ by dsimp only; rw [hω]))
  rw [← hcongr]
  exact hf.rpow_mul_measure_le_iSup_le_setLIntegral_posPart hcont ε hp

end ContinuousTimeEventLp

end EventRefinedLp

/-! ### Doob's strong `Lᵖ` maximal inequalities (`1 < p < ∞`) -/

section StrongLp

variable [LinearOrder ι] [IsFiniteMeasure μ] {ℱ : Filtration ι m0} {f : ι → Ω → ℝ}

/-- **Doob's `Lᵖ` maximal inequality on a countable set (positive-part form).** For `1 < p < ∞` in
`ℝ≥0∞`, no sign or `MemLp` assumption on `f` is needed. -/
theorem eLpNorm_biSup_ofReal_le_posPart
    (hf : Submartingale f ℱ μ) {S : Set ι} (hS : S.Countable) {T : ι} (hST : ∀ t ∈ S, t ≤ T)
    {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞) :
    eLpNorm (fun ω ↦ ⨆ t ∈ S, ENNReal.ofReal (f t ω)) p μ ≤
      p / (p - 1) * eLpNorm ((f⁺) T) p μ := by
  have := hS.to_subtype
  have hu : AEStronglyMeasurable (fun ω ↦ ⨆ t ∈ S, ENNReal.ofReal (f t ω)) μ := by
    have hmeas : AEMeasurable (fun ω ↦ ⨆ s : S, ENNReal.ofReal (f s ω)) μ :=
      AEMeasurable.iSup fun s : S ↦
        (((hf.stronglyAdapted s).measurable.mono (ℱ.le s) le_rfl).aemeasurable).ennreal_ofReal
    simpa only [iSup_subtype] using hmeas.aestronglyMeasurable
  refine TauCeti.eLpNorm_le_of_mul_meas_ofReal_lt_le_setLIntegral hu hp hp_top
    (fun _ _ ↦ measure_ne_top μ _) fun t ht ↦ ?_
  let ε : ℝ≥0 := Real.toNNReal t
  have hε_coe : (ε : ℝ) = t := Real.coe_toNNReal t ht.le
  have hε_enn : (ε : ℝ≥0∞) = ENNReal.ofReal t := by rw [← ENNReal.ofReal_coe_nnreal, hε_coe]
  have hset : {ω | ENNReal.ofReal t < ‖⨆ s ∈ S, ENNReal.ofReal (f s ω)‖ₑ} =
      {ω | ∃ s ∈ S, (ε : ℝ) < f s ω} := by
    ext ω
    simp only [mem_ofPred_eq, eNorm_eq_self, ← hε_enn, lt_iSup_iff, exists_prop,
      ENNReal.coe_lt_ofReal]
  rw [hset, ← hε_enn]
  refine (hf.mul_measure_exists_mem_lt_le_setIntegral_posPart_of_countable ε hS hST).trans_eq ?_
  rw [ofReal_integral_eq_lintegral_ofReal (hf.pos.integrable T).integrableOn
    (Eventually.of_forall (apply_posPart_nonneg f T))]
  exact lintegral_congr fun ω ↦ (Real.eNorm_eq_ofReal (apply_posPart_nonneg f T ω)).symm

/-- **Doob's `Lᵖ` maximal inequality on a countable set.** Requires nonnegativity only at the
terminal time `T`, and no `MemLp` hypothesis. -/
theorem eLpNorm_biSup_ofReal_le
    (hf : Submartingale f ℱ μ) {S : Set ι} (hS : S.Countable) {T : ι} (hST : ∀ t ∈ S, t ≤ T)
    (hposT : 0 ≤ᵐ[μ] f T) {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞) :
    eLpNorm (fun ω ↦ ⨆ t ∈ S, ENNReal.ofReal (f t ω)) p μ ≤
      p / (p - 1) * eLpNorm (f T) p μ := by
  have hae : (f⁺) T =ᵐ[μ] f T := posPart_ae_eq_of_nonneg hposT
  simpa only [eLpNorm_congr_ae hae] using hf.eLpNorm_biSup_ofReal_le_posPart hS hST hp hp_top

end StrongLp

section DiscreteTimeLp

variable [IsFiniteMeasure μ] {ℱ : Filtration ℕ m0} {f : ℕ → Ω → ℝ}

/-- **Doob's discrete-time `Lᵖ` maximal inequality (positive-part form).** No `MemLp` assumption is
needed. -/
theorem eLpNorm_partialSups_posPart_le
    (hf : Submartingale f ℱ μ) (n : ℕ) {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞) :
    eLpNorm (partialSups (f⁺) n) p μ ≤ p / (p - 1) * eLpNorm ((f⁺) n) p μ := by
  have heq (ω : Ω) : ‖partialSups (f⁺) n ω‖ₑ = ⨆ k ∈ Set.Iic n, ENNReal.ofReal (f k ω) := by
    have hnn : 0 ≤ partialSups (f⁺) n ω :=
      (apply_posPart_nonneg f 0 ω).trans (le_partialSups_of_le (f⁺) (Nat.zero_le n) ω)
    rw [Real.eNorm_eq_ofReal hnn, Pi.partialSups_apply, partialSups_apply]
    refine le_antisymm ?_ ?_
    · obtain ⟨k, hk, hsup⟩ := Finset.exists_mem_eq_sup' Finset.nonempty_Iic (fun j ↦ (f⁺) j ω)
      rw [hsup, Pi.posPart_apply, Pi.posPart_apply, ofReal_posPart_eq]
      exact le_iSup₂_of_le k (Finset.mem_Iic.1 hk) le_rfl
    · refine iSup₂_le fun k hk ↦ ?_
      rw [← ofReal_posPart_eq]
      exact ENNReal.ofReal_le_ofReal
        (Finset.le_sup' (f := fun j ↦ (f⁺) j ω) (Finset.mem_Iic.2 hk))
  have hm_sup : AEStronglyMeasurable (partialSups (f⁺) n) μ := by
    rw [partialSups_apply]
    exact (Finset.sup'_induction _ _ (fun _ h₁ _ h₂ ↦ h₁.sup h₂) fun k _ ↦
      (hf.pos.stronglyAdapted k).mono (ℱ.le k)).aestronglyMeasurable
  calc eLpNorm (partialSups (f⁺) n) p μ
      ≤ eLpNorm (fun ω ↦ ⨆ k ∈ Set.Iic n, ENNReal.ofReal (f k ω)) p μ :=
        eLpNorm_mono_eNorm hm_sup fun ω ↦ by simpa only [eNorm_eq_self] using (heq ω).le
    _ ≤ p / (p - 1) * eLpNorm ((f⁺) n) p μ :=
        hf.eLpNorm_biSup_ofReal_le_posPart (Set.finite_Iic n).countable (fun _ hk ↦ hk) hp hp_top

/-- **Doob's discrete-time `Lᵖ` maximal inequality** for an almost everywhere nonnegative
submartingale up to time `n`. -/
theorem eLpNorm_partialSups_le
    (hf : Submartingale f ℱ μ) {n : ℕ} (hpos : ∀ k ≤ n, 0 ≤ᵐ[μ] f k)
    {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞) :
    eLpNorm (partialSups f n) p μ ≤ p / (p - 1) * eLpNorm (f n) p μ := by
  have hae_sup : partialSups f n =ᵐ[μ] partialSups (f⁺) n := by
    have hall : ∀ᵐ ω ∂μ, ∀ k ∈ Finset.Iic n, f k ω = (f⁺) k ω :=
      (Finset.Iic n).eventually_all.2 fun k hk ↦
        (posPart_ae_eq_of_nonneg (hpos k (Finset.mem_Iic.1 hk))).symm
    filter_upwards [hall] with ω hω
    simp only [Pi.partialSups_apply, partialSups_apply]
    exact Finset.sup'_congr Finset.nonempty_Iic rfl hω
  have hae_n : f n =ᵐ[μ] (f⁺) n := (posPart_ae_eq_of_nonneg (hpos n le_rfl)).symm
  rw [eLpNorm_congr_ae hae_sup, eLpNorm_congr_ae hae_n]
  exact hf.eLpNorm_partialSups_posPart_le n hp hp_top

/-- **Doob's discrete-time `Lᵖ` maximal inequality (Bochner moment form).** Directly generalizes
`MeasureTheory.Submartingale.integral_sq_partialSups_le` from `p = 2` (constant `4`) to all
`1 < p < ∞` (constant `(p / (p - 1)) ^ p`), requiring `MemLp` only at the terminal step `n`. -/
theorem integral_rpow_partialSups_le
    (hf : Submartingale f ℱ μ) {n : ℕ} (hpos : ∀ k ≤ n, 0 ≤ᵐ[μ] f k)
    {p : ℝ} (hp : 1 < p) (hn : MemLp (f n) (ENNReal.ofReal p) μ) :
    ∫ ω, (partialSups f n ω) ^ p ∂μ ≤ (p / (p - 1)) ^ p * ∫ ω, (f n ω) ^ p ∂μ := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hp_enn : 1 < ENNReal.ofReal p := by
    rwa [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff hp0]
  have hp_ne0 : ENNReal.ofReal p ≠ 0 := (zero_lt_one.trans hp_enn).ne'
  have hbound := hf.eLpNorm_partialSups_le hpos hp_enn ENNReal.ofReal_ne_top
  have hconst : ENNReal.ofReal p / (ENNReal.ofReal p - 1) = ENNReal.ofReal (p / (p - 1)) := by
    rw [ENNReal.ofReal_div_of_pos (sub_pos.2 hp), ENNReal.ofReal_sub _ zero_le_one,
      ENNReal.ofReal_one]
  rw [hconst] at hbound
  have hLp (k : ℕ) (hk : k ≤ n) : MemLp (f k) (ENNReal.ofReal p) μ :=
    hf.memLp_of_le hk (hpos k hk) hp_enn.le hn
  have hM : MemLp (partialSups f n) (ENNReal.ofReal p) μ := MemLp.partialSups hLp
  have heq_M := lintegral_rpow_enorm_eq_eLpNorm_rpow hp_ne0 ENNReal.ofReal_ne_top
    hM.aestronglyMeasurable
  have heq_n := lintegral_rpow_enorm_eq_eLpNorm_rpow hp_ne0 ENNReal.ofReal_ne_top
    hn.aestronglyMeasurable
  rw [ENNReal.toReal_ofReal hp0.le] at heq_M heq_n
  have hpow := ENNReal.rpow_le_rpow hbound hp0.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
    ENNReal.ofReal_rpow_of_pos (div_pos hp0 (sub_pos.2 hp)), ← heq_M, ← heq_n] at hpow
  have hsup_nn : 0 ≤ᵐ[μ] partialSups f n :=
    (hpos 0 (Nat.zero_le n)).mono fun ω hω ↦ hω.trans (le_partialSups_of_le f (Nat.zero_le n) ω)
  have hlhs : ∫⁻ ω, ‖partialSups f n ω‖ₑ ^ p ∂μ =
      ENNReal.ofReal (∫ ω, (partialSups f n ω) ^ p ∂μ) :=
    (lintegral_congr_ae (hsup_nn.mono fun ω hω ↦ by
      change 0 ≤ partialSups f n ω at hω
      simp only [Real.eNorm_eq_ofReal hω])).trans
      (lintegral_ofReal_rpow_eq_ofReal_integral hp0 hsup_nn hM)
  have hrhs : ∫⁻ ω, ‖f n ω‖ₑ ^ p ∂μ = ENNReal.ofReal (∫ ω, (f n ω) ^ p ∂μ) :=
    (lintegral_congr_ae ((hpos n le_rfl).mono fun ω hω ↦ by
      change 0 ≤ f n ω at hω
      simp only [Real.eNorm_eq_ofReal hω])).trans
        (lintegral_ofReal_rpow_eq_ofReal_integral hp0 (hpos n le_rfl) hn)
  rw [hlhs, hrhs, ← ENNReal.ofReal_mul (by positivity)] at hpow
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (by positivity) (integral_nonneg_of_ae
      ((hpos n le_rfl).mono fun _ h ↦ Real.rpow_nonneg h _)))).1 hpow

end DiscreteTimeLp

section ContinuousTimeStrongLp

variable [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι]
  [IsFiniteMeasure μ] {ℱ : Filtration ι m0} {f : ι → Ω → ℝ}

/-- **Doob's continuous-time `Lᵖ` maximal inequality (lower-integral positive-part form).** Holds
for all `1 < p < ∞` with no sign or `MemLp` assumption on `f`. -/
theorem lintegral_iSup_ofReal_rpow_le_posPart
    (hf : Submartingale f ℱ μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ f u ω) (Ioi t) t)
    {p : ℝ} (hp : 1 < p) :
    ∫⁻ ω, (⨆ t ≤ T, ENNReal.ofReal (f t ω)) ^ p ∂μ ≤
      ENNReal.ofReal (p / (p - 1)) ^ p * ∫⁻ ω, ENNReal.ofReal ((f⁺) T ω) ^ p ∂μ := by
  have hu : AEMeasurable (fun ω ↦ ⨆ t ≤ T, ENNReal.ofReal (f t ω)) μ :=
    aemeasurable_iSup_le_ofReal
      (fun t ↦ ((hf.stronglyAdapted t).measurable.mono (ℱ.le t) le_rfl).aemeasurable) hcont
  have hv : AEMeasurable (fun ω ↦ ENNReal.ofReal ((f⁺) T ω)) μ :=
    (((hf.pos.stronglyAdapted T).measurable.mono (ℱ.le T) le_rfl).aemeasurable).ennreal_ofReal
  refine TauCeti.lintegral_rpow_le_of_mul_meas_ofReal_lt_le_setLIntegral hu hv hp
    (fun _ _ ↦ measure_ne_top μ _) fun t ht ↦ ?_
  let ε : ℝ≥0 := Real.toNNReal t
  have hε_coe : (ε : ℝ) = t := Real.coe_toNNReal t ht.le
  have hε_enn : (ε : ℝ≥0∞) = ENNReal.ofReal t := by rw [← ENNReal.ofReal_coe_nnreal, hε_coe]
  have hset : {ω | ENNReal.ofReal t < ⨆ s ≤ T, ENNReal.ofReal (f s ω)} =
      {ω | ∃ s ≤ T, (ε : ℝ) < f s ω} := by
    ext ω
    simp only [mem_ofPred_eq, ← hε_enn, lt_iSup_iff, exists_prop, ENNReal.coe_lt_ofReal]
  rw [hset, ← hε_enn]
  exact (hf.mul_measure_exists_le_lt_le_setIntegral_posPart hcont ε).trans_eq
    (ofReal_integral_eq_lintegral_ofReal (hf.pos.integrable T).integrableOn
      (Eventually.of_forall (apply_posPart_nonneg f T)))

/-- **Doob's continuous-time `Lᵖ` maximal inequality (positive-part `eLpNorm` form).** Holds for
all `1 < p < ∞` in `ℝ≥0∞` with no sign or `MemLp` assumption on `f`. -/
theorem eLpNorm_iSup_ofReal_le_posPart
    (hf : Submartingale f ℱ μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ f u ω) (Ioi t) t)
    {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞) :
    eLpNorm (fun ω ↦ ⨆ t ≤ T, ENNReal.ofReal (f t ω)) p μ ≤
      p / (p - 1) * eLpNorm ((f⁺) T) p μ := by
  obtain ⟨S, hSc, hST, hS⟩ :=
    TopologicalSpace.exists_countable_subset_Iic_exists_mem_lt (α := ℝ) T
  have hae : (fun ω ↦ ⨆ t ≤ T, ENNReal.ofReal (f t ω)) =ᵐ[μ]
      fun ω ↦ ⨆ t ∈ S, ENNReal.ofReal (f t ω) := by
    filter_upwards [hcont] with ω hω
    refine le_antisymm ?_ (iSup₂_le fun s hs ↦ le_iSup₂_of_le s (hST hs) le_rfl)
    refine iSup₂_le fun t htT ↦ le_of_forall_lt fun a ha ↦ ?_
    have hatop : a ≠ ∞ := ha.ne_top
    rw [← ENNReal.ofReal_toReal hatop, ENNReal.ofReal_lt_ofReal_iff'] at ha
    obtain ⟨s, hs, has⟩ := hS hω htT ha.1
    refine lt_of_lt_of_le ?_ (le_iSup₂ (f := fun s _ ↦ ENNReal.ofReal (f s ω)) s hs)
    rwa [← ENNReal.ofReal_toReal hatop,
      ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg]
  rw [eLpNorm_congr_ae hae]
  exact hf.eLpNorm_biSup_ofReal_le_posPart hSc (fun _ hs ↦ hST hs) hp hp_top

/-- **Doob's continuous-time `Lᵖ` maximal inequality (`eLpNorm` form).** Requires nonnegativity
only at the terminal time `T` (`0 ≤ᵐ[μ] f T`), and no `MemLp` hypothesis. -/
theorem eLpNorm_iSup_ofReal_le
    (hf : Submartingale f ℱ μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ f u ω) (Ioi t) t)
    (hposT : 0 ≤ᵐ[μ] f T) {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞) :
    eLpNorm (fun ω ↦ ⨆ t ≤ T, ENNReal.ofReal (f t ω)) p μ ≤
      p / (p - 1) * eLpNorm (f T) p μ := by
  have hae : (f⁺) T =ᵐ[μ] f T := posPart_ae_eq_of_nonneg hposT
  simpa only [eLpNorm_congr_ae hae] using hf.eLpNorm_iSup_ofReal_le_posPart hcont hp hp_top

/-- **The real running supremum of a right-continuous submartingale belongs to `Lᵖ`** (`1 < p < ∞`)
whenever `(f⁺) T ∈ Lᵖ`. -/
theorem memLp_toReal_iSup_ofReal
    (hf : Submartingale f ℱ μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ f u ω) (Ioi t) t)
    {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞) (hT : MemLp ((f⁺) T) p μ) :
    MemLp (fun ω ↦ (⨆ t ≤ T, ENNReal.ofReal (f t ω)).toReal) p μ := by
  have hY : AEMeasurable (fun ω ↦ ⨆ t ≤ T, ENNReal.ofReal (f t ω)) μ :=
    aemeasurable_iSup_le_ofReal
      (fun t ↦ ((hf.stronglyAdapted t).measurable.mono (ℱ.le t) le_rfl).aemeasurable) hcont
  rw [memLp_iff]
  have heq : eLpNorm (fun ω ↦ (⨆ t ≤ T, ENNReal.ofReal (f t ω)).toReal) p μ =
      eLpNorm (fun ω ↦ ⨆ t ≤ T, ENNReal.ofReal (f t ω)) p μ := by
    refine le_antisymm ?_ ?_
    · exact eLpNorm_mono_eNorm hY.ennreal_toReal.aestronglyMeasurable fun ω ↦ by
        simp [Real.eNorm_eq_ofReal ENNReal.toReal_nonneg, ENNReal.ofReal_toReal_le]
    · refine eLpNorm_mono_eNorm_ae hY.aestronglyMeasurable ?_
      filter_upwards [hf.ae_iSup_ofReal_lt_top hcont] with ω hω
      simp [Real.eNorm_eq_ofReal ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hω.ne]
  rw [heq]
  have hc_lt : p / (p - 1) < ∞ := ENNReal.div_lt_top hp_top (tsub_pos_of_lt hp).ne'
  exact (hf.eLpNorm_iSup_ofReal_le_posPart hcont hp hp_top).trans_lt
    (ENNReal.mul_lt_top hc_lt hT.eLpNorm_lt_top)

/-- **Doob's continuous-time `Lᵖ` maximal inequality (positive-part Bochner moment form).** For
`1 < p < ∞` and `(f⁺) T ∈ Lᵖ`, the `p`-th moment of `(⨆ t ≤ T, ofReal (f t ω)).toReal` is at most
`(p / (p - 1)) ^ p` times the `p`-th moment of `(f⁺) T`. -/
theorem integral_toReal_iSup_ofReal_rpow_le_posPart
    (hf : Submartingale f ℱ μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ f u ω) (Ioi t) t)
    {p : ℝ} (hp : 1 < p) (hT : MemLp ((f⁺) T) (ENNReal.ofReal p) μ) :
    ∫ ω, (⨆ t ≤ T, ENNReal.ofReal (f t ω)).toReal ^ p ∂μ ≤
      (p / (p - 1)) ^ p * ∫ ω, ((f⁺) T ω) ^ p ∂μ := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hp_enn : 1 < ENNReal.ofReal p := by
    rwa [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff hp0]
  have hM := hf.memLp_toReal_iSup_ofReal hcont hp_enn ENNReal.ofReal_ne_top hT
  have hbound := hf.lintegral_iSup_ofReal_rpow_le_posPart hcont hp
  have hlhs : ∫⁻ ω, (⨆ t ≤ T, ENNReal.ofReal (f t ω)) ^ p ∂μ =
      ENNReal.ofReal (∫ ω, (⨆ t ≤ T, ENNReal.ofReal (f t ω)).toReal ^ p ∂μ) :=
    (lintegral_congr_ae ((hf.ae_iSup_ofReal_lt_top hcont).mono fun ω hω ↦
      congrArg (· ^ p) (ENNReal.ofReal_toReal hω.ne).symm)).trans
      (lintegral_ofReal_rpow_eq_ofReal_integral hp0
        (Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg) hM)
  have hrhs : ∫⁻ ω, ENNReal.ofReal ((f⁺) T ω) ^ p ∂μ =
      ENNReal.ofReal (∫ ω, ((f⁺) T ω) ^ p ∂μ) :=
    lintegral_ofReal_rpow_eq_ofReal_integral hp0
      (Eventually.of_forall (apply_posPart_nonneg f T)) hT
  rw [hlhs, hrhs, ENNReal.ofReal_rpow_of_pos (div_pos hp0 (sub_pos.2 hp)),
    ← ENNReal.ofReal_mul (by positivity)] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (by positivity) (integral_nonneg fun ω ↦
      Real.rpow_nonneg (apply_posPart_nonneg f T ω) _))).1 hbound

/-- **Doob's continuous-time `Lᵖ` maximal inequality (Bochner moment form).** Requires
nonnegativity and `MemLp` only at the terminal time `T`. -/
theorem integral_toReal_iSup_ofReal_rpow_le
    (hf : Submartingale f ℱ μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ f u ω) (Ioi t) t)
    (hposT : 0 ≤ᵐ[μ] f T) {p : ℝ} (hp : 1 < p) (hT : MemLp (f T) (ENNReal.ofReal p) μ) :
    ∫ ω, (⨆ t ≤ T, ENNReal.ofReal (f t ω)).toReal ^ p ∂μ ≤
      (p / (p - 1)) ^ p * ∫ ω, f T ω ^ p ∂μ := by
  have hae : (f⁺) T =ᵐ[μ] f T := posPart_ae_eq_of_nonneg hposT
  have hcongr : ∫ ω, ((f⁺) T ω) ^ p ∂μ = ∫ ω, f T ω ^ p ∂μ :=
    integral_congr_ae (hae.mono fun _ hω ↦ congrArg (· ^ p) hω)
  rw [← hcongr]
  exact hf.integral_toReal_iSup_ofReal_rpow_le_posPart hcont hp (hT.ae_eq hae.symm)

end ContinuousTimeStrongLp

end MeasureTheory.Submartingale

/-! ### Banach-valued martingales -/

namespace MeasureTheory.Martingale

variable {Ω E ι : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

section DiscreteTime

variable [IsFiniteMeasure μ] {ℱ : Filtration ℕ mΩ} {X : ℕ → Ω → E}

/-- **Doob's discrete-time `Lᵖ` maximal inequality for Banach-valued martingales (`eLpNorm` form).**
No `MemLp` assumption is needed. -/
theorem eLpNorm_partialSups_norm_le
    (hX : Martingale X ℱ μ) (n : ℕ) {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞) :
    eLpNorm (partialSups (fun k ω ↦ ‖X k ω‖) n) p μ ≤ p / (p - 1) * eLpNorm (X n) p μ := by
  rw [← eLpNorm_norm (X n) ((hX.stronglyAdapted n).mono (ℱ.le n)).aestronglyMeasurable]
  exact hX.norm.eLpNorm_partialSups_le (fun _ _ ↦ Eventually.of_forall fun _ ↦ norm_nonneg _)
    hp hp_top

/-- **Doob's discrete-time `Lᵖ` maximal inequality for Banach-valued martingales (Bochner moment
form).** Directly generalizes `MeasureTheory.Martingale.integral_sq_partialSups_norm_le` from
`p = 2` to all `1 < p < ∞`, requiring `MemLp` only at the terminal step `n`. -/
theorem integral_rpow_partialSups_norm_le
    (hX : Martingale X ℱ μ) (n : ℕ) {p : ℝ} (hp : 1 < p)
    (hn : MemLp (X n) (ENNReal.ofReal p) μ) :
    ∫ ω, (partialSups (fun k ω ↦ ‖X k ω‖) n ω) ^ p ∂μ ≤
      (p / (p - 1)) ^ p * ∫ ω, ‖X n ω‖ ^ p ∂μ :=
  hX.norm.integral_rpow_partialSups_le (fun _ _ ↦ Eventually.of_forall fun _ ↦ norm_nonneg _)
    hp hn.norm

end DiscreteTime

section CountableTime

variable [LinearOrder ι] [IsFiniteMeasure μ] {ℱ : Filtration ι mΩ} {M : ι → Ω → E}

/-- **Doob's `Lᵖ` maximal inequality on a countable set for Banach-valued martingales.** -/
theorem eLpNorm_biSup_enorm_le
    (hM : Martingale M ℱ μ) {S : Set ι} (hS : S.Countable) {T : ι} (hST : ∀ t ∈ S, t ≤ T)
    {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞) :
    eLpNorm (fun ω ↦ ⨆ t ∈ S, ‖M t ω‖ₑ) p μ ≤ p / (p - 1) * eLpNorm (M T) p μ := by
  simp_rw [← ofReal_norm]
  rw [← eLpNorm_norm (M T) ((hM.stronglyAdapted T).mono (ℱ.le T)).aestronglyMeasurable]
  exact hM.norm.eLpNorm_biSup_ofReal_le hS hST
    (Eventually.of_forall fun _ ↦ norm_nonneg _) hp hp_top

end CountableTime

section ContinuousTime

variable [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι]
  [IsFiniteMeasure μ] {ℱ : Filtration ι mΩ} {M : ι → Ω → E}

omit [IsFiniteMeasure μ] in
/-- **Almost everywhere measurability of the running extended norm of a right-continuous
martingale.** -/
theorem aemeasurable_iSup_enorm
    (hM : Martingale M ℱ μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ M u ω) (Ioi t) t) :
    AEMeasurable (fun ω ↦ ⨆ t ≤ T, ‖M t ω‖ₑ) μ := by
  simp_rw [← ofReal_norm]
  exact aemeasurable_iSup_le_ofReal
    (fun t ↦ ((hM.norm.stronglyAdapted t).measurable.mono (ℱ.le t) le_rfl).aemeasurable)
    (hcont.mono fun ω hω t ht ↦ (hω t ht).norm)

/-- **Almost sure finiteness of the running norm supremum of a right-continuous martingale.** No
`MemLp` assumption beyond martingale integrability is needed. -/
theorem ae_iSup_enorm_lt_top
    (hM : Martingale M ℱ μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ M u ω) (Ioi t) t) :
    ∀ᵐ ω ∂μ, (⨆ t ≤ T, ‖M t ω‖ₑ) < ∞ := by
  simp_rw [← ofReal_norm]
  exact hM.norm.ae_iSup_ofReal_lt_top (hcont.mono fun ω hω t ht ↦ (hω t ht).norm)

/-- **Unconditional event-refined `Lᵖ` Doob inequality for Banach-valued martingales
(lower-integral form).** Holds for all `1 ≤ p < ∞` and `ε : ℝ≥0` with no `MemLp` hypothesis. -/
theorem rpow_mul_measure_le_iSup_enorm_le_setLIntegral
    (hM : Martingale M ℱ μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ M u ω) (Ioi t) t)
    (ε : ℝ≥0) {p : ℝ} (hp : 1 ≤ p) :
    (ε : ℝ≥0∞) ^ p * μ {ω | (ε : ℝ≥0∞) ≤ ⨆ t ≤ T, ‖M t ω‖ₑ} ≤
      ∫⁻ ω in {ω | (ε : ℝ≥0∞) ≤ ⨆ t ≤ T, ‖M t ω‖ₑ}, ‖M T ω‖ₑ ^ p ∂μ := by
  simp_rw [← ofReal_norm]
  have h := hM.norm.rpow_mul_measure_le_iSup_le_setLIntegral_posPart
    (hcont.mono fun ω hω t ht ↦ (hω t ht).norm) ε hp
  have hpos (ω : Ω) : ENNReal.ofReal (((fun t ω' ↦ ‖M t ω'‖)⁺) T ω) = ENNReal.ofReal ‖M T ω‖ :=
    Submartingale.ofReal_posPart_eq ‖M T ω‖
  simpa only [hpos] using h

/-- **Event-refined `Lᵖ` Doob inequality for Banach-valued martingales (Bochner form).** Requires
`MemLp` only at the terminal time `T`. -/
theorem rpow_mul_measure_le_iSup_enorm_le_setIntegral
    (hM : Martingale M ℱ μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ M u ω) (Ioi t) t)
    (ε : ℝ≥0) {p : ℝ} (hp : 1 ≤ p) (hT : MemLp (M T) (ENNReal.ofReal p) μ) :
    (ε : ℝ≥0∞) ^ p * μ {ω | (ε : ℝ≥0∞) ≤ ⨆ t ≤ T, ‖M t ω‖ₑ} ≤
      ENNReal.ofReal (∫ ω in {ω | (ε : ℝ≥0∞) ≤ ⨆ t ≤ T, ‖M t ω‖ₑ}, ‖M T ω‖ ^ p ∂μ) := by
  simp_rw [← ofReal_norm]
  exact hM.norm.rpow_mul_measure_le_iSup_le_setIntegral
    (hcont.mono fun ω hω t ht ↦ (hω t ht).norm) (Eventually.of_forall fun _ ↦ norm_nonneg _)
    ε hp hT.norm

/-- **Doob's continuous-time `Lᵖ` maximal inequality for Banach-valued martingales (lower-integral
form).** Holds for all `1 < p < ∞` with no `MemLp` hypothesis. -/
theorem lintegral_iSup_enorm_rpow_le
    (hM : Martingale M ℱ μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ M u ω) (Ioi t) t)
    {p : ℝ} (hp : 1 < p) :
    ∫⁻ ω, (⨆ t ≤ T, ‖M t ω‖ₑ) ^ p ∂μ ≤
      ENNReal.ofReal (p / (p - 1)) ^ p * ∫⁻ ω, ‖M T ω‖ₑ ^ p ∂μ := by
  simp_rw [← ofReal_norm]
  have h := hM.norm.lintegral_iSup_ofReal_rpow_le_posPart
    (hcont.mono fun ω hω t ht ↦ (hω t ht).norm) hp
  have hpos (ω : Ω) : ENNReal.ofReal (((fun t ω' ↦ ‖M t ω'‖)⁺) T ω) = ENNReal.ofReal ‖M T ω‖ :=
    Submartingale.ofReal_posPart_eq ‖M T ω‖
  simpa only [hpos] using h

/-- **Doob's continuous-time `Lᵖ` maximal inequality for Banach-valued martingales (`eLpNorm`
form).** Holds for all `1 < p < ∞` in `ℝ≥0∞` with no `MemLp` hypothesis. -/
theorem eLpNorm_iSup_enorm_le
    (hM : Martingale M ℱ μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ M u ω) (Ioi t) t)
    {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞) :
    eLpNorm (fun ω ↦ ⨆ t ≤ T, ‖M t ω‖ₑ) p μ ≤ p / (p - 1) * eLpNorm (M T) p μ := by
  simp_rw [← ofReal_norm]
  rw [← eLpNorm_norm (M T) ((hM.stronglyAdapted T).mono (ℱ.le T)).aestronglyMeasurable]
  exact hM.norm.eLpNorm_iSup_ofReal_le
    (hcont.mono fun ω hω t ht ↦ (hω t ht).norm) (Eventually.of_forall fun _ ↦ norm_nonneg _)
    hp hp_top

/-- **The real running norm supremum of a right-continuous martingale belongs to `Lᵖ`**
(`1 < p < ∞`) whenever `M T ∈ Lᵖ`. -/
theorem memLp_toReal_iSup_enorm
    (hM : Martingale M ℱ μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ M u ω) (Ioi t) t)
    {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞) (hT : MemLp (M T) p μ) :
    MemLp (fun ω ↦ (⨆ t ≤ T, ‖M t ω‖ₑ).toReal) p μ := by
  have hpos : ((fun t ω ↦ ‖M t ω‖)⁺) T = fun ω ↦ ‖M T ω‖ := by
    ext ω
    change max ‖M T ω‖ 0 = ‖M T ω‖
    exact max_eq_left (norm_nonneg _)
  simp_rw [← ofReal_norm]
  exact hM.norm.memLp_toReal_iSup_ofReal
    (hcont.mono fun ω hω t ht ↦ (hω t ht).norm) hp hp_top (by rw [hpos]; exact hT.norm)

/-- **Doob's continuous-time `Lᵖ` maximal inequality for Banach-valued martingales (Bochner moment
form).** Requires `MemLp` only at the terminal time `T`. -/
theorem integral_toReal_iSup_enorm_rpow_le
    (hM : Martingale M ℱ μ) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ M u ω) (Ioi t) t)
    {p : ℝ} (hp : 1 < p) (hT : MemLp (M T) (ENNReal.ofReal p) μ) :
    ∫ ω, (⨆ t ≤ T, ‖M t ω‖ₑ).toReal ^ p ∂μ ≤
      (p / (p - 1)) ^ p * ∫ ω, ‖M T ω‖ ^ p ∂μ := by
  simp_rw [← ofReal_norm]
  exact hM.norm.integral_toReal_iSup_ofReal_rpow_le
    (hcont.mono fun ω hω t ht ↦ (hω t ht).norm) (Eventually.of_forall fun _ ↦ norm_nonneg _)
    hp hT.norm

/-- **Uniform `Lᵖ` path convergence from terminal `Lᵖ` convergence (`1 < p < ∞`).** For
right-continuous Banach-valued martingales before `T`, convergence of `M n T → Y T` in `Lᵖ` implies
`Lᵖ` convergence of the uniform running error `⨆ t ≤ T, ‖M n t ω - Y t ω‖ₑ` to `0`. -/
theorem tendsto_eLpNorm_iSup_enorm_sub {α : Type*} {Y : ι → Ω → E}
    (hY : Martingale Y ℱ μ) {M : α → ι → Ω → E} (hM : ∀ n, Martingale (M n) ℱ μ)
    {T : ι} {l : Filter α}
    (hYcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ Y u ω) (Ioi t) t)
    (hMcont : ∀ n, ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ M n u ω) (Ioi t) t)
    {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞)
    (hlim : Tendsto (fun n ↦ eLpNorm (M n T - Y T) p μ) l (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm (fun ω ↦ ⨆ t ≤ T, ‖M n t ω - Y t ω‖ₑ) p μ) l (𝓝 0) := by
  have hc_ne : p / (p - 1) ≠ ∞ := (ENNReal.div_lt_top hp_top (tsub_pos_of_lt hp).ne').ne
  have hbound (n : α) :
      eLpNorm (fun ω ↦ ⨆ t ≤ T, ‖M n t ω - Y t ω‖ₑ) p μ ≤
        p / (p - 1) * eLpNorm (M n T - Y T) p μ := by
    have hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ (M n - Y) u ω) (Ioi t) t := by
      filter_upwards [hMcont n, hYcont] with ω h₁ h₂ t ht
      exact (h₁ t ht).sub (h₂ t ht)
    simpa only [Pi.sub_apply] using ((hM n).sub hY).eLpNorm_iSup_enorm_le hcont hp hp_top
  have hmul : Tendsto (fun n ↦ p / (p - 1) * eLpNorm (M n T - Y T) p μ) l (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hlim (.inr hc_ne)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmul
    (fun _ ↦ zero_le) hbound

end ContinuousTime

end MeasureTheory.Martingale
