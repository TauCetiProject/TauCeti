/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Martingale.Basic
public import TauCeti.Probability.Process.Filtration.Comp
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# Martingale closure properties, division by a process, norms, and submartingale bounds

`MeasureTheory.StronglyAdapted.martingale_iff_setIntegral_eq` characterizes martingales
among adapted integrable processes by equality of set integrals at two dates. This is useful
for transporting martingales between measures without comparing conditional-expectation
representatives.

Closure properties of martingales, including building blocks of the elementary stochastic
integral:

* multiplying a martingale by a random scalar measurable at every time preserves the
  martingale property when the products are integrable, in particular for bounded scalars
  (`MeasureTheory.Martingale.smul_of_stronglyMeasurable`, `MeasureTheory.Martingale.bdd_smul`);
* restricting a martingale to an event measurable at every time preserves the martingale
  property (`MeasureTheory.Martingale.indicator`);
* a martingale `X` with values in a Banach space, frozen at a fixed date `w`, `t ↦ X (min w t)`,
  is a martingale (`MeasureTheory.Martingale.const_min`);
* if a real martingale `Y` vanishes up to a date `r`, then multiplying it by a random variable
  known at time `r` gives a martingale, provided every product is integrable, as it is for a
  bounded multiplier (`MeasureTheory.Martingale.mul_left_of_eq_zero`).

Together they show that a position chosen at `r`, times the change of a martingale over
`(r, r']`, is a martingale whenever this product is integrable at every time.

The following results need only a preordered time index. Sampling along a monotone time map
preserves martingales, supermartingales, and submartingales with respect to the sampled
filtration (`MeasureTheory.Martingale.comp`, `MeasureTheory.Supermartingale.comp`, and
`MeasureTheory.Submartingale.comp`). The norm of a Banach-valued
martingale is a submartingale (`MeasureTheory.Martingale.norm`). A square-integrable real
martingale has conditional square equal to its current square plus the conditional square
of its future increment (`MeasureTheory.Martingale.condExp_sq`). For a real submartingale,
multiplication by a nonnegative position known at an earlier date preserves the expectation
inequality when both products are integrable (`MeasureTheory.Submartingale.integral_mul_le`).
In particular, positions need not be bounded. Nonnegative submartingale values inherit Lᵖ
integrability from later values for `p ≥ 1` (`MeasureTheory.Submartingale.memLp_of_le`).

If `V / N` is a martingale under `Q` for a real process `N`, then `V` is recovered from its value
at a later date `j` as `V i = N i * Q[V j / N j | ℱ i]` wherever `N i` does not vanish
(`MeasureTheory.Martingale.ae_eq_mul_condExp_div`), so two such processes agreeing at `j` agree at
every earlier date (`MeasureTheory.Martingale.ae_eq_of_ae_eq_of_div`). In finance `N` is a
numeraire, the first statement is the conditional pricing formula and the second the law of one
price.
-/

public section

noncomputable section

open Filter
open scoped ENNReal

namespace MeasureTheory

section Sampling

variable {Ω ι κ E : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
  [Preorder ι] [Preorder κ] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ℱ : Filtration ι m} {X : ι → Ω → E} {τ : κ → ι}

/-- Sampling a martingale along a monotone map gives a martingale. -/
theorem Martingale.comp (hX : Martingale X ℱ μ) (hτ : Monotone τ) :
    Martingale (fun n ↦ X (τ n)) (ℱ.comp hτ) μ := by
  refine ⟨hX.stronglyAdapted.comp hτ, fun i j hij ↦ ?_⟩
  simpa only [Filtration.comp_apply] using hX.condExp_ae_eq (hτ hij)

/-- Sampling a supermartingale along a monotone map gives a supermartingale. -/
theorem Supermartingale.comp [LE E] (hX : Supermartingale X ℱ μ) (hτ : Monotone τ) :
    Supermartingale (fun n ↦ X (τ n)) (ℱ.comp hτ) μ := by
  refine ⟨hX.stronglyAdapted.comp hτ, fun i j hij ↦ ?_, fun i ↦ hX.integrable (τ i)⟩
  simpa only [Filtration.comp_apply] using hX.condExp_ae_le (hτ hij)

/-- Sampling a submartingale along a monotone map gives a submartingale. -/
theorem Submartingale.comp [LE E] (hX : Submartingale X ℱ μ) (hτ : Monotone τ) :
    Submartingale (fun n ↦ X (τ n)) (ℱ.comp hτ) μ := by
  refine ⟨hX.stronglyAdapted.comp hτ, fun i j hij ↦ ?_, fun i ↦ hX.integrable (τ i)⟩
  simpa only [Filtration.comp_apply] using hX.ae_le_condExp (hτ hij)

end Sampling

/-- An adapted integrable process is a martingale exactly when its integrals on every
event known at an earlier date are unchanged between the two dates. -/
theorem StronglyAdapted.martingale_iff_setIntegral_eq {Ω ι E : Type*}
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [Preorder ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {ℱ : Filtration ι mΩ} [SigmaFiniteFiltration μ ℱ] {X : ι → Ω → E}
    (hX : StronglyAdapted ℱ X) (hint : ∀ t, Integrable (X t) μ) :
    Martingale X ℱ μ ↔ ∀ s t, s ≤ t → ∀ A, MeasurableSet[ℱ s] A →
      ∫ ω in A, X s ω ∂μ = ∫ ω in A, X t ω ∂μ := by
  refine ⟨fun h s t hst A hA ↦ h.setIntegral_eq hst hA, fun h ↦ ⟨hX, ?_⟩⟩
  intro s t hst
  exact (ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le s) (hint t)
    (fun _ _ _ ↦ (hint s).integrableOn) (fun A hA _ ↦ h s t hst A hA)
    (hX s).aestronglyMeasurable).symm

section Div

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P Q : Measure Ω} [Preorder ι]
  {ℱ : Filtration ι mΩ} {V V' N : ι → Ω → ℝ} {i j : ι}

/-- If `V / N` is a martingale under a measure `Q` with `P ≪ Q`, then `V` is determined by its
value at a later date `j`: at every date `i ≤ j` at which `N` does not vanish,
`V_i = N_i E_Q[V_j / N_j | ℱ_i]`, `P`-almost surely. For the wealth `V` of a strategy and a
numeraire `N`, this is the conditional pricing formula. -/
theorem Martingale.ae_eq_mul_condExp_div (hV : Martingale (V / N) ℱ Q) (hPQ : P ≪ Q)
    (hN : ∀ᵐ ω ∂P, N i ω ≠ 0) (hij : i ≤ j) :
    V i =ᵐ[P] N i * Q[V j / N j | ℱ i] := by
  filter_upwards [hPQ.ae_le (hV.condExp_ae_eq hij), hN] with ω hω hNω
  simp only [Pi.mul_apply, Pi.div_apply] at hω ⊢
  rw [hω]
  field_simp

/-- If `V / N` and `V' / N` are martingales under a measure `Q` equivalent to `P`, and `V` and
`V'` agree at a date `j`, then they agree at every earlier date `i` at which `N` does not
vanish. For the wealth of two strategies and a common numeraire `N`, this is the law of one
price: in particular the two strategies have the same initial cost. -/
theorem Martingale.ae_eq_of_ae_eq_of_div (hV : Martingale (V / N) ℱ Q)
    (hV' : Martingale (V' / N) ℱ Q) (hPQ : P ≪ Q) (hQP : Q ≪ P) (hN : ∀ᵐ ω ∂P, N i ω ≠ 0)
    (hij : i ≤ j) (hj : V j =ᵐ[P] V' j) : V i =ᵐ[P] V' i := by
  have hcond : Q[V j / N j | ℱ i] =ᵐ[Q] Q[V' j / N j | ℱ i] := by
    refine condExp_congr_ae ?_
    filter_upwards [hQP.ae_le hj] with ω hω
    simp only [Pi.div_apply, hω]
  filter_upwards [hV.ae_eq_mul_condExp_div hPQ hN hij, hV'.ae_eq_mul_condExp_div hPQ hN hij,
    hPQ.ae_le hcond] with ω h₁ h₂ h₃
  rw [h₁, h₂, Pi.mul_apply, Pi.mul_apply, h₃]

end Div

/-- Restricting a martingale to an event measurable at every time preserves the martingale
property. In particular, for an index with a bottom element it suffices that the event be
measurable at the bottom time. -/
theorem Martingale.indicator {Ω ι E : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    [Preorder ι] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {ℱ : Filtration ι m} {X : ι → Ω → E} (hX : Martingale X ℱ μ) {s : Set Ω}
    (hs : ∀ t, MeasurableSet[ℱ t] s) :
    Martingale (fun t ↦ s.indicator (X t)) ℱ μ := by
  refine ⟨fun t ↦ (hX.stronglyMeasurable t).indicator (hs t), fun i j hij ↦ ?_⟩
  exact (condExp_indicator (hX.integrable j) (hs i)).trans (hX.condExp_ae_eq hij).indicator

section NormAndMultipliers

variable {Ω ι E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [Preorder ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ℱ : Filtration ι mΩ} {X : ι → Ω → E} {Y : ι → Ω → ℝ}

/-- Multiplication by a random real scalar measurable at every time preserves a martingale
whenever all the products are integrable. No sigma-finiteness assumption is needed. -/
theorem Martingale.smul_of_stronglyMeasurable (hX : Martingale X ℱ μ) {c : Ω → ℝ}
    (hc : ∀ t, StronglyMeasurable[ℱ t] c)
    (hint : ∀ t, Integrable (fun ω ↦ c ω • X t ω) μ) :
    Martingale (fun t ω ↦ c ω • X t ω) ℱ μ := by
  refine ⟨fun t ↦ (hc t).smul (hX.stronglyMeasurable t), fun s t hst ↦ ?_⟩
  exact (condExp_smul_of_aestronglyMeasurable_left (hc s).aestronglyMeasurable
    (hint t) (hX.integrable t)).trans
      ((hX.condExp_ae_eq hst).mono fun ω hω ↦ by simp only [Pi.smul_apply', hω])

/-- An almost surely bounded random real scalar measurable at every time preserves
Banach-valued martingales. -/
theorem Martingale.bdd_smul (hX : Martingale X ℱ μ) {c : Ω → ℝ}
    (hc : ∀ t, StronglyMeasurable[ℱ t] c) (C : ℝ) (hbound : ∀ᵐ ω ∂μ, ‖c ω‖ ≤ C) :
    Martingale (fun t ω ↦ c ω • X t ω) ℱ μ := by
  apply hX.smul_of_stronglyMeasurable hc
  intro t
  exact (hX.integrable t).bdd_smul C ((hc t).mono (ℱ.le t)).aestronglyMeasurable hbound

/-- The norm of a Banach-valued martingale is a submartingale. -/
theorem Martingale.norm (hX : Martingale X ℱ μ) :
    Submartingale (fun t ω => ‖X t ω‖) ℱ μ := by
  refine ⟨fun t => (hX.stronglyAdapted t).norm, fun s t hst => ?_,
    fun t => (hX.integrable t).norm⟩
  filter_upwards [hX.condExp_ae_eq hst, norm_condExp_le (m := ℱ s) (X t)] with ω he hle
  simpa only [he] using hle

/-- The conditional square of a square-integrable real martingale value is
the current square plus the conditional square of the future increment. -/
theorem Martingale.condExp_sq (hY : Martingale Y ℱ μ) {i j : ι}
    (hij : i ≤ j) (hj : MemLp (Y j) 2 μ) :
    μ[fun ω ↦ Y j ω ^ 2 | ℱ i] =ᵐ[μ]
      fun ω ↦ Y i ω ^ 2 + μ[fun ω ↦ (Y j ω - Y i ω) ^ 2 | ℱ i] ω := by
  have hc := hY.condExp_ae_eq hij
  by_cases hμ : SigmaFinite (μ.trim (ℱ.le i))
  · have hi := (hj.condExp (m := ℱ i) one_le_two).ae_eq hc
    have hmul : Integrable (Y i * Y j) μ := memLp_one_iff_integrable.mp (hi.mul hj)
    have hexpand : (fun ω ↦ (Y j ω - Y i ω) ^ 2) =
        (Y j) ^ 2 - (2 : ℝ) • (Y i * Y j) + (Y i) ^ 2 := by
      ext ω
      simp only [Pi.sub_apply, Pi.add_apply, Pi.pow_apply, Pi.smul_apply, smul_eq_mul,
        Pi.mul_apply]
      ring
    rw [hexpand]
    filter_upwards [condExp_add (m := ℱ i) (hj.integrable_sq.sub (hmul.const_mul 2))
        hi.integrable_sq,
      condExp_sub (m := ℱ i) hj.integrable_sq (hmul.const_mul 2),
      condExp_smul (m := ℱ i) (2 : ℝ) (Y i * Y j),
      condExp_mul_of_stronglyMeasurable_left (hY.stronglyAdapted i) hmul (hY.integrable j),
      hc] with ω hadd hsub hscale hpull hmart
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Pi.mul_apply, Pi.pow_def, Pi.smul_def, Pi.mul_def] at hadd hsub hscale hpull ⊢
    rw [hadd, hsub, hscale, hpull, hmart,
      condExp_of_stronglyMeasurable (f := fun ω ↦ Y i ω ^ 2)
        (ℱ.le i) ((hY.stronglyAdapted i).pow 2)
        hi.integrable_sq]
    ring
  · simp only [condExp_of_not_sigmaFinite (ℱ.le i) hμ, Pi.zero_apply] at hc ⊢
    filter_upwards [hc] with ω hω
    simp [← hω]

/-- A nonnegative position known at time `i` preserves a submartingale's expectation inequality
between `i` and `j`, provided its products with both values are integrable. -/
theorem Submartingale.integral_mul_le [SigmaFiniteFiltration μ ℱ]
    (hY : Submartingale Y ℱ μ) {i j : ι} (hij : i ≤ j) {a : Ω → ℝ}
    (ha : StronglyMeasurable[ℱ i] a) (hpos : 0 ≤ᵐ[μ] a)
    (hi : Integrable (a * Y i) μ) (hj : Integrable (a * Y j) μ) :
    ∫ ω, a ω * Y i ω ∂μ ≤ ∫ ω, a ω * Y j ω ∂μ := by
  have he := condExp_mul_of_stronglyMeasurable_left ha hj (hY.integrable j)
  calc
    _ ≤ ∫ ω, (a * μ[Y j | ℱ i]) ω ∂μ := by
      apply integral_mono_ae hi (integrable_condExp.congr he)
      filter_upwards [hpos, hY.ae_le_condExp hij] with ω hp hle
      exact mul_le_mul_of_nonneg_left hle hp
    _ = ∫ ω, μ[a * Y j | ℱ i] ω ∂μ := integral_congr_ae he.symm
    _ = _ := integral_condExp (ℱ.le i)

/-- A nonnegative submartingale value inherits Lᵖ integrability from a later value,
for every `p ≥ 1`. Only the earlier value needs to be nonnegative. -/
theorem Submartingale.memLp_of_le (hY : Submartingale Y ℱ μ) {i j : ι} (hij : i ≤ j)
    (hpos : 0 ≤ᵐ[μ] Y i) {p : ℝ≥0∞} (hp : 1 ≤ p) (hj : MemLp (Y j) p μ) :
    MemLp (Y i) p μ := by
  apply (MemLp.condExp (m := ℱ i) hp hj).mono'
    ((hY.stronglyAdapted i).mono (ℱ.le i)).aestronglyMeasurable
  filter_upwards [hpos, hY.ae_le_condExp hij] with ω hposω hω
  simpa only [Real.norm_eq_abs, abs_of_nonneg hposω] using hω

end NormAndMultipliers

variable {Ω ι E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [LinearOrder ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ℱ : Filtration ι mΩ} {X : ι → Ω → E} {Y : ι → Ω → ℝ}

omit [CompleteSpace E] in
/-- A martingale frozen at a fixed date `w`, `t ↦ X (min w t)`, is a martingale. -/
theorem Martingale.const_min [SigmaFiniteFiltration μ ℱ] (hX : Martingale X ℱ μ) (w : ι) :
    Martingale (fun t ↦ X (min w t)) ℱ μ := by
  -- `X w` is integrable: otherwise its conditional expectation would vanish, forcing `X w = 0`
  have hint : Integrable (X w) μ := by
    by_contra h
    have h0 := hX.condExp_ae_eq (le_refl w)
    rw [condExp_of_not_integrable h] at h0
    exact h ((integrable_zero _ _ _).congr h0)
  refine ⟨fun t ↦ hX.stronglyAdapted.stronglyMeasurable_le (min_le_right _ _),
    fun s t hst ↦ ?_⟩
  beta_reduce
  rcases le_or_gt w s with hws | hsw
  · rw [min_eq_left (hws.trans hst), min_eq_left hws,
      condExp_of_stronglyMeasurable (ℱ.le s) ((hX.stronglyAdapted w).mono (ℱ.mono hws))
        hint]
  · rw [min_eq_right hsw.le]
    exact hX.condExp_ae_eq (le_min hsw.le hst)

/-- If a martingale `Y` vanishes up to a date `r`, and `a` is a random variable known at time `r`
such that every product `a * Y t` is integrable, then `t ↦ a * Y t` is a martingale. -/
theorem Martingale.mul_left_of_eq_zero [SigmaFiniteFiltration μ ℱ] {a : Ω → ℝ} {r : ι}
    (hY : Martingale Y ℱ μ) (hY₀ : ∀ t ≤ r, Y t = 0) (ha : StronglyMeasurable[ℱ r] a)
    (hmul : ∀ t, Integrable (a * Y t) μ) : Martingale (fun t ↦ a * Y t) ℱ μ := by
  -- Once `a` is known, it factors out of the conditional expectation.
  have hlate : ∀ s t, r ≤ s → s ≤ t → μ[a * Y t | ℱ s] =ᵐ[μ] a * Y s := fun s t hrs hst ↦
    (condExp_mul_of_stronglyMeasurable_left (ha.mono (ℱ.mono hrs)) (hmul t)
      (hY.integrable t)).trans ((EventuallyEq.refl _ _).mul (hY.condExp_ae_eq hst))
  refine ⟨fun t ↦ ?_, fun s t hst ↦ ?_⟩
  · rcases le_or_gt r t with hrt | htr
    · exact (ha.mono (ℱ.mono hrt)).mul (hY.stronglyMeasurable t)
    · simp only [hY₀ t htr.le, mul_zero]
      exact stronglyMeasurable_zero
  beta_reduce
  rcases le_or_gt r s with hrs | hsr
  · exact hlate s t hrs hst
  rw [hY₀ s hsr.le, mul_zero]
  rcases le_or_gt t r with htr | hrt
  · rw [hY₀ t htr, mul_zero, condExp_zero]
  -- Otherwise condition first on the information at `r`, where `Y` still vanishes.
  calc μ[a * Y t | ℱ s]
      =ᵐ[μ] μ[μ[a * Y t | ℱ r] | ℱ s] :=
        (condExp_condExp_of_le (ℱ.mono hsr.le) (ℱ.le r)).symm
    _ =ᵐ[μ] μ[a * Y r | ℱ s] := condExp_congr_ae (hlate r t le_rfl hrt.le)
    _ = 0 := by rw [hY₀ r le_rfl, mul_zero, condExp_zero]

end MeasureTheory
