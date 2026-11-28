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
import TauCeti.Probability.Moments.CondVar

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
`(r, r']`, is a martingale whenever this product is integrable at every time. Over any event
`S ∈ ℱ s`, a real martingale increment is orthogonal to any `ℱ s`-measurable Banach-valued
multiplier (`MeasureTheory.Martingale.setIntegral_sub_smul_eq_zero`), and the same holds for a
compensated squared increment `(Y t - Y s) ^ 2 - (A t - A s)` when `Y ^ 2 - A` is also a martingale
(`MeasureTheory.Martingale.setIntegral_sq_sub_smul_eq_zero`).

The following results need only a preordered time index. Sampling along a monotone time map
preserves martingales, supermartingales, and submartingales with respect to the sampled
filtration (`MeasureTheory.Martingale.comp`, `MeasureTheory.Supermartingale.comp`, and
`MeasureTheory.Submartingale.comp`). The norm of a Banach-valued
martingale is a submartingale (`MeasureTheory.Martingale.norm`), and raising an almost everywhere
nonnegative real submartingale — in particular the norm of a Banach-valued martingale — to an
integrable power `p ≥ 1` gives a submartingale (`MeasureTheory.Submartingale.rpow` and
`MeasureTheory.Martingale.norm_rpow`). A square-integrable real
martingale has conditional square equal to its current square plus the conditional square
of its future increment (`MeasureTheory.Martingale.condExp_sq`). For a real submartingale,
multiplication by a nonnegative position known at an earlier date preserves the expectation
inequality when both products are integrable (`MeasureTheory.Submartingale.integral_mul_le`).
In particular, positions need not be bounded. A predictable height times a later martingale
increment has mean zero when the product is integrable
(`MeasureTheory.Martingale.integral_mul_sub_eq_zero`), with a Banach-valued scalar-action form
`MeasureTheory.Martingale.integral_smul_sub_eq_zero`. Martingale values inherit deterministic
norm bounds and, for `p ≥ 1`, Lᵖ integrability from later values
(`MeasureTheory.Martingale.ae_norm_le_of_le`, `MeasureTheory.Martingale.memLp_of_le`).
A martingale value vanishes a.e. at any date whose filtration trim is not sigma-finite
(`MeasureTheory.Martingale.ae_eq_zero_of_not_sigmaFinite`).
Shorter increments with the same starting date inherit deterministic norm bounds
(`MeasureTheory.Martingale.ae_norm_sub_le_of_le`), whereas increments over any contained interval
inherit Lᵖ integrability for `p ≥ 1` from the containing increment
(`MeasureTheory.Martingale.memLp_sub_of_le`).
Nonnegative submartingale values inherit Lᵖ
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

/-- A martingale value inherits Lᵖ integrability from a later value for `p ≥ 1`. -/
theorem Martingale.memLp_of_le (hX : Martingale X ℱ μ) {i j : ι} (hij : i ≤ j)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hj : MemLp (X j) p μ) : MemLp (X i) p μ :=
  (hj.condExp (m := ℱ i) hp).ae_eq (hX.condExp_ae_eq hij)

omit [CompleteSpace E] in
/-- A martingale value vanishes almost everywhere if the measure trimmed to the filtration at
that date is not sigma-finite. -/
theorem Martingale.ae_eq_zero_of_not_sigmaFinite (hX : Martingale X ℱ μ) {i : ι}
    (hi : ¬SigmaFinite (μ.trim (ℱ.le i))) : X i =ᵐ[μ] 0 := by
  simpa only [condExp_of_not_sigmaFinite (ℱ.le i) hi] using
    (hX.condExp_ae_eq (i := i) le_rfl).symm

/-- Conditioning a martingale increment on an intermediate date keeps its past part. -/
theorem Martingale.condExp_sub_ae_eq (hX : Martingale X ℱ μ) {s t u : ι}
    (hst : s ≤ t) (htu : t ≤ u) : μ[X u - X s | ℱ t] =ᵐ[μ] X t - X s := by
  have hs : μ[X s | ℱ t] =ᵐ[μ] X s := by
    by_cases ht : SigmaFinite (μ.trim (ℱ.le t))
    · exact EventuallyEq.of_eq (condExp_of_stronglyMeasurable (ℱ.le t)
        ((hX.stronglyMeasurable s).mono (ℱ.mono hst)) (hX.integrable s))
    · have hs : ¬SigmaFinite (μ.trim (ℱ.le s)) := fun hs ↦
        ht (sigmaFiniteTrim_mono (ℱ.le t) (ℱ.mono hst))
      rw [condExp_of_not_sigmaFinite (ℱ.le t) ht]
      exact (hX.ae_eq_zero_of_not_sigmaFinite hs).symm
  exact (condExp_sub (hX.integrable u) (hX.integrable s) _).trans
    ((hX.condExp_ae_eq htu).sub hs)

/-- A martingale increment inherits Lᵖ integrability from an increment over a containing
interval, for `p ≥ 1`. The initial value need only be integrable. -/
theorem Martingale.memLp_sub_of_le (hX : Martingale X ℱ μ) {s t u v : ι}
    (hst : s ≤ t) (htu : t ≤ u) (huv : u ≤ v) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hv : MemLp (X v - X s) p μ) : MemLp (X u - X t) p μ := by
  have hu := (hv.condExp (m := ℱ u) hp).ae_eq (hX.condExp_sub_ae_eq (hst.trans htu) huv)
  have ht := (hv.condExp (m := ℱ t) hp).ae_eq (hX.condExp_sub_ae_eq hst (htu.trans huv))
  simpa only [Pi.sub_def, sub_sub_sub_cancel_right] using hu.sub ht

/-- On a nondecreasing finite grid, Lᵖ integrability of the total martingale increment
implies Lᵖ integrability of each grid increment, for `p ≥ 1`. No Lᵖ assumption on the
initial value is needed. -/
theorem Martingale.memLp_sub_of_monotoneOn (hX : Martingale X ℱ μ) {τ : ℕ → ι} {n : ℕ}
    (hτ : MonotoneOn τ (Set.Iic n)) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hn : MemLp (X (τ n) - X (τ 0)) p μ) {i : ℕ} (hi : i < n) :
    MemLp (X (τ (i + 1)) - X (τ i)) p μ :=
  hX.memLp_sub_of_le (hτ (by simp) hi.le (Nat.zero_le i))
    (hτ hi.le hi (Nat.le_succ i)) (hτ hi (by simp) hi) hp hn

/-- Raising an almost everywhere nonnegative real submartingale to a power `p ≥ 1` gives a
submartingale whenever the powered values are integrable. No sigma-finiteness assumption on the
filtration trims is required. -/
theorem Submartingale.rpow (hY : Submartingale Y ℱ μ) (hpos : ∀ t, 0 ≤ᵐ[μ] Y t) {p : ℝ}
    (hp : 1 ≤ p) (hint : ∀ t, Integrable (fun ω ↦ Y t ω ^ p) μ) :
    Submartingale (fun t ω ↦ Y t ω ^ p) ℱ μ := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  refine ⟨fun t ↦ (Real.continuous_rpow_const hp0.le).comp_stronglyMeasurable
    (hY.stronglyAdapted t), fun i j hij ↦ ?_, hint⟩
  by_cases hμ : SigmaFinite (μ.trim (ℱ.le i))
  · have hl :=
      (Real.continuous_rpow_const hp0.le).lowerSemicontinuous.lowerSemicontinuousOn (Set.Ici 0)
    have hjensen := (convexOn_rpow hp).map_condExp_le (ℱ.le i) hl (hpos j) isClosed_Ici
      (hY.integrable j) (hint j)
    filter_upwards [hpos i, hY.ae_le_condExp hij, hjensen] with ω hpos_i hle hjen
    exact (Real.rpow_le_rpow hpos_i hle hp0.le).trans hjen
  · have hcond0 : μ[Y j | ℱ i] = 0 := condExp_of_not_sigmaFinite (ℱ.le i) hμ
    have hcondp0 : μ[fun ω ↦ Y j ω ^ p | ℱ i] = 0 := condExp_of_not_sigmaFinite (ℱ.le i) hμ
    filter_upwards [hpos i, hY.ae_le_condExp hij] with ω hpos_i hle
    have hYi0 : Y i ω = 0 := le_antisymm (by simpa [hcond0] using hle) hpos_i
    simp [hYi0, hcondp0, Real.zero_rpow hp0.ne']

/-- For `p ≥ 1`, the `p`-th power of the norm of a Banach-valued martingale is a submartingale
whenever it is integrable at each date. -/
theorem Martingale.norm_rpow (hX : Martingale X ℱ μ) {p : ℝ} (hp : 1 ≤ p)
    (hint : ∀ t, Integrable (fun ω ↦ ‖X t ω‖ ^ p) μ) :
    Submartingale (fun t ω ↦ ‖X t ω‖ ^ p) ℱ μ :=
  hX.norm.rpow (fun _ ↦ .of_forall fun _ ↦ norm_nonneg _) hp hint

open scoped ProbabilityTheory in
/-- The conditional square of a square-integrable real martingale value is
the current square plus the conditional square of the future increment. -/
theorem Martingale.condExp_sq (hY : Martingale Y ℱ μ) {i j : ι}
    (hij : i ≤ j) (hj : MemLp (Y j) 2 μ) :
    μ[fun ω ↦ Y j ω ^ 2 | ℱ i] =ᵐ[μ]
      fun ω ↦ Y i ω ^ 2 + μ[fun ω ↦ (Y j ω - Y i ω) ^ 2 | ℱ i] ω := by
  have hc := hY.condExp_ae_eq hij
  -- The conditional variance of `Y j` given `ℱ i`, centred at `μ[Y j | ℱ i] = Y i`.
  have hvar : Var[Y j; μ | ℱ i] =ᵐ[μ] μ[fun ω ↦ (Y j ω - Y i ω) ^ 2 | ℱ i] :=
    ProbabilityTheory.condVar_ae_eq_condExp_sub_sq_of_condExp_ae_eq hc
  filter_upwards [ProbabilityTheory.condVar_ae_eq_condExp_sq_sub_sq_condExp' (ℱ.le i) hj, hvar, hc]
    with ω h₁ h₂ h₃
  simp only [Pi.sub_apply, Pi.pow_apply] at h₁
  rw [Pi.pow_def] at h₁
  rw [← h₂, h₁, h₃]
  ring

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

omit [CompleteSpace E] in
/-- The integral of a predictable height times a later martingale increment is zero.
In the nonintegrable case or for an incomplete codomain, the integral is zero by convention. -/
theorem Martingale.integral_smul_sub_eq_zero
    (hX : Martingale X ℱ μ) {s t : ι} [SigmaFinite (μ.trim (ℱ.le s))] (hst : s ≤ t)
    {ξ : Ω → ℝ} (hξ : AEStronglyMeasurable[ℱ s] ξ μ) :
    ∫ ω, ξ ω • (X t ω - X s ω) ∂μ = 0 := by
  by_cases hE : CompleteSpace E
  swap
  · exact integral_of_not_completeSpace hE
  by_cases hint : Integrable (ξ • (X t - X s)) μ
  swap
  · simpa only [Pi.smul_def', Pi.sub_def] using integral_undef hint
  have hzero : μ[X t - X s | ℱ s] =ᵐ[μ] 0 := by
    simpa only [sub_self] using hX.condExp_sub_ae_eq le_rfl hst
  have hpull := condExp_smul_of_aestronglyMeasurable_left hξ hint
    ((hX.integrable t).sub (hX.integrable s))
  have heq : μ[ξ • (X t - X s) | ℱ s] =ᵐ[μ] 0 := by
    filter_upwards [hpull, hzero] with ω hp hz
    simpa [hz] using hp
  simpa only [Pi.smul_apply', Pi.sub_apply, Pi.zero_apply, integral_zero] using
    (integral_condExp (ℱ.le s) (f := ξ • (X t - X s))).symm.trans (integral_congr_ae heq)

/-- The integral of a predictable real height times a later real martingale increment is zero.
In the nonintegrable case, the integral is zero by convention. -/
theorem Martingale.integral_mul_sub_eq_zero
    (hM : Martingale Y ℱ μ) {s t : ι} [SigmaFinite (μ.trim (ℱ.le s))] (hst : s ≤ t)
    {ξ : Ω → ℝ} (hξ : AEStronglyMeasurable[ℱ s] ξ μ) :
    ∫ ω, ξ ω * (Y t ω - Y s ω) ∂μ = 0 := by
  simpa only [smul_eq_mul] using hM.integral_smul_sub_eq_zero hst hξ

/-- A deterministic almost-sure norm bound on a martingale at a later date also bounds
its value at every earlier date. -/
theorem Martingale.ae_norm_le_of_le (hX : Martingale X ℱ μ) {i j : ι} (hij : i ≤ j)
    {C : ℝ} (hb : ∀ᵐ ω ∂μ, ‖X j ω‖ ≤ C) : ∀ᵐ ω ∂μ, ‖X i ω‖ ≤ C := by
  filter_upwards [ae_bdd_norm_condExp_of_ae_bdd_norm (m := ℱ i) hb,
    hX.condExp_ae_eq hij] with ω hb he
  simpa only [he] using hb

/-- A deterministic almost-sure norm bound on a martingale increment also bounds shorter
increments with the same starting date. -/
theorem Martingale.ae_norm_sub_le_of_le (hX : Martingale X ℱ μ) {s t u : ι}
    (hst : s ≤ t) (htu : t ≤ u) {C : ℝ} (hb : ∀ᵐ ω ∂μ, ‖X u ω - X s ω‖ ≤ C) :
    ∀ᵐ ω ∂μ, ‖X t ω - X s ω‖ ≤ C := by
  filter_upwards [ae_bdd_norm_condExp_of_ae_bdd_norm (m := ℱ t) hb,
    hX.condExp_sub_ae_eq hst htu] with ω hb he
  exact (congrArg (fun x : E ↦ ‖x‖) he).symm.le.trans hb

/-- A nonnegative submartingale value inherits Lᵖ integrability from a later value,
for every `p ≥ 1`. Only the earlier value needs to be nonnegative. -/
theorem Submartingale.memLp_of_le (hY : Submartingale Y ℱ μ) {i j : ι} (hij : i ≤ j)
    (hpos : 0 ≤ᵐ[μ] Y i) {p : ℝ≥0∞} (hp : 1 ≤ p) (hj : MemLp (Y j) p μ) :
    MemLp (Y i) p μ := by
  apply (MemLp.condExp (m := ℱ i) hp hj).mono'
    ((hY.stronglyAdapted i).mono (ℱ.le i)).aestronglyMeasurable
  filter_upwards [hpos, hY.ae_le_condExp hij] with ω hposω hω
  simpa only [Real.norm_eq_abs, abs_of_nonneg hposω] using hω

/-- An increment of a real martingale is orthogonal to every `ℱ s`-measurable Banach-valued
multiplier over every event in `ℱ s`, provided the restricted product is integrable. -/
theorem Martingale.setIntegral_sub_smul_eq_zero [SigmaFiniteFiltration μ ℱ] (hY : Martingale Y ℱ μ)
    {s t : ι} (hst : s ≤ t) {S : Set Ω} (hS : MeasurableSet[ℱ s] S) {Z : Ω → E}
    (hZ : AEStronglyMeasurable[ℱ s] Z μ) (hint : IntegrableOn (fun ω ↦ (Y t ω - Y s ω) • Z ω) S μ) :
    ∫ ω in S, (Y t ω - Y s ω) • Z ω ∂μ = 0 := by
  have hind : S.indicator (fun ω ↦ (Y t ω - Y s ω) • Z ω) = (Y t - Y s) • S.indicator Z := by
    ext ω; exact congrFun (Set.indicator_smul S (fun ω ↦ Y t ω - Y s ω) Z) ω
  have hZS : AEStronglyMeasurable[ℱ s] (S.indicator Z) μ := by
    obtain ⟨g, hg, hZg⟩ := hZ
    exact ⟨S.indicator g, hg.indicator hS,
      hZg.mono fun ω hω ↦ by by_cases h : ω ∈ S <;> simp [h, hω]⟩
  have hint' : Integrable ((Y t - Y s) • S.indicator Z) μ :=
    hind ▸ (integrable_indicator_iff (ℱ.le s S hS)).2 hint
  have hpull := condExp_smul_of_aestronglyMeasurable_right ((hY.integrable t).sub (hY.integrable s))
    hint' hZS
  rw [← integral_indicator (ℱ.le s S hS), hind, ← integral_condExp (ℱ.le s),
    integral_congr_ae (g := fun _ ↦ (0 : E)) ?_, integral_zero]
  filter_upwards [hpull, condExp_sub (m := ℱ s) (hY.integrable t) (hY.integrable s),
    hY.condExp_ae_eq hst] with ω hp hd hm
  simp only [Pi.smul_apply', Pi.sub_apply] at *
  rw [hp, hd, hm, condExp_of_stronglyMeasurable (ℱ.le s) (hY.stronglyAdapted s) (hY.integrable s),
    sub_self, zero_smul]

/-- If `Y` and `Y ^ 2 - A` are real martingales, the compensated squared increment
`(Y t - Y s) ^ 2 - (A t - A s)` is orthogonal to every `ℱ s`-measurable Banach-valued multiplier
over every event in `ℱ s`, under the corresponding integrability assumptions. -/
theorem Martingale.setIntegral_sq_sub_smul_eq_zero [SigmaFiniteFiltration μ ℱ] {A : ι → Ω → ℝ}
    (hY : Martingale Y ℱ μ) (hQ : Martingale (fun u ω ↦ Y u ω ^ 2 - A u ω) ℱ μ)
    {s t : ι} (hst : s ≤ t) {S : Set Ω} (hS : MeasurableSet[ℱ s] S) {Z : Ω → E}
    (hZ : AEStronglyMeasurable[ℱ s] Z μ)
    (hintQ : IntegrableOn (fun ω ↦ ((Y t ω ^ 2 - A t ω) - (Y s ω ^ 2 - A s ω)) • Z ω) S μ)
    (hintY : IntegrableOn (fun ω ↦ (Y t ω - Y s ω) • (Y s ω • Z ω)) S μ) :
    ∫ ω in S, ((Y t ω - Y s ω) ^ 2 - (A t ω - A s ω)) • Z ω ∂μ = 0 := by
  have hid (ω : Ω) : ((Y t ω - Y s ω) ^ 2 - (A t ω - A s ω)) • Z ω =
      ((Y t ω ^ 2 - A t ω) - (Y s ω ^ 2 - A s ω)) • Z ω -
        (2 : ℝ) • ((Y t ω - Y s ω) • (Y s ω • Z ω)) := by
    rw [smul_smul, smul_smul, ← sub_smul]; congr 1; ring
  simp_rw [hid]
  rw [integral_sub (g := fun ω ↦ (2 : ℝ) • ((Y t ω - Y s ω) • (Y s ω • Z ω))) hintQ
      (hintY.smul (2 : ℝ)), integral_smul, hQ.setIntegral_sub_smul_eq_zero hst hS hZ hintQ,
    hY.setIntegral_sub_smul_eq_zero hst hS (Z := fun ω ↦ Y s ω • Z ω)
      ((hY.stronglyAdapted s).aestronglyMeasurable.smul hZ) hintY, smul_zero, sub_self]

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

/-- Conditioning an increment restricted to an event known at its starting date truncates
the increment to the conditioning date, with zero increment before its start. -/
theorem Martingale.condExp_indicator_sub (hX : Martingale X ℱ μ) {s t : ι} (hst : s ≤ t) {A : Set Ω}
    (hA : MeasurableSet[ℱ s] A) (S : ι) :
    μ[A.indicator (X t - X s) | ℱ S] =ᵐ[μ]
      A.indicator (X (max s (min t S)) - X s) := by
  have hcond (u : ι) [SigmaFinite (μ.trim (ℱ.le u))] :
      μ[X t - X s | ℱ u] =ᵐ[μ] X (min t u) - X (min s u) := by
    have heval (v : ι) : μ[X v | ℱ u] =ᵐ[μ] X (min v u) := by
      rcases le_total v u with hvu | huv
      · rw [min_eq_left hvu, condExp_of_stronglyMeasurable (ℱ.le u)
          ((hX.stronglyMeasurable v).mono (ℱ.mono hvu)) (hX.integrable v)]
      · simpa only [min_eq_right huv] using hX.condExp_ae_eq huv
    exact (condExp_sub (hX.integrable t) (hX.integrable s) _).trans
      ((heval t).sub (heval s))
  have hint := (hX.integrable t).sub (hX.integrable s)
  by_cases hμS : SigmaFinite (μ.trim (ℱ.le S))
  swap
  · rw [condExp_of_not_sigmaFinite (ℱ.le S) hμS]
    by_cases hsS : s ≤ S
    · have hzero (u : ι) (hu : u ≤ S) : X u =ᵐ[μ] 0 := by
        have hμu : ¬SigmaFinite (μ.trim (ℱ.le u)) :=
          fun _ ↦ hμS (sigmaFiniteTrim_mono (ℱ.le S) (ℱ.mono hu))
        simpa only [condExp_of_not_sigmaFinite (ℱ.le u) hμu] using
          (hX.condExp_ae_eq (le_refl u)).symm
      simpa only [sub_zero, Set.indicator_zero'] using
        ((hzero _ (max_le hsS (min_le_right t S))).sub (hzero s hsS)).indicator.symm
    · simp [min_eq_right ((le_of_not_ge hsS).trans hst),
        max_eq_left (le_of_not_ge hsS)]
  by_cases hSs : S ≤ s
  · have : SigmaFinite (μ.trim (ℱ.le s)) :=
      sigmaFiniteTrim_mono (ℱ.le s) (ℱ.mono hSs)
    have hzero : μ[A.indicator (X t - X s) | ℱ s] =ᵐ[μ] 0 := by
      simpa only [min_eq_right hst, min_self, sub_self, Set.indicator_zero'] using
        (condExp_indicator hint hA).trans (hcond s).indicator
    calc
      _ =ᵐ[μ] μ[μ[A.indicator (X t - X s) | ℱ s] | ℱ S] :=
        (condExp_condExp_of_le (ℱ.mono hSs) (ℱ.le s)).symm
      _ =ᵐ[μ] μ[0 | ℱ S] := condExp_congr_ae hzero
      _ = _ := by rw [condExp_zero, min_eq_right (hSs.trans hst),
        max_eq_left hSs, sub_self, Set.indicator_zero']
  · have hsS := le_of_not_ge hSs
    simpa only [min_eq_left hsS, max_eq_right (le_min hst hsS)] using
      (condExp_indicator hint (ℱ.mono hsS _ hA)).trans (hcond S).indicator

end MeasureTheory
