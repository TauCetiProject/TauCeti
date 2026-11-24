/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.MaximumPrinciple.Drift
import TauCeti.Analysis.Sobolev.FiniteMeasure
import TauCeti.Analysis.Sobolev.W1p.LevelSet
import TauCeti.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# The weak maximum principle with a drift in `Lᵖ`

Let `Ω ⊆ ℝⁿ` be open and let

`L u = -∂ᵢ(aⁱʲ ∂ⱼu + eⁱ u) + bⁱ ∂ᵢu + c u`

have measurable, uniformly elliptic `a` with constants `0 < λ ≤ Λ`, bounded measurable `c` and `e`
satisfying the weak sign condition `∫ c φ + ⟪e, ∇φ⟫ ≥ 0` for every nonnegative `φ ∈ H¹₀(Ω)`, and a
drift `b ∈ Lᵖ(Ω)` that need not be bounded. This file proves the **weak maximum principle** for
weak subsolutions of `L`: if `u ∈ H¹(Ω)` satisfies

`a_{0, c}(u, φ) + ∫ u ⟪e, ∇φ⟫ + ∫ ⟪b, ∇u⟫ φ ≤ 0` for every nonnegative `φ ∈ H¹₀(Ω)`,

and `(u - k)⁺ ∈ H¹₀(Ω)` for a constant `k ≥ 0`, then `u ≤ k` almost everywhere
(`TauCeti.PDE.UniformlyEllipticOn.value_le_const_of_memLp_drift_of_measure_ne_top`). On an open
set `Ω` of finite measure it suffices that `p > max(2, n)`. This is the integrability of the lower
order coefficients in Gilbarg–Trudinger's remark on Theorem 8.16, and the drift class of the Hopf
lemma for weak supersolutions of Rosales, whose first order coefficient `cⁱ ∂ᵢu` lies in `L^q`,
`q > n`. For bounded `b` the statement is
`TauCeti.PDE.UniformlyEllipticOn.value_le_const_of_forall_integral_nonneg_of_measure_ne_top`.

## The argument

The argument is Gilbarg–Trudinger's, with Hölder's inequality in three exponents in place of the
bound `‖b‖ ≤ β`. Suppose that `‖w‖_q ≤ S ‖∇w‖₂` on `H¹₀(Ω)` with `1/p + 1/q = 1/2`. For a level
`l ≥ k` put `v = (u - l)⁺`. The sign condition reduces the operator tested against `v` to
`-∂ᵢ(aⁱʲ ∂ⱼ·) - eⁱ ∂ᵢ` with no mass (`TauCeti.PDE.energyFormH1_sub_zero_posPartAbove_self_le`), and
since `∇u = ∇v` where `v ≠ 0`,

`λ ‖∇v‖₂² ≤ ∫_Γ (σ + ‖b‖) |∇v| v ≤ ‖1_Γ (σ + ‖b‖)‖_p ‖∇v‖₂ ‖v‖_q ≤ S ‖1_Γ (σ + ‖b‖)‖_p ‖∇v‖₂²`,

where `σ` bounds `e` and `Γ = {u > l, ∇u ≠ 0}`. If `u > k` on a set of positive measure, there are
levels along which `∇v ≠ 0` and `|Γ| → 0`
(`TauCeti.W1p.exists_tendsto_measure_lt_value_and_gradient_ne_zero`). Then
`‖1_Γ (σ + ‖b‖)‖_p → 0`, because `p < ∞` and `b ∈ Lᵖ`, and this contradicts `λ > 0`.

On a set of finite measure the Sobolev inequality holds with `q = 2p/(p - 2)` as soon as `p > n`
(`TauCeti.W1p.eLpNorm_value_le_mul_measure_rpow_mul_enorm_gradient_of_lt`).

## Main declarations

* `TauCeti.PDE.UniformlyEllipticOn.value_le_const_of_memLp_drift_of_forall_eLpNorm_le`: the weak
  maximum principle under a Sobolev inequality `‖w‖_q ≤ S ‖∇w‖₂` on `H¹₀(Ω)`,
  `1/p + 1/q = 1/2`.
* `TauCeti.PDE.UniformlyEllipticOn.value_le_const_of_memLp_drift_of_measure_ne_top`: the weak
  maximum principle on an open set of finite measure, for `p > max(2, n)`.
* `TauCeti.PDE.UniformlyEllipticOn.value_le_of_memLp_drift_of_forall_eLpNorm_le` and
  `TauCeti.PDE.UniformlyEllipticOn.value_le_of_memLp_drift_of_measure_ne_top`: the comparison
  principles.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.1 and the remark after Theorem 8.16.
* L. Rosales, *Generalizing Hopf's boundary point lemma*, Canad. Math. Bull. (2019),
  arXiv:1806.07003, Lemma 3.2.
-/

public section

noncomputable section

open Filter MeasureTheory Set TopologicalSpace Module
open scoped ENNReal NNReal Topology InnerProductSpace

namespace TauCeti.PDE

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b e : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {c : EuclideanSpace ℝ ι → ℝ} {lam Lam gamma sigma : ℝ} {p q : ℝ≥0∞}

/-- Hölder's inequality with the exponents `p`, `2` and `q`, `1/p + 1/q = 1/2`, on a measurable set
`Γ`: `∫_Γ |w| |g| |f| ≤ ‖1_Γ w‖_p ‖g‖₂ ‖f‖_q`. -/
private theorem setLIntegral_enorm_mul_enorm_mul_enorm_le {F : Type*} [NormedAddCommGroup F]
    {μ : Measure (EuclideanSpace ℝ ι)} (hpq : p⁻¹ + q⁻¹ = 2⁻¹)
    {w : EuclideanSpace ℝ ι → F} {g : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {f : EuclideanSpace ℝ ι → ℝ} (hw : AEStronglyMeasurable w μ)
    (hg : AEStronglyMeasurable g μ) (hf : AEStronglyMeasurable f μ)
    {Γ : Set (EuclideanSpace ℝ ι)} (hΓ : MeasurableSet Γ) :
    ∫⁻ x in Γ, ‖w x‖ₑ * (‖g x‖ₑ * ‖f x‖ₑ) ∂μ ≤
      eLpNorm (Γ.indicator w) p μ * (eLpNorm g 2 μ * eLpNorm f q μ) := by
  have : p.HolderTriple q 2 := ⟨hpq⟩
  have hwΓ : AEStronglyMeasurable (Γ.indicator w) μ := hw.indicator hΓ
  have h₁ := eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1) hg.norm
    (hwΓ.norm.smul hf) (μ := μ)
  have h₂ := eLpNorm_smul_le_mul_eLpNorm (p := p) (q := q) (r := 2) hwΓ.norm hf (μ := μ)
  rw [eLpNorm_norm g hg] at h₁
  rw [eLpNorm_norm _ hwΓ] at h₂
  calc ∫⁻ x in Γ, ‖w x‖ₑ * (‖g x‖ₑ * ‖f x‖ₑ) ∂μ
      = ∫⁻ x, ‖((fun x ↦ ‖g x‖) • ((fun x ↦ ‖Γ.indicator w x‖) • f)) x‖ₑ ∂μ := by
        rw [← lintegral_indicator hΓ]
        refine lintegral_congr fun x ↦ ?_
        by_cases hx : x ∈ Γ
        · simp only [indicator_of_mem hx, Pi.mul_apply, smul_eq_mul, eNorm_mul,
            eNorm_norm]
          ring
        · simp [indicator_of_notMem hx]
    _ = eLpNorm ((fun x ↦ ‖g x‖) • ((fun x ↦ ‖Γ.indicator w x‖) • f)) 1 μ :=
        (eLpNorm_one_eq_lintegral_eNorm (hg.norm.smul (hwΓ.norm.smul hf))).symm
    _ ≤ eLpNorm g 2 μ * eLpNorm ((fun x ↦ ‖Γ.indicator w x‖) • f) 2 μ := h₁
    _ ≤ eLpNorm (Γ.indicator w) p μ * (eLpNorm g 2 μ * eLpNorm f q μ) := by
        rw [mul_left_comm]
        gcongr

/-- If `b ∈ Lᵖ`, `g ∈ L²` and `‖f‖_q < ∞` with `1/p + 1/q = 1/2`, then `‖b‖ |g| |f|` is
integrable. -/
private theorem integrable_norm_mul_norm_mul_norm {μ : Measure (EuclideanSpace ℝ ι)}
    (hb : MemLp b p μ) (hpq : p⁻¹ + q⁻¹ = 2⁻¹) {g : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    (hg : MemLp g 2 μ) {f : EuclideanSpace ℝ ι → ℝ} (hf : AEStronglyMeasurable f μ)
    (hfq : eLpNorm f q μ ≠ ∞) :
    Integrable (fun x ↦ ‖b x‖ * (‖g x‖ * ‖f x‖)) μ := by
  refine ⟨hb.aestronglyMeasurable.norm.mul (hg.aestronglyMeasurable.norm.mul hf.norm), ?_⟩
  have h := setLIntegral_enorm_mul_enorm_mul_enorm_le hpq hb.aestronglyMeasurable
    hg.aestronglyMeasurable hf MeasurableSet.univ
  rw [Measure.restrict_univ, indicator_univ] at h
  refine lt_of_le_of_lt (le_of_eq ?_) (h.trans_lt (ENNReal.mul_lt_top hb.eLpNorm_lt_top
    (ENNReal.mul_lt_top hg.eLpNorm_lt_top hfq.lt_top)))
  refine lintegral_congr fun x ↦ ?_
  simp only [eNorm_mul, eNorm_norm]

/-- If `b ∈ Lᵖ`, `u ∈ H¹(Ω)` and `‖φ‖_q < ∞` with `1/p + 1/q = 1/2`, then the drift term
`⟪b, ∇u⟫ φ` of the weak form is integrable. -/
private theorem integrable_inner_gradient_mul_value (hb : MemLp b p (mu.restrict Omega))
    (hpq : p⁻¹ + q⁻¹ = 2⁻¹) (u : W1p mu Omega 2) {φ : W1p mu Omega 2}
    (hφ : eLpNorm (W1p.value φ) q (mu.restrict Omega) ≠ ∞) :
    Integrable (fun x ↦ ⟪b x, W1p.gradient u x⟫_ℝ * W1p.value φ x) (mu.restrict Omega) := by
  refine (integrable_norm_mul_norm_mul_norm hb hpq (Lp.memLp (W1p.gradient u))
    (Lp.aestronglyMeasurable _) hφ).mono'
    ((hb.aestronglyMeasurable.inner (Lp.aestronglyMeasurable _)).mul (Lp.aestronglyMeasurable _))
    (ae_of_all _ fun x ↦ ?_)
  rw [norm_mul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (norm_inner_le_norm _ _) (norm_nonneg _)

variable [DecidableEq ι]

omit [DecidableEq ι] in
/-- Above a level `l ≥ 0`, the drift term of the weak form tested against `v = (u - l)⁺` only sees
`v`: `∫ ⟪b, ∇u⟫ v = ∫ ⟪b, ∇v⟫ v`, since `∇u = ∇v` where `v ≠ 0`. -/
private theorem integral_inner_gradient_mul_value_posPartAbove {l : ℝ} (hl : 0 ≤ l)
    (u : W1p mu Omega 2) :
    ∫ x in Omega, ⟪b x, W1p.gradient u x⟫_ℝ *
        W1p.value (W1p.posPartAbove (by norm_num) hl u) x ∂mu =
      ∫ x in Omega, ⟪b x, W1p.gradient (W1p.posPartAbove (by norm_num) hl u) x⟫_ℝ *
        W1p.value (W1p.posPartAbove (by norm_num) hl u) x ∂mu := by
  refine integral_congr_ae ?_
  filter_upwards [W1p.value_posPartAbove_ae (by norm_num) hl u,
    W1p.gradient_posPartAbove_ae (by norm_num) hl u] with x hvx hgx
  rw [hgx, hvx]
  by_cases hx : l < W1p.value u x
  · rw [indicator_of_mem (s := {y | l < W1p.value u y}) hx]
  · rw [indicator_of_notMem (s := {y | l < W1p.value u y}) hx,
      max_eq_right (sub_nonpos.2 (not_lt.1 hx))]
    simp

/-- The energy inequality behind the weak maximum principle with a drift in `Lᵖ`: for a weak
subsolution `u` and `v = (u - l)⁺ ∈ H¹₀(Ω)` with `‖v‖_q < ∞`, `λ ‖∇v‖₂² ≤ ∫ (σ + ‖b‖) |∇v| v`. -/
private theorem UniformlyEllipticOn.mul_norm_gradient_sq_le_integral_of_memLp_drift
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) (hb : MemLp b p (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (he : AEStronglyMeasurable e (mu.restrict Omega))
    (hc_bound : ∀ x ∈ Omega, ‖c x‖ ≤ gamma) (he_bound : ∀ x ∈ Omega, ‖e x‖ ≤ sigma)
    (hsign : ∀ φ : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (φ : W1p mu Omega 2) x) →
        0 ≤ ∫ x in Omega, c x * W1p.value (φ : W1p mu Omega 2) x +
          ⟪e x, W1p.gradient (φ : W1p mu Omega 2) x⟫_ℝ ∂mu)
    (hpq : p⁻¹ + q⁻¹ = 2⁻¹) {l : ℝ} (hl : 0 ≤ l) {u : W1p mu Omega 2}
    (hmem : W1p.posPartAbove (by norm_num) hl u ∈ w1p0Submodule mu Omega 2)
    (hfq : eLpNorm (W1p.value (W1p.posPartAbove (by norm_num) hl u)) q (mu.restrict Omega) ≠ ∞)
    (hu : ∀ φ : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (φ : W1p mu Omega 2) x) →
        energyFormH1 a 0 c u (φ : W1p mu Omega 2) +
          ∫ x in Omega, W1p.value u x * ⟪e x, W1p.gradient (φ : W1p mu Omega 2) x⟫_ℝ ∂mu +
          ∫ x in Omega, ⟪b x, W1p.gradient u x⟫_ℝ * W1p.value (φ : W1p mu Omega 2) x ∂mu ≤ 0) :
    lam * ‖W1p.gradient (W1p.posPartAbove (by norm_num) hl u)‖ ^ 2 ≤
      ∫ x in Omega, (sigma + ‖b x‖) *
        (‖W1p.gradient (W1p.posPartAbove (by norm_num) hl u) x‖ *
          ‖W1p.value (W1p.posPartAbove (by norm_num) hl u) x‖) ∂mu := by
  set v := W1p.posPartAbove (by norm_num) hl u
  set f := W1p.value v
  set g := W1p.gradient v
  -- The coefficient bounds of the reduced operator `-∂ᵢ(aⁱʲ ∂ⱼ·) - eⁱ ∂ᵢ`.
  have hcoeff := memLp_energyIntegrand_of_bounds h.upper_nonneg ha aestronglyMeasurable_zero hc
    (fun x hx eta xi ↦ h.upper_bound hx eta xi) (beta := 0) (fun x _ ↦ by simp) hc_bound
  have hbe_bound : ∀ x ∈ Omega, ‖((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) - e) x‖ ≤
      sigma := fun x hx ↦ by simpa using he_bound x hx
  have hcoeff' := memLp_energyIntegrand_of_bounds h.upper_nonneg ha
    (aestronglyMeasurable_zero.sub he) aestronglyMeasurable_zero
    (fun x hx eta xi ↦ h.upper_bound hx eta xi) hbe_bound (gamma := 0) fun x _ ↦ by simp
  have hint₁ : Integrable (fun x ↦ ‖g x‖ * ‖f x‖) (mu.restrict Omega) :=
    (Lp.memLp g).norm.integrable_mul (Lp.memLp f).norm
  have hint₂ : Integrable (fun x ↦ ‖b x‖ * (‖g x‖ * ‖f x‖)) (mu.restrict Omega) :=
    integrable_norm_mul_norm_mul_norm hb hpq (Lp.memLp g) (Lp.aestronglyMeasurable _) hfq
  have hneg : -∫ x in Omega, ⟪b x, g x⟫_ℝ * f x ∂mu ≤
      ∫ x in Omega, ‖b x‖ * (‖g x‖ * ‖f x‖) ∂mu := by
    refine (neg_le_abs _).trans ((Real.norm_eq_abs _).symm.le.trans
      ((norm_integral_le_integral_norm _).trans
      (integral_mono_of_nonneg (ae_of_all _ fun x ↦ norm_nonneg _) hint₂
        (ae_of_all _ fun x ↦ ?_))))
    dsimp only
    rw [norm_mul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (norm_inner_le_norm _ _) (norm_nonneg _)
  have h₁ := mul_norm_gradient_sq_sub_le_energyFormH1_self h hcoeff' hbe_bound
    (fun _ _ ↦ le_rfl) v
  have h₂ := energyFormH1_sub_zero_posPartAbove_self_le hcoeff hcoeff' hc he hc_bound he_bound
    hsign hl hmem
  have h₃ := hu ⟨v, hmem⟩ (W1p.value_posPartAbove_nonneg_ae (by norm_num) hl u)
  simp only at h₃
  rw [integral_inner_gradient_mul_value_posPartAbove hl u] at h₃
  have hsplit : ∫ x in Omega, (sigma + ‖b x‖) * (‖g x‖ * ‖f x‖) ∂mu =
      sigma * ∫ x in Omega, ‖g x‖ * ‖f x‖ ∂mu +
        ∫ x in Omega, ‖b x‖ * (‖g x‖ * ‖f x‖) ∂mu := by
    rw [← integral_const_mul, ← integral_add (hint₁.const_mul sigma) hint₂]
    exact integral_congr_ae (ae_of_all _ fun x ↦ by ring)
  rw [hsplit]
  linarith

omit [DecidableEq ι] in
/-- In `ℝ≥0∞`, the right-hand side of the energy inequality is an integral over
`Γ = {u > l, ∇u ≠ 0}`, outside of which the gradient of `v = (u - l)⁺` vanishes. -/
private theorem ofReal_integral_eq_setLIntegral_posPartAbove (hb : MemLp b p (mu.restrict Omega))
    (hpq : p⁻¹ + q⁻¹ = 2⁻¹) (hsigma : 0 ≤ sigma) {l : ℝ} (hl : 0 ≤ l) {u : W1p mu Omega 2}
    (hfq : eLpNorm (W1p.value (W1p.posPartAbove (by norm_num) hl u)) q (mu.restrict Omega) ≠ ∞) :
    ENNReal.ofReal (∫ x in Omega, (sigma + ‖b x‖) *
        (‖W1p.gradient (W1p.posPartAbove (by norm_num) hl u) x‖ *
          ‖W1p.value (W1p.posPartAbove (by norm_num) hl u) x‖) ∂mu) =
      ∫⁻ x in {x | l < W1p.value u x ∧ W1p.gradient u x ≠ 0}, ‖sigma + ‖b x‖‖ₑ *
        (‖W1p.gradient (W1p.posPartAbove (by norm_num) hl u) x‖ₑ *
          ‖W1p.value (W1p.posPartAbove (by norm_num) hl u) x‖ₑ) ∂mu.restrict Omega := by
  set v := W1p.posPartAbove (by norm_num) hl u
  set f := W1p.value v
  set g := W1p.gradient v
  set Γ := {x | l < W1p.value u x ∧ W1p.gradient u x ≠ 0}
  have hΓ : MeasurableSet Γ :=
    (measurableSet_lt measurable_const (Lp.stronglyMeasurable (W1p.value u)).measurable).inter
      ((Lp.stronglyMeasurable (W1p.gradient u)).measurable (measurableSet_singleton 0).compl)
  have hint : Integrable (fun x ↦ (sigma + ‖b x‖) * (‖g x‖ * ‖f x‖)) (mu.restrict Omega) :=
    ((((Lp.memLp g).norm.integrable_mul (Lp.memLp f).norm).const_mul sigma).add
      (integrable_norm_mul_norm_mul_norm hb hpq (Lp.memLp g) (Lp.aestronglyMeasurable _)
        hfq)).congr (ae_of_all _ fun x ↦ by simp only [Pi.add_apply, Pi.mul_apply]; ring)
  rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x ↦ by positivity),
    ← lintegral_indicator hΓ]
  refine lintegral_congr_ae ?_
  filter_upwards [W1p.gradient_posPartAbove_ae (by norm_num) hl u] with x hgx
  by_cases hxΓ : x ∈ Γ
  · rw [indicator_of_mem hxΓ, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul
      (norm_nonneg _), Real.eNorm_of_nonneg (by positivity : 0 ≤ sigma + ‖b x‖)]
    simp only [ofReal_norm]
  · rw [indicator_of_notMem hxΓ]
    have hg0 : g x = 0 := by
      rw [show g x = _ from hgx]
      by_cases hlt : l < W1p.value u x
      · rw [indicator_of_mem (s := {y | l < W1p.value u y}) hlt]
        by_contra hne
        exact hxΓ ⟨hlt, hne⟩
      · exact indicator_of_notMem (s := {y | l < W1p.value u y}) hlt _
    simp [hg0]

/-- The level estimate of the weak maximum principle with a drift in `Lᵖ`. Let `u` be a weak
subsolution and let `l ≥ k ≥ 0` be a level which `u` exceeds on a set of positive measure, with
`(u - k)⁺ ∈ H¹₀(Ω)`. Then `λ ≤ S ‖1_Γ (σ + ‖b‖)‖_p` for `Γ = {u > l, ∇u ≠ 0}`. -/
private theorem UniformlyEllipticOn.ofReal_le_mul_eLpNorm_indicator_of_not_ae_value_le
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) (hb : MemLp b p (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (he : AEStronglyMeasurable e (mu.restrict Omega))
    (hc_bound : ∀ x ∈ Omega, ‖c x‖ ≤ gamma) (he_bound : ∀ x ∈ Omega, ‖e x‖ ≤ sigma)
    (hsigma : 0 ≤ sigma)
    (hsign : ∀ φ : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (φ : W1p mu Omega 2) x) →
        0 ≤ ∫ x in Omega, c x * W1p.value (φ : W1p mu Omega 2) x +
          ⟪e x, W1p.gradient (φ : W1p mu Omega 2) x⟫_ℝ ∂mu)
    (hpq : p⁻¹ + q⁻¹ = 2⁻¹) {S : ℝ≥0}
    (hsob : ∀ v ∈ w1p0Submodule mu Omega 2,
      eLpNorm (W1p.value v) q (mu.restrict Omega) ≤ S * ‖W1p.gradient v‖ₑ)
    {k l : ℝ} (hk : 0 ≤ k) (hkl : k ≤ l) {u : W1p mu Omega 2}
    (hboundary : W1p.posPartAbove (by norm_num) hk u ∈ w1p0Submodule mu Omega 2)
    (hu : ∀ φ : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (φ : W1p mu Omega 2) x) →
        energyFormH1 a 0 c u (φ : W1p mu Omega 2) +
          ∫ x in Omega, W1p.value u x * ⟪e x, W1p.gradient (φ : W1p mu Omega 2) x⟫_ℝ ∂mu +
          ∫ x in Omega, ⟪b x, W1p.gradient u x⟫_ℝ * W1p.value (φ : W1p mu Omega 2) x ∂mu ≤ 0)
    (hnot : ¬ ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ l) :
    ENNReal.ofReal lam ≤ S * eLpNorm ({x | l < W1p.value u x ∧ W1p.gradient u x ≠ 0}.indicator
      fun x ↦ sigma + ‖b x‖) p (mu.restrict Omega) := by
  set μ := mu.restrict Omega
  have hl : 0 ≤ l := hk.trans hkl
  set v := W1p.posPartAbove (by norm_num) hl u
  set f := W1p.value v
  set g := W1p.gradient v
  set Γ := {x | l < W1p.value u x ∧ W1p.gradient u x ≠ 0}
  have hmem : v ∈ w1p0Submodule mu Omega 2 :=
    W1p.posPartAbove_mem_w1p0Submodule_of_le (by norm_num) hk hkl hboundary
  have hfq : eLpNorm f q μ ≠ ∞ :=
    ((hsob v hmem).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top eNorm_lt_top)).ne
  have hΓ : MeasurableSet Γ :=
    (measurableSet_lt measurable_const (Lp.stronglyMeasurable (W1p.value u)).measurable).inter
      ((Lp.stronglyMeasurable (W1p.gradient u)).measurable (measurableSet_singleton 0).compl)
  -- `λ ‖∇v‖² ≤ ∫_Γ (σ + ‖b‖) |∇v| v ≤ ‖1_Γ (σ + ‖b‖)‖_p ‖∇v‖₂ ‖v‖_q`.
  have hlin := (ENNReal.ofReal_le_ofReal (h.mul_norm_gradient_sq_le_integral_of_memLp_drift ha hb
    hc he hc_bound he_bound hsign hpq hl hmem hfq hu)).trans_eq
    (ofReal_integral_eq_setLIntegral_posPartAbove hb hpq hsigma hl hfq)
  have hholder := setLIntegral_enorm_mul_enorm_mul_enorm_le hpq (w := fun x ↦ sigma + ‖b x‖)
    (μ := μ) (aestronglyMeasurable_const.add hb.aestronglyMeasurable.norm)
    (Lp.aestronglyMeasurable g) (Lp.aestronglyMeasurable f) hΓ
  set B := eLpNorm (Γ.indicator fun x ↦ sigma + ‖b x‖) p μ
  have hcore : ENNReal.ofReal lam * ‖g‖ₑ ^ 2 ≤ S * B * ‖g‖ₑ ^ 2 := by
    calc ENNReal.ofReal lam * ‖g‖ₑ ^ 2 = ENNReal.ofReal (lam * ‖g‖ ^ 2) := by
          rw [ENNReal.ofReal_mul h.pos.le, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      _ ≤ B * (eLpNorm g 2 μ * eLpNorm f q μ) := hlin.trans hholder
      _ ≤ B * (‖g‖ₑ * (S * ‖g‖ₑ)) := by
          rw [← Lp.eNorm_def]
          gcongr
          exact hsob v hmem
      _ = S * B * ‖g‖ₑ ^ 2 := by ring
  -- `∇v ≠ 0`: otherwise the Sobolev inequality forces `v = 0`, that is `u ≤ l`.
  have hq0 : q ≠ 0 := by
    rintro rfl
    simp only [ENNReal.inv_zero, add_top] at hpq
    exact ENNReal.inv_ne_top.2 two_ne_zero hpq.symm
  have hN : ‖g‖ₑ ≠ 0 := by
    intro hzero
    refine hnot ?_
    have hv0' : eLpNorm f q μ = 0 :=
      le_antisymm ((hsob v hmem).trans_eq (by rw [hzero, mul_zero])) zero_le
    rw [eLpNorm_eq_zero_iff hq0] at hv0'
    filter_upwards [hv0', W1p.value_posPartAbove_ae (by norm_num) hl u] with x h₁ h₂
    rw [show f x = _ from h₂, Pi.zero_apply] at h₁
    linarith [le_max_left (W1p.value u x - l) 0]
  exact (ENNReal.mul_le_mul_iff_left (pow_ne_zero 2 hN) (ENNReal.pow_ne_top eNorm_ne_top)).1 hcore

omit [DecidableEq ι] in
/-- If `b ∈ Lᵖ` with `1 ≤ p < ∞` and `σ ≥ 0`, then `‖1_{Γⱼ} (σ + ‖b‖)‖_p → 0` along measurable
sets with `|Γⱼ| → 0`. -/
private theorem tendsto_eLpNorm_indicator_const_add_norm {μ : Measure (EuclideanSpace ℝ ι)}
    (hb : MemLp b p μ) (hp1 : 1 ≤ p) (hp : p ≠ ∞) {Γ : ℕ → Set (EuclideanSpace ℝ ι)}
    (hΓ : ∀ j, MeasurableSet (Γ j)) (htend : Tendsto (fun j ↦ μ (Γ j)) atTop (𝓝 0)) :
    Tendsto (fun j ↦ eLpNorm ((Γ j).indicator fun x ↦ sigma + ‖b x‖) p μ) atTop (𝓝 0) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  have hconst : Tendsto (fun j ↦ eLpNorm ((Γ j).indicator fun _ ↦ sigma) p μ) atTop (𝓝 0) := by
    have hexp : 0 < 1 / p.toReal := one_div_pos.2 (ENNReal.toReal_pos hp0 hp)
    simp_rw [eLpNorm_indicator_const (hΓ _).nullMeasurableSet hp0 hp]
    have h := ENNReal.Tendsto.const_mul (a := ‖sigma‖ₑ)
      (((ENNReal.continuous_rpow_const (y := 1 / p.toReal)).tendsto 0).comp htend)
      (Or.inr eNorm_ne_top)
    rwa [ENNReal.zero_rpow_of_pos hexp, mul_zero] at h
  have hdrift : Tendsto (fun j ↦ eLpNorm ((Γ j).indicator b) p μ) atTop (𝓝 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    obtain ⟨δ, hδ, hδb⟩ := hb.eLpNorm_indicator_le hp1 hp hε
    filter_upwards [ENNReal.tendsto_nhds_zero.1 htend δ hδ] with j hj
    exact hδb _ (hΓ j).nullMeasurableSet hj
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using hconst.add hdrift) (fun _ ↦ zero_le) fun j ↦ ?_
  calc eLpNorm ((Γ j).indicator fun x ↦ sigma + ‖b x‖) p μ
      = eLpNorm (((Γ j).indicator fun _ ↦ sigma) + (Γ j).indicator fun x ↦ ‖b x‖) p μ := by
        rw [← indicator_add']
        rfl
    _ ≤ eLpNorm ((Γ j).indicator fun _ ↦ sigma) p μ +
          eLpNorm ((Γ j).indicator fun x ↦ ‖b x‖) p μ := eLpNorm_add_le hp1
    _ = eLpNorm ((Γ j).indicator fun _ ↦ sigma) p μ + eLpNorm ((Γ j).indicator b) p μ := by
        congr 1
        refine eLpNorm_congr_norm_ae (hb.aestronglyMeasurable.norm.indicator (hΓ j))
          (hb.aestronglyMeasurable.indicator (hΓ j)) (ae_of_all _ fun x ↦ ?_)
        by_cases hx : x ∈ Γ j <;> simp [hx]

/-- **The weak maximum principle with a drift in `Lᵖ`**, under a Sobolev inequality
(Gilbarg–Trudinger, Theorem 8.1 and the remark after Theorem 8.16). Let `Ω ⊆ ℝⁿ` be open, let
`1/p + 1/q = 1/2` with `p < ∞`, and suppose `‖w‖_q ≤ S ‖∇w‖₂` on `H¹₀(Ω)`. Let

`L u = -∂ᵢ(aⁱʲ ∂ⱼu + eⁱ u) + bⁱ ∂ᵢu + c u`

have measurable, uniformly elliptic `a` with constants `λ, Λ`, a drift `b ∈ Lᵖ(Ω)`, and bounded
measurable `c`, `e` satisfying the weak sign condition `∫ c φ + ⟪e, ∇φ⟫ ≥ 0` for every nonnegative
`φ ∈ H¹₀(Ω)`. If `u ∈ H¹(Ω)` is a weak subsolution,
`a_{0, c}(u, φ) + ∫ u ⟪e, ∇φ⟫ + ∫ ⟪b, ∇u⟫ φ ≤ 0` for every nonnegative `φ ∈ H¹₀(Ω)`, and
`(u - k)⁺ ∈ H¹₀(Ω)` for some `k ≥ 0`, then `u ≤ k` almost everywhere. No smallness of `b` is
needed, and `Ω` need not have finite measure. -/
theorem UniformlyEllipticOn.value_le_const_of_memLp_drift_of_forall_eLpNorm_le
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) (hb : MemLp b p (mu.restrict Omega))
    (hp : p ≠ ∞) (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (he : AEStronglyMeasurable e (mu.restrict Omega))
    (hc_bound : ∀ x ∈ Omega, ‖c x‖ ≤ gamma) (he_bound : ∀ x ∈ Omega, ‖e x‖ ≤ sigma)
    (hsign : ∀ φ : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (φ : W1p mu Omega 2) x) →
        0 ≤ ∫ x in Omega, c x * W1p.value (φ : W1p mu Omega 2) x +
          ⟪e x, W1p.gradient (φ : W1p mu Omega 2) x⟫_ℝ ∂mu)
    (hpq : p⁻¹ + q⁻¹ = 2⁻¹) {S : ℝ≥0}
    (hsob : ∀ v ∈ w1p0Submodule mu Omega 2,
      eLpNorm (W1p.value v) q (mu.restrict Omega) ≤ S * ‖W1p.gradient v‖ₑ)
    {k : ℝ} (hk : 0 ≤ k) {u : W1p mu Omega 2}
    (hboundary : W1p.posPartAbove (by norm_num) hk u ∈ w1p0Submodule mu Omega 2)
    (hu : ∀ φ : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (φ : W1p mu Omega 2) x) →
        energyFormH1 a 0 c u (φ : W1p mu Omega 2) +
          ∫ x in Omega, W1p.value u x * ⟪e x, W1p.gradient (φ : W1p mu Omega 2) x⟫_ℝ ∂mu +
          ∫ x in Omega, ⟪b x, W1p.gradient u x⟫_ℝ * W1p.value (φ : W1p mu Omega 2) x ∂mu ≤ 0) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ k := by
  set μ := mu.restrict Omega
  have he_bound' : ∀ x ∈ Omega, ‖e x‖ ≤ max sigma 0 :=
    fun x hx ↦ (he_bound x hx).trans (le_max_left _ _)
  have hp1 : 1 ≤ p := by
    have h2 : 2 ≤ p := ENNReal.inv_le_inv.1 (hpq ▸ le_self_add)
    exact one_le_two.trans h2
  -- Since `u ∈ L²` and `k ≥ 0`, the superlevel sets `{u > l}`, `l > k`, have finite measure.
  have hfin : ∀ l, k < l → μ {x | l < W1p.value u x} ≠ ∞ := fun l hkl ↦
    ((Lp.memLp (W1p.value u)).measure_gt_lt_top two_ne_zero ENNReal.ofNat_ne_top
      (hk.trans_lt hkl)).ne
  by_contra hcon
  obtain ⟨l, hl, htend⟩ :=
    W1p.exists_tendsto_measure_lt_value_and_gradient_ne_zero (by norm_num) u hfin hcon
  set Γ : ℕ → Set (EuclideanSpace ℝ ι) :=
    fun j ↦ {x | l j < W1p.value u x ∧ W1p.gradient u x ≠ 0}
  have hΓ : ∀ j, MeasurableSet (Γ j) := fun j ↦
    (measurableSet_lt measurable_const (Lp.stronglyMeasurable (W1p.value u)).measurable).inter
      ((Lp.stronglyMeasurable (W1p.gradient u)).measurable (measurableSet_singleton 0).compl)
  -- Along the levels, `‖1_Γ (σ + ‖b‖)‖_p → 0`, since `|Γ| → 0` and `p < ∞`.
  have hlim : Tendsto (fun j ↦ (S : ℝ≥0∞) *
      eLpNorm ((Γ j).indicator fun x ↦ max sigma 0 + ‖b x‖) p μ) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul
      (tendsto_eLpNorm_indicator_const_add_norm hb hp1 hp hΓ htend) (Or.inr ENNReal.coe_ne_top)
  exact (ENNReal.ofReal_pos.2 h.pos).ne' (le_antisymm (ge_of_tendsto' hlim fun j ↦
    h.ofReal_le_mul_eLpNorm_indicator_of_not_ae_value_le ha hb hc he hc_bound he_bound'
      (le_max_right _ _) hsign hpq hsob hk (hl j).1 hboundary hu (hl j).2) zero_le)

/-- **The comparison principle with a drift in `Lᵖ`**, under a Sobolev inequality. Under the
hypotheses of `TauCeti.PDE.UniformlyEllipticOn.value_le_const_of_memLp_drift_of_forall_eLpNorm_le`,
if `L u ≤ L v` weakly and `(u - v)⁺ ∈ H¹₀(Ω)`, then `u ≤ v` almost everywhere. -/
theorem UniformlyEllipticOn.value_le_of_memLp_drift_of_forall_eLpNorm_le
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) (hb : MemLp b p (mu.restrict Omega))
    (hp : p ≠ ∞) (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (he : AEStronglyMeasurable e (mu.restrict Omega))
    (hc_bound : ∀ x ∈ Omega, ‖c x‖ ≤ gamma) (he_bound : ∀ x ∈ Omega, ‖e x‖ ≤ sigma)
    (hsign : ∀ φ : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (φ : W1p mu Omega 2) x) →
        0 ≤ ∫ x in Omega, c x * W1p.value (φ : W1p mu Omega 2) x +
          ⟪e x, W1p.gradient (φ : W1p mu Omega 2) x⟫_ℝ ∂mu)
    (hpq : p⁻¹ + q⁻¹ = 2⁻¹) {S : ℝ≥0}
    (hsob : ∀ v ∈ w1p0Submodule mu Omega 2,
      eLpNorm (W1p.value v) q (mu.restrict Omega) ≤ S * ‖W1p.gradient v‖ₑ)
    {u v : W1p mu Omega 2}
    (hboundary : W1p.posPart (by norm_num) (u - v) ∈ w1p0Submodule mu Omega 2)
    (huv : ∀ φ : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (φ : W1p mu Omega 2) x) →
        energyFormH1 a 0 c u (φ : W1p mu Omega 2) +
            ∫ x in Omega, W1p.value u x * ⟪e x, W1p.gradient (φ : W1p mu Omega 2) x⟫_ℝ ∂mu +
            ∫ x in Omega, ⟪b x, W1p.gradient u x⟫_ℝ * W1p.value (φ : W1p mu Omega 2) x ∂mu ≤
          energyFormH1 a 0 c v (φ : W1p mu Omega 2) +
            ∫ x in Omega, W1p.value v x * ⟪e x, W1p.gradient (φ : W1p mu Omega 2) x⟫_ℝ ∂mu +
            ∫ x in Omega, ⟪b x, W1p.gradient v x⟫_ℝ * W1p.value (φ : W1p mu Omega 2) x ∂mu) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ W1p.value v x := by
  have hcoeff := memLp_energyIntegrand_of_bounds h.upper_nonneg ha aestronglyMeasurable_zero hc
    (fun x hx eta xi ↦ h.upper_bound hx eta xi) (beta := 0) (fun x _ ↦ by simp) hc_bound
  -- The weak form is linear in `u`, so `u - v` is a weak subsolution.
  have hsub := h.value_le_const_of_memLp_drift_of_forall_eLpNorm_le ha hb hp hc he hc_bound
    he_bound hsign hpq hsob le_rfl (u := u - v) (by rwa [W1p.posPartAbove_zero]) fun φ hφ ↦ by
      have hφq : eLpNorm (W1p.value (φ : W1p mu Omega 2)) q (mu.restrict Omega) ≠ ∞ :=
        ((hsob _ φ.property).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top eNorm_lt_top)).ne
      have hint_e : ∫ x in Omega, W1p.value (u - v) x *
            ⟪e x, W1p.gradient (φ : W1p mu Omega 2) x⟫_ℝ ∂mu =
          (∫ x in Omega, W1p.value u x * ⟪e x, W1p.gradient (φ : W1p mu Omega 2) x⟫_ℝ ∂mu) -
            ∫ x in Omega, W1p.value v x * ⟪e x, W1p.gradient (φ : W1p mu Omega 2) x⟫_ℝ ∂mu := by
        rw [← integral_sub (integrable_value_mul_inner_gradient he he_bound u _)
          (integrable_value_mul_inner_gradient he he_bound v _)]
        refine integral_congr_ae ?_
        filter_upwards [W1p.value_sub_ae u v] with x hx
        rw [hx, Pi.sub_apply, sub_mul]
      have hint_b : ∫ x in Omega, ⟪b x, W1p.gradient (u - v) x⟫_ℝ *
            W1p.value (φ : W1p mu Omega 2) x ∂mu =
          (∫ x in Omega, ⟪b x, W1p.gradient u x⟫_ℝ * W1p.value (φ : W1p mu Omega 2) x ∂mu) -
            ∫ x in Omega, ⟪b x, W1p.gradient v x⟫_ℝ * W1p.value (φ : W1p mu Omega 2) x ∂mu := by
        rw [← integral_sub (integrable_inner_gradient_mul_value hb hpq u hφq)
          (integrable_inner_gradient_mul_value hb hpq v hφq)]
        refine integral_congr_ae ?_
        filter_upwards [W1p.gradient_sub_ae u v] with x hx
        rw [hx, Pi.sub_apply, inner_sub_right, sub_mul]
      rw [energyFormH1_sub_left hcoeff, hint_e, hint_b]
      linarith [huv φ hφ]
  filter_upwards [hsub, W1p.value_sub_ae u v] with x hx hval
  rw [hval, Pi.sub_apply] at hx
  exact sub_nonpos.mp hx

omit [DecidableEq ι] in
/-- On an open set of finite measure in dimension `n ≥ 1`, a drift exponent `p > max(2, n)`
admits a Sobolev inequality `‖w‖_q ≤ S ‖∇w‖₂` on `H¹₀(Ω)` with `1/p + 1/q = 1/2`. -/
private theorem exists_inv_add_inv_eq_and_forall_eLpNorm_le [Nonempty ι] (hOmega : mu Omega ≠ ∞)
    (hp : p ≠ ∞) (hp2 : 2 < p) (hn : (Fintype.card ι : ℝ) < p.toReal) :
    ∃ q : ℝ≥0∞, p⁻¹ + q⁻¹ = 2⁻¹ ∧ ∃ S : ℝ≥0, ∀ v ∈ w1p0Submodule mu Omega 2,
      eLpNorm (W1p.value v) q (mu.restrict Omega) ≤ S * ‖W1p.gradient v‖ₑ := by
  set r := p.toReal
  have hr2 : 2 < r := by
    simpa using (ENNReal.toReal_lt_toReal ENNReal.ofNat_ne_top hp).2 hp2
  have hd : 0 < 2⁻¹ - r⁻¹ := sub_pos.2 (inv_strictAnti₀ two_pos hr2)
  set q : ℝ≥0 := Real.toNNReal (2⁻¹ - r⁻¹)⁻¹
  have hq : (q : ℝ) = (2⁻¹ - r⁻¹)⁻¹ := Real.coe_toNNReal _ (inv_pos.2 hd).le
  refine ⟨q, ?_, ?_⟩
  · have hpr : p = ENNReal.ofReal r := (ENNReal.ofReal_toReal hp).symm
    have hqr : (q : ℝ≥0∞) = ENNReal.ofReal (2⁻¹ - r⁻¹)⁻¹ := rfl
    rw [hpr, hqr, ← ENNReal.ofReal_inv_of_pos (by linarith),
      ← ENNReal.ofReal_inv_of_pos (inv_pos.2 hd), inv_inv,
      ← ENNReal.ofReal_add (inv_nonneg.2 (by linarith)) hd.le, add_sub_cancel,
      ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
  · have h2q : (2 : ℝ≥0∞) ≤ q := by
      have h : (2 : ℝ) ≤ q := by
        rw [hq]
        exact (le_inv_comm₀ two_pos hd).2 (sub_le_self _ (inv_nonneg.2 (by linarith)))
      exact_mod_cast h
    have hδ : (2 : ℝ≥0∞).toReal⁻¹ - (q : ℝ)⁻¹ = r⁻¹ := by
      rw [hq, inv_inv, ENNReal.toReal_ofNat]
      ring
    have hδn : r⁻¹ < (finrank ℝ (EuclideanSpace ℝ ι) : ℝ)⁻¹ := by
      rw [finrank_euclideanSpace]
      exact inv_strictAnti₀ (by exact_mod_cast Fintype.card_pos) hn
    set C : ℝ≥0∞ := ENNReal.ofReal ((finrank ℝ (EuclideanSpace ℝ ι) : ℝ)⁻¹ *
      mu.real (Metric.ball 0 1) ^ (-(finrank ℝ (EuclideanSpace ℝ ι) : ℝ)⁻¹) *
      ((1 - r⁻¹) / ((finrank ℝ (EuclideanSpace ℝ ι) : ℝ)⁻¹ - r⁻¹)) ^ (1 - r⁻¹)) *
      mu Omega ^ ((finrank ℝ (EuclideanSpace ℝ ι) : ℝ)⁻¹ - r⁻¹)
    have hC : C ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.2 hδn.le) hOmega)
    refine ⟨C.toNNReal, fun v hv ↦ ?_⟩
    rw [ENNReal.coe_toNNReal hC]
    exact W1p.eLpNorm_value_le_mul_measure_rpow_mul_enorm_gradient_of_lt hOmega h2q hδ hδn hv

/-- **The weak maximum principle with a drift in `Lᵖ`** (Gilbarg–Trudinger, Theorem 8.1 and the
remark after Theorem 8.16). Let `Ω ⊆ ℝⁿ`, `n ≥ 1`, be open with finite measure, and let

`L u = -∂ᵢ(aⁱʲ ∂ⱼu + eⁱ u) + bⁱ ∂ᵢu + c u`

have measurable, uniformly elliptic `a` with constants `λ, Λ`, a drift `b ∈ Lᵖ(Ω)` with
`max(2, n) < p < ∞`, and bounded measurable `c`, `e` satisfying the weak sign condition
`∫ c φ + ⟪e, ∇φ⟫ ≥ 0` for every nonnegative `φ ∈ H¹₀(Ω)`. If `u ∈ H¹(Ω)` is a weak subsolution,
`a_{0, c}(u, φ) + ∫ u ⟪e, ∇φ⟫ + ∫ ⟪b, ∇u⟫ φ ≤ 0` for every nonnegative `φ ∈ H¹₀(Ω)`, and
`(u - k)⁺ ∈ H¹₀(Ω)` for some `k ≥ 0`, then `u ≤ k` almost everywhere. No smallness of `b` and no
regularity of `∂Ω` is needed. -/
theorem UniformlyEllipticOn.value_le_const_of_memLp_drift_of_measure_ne_top [Nonempty ι]
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) (hb : MemLp b p (mu.restrict Omega))
    (hp : p ≠ ∞) (hp2 : 2 < p) (hn : (Fintype.card ι : ℝ) < p.toReal)
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (he : AEStronglyMeasurable e (mu.restrict Omega))
    (hc_bound : ∀ x ∈ Omega, ‖c x‖ ≤ gamma) (he_bound : ∀ x ∈ Omega, ‖e x‖ ≤ sigma)
    (hsign : ∀ φ : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (φ : W1p mu Omega 2) x) →
        0 ≤ ∫ x in Omega, c x * W1p.value (φ : W1p mu Omega 2) x +
          ⟪e x, W1p.gradient (φ : W1p mu Omega 2) x⟫_ℝ ∂mu)
    (hOmega : mu Omega ≠ ∞) {k : ℝ} (hk : 0 ≤ k) {u : W1p mu Omega 2}
    (hboundary : W1p.posPartAbove (by norm_num) hk u ∈ w1p0Submodule mu Omega 2)
    (hu : ∀ φ : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (φ : W1p mu Omega 2) x) →
        energyFormH1 a 0 c u (φ : W1p mu Omega 2) +
          ∫ x in Omega, W1p.value u x * ⟪e x, W1p.gradient (φ : W1p mu Omega 2) x⟫_ℝ ∂mu +
          ∫ x in Omega, ⟪b x, W1p.gradient u x⟫_ℝ * W1p.value (φ : W1p mu Omega 2) x ∂mu ≤ 0) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ k := by
  obtain ⟨q, hpq, S, hsob⟩ := exists_inv_add_inv_eq_and_forall_eLpNorm_le hOmega hp hp2 hn
  exact h.value_le_const_of_memLp_drift_of_forall_eLpNorm_le ha hb hp hc he hc_bound he_bound
    hsign hpq hsob hk hboundary hu

/-- **The comparison principle with a drift in `Lᵖ`.** Under the hypotheses of
`TauCeti.PDE.UniformlyEllipticOn.value_le_const_of_memLp_drift_of_measure_ne_top`, if `L u ≤ L v`
weakly and `(u - v)⁺ ∈ H¹₀(Ω)`, then `u ≤ v` almost everywhere. In particular the weak Dirichlet
problem for `L` has at most one solution. -/
theorem UniformlyEllipticOn.value_le_of_memLp_drift_of_measure_ne_top [Nonempty ι]
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) (hb : MemLp b p (mu.restrict Omega))
    (hp : p ≠ ∞) (hp2 : 2 < p) (hn : (Fintype.card ι : ℝ) < p.toReal)
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (he : AEStronglyMeasurable e (mu.restrict Omega))
    (hc_bound : ∀ x ∈ Omega, ‖c x‖ ≤ gamma) (he_bound : ∀ x ∈ Omega, ‖e x‖ ≤ sigma)
    (hsign : ∀ φ : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (φ : W1p mu Omega 2) x) →
        0 ≤ ∫ x in Omega, c x * W1p.value (φ : W1p mu Omega 2) x +
          ⟪e x, W1p.gradient (φ : W1p mu Omega 2) x⟫_ℝ ∂mu)
    (hOmega : mu Omega ≠ ∞) {u v : W1p mu Omega 2}
    (hboundary : W1p.posPart (by norm_num) (u - v) ∈ w1p0Submodule mu Omega 2)
    (huv : ∀ φ : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (φ : W1p mu Omega 2) x) →
        energyFormH1 a 0 c u (φ : W1p mu Omega 2) +
            ∫ x in Omega, W1p.value u x * ⟪e x, W1p.gradient (φ : W1p mu Omega 2) x⟫_ℝ ∂mu +
            ∫ x in Omega, ⟪b x, W1p.gradient u x⟫_ℝ * W1p.value (φ : W1p mu Omega 2) x ∂mu ≤
          energyFormH1 a 0 c v (φ : W1p mu Omega 2) +
            ∫ x in Omega, W1p.value v x * ⟪e x, W1p.gradient (φ : W1p mu Omega 2) x⟫_ℝ ∂mu +
            ∫ x in Omega, ⟪b x, W1p.gradient v x⟫_ℝ * W1p.value (φ : W1p mu Omega 2) x ∂mu) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ W1p.value v x := by
  obtain ⟨q, hpq, S, hsob⟩ := exists_inv_add_inv_eq_and_forall_eLpNorm_le hOmega hp hp2 hn
  exact h.value_le_of_memLp_drift_of_forall_eLpNorm_le ha hb hp hc he hc_bound he_bound hsign hpq
    hsob hboundary huv

end TauCeti.PDE
