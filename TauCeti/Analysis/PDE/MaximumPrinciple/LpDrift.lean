/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.MaximumPrinciple.Drift
import Mathlib.MeasureTheory.Function.UniformIntegrable
import TauCeti.Analysis.PDE.MaximumPrinciple.GlobalBoundedness.Basic
import TauCeti.Analysis.Sobolev.W1p.LevelSet

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
`q > n`.

Under a Sobolev inequality the drift may be split into a bounded part and a part in `Lᵖ`: it
suffices that `‖b‖ ≤ β + d` on `Ω` for a constant `β` and some `d ∈ Lᵖ(Ω)`
(`TauCeti.PDE.UniformlyEllipticOn.value_le_const_of_memLp_drift_of_forall_eLpNorm_le`), and then
`Ω` need not have finite measure. This covers bounded drifts (`d = 0`) as well as drifts in `Lᵖ`
(`β = 0`, `d = ‖b‖`).

## The argument

The argument is Gilbarg–Trudinger's, with Hölder's inequality in three exponents in place of the
bound `‖b‖ ≤ β`. Suppose that `‖w‖_q ≤ S ‖∇w‖₂` on `H¹₀(Ω)` with `1/p + 1/q = 1/2`. For a level
`l ≥ k` put `v = (u - l)⁺`. The sign condition reduces the operator tested against `v` to
`-∂ᵢ(aⁱʲ ∂ⱼ·) - eⁱ ∂ᵢ` with no mass (`TauCeti.PDE.energyFormH1_sub_zero_posPartAbove_self_le`), and
since `∇u = ∇v` where `v ≠ 0`, with `W = σ + β + |d|`,

`λ ‖∇v‖₂² ≤ ∫_Γ W |∇v| v ≤ ‖1_Γ W‖_p ‖∇v‖₂ ‖v‖_q ≤ S ‖1_Γ W‖_p ‖∇v‖₂²`,

where `σ` bounds `e` and `Γ = {u > l, ∇u ≠ 0}`, outside of which `∇v = 0`
(`TauCeti.W1p.ae_mem_of_gradient_posPartAbove_ne_zero`, and
`TauCeti.W1p.ofReal_integral_mul_norm_gradient_mul_norm_value_eq` for the first step). If `u > l`
on a set of positive measure then `∇v ≠ 0` (`TauCeti.W1p.enorm_gradient_posPartAbove_ne_zero`),
so `λ ≤ S ‖1_Γ W‖_p`. As `|Γ| → 0`, `‖1_Γ W‖_p → 0`, because `p < ∞` and `d ∈ Lᵖ`
(`MeasureTheory.MemLp.tendsto_eLpNorm_restrict_zero`), and the level-set argument
`TauCeti.W1p.ae_value_le_of_forall_le_of_tendsto` concludes, as it does for bounded drifts in
`TauCeti.PDE.UniformlyEllipticOn.value_le_const_of_forall_eLpNorm_le`.

On a set of finite measure the Sobolev inequality holds with `q = 2p/(p - 2)` as soon as `p > n`
(`TauCeti.PDE.exists_inv_add_inv_eq_and_forall_eLpNorm_value_le_of_measure_ne_top`), and bounded
drifts lie in `Lᵖ(Ω)`.

## Main declarations

* `TauCeti.PDE.UniformlyEllipticOn.value_le_const_of_memLp_drift_of_forall_eLpNorm_le`: the weak
  maximum principle for a drift `‖b‖ ≤ β + d`, `d ∈ Lᵖ`, under a Sobolev inequality
  `‖w‖_q ≤ S ‖∇w‖₂` on `H¹₀(Ω)`, `1/p + 1/q = 1/2`.
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
  {c d : EuclideanSpace ℝ ι → ℝ} {lam Lam beta gamma sigma : ℝ} {p q : ℝ≥0∞}

/-- If `d ∈ Lᵖ`, `g ∈ L²` and `f ∈ L² ∩ L^q` with `1/p + 1/q = 1/2`, then `(C + |d|) |g| |f|` is
integrable for every constant `C`. -/
private theorem integrable_const_add_norm_mul_norm_mul_norm {μ : Measure (EuclideanSpace ℝ ι)}
    (C : ℝ) (hd : MemLp d p μ) (hpq : p⁻¹ + q⁻¹ = 2⁻¹)
    {g : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} (hg : MemLp g 2 μ)
    {f : EuclideanSpace ℝ ι → ℝ} (hf : MemLp f 2 μ) (hfq : MemLp f q μ) :
    Integrable (fun x ↦ (C + ‖d x‖) * (‖g x‖ * ‖f x‖)) μ := by
  have : p.HolderTriple q 2 := ⟨hpq⟩
  exact (((hg.norm.integrable_mul hf.norm).const_mul C).add
    (hd.integrable_norm_mul_norm_mul_norm (r := 2) (s := 2) hg hfq)).congr
    (ae_of_all _ fun x ↦ by simp only [Pi.add_apply, Pi.mul_apply]; ring)

omit [mu.IsAddHaarMeasure] in
/-- If `‖b‖ ≤ β + |d|` on `Ω`, then `|⟪b, g⟫ f| ≤ (β + |d|) |g| |f|` almost everywhere on `Ω`. -/
private theorem ae_norm_inner_mul_le_const_add_norm_mul
    (hb_bound : ∀ x ∈ Omega, ‖b x‖ ≤ beta + ‖d x‖)
    (g : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (f : EuclideanSpace ℝ ι → ℝ) :
    ∀ᵐ x ∂mu.restrict Omega, ‖⟪b x, g x⟫_ℝ * f x‖ ≤ (beta + ‖d x‖) * (‖g x‖ * ‖f x‖) := by
  filter_upwards [ae_restrict_mem Omega.isOpen.measurableSet] with x hx
  rw [norm_mul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right ((norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (hb_bound x hx) (norm_nonneg _))) (norm_nonneg _)

/-- If `‖b‖ ≤ β + |d|` on `Ω` with `d ∈ Lᵖ`, `u ∈ H¹(Ω)` and `φ ∈ H¹(Ω) ∩ L^q` with
`1/p + 1/q = 1/2`, then the drift term `⟪b, ∇u⟫ φ` of the weak form is integrable. -/
private theorem integrable_inner_gradient_mul_value
    (hb : AEStronglyMeasurable b (mu.restrict Omega)) (hd : MemLp d p (mu.restrict Omega))
    (hb_bound : ∀ x ∈ Omega, ‖b x‖ ≤ beta + ‖d x‖)
    (hpq : p⁻¹ + q⁻¹ = 2⁻¹) (u : W1p mu Omega 2) {φ : W1p mu Omega 2}
    (hφ : MemLp (W1p.value φ) q (mu.restrict Omega)) :
    Integrable (fun x ↦ ⟪b x, W1p.gradient u x⟫_ℝ * W1p.value φ x) (mu.restrict Omega) :=
  (integrable_const_add_norm_mul_norm_mul_norm beta hd hpq (Lp.memLp (W1p.gradient u))
    (Lp.memLp _) hφ).mono'
    ((hb.inner (Lp.aestronglyMeasurable _)).mul (Lp.aestronglyMeasurable _))
    (ae_norm_inner_mul_le_const_add_norm_mul hb_bound _ _)

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

/-- The energy inequality behind the weak maximum principle with a drift `‖b‖ ≤ β + |d|`,
`d ∈ Lᵖ`: for a weak subsolution `u` and `v = (u - l)⁺ ∈ H¹₀(Ω) ∩ L^q`,
`λ ‖∇v‖₂² ≤ ∫ (σ + β + |d|) |∇v| v`. -/
private theorem UniformlyEllipticOn.mul_norm_gradient_sq_le_integral_of_memLp_drift
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) (hd : MemLp d p (mu.restrict Omega))
    (hb_bound : ∀ x ∈ Omega, ‖b x‖ ≤ beta + ‖d x‖)
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (he : AEStronglyMeasurable e (mu.restrict Omega))
    (hc_bound : ∀ x ∈ Omega, ‖c x‖ ≤ gamma) (he_bound : ∀ x ∈ Omega, ‖e x‖ ≤ sigma)
    (hsign : ∀ φ : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (φ : W1p mu Omega 2) x) →
        0 ≤ ∫ x in Omega, c x * W1p.value (φ : W1p mu Omega 2) x +
          ⟪e x, W1p.gradient (φ : W1p mu Omega 2) x⟫_ℝ ∂mu)
    (hpq : p⁻¹ + q⁻¹ = 2⁻¹) {l : ℝ} (hl : 0 ≤ l) {u : W1p mu Omega 2}
    (hmem : W1p.posPartAbove (by norm_num) hl u ∈ w1p0Submodule mu Omega 2)
    (hfq : MemLp (W1p.value (W1p.posPartAbove (by norm_num) hl u)) q (mu.restrict Omega))
    (hu : ∀ φ : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (φ : W1p mu Omega 2) x) →
        energyFormH1 a 0 c u (φ : W1p mu Omega 2) +
          ∫ x in Omega, W1p.value u x * ⟪e x, W1p.gradient (φ : W1p mu Omega 2) x⟫_ℝ ∂mu +
          ∫ x in Omega, ⟪b x, W1p.gradient u x⟫_ℝ * W1p.value (φ : W1p mu Omega 2) x ∂mu ≤ 0) :
    lam * ‖W1p.gradient (W1p.posPartAbove (by norm_num) hl u)‖ ^ 2 ≤
      ∫ x in Omega, (sigma + beta + ‖d x‖) *
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
  have hint₂ : Integrable (fun x ↦ (beta + ‖d x‖) * (‖g x‖ * ‖f x‖)) (mu.restrict Omega) :=
    integrable_const_add_norm_mul_norm_mul_norm beta hd hpq (Lp.memLp g) (Lp.memLp f) hfq
  have hneg : -∫ x in Omega, ⟪b x, g x⟫_ℝ * f x ∂mu ≤
      ∫ x in Omega, (beta + ‖d x‖) * (‖g x‖ * ‖f x‖) ∂mu := by
    refine (neg_le_abs _).trans ((Real.norm_eq_abs _).symm.le.trans
      ((norm_integral_le_integral_norm _).trans
      (integral_mono_of_nonneg (ae_of_all _ fun x ↦ norm_nonneg _) hint₂
        (ae_norm_inner_mul_le_const_add_norm_mul hb_bound g f))))
  have h₁ := mul_norm_gradient_sq_sub_le_energyFormH1_self h hcoeff' hbe_bound
    (fun _ _ ↦ le_rfl) v
  have h₂ := energyFormH1_sub_zero_posPartAbove_self_le hcoeff hcoeff' hc he hc_bound he_bound
    hsign hl hmem
  have h₃ := hu ⟨v, hmem⟩ (W1p.value_posPartAbove_nonneg_ae (by norm_num) hl u)
  simp only at h₃
  rw [integral_inner_gradient_mul_value_posPartAbove hl u] at h₃
  have hsplit : ∫ x in Omega, (sigma + beta + ‖d x‖) * (‖g x‖ * ‖f x‖) ∂mu =
      sigma * ∫ x in Omega, ‖g x‖ * ‖f x‖ ∂mu +
        ∫ x in Omega, (beta + ‖d x‖) * (‖g x‖ * ‖f x‖) ∂mu := by
    rw [← integral_const_mul, ← integral_add (hint₁.const_mul sigma) hint₂]
    exact integral_congr_ae (ae_of_all _ fun x ↦ by ring)
  rw [hsplit]
  linarith

/-- The level estimate of the weak maximum principle with a drift `‖b‖ ≤ β + |d|`, `d ∈ Lᵖ`.
Let `u` be a weak subsolution and let `l ≥ k ≥ 0` be a level which `u` exceeds on a set of
positive measure, with `(u - k)⁺ ∈ H¹₀(Ω)`. Then `λ ≤ S ‖1_Γ (σ + β + |d|)‖_p` for
`Γ = {u > l, ∇u ≠ 0}`. -/
private theorem UniformlyEllipticOn.ofReal_le_mul_eLpNorm_indicator_of_not_ae_value_le
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) (hd : MemLp d p (mu.restrict Omega))
    (hb_bound : ∀ x ∈ Omega, ‖b x‖ ≤ beta + ‖d x‖) (hbeta : 0 ≤ beta)
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
      fun x ↦ sigma + beta + ‖d x‖) p (mu.restrict Omega) := by
  set μ := mu.restrict Omega
  have hl : 0 ≤ l := hk.trans hkl
  set v := W1p.posPartAbove (by norm_num) hl u
  set f := W1p.value v
  set g := W1p.gradient v
  set Γ := {x | l < W1p.value u x ∧ W1p.gradient u x ≠ 0}
  have hmem : v ∈ w1p0Submodule mu Omega 2 :=
    W1p.posPartAbove_mem_w1p0Submodule_of_le (by norm_num) hk hkl hboundary
  have hfq : MemLp f q μ :=
    memLp_iff.2 ((hsob v hmem).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top eNorm_lt_top))
  have hΓ : MeasurableSet Γ := W1p.measurableSet_lt_value_and_gradient_ne_zero u l
  -- `λ ‖∇v‖² ≤ ∫_Γ (σ + β + |d|) |∇v| v ≤ ‖1_Γ (σ + β + |d|)‖_p ‖∇v‖₂ ‖v‖_q`, since `∇v = 0`
  -- almost everywhere outside `Γ`.
  have hlin := (ENNReal.ofReal_le_ofReal (h.mul_norm_gradient_sq_le_integral_of_memLp_drift ha hd
    hb_bound hc he hc_bound he_bound hsign hpq hl hmem hfq hu)).trans_eq
    (W1p.ofReal_integral_mul_norm_gradient_mul_norm_value_eq (ae_of_all _ fun x ↦ by positivity)
      (integrable_const_add_norm_mul_norm_mul_norm (sigma + beta) hd hpq (Lp.memLp g)
        (Lp.memLp f) hfq) hΓ (W1p.ae_mem_of_gradient_posPartAbove_ne_zero (by norm_num) hl u))
  have hholder : ∫⁻ x in Γ, ‖sigma + beta + ‖d x‖‖ₑ * (‖g x‖ₑ * ‖f x‖ₑ) ∂μ ≤
      eLpNorm (Γ.indicator fun x ↦ sigma + beta + ‖d x‖) p μ *
        (eLpNorm g 2 μ * eLpNorm f q μ) := by
    have : p.HolderTriple q 2 := ⟨hpq⟩
    refine (lintegral_enorm_mul_enorm_mul_enorm_le (p := p) (q := q) (r := 2) (s := 2)
      (w := fun x ↦ sigma + beta + ‖d x‖)
      (aestronglyMeasurable_const.add hd.aestronglyMeasurable.norm).restrict
      (Lp.aestronglyMeasurable g).restrict (Lp.aestronglyMeasurable f).restrict).trans ?_
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hΓ.nullMeasurableSet]
    gcongr <;> exact Measure.restrict_le_self
  set B := eLpNorm (Γ.indicator fun x ↦ sigma + beta + ‖d x‖) p μ
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
  have hN := W1p.enorm_gradient_posPartAbove_ne_zero (by norm_num) hl hq0 (hsob v hmem) hnot
  exact (ENNReal.mul_le_mul_iff_left (pow_ne_zero 2 hN) (ENNReal.pow_ne_top eNorm_ne_top)).1 hcore

/-- **The weak maximum principle with a drift in `L^∞ + Lᵖ`**, under a Sobolev inequality
(Gilbarg–Trudinger, Theorem 8.1 and the remark after Theorem 8.16). Let `Ω ⊆ ℝⁿ` be open, let
`1/p + 1/q = 1/2` with `p < ∞`, and suppose `‖w‖_q ≤ S ‖∇w‖₂` on `H¹₀(Ω)`. Let

`L u = -∂ᵢ(aⁱʲ ∂ⱼu + eⁱ u) + bⁱ ∂ᵢu + c u`

have measurable, uniformly elliptic `a` with constants `λ, Λ`, a drift with
`‖b‖ ≤ β + d` on `Ω` for a constant `β` and some `d ∈ Lᵖ(Ω)`, and bounded measurable `c`, `e`
satisfying the weak sign condition `∫ c φ + ⟪e, ∇φ⟫ ≥ 0` for every nonnegative `φ ∈ H¹₀(Ω)`. If
`u ∈ H¹(Ω)` is a weak subsolution, `a_{0, c}(u, φ) + ∫ u ⟪e, ∇φ⟫ + ∫ ⟪b, ∇u⟫ φ ≤ 0` for every
nonnegative `φ ∈ H¹₀(Ω)`, and `(u - k)⁺ ∈ H¹₀(Ω)` for some `k ≥ 0`, then `u ≤ k` almost
everywhere. No smallness of `b` is needed, and `Ω` need not have finite measure. A drift `b ∈ Lᵖ`
is the case `β = 0`, `d = ‖b‖`, and a bounded drift `‖b‖ ≤ β` the case `d = 0`. -/
theorem UniformlyEllipticOn.value_le_const_of_memLp_drift_of_forall_eLpNorm_le
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) (hd : MemLp d p (mu.restrict Omega))
    (hp : p ≠ ∞) (hb_bound : ∀ x ∈ Omega, ‖b x‖ ≤ beta + d x)
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
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
  have hb_bound' : ∀ x ∈ Omega, ‖b x‖ ≤ max beta 0 + ‖d x‖ :=
    fun x hx ↦ (hb_bound x hx).trans (add_le_add (le_max_left _ _) (Real.le_norm_self _))
  set C := max sigma 0 + max beta 0
  have hp1 : 1 ≤ p := one_le_two.trans (ENNReal.inv_le_inv.1 (hpq ▸ le_self_add))
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  -- At every admissible level `l`, `λ ≤ S ‖1_Γ (C + |d|)‖_p` for `Γ = {u > l, ∇u ≠ 0}`.
  refine W1p.ae_value_le_of_forall_le_of_tendsto (by norm_num) u hk
    (F := fun Γ ↦ S * eLpNorm (Γ.indicator fun x ↦ C + ‖d x‖) p μ) (fun Γ hΓ htend ↦ ?_)
    (ENNReal.ofReal_pos.2 h.pos).ne' fun l hkl hnot ↦
      h.ofReal_le_mul_eLpNorm_indicator_of_not_ae_value_le ha hd hb_bound' (le_max_right _ _)
        hc he hc_bound he_bound' (le_max_right _ _) hsign hpq hsob hk hkl hboundary hu hnot
  -- `‖1_Γ (C + |d|)‖_p → 0` as `|Γ| → 0`, since `p < ∞` and `d ∈ Lᵖ`.
  have hconst : Tendsto (fun j ↦ eLpNorm ((Γ j).indicator fun _ ↦ C) p μ) atTop (𝓝 0) := by
    have hexp : 0 < 1 / p.toReal := one_div_pos.2 (ENNReal.toReal_pos hp0 hp)
    simp_rw [eLpNorm_indicator_const (hΓ _).nullMeasurableSet hp0 hp]
    have h := ENNReal.Tendsto.const_mul (a := ‖C‖ₑ)
      (((ENNReal.continuous_rpow_const (y := 1 / p.toReal)).tendsto 0).comp htend)
      (Or.inr eNorm_ne_top)
    rwa [ENNReal.zero_rpow_of_pos hexp, mul_zero] at h
  have hdrift : Tendsto (fun j ↦ eLpNorm ((Γ j).indicator fun x ↦ ‖d x‖) p μ) atTop (𝓝 0) := by
    simp_rw [eLpNorm_indicator_eq_eLpNorm_restrict (hΓ _).nullMeasurableSet]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      ((hd.norm.tendsto_eLpNorm_restrict_zero hp1 hp).comp htend)
      (Eventually.of_forall fun _ ↦ bot_le)
      (Eventually.of_forall fun j ↦ le_iSup_of_le (Γ j) (le_iSup_of_le le_rfl le_rfl))
  have hsum : Tendsto (fun j ↦ eLpNorm ((Γ j).indicator fun x ↦ C + ‖d x‖) p μ) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using hconst.add hdrift) (fun _ ↦ zero_le) fun j ↦ ?_
    calc eLpNorm ((Γ j).indicator fun x ↦ C + ‖d x‖) p μ
        = eLpNorm (((Γ j).indicator fun _ ↦ C) + (Γ j).indicator fun x ↦ ‖d x‖) p μ := by
          congr 1
          ext x
          by_cases hx : x ∈ Γ j <;> simp [hx]
      _ ≤ eLpNorm ((Γ j).indicator fun _ ↦ C) p μ +
            eLpNorm ((Γ j).indicator fun x ↦ ‖d x‖) p μ := eLpNorm_add_le hp1
  simpa using ENNReal.Tendsto.const_mul hsum (Or.inr ENNReal.coe_ne_top)

/-- **The comparison principle with a drift in `L^∞ + Lᵖ`**, under a Sobolev inequality. Under
the hypotheses of
`TauCeti.PDE.UniformlyEllipticOn.value_le_const_of_memLp_drift_of_forall_eLpNorm_le`, with `b`
measurable, if `L u ≤ L v` weakly and `(u - v)⁺ ∈ H¹₀(Ω)`, then `u ≤ v` almost everywhere. -/
theorem UniformlyEllipticOn.value_le_of_memLp_drift_of_forall_eLpNorm_le
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega)) (hd : MemLp d p (mu.restrict Omega))
    (hp : p ≠ ∞) (hb_bound : ∀ x ∈ Omega, ‖b x‖ ≤ beta + d x)
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
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
  have hb_bound' : ∀ x ∈ Omega, ‖b x‖ ≤ beta + ‖d x‖ :=
    fun x hx ↦ (hb_bound x hx).trans (add_le_add_right (Real.le_norm_self _) _)
  -- The weak form is linear in `u`, so `u - v` is a weak subsolution.
  have hsub := h.value_le_const_of_memLp_drift_of_forall_eLpNorm_le ha hd hp hb_bound hc he
    hc_bound he_bound hsign hpq hsob le_rfl (u := u - v) (by rwa [W1p.posPartAbove_zero])
    fun φ hφ ↦ by
      have hφq : MemLp (W1p.value (φ : W1p mu Omega 2)) q (mu.restrict Omega) :=
        memLp_iff.2 ((hsob _ φ.property).trans_lt
          (ENNReal.mul_lt_top ENNReal.coe_lt_top eNorm_lt_top))
      have hint_b : ∫ x in Omega, ⟪b x, W1p.gradient (u - v) x⟫_ℝ *
            W1p.value (φ : W1p mu Omega 2) x ∂mu =
          (∫ x in Omega, ⟪b x, W1p.gradient u x⟫_ℝ * W1p.value (φ : W1p mu Omega 2) x ∂mu) -
            ∫ x in Omega, ⟪b x, W1p.gradient v x⟫_ℝ * W1p.value (φ : W1p mu Omega 2) x ∂mu := by
        rw [← integral_sub (integrable_inner_gradient_mul_value hb hd hb_bound' hpq u hφq)
          (integrable_inner_gradient_mul_value hb hd hb_bound' hpq v hφq)]
        refine integral_congr_ae ?_
        filter_upwards [W1p.gradient_sub_ae u v] with x hx
        rw [hx, Pi.sub_apply, inner_sub_right, sub_mul]
      rw [energyFormH1_sub_left hcoeff, integral_value_sub_mul_inner_gradient he he_bound, hint_b]
      linarith [huv φ hφ]
  filter_upwards [hsub, W1p.value_sub_ae u v] with x hx hval
  rw [hval, Pi.sub_apply] at hx
  exact sub_nonpos.mp hx

/-- **The weak maximum principle with a drift in `Lᵖ`** (Gilbarg–Trudinger, Theorem 8.1 and the
remark after Theorem 8.16). Let `Ω ⊆ ℝⁿ`, `n ≥ 1`, be open with finite measure, and let

`L u = -∂ᵢ(aⁱʲ ∂ⱼu + eⁱ u) + bⁱ ∂ᵢu + c u`

have measurable, uniformly elliptic `a` with constants `λ, Λ`, a drift `b ∈ Lᵖ(Ω)` with
`max(2, n) < p < ∞`, and bounded measurable `c`, `e` satisfying the weak sign condition
`∫ c φ + ⟪e, ∇φ⟫ ≥ 0` for every nonnegative `φ ∈ H¹₀(Ω)`. If `u ∈ H¹(Ω)` is a weak subsolution,
`a_{0, c}(u, φ) + ∫ u ⟪e, ∇φ⟫ + ∫ ⟪b, ∇u⟫ φ ≤ 0` for every nonnegative `φ ∈ H¹₀(Ω)`, and
`(u - k)⁺ ∈ H¹₀(Ω)` for some `k ≥ 0`, then `u ≤ k` almost everywhere. No smallness of `b` and no
regularity of `∂Ω` is needed. Since `Ω` has finite measure, bounded drifts lie in `Lᵖ(Ω)`. -/
theorem UniformlyEllipticOn.value_le_const_of_memLp_drift_of_measure_ne_top [Nonempty ι]
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) (hb : MemLp b p (mu.restrict Omega))
    (hp2 : 2 < p) (hn : (Fintype.card ι : ℝ) < p.toReal)
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
  have hp : p ≠ ∞ := (ENNReal.toReal_pos_iff.1 ((Nat.cast_nonneg _).trans_lt hn)).2.ne
  obtain ⟨q, hpq, S, hsob⟩ :=
    exists_inv_add_inv_eq_and_forall_eLpNorm_value_le_of_measure_ne_top hOmega hp2 hn
  exact h.value_le_const_of_memLp_drift_of_forall_eLpNorm_le ha hb.norm hp
    (beta := 0) (fun x _ ↦ (zero_add _).ge) hc he hc_bound he_bound hsign hpq hsob hk hboundary hu

/-- **The comparison principle with a drift in `Lᵖ`.** Under the hypotheses of
`TauCeti.PDE.UniformlyEllipticOn.value_le_const_of_memLp_drift_of_measure_ne_top`, if `L u ≤ L v`
weakly and `(u - v)⁺ ∈ H¹₀(Ω)`, then `u ≤ v` almost everywhere. In particular the weak Dirichlet
problem for `L` has at most one solution. -/
theorem UniformlyEllipticOn.value_le_of_memLp_drift_of_measure_ne_top [Nonempty ι]
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) (hb : MemLp b p (mu.restrict Omega))
    (hp2 : 2 < p) (hn : (Fintype.card ι : ℝ) < p.toReal)
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
  have hp : p ≠ ∞ := (ENNReal.toReal_pos_iff.1 ((Nat.cast_nonneg _).trans_lt hn)).2.ne
  obtain ⟨q, hpq, S, hsob⟩ :=
    exists_inv_add_inv_eq_and_forall_eLpNorm_value_le_of_measure_ne_top hOmega hp2 hn
  exact h.value_le_of_memLp_drift_of_forall_eLpNorm_le ha hb.aestronglyMeasurable hb.norm hp
    (beta := 0) (fun x _ ↦ (zero_add _).ge) hc he hc_bound he_bound hsign hpq hsob hboundary huv

end TauCeti.PDE
