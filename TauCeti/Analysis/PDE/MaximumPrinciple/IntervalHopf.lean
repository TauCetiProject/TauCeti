/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Interval.Representative
public import TauCeti.Analysis.Sobolev.W1p.Zero
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import TauCeti.Analysis.Sobolev.W1p.Interval.AbsolutelyContinuous
import TauCeti.Analysis.SpecialFunctions.Ramp
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Comp
import TauCeti.MeasureTheory.Function.LpSeminorm.ContinuousOn
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive

/-!
# Hopf's boundary-point lemma for weak supersolutions on an interval

On an interval `(x₀, x₁)` consider the divergence-form operator

`L u = (a u' + b u)' + c u' + d u`

in the sign convention of Gilbarg–Trudinger, Chapter 8: `u ∈ W^{1,2}(x₀, x₁)` is a *weak
supersolution*, `L u ≤ 0`, when

`∫ ((a u' + b u) w' - (c u' + d u) w) ≥ 0` for every `w ∈ W^{1,2}_0(x₀, x₁)` with `w ≥ 0`.

The coefficients are only assumed to satisfy `λ ≤ a ≤ Λ` with `λ > 0` and `|b| ≤ β` almost
everywhere, `a` and `b` measurable, `c ∈ L²` and `d ∈ L¹`. **Hopf's lemma**
(`TauCeti.PDE.IsIntervalWeakSupersolution.exists_pos_mul_le_intervalRepresentativeL`) says that
if the continuous representative of such a `u` vanishes at `x₀` and is positive on `(x₀, x₁)`,
then it leaves `x₀` at a positive linear rate: `ε h ≤ u (x₀ + h)` for some `ε > 0` and all small
`h > 0`. In particular a right derivative of `u` at `x₀`, if it exists, is positive
(`TauCeti.PDE.IsIntervalWeakSupersolution.pos_of_hasDerivWithinAt_intervalRepresentativeL`).
No sign condition is imposed on `b`, `c` or `d`. In higher dimensions the divergence-form Hopf
lemma needs some continuity of the coefficients at the boundary point (Rosales assumes Hölder
continuous `a` and `b`). In one dimension no continuity of the coefficients is needed: the
weighted flux is monotone up to an integrable error.

## The argument

Let `q = c / a` and let `m = exp (∫ q)` be the integrating factor. Testing the supersolution
inequality with `m φ` cancels the first-order term: for the weighted flux `Φ = m (a u' + b u)`
and `k = m (d - q b) u`,

`∫ k φ ≤ ∫ Φ φ'` for every absolutely continuous `φ ≥ 0` with `φ' ∈ L²`, vanishing at `x₀` and
`x₁`.

Taking for `φ` the difference of two ramps of width `δ` and letting `δ → 0` at two Lebesgue
points `s < t` of `Φ` gives `Φ t ≤ Φ s + ∫ y in s..t, |k y|`. So either `Φ s` exceeds the mass of
`|k|` on `(x₀, s)` at some Lebesgue point `s`, and then the flux, hence `u'`, is bounded below by
a positive constant near `x₀`; or `Φ y ≤ ∫ z in x₀..y, |k z|` almost everywhere. In the second case
`k` is controlled by `u`, so `u' ≤ C max_{[x₀, x₀ + h]} u` on `(x₀, x₀ + h)`, and integrating from
`x₀`, where `u` vanishes, forces `u = 0` on a short interval, contradicting its positivity.

## Main declarations

* `TauCeti.PDE.IsIntervalWeakSupersolution`: `u ∈ W^{1,2}(x₀, x₁)` is a weak supersolution of
  `(a u' + b u)' + c u' + d u ≤ 0`.
* `TauCeti.PDE.IsIntervalWeakSupersolution.of_integral_nonneg`: for `a ∈ L^∞`, `b ∈ L²`,
  `c ∈ L²` and `d ∈ L¹`, the integral inequality alone gives a weak supersolution.
* `TauCeti.PDE.IsIntervalWeakSupersolution.integral_nonneg_of_absolutelyContinuousOnInterval`:
  absolutely continuous `ψ ≥ 0` vanishing at both endpoints, with `ψ' ∈ L²`, are admissible test
  functions.
* `TauCeti.PDE.IsIntervalWeakSupersolution.exists_pos_mul_le_intervalRepresentativeL`:
  **Hopf's lemma** for weak supersolutions on an interval, in difference-quotient form.
* `TauCeti.PDE.IsIntervalWeakSupersolution.pos_of_hasDerivWithinAt_intervalRepresentativeL`: the
  derivative form.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 8.1 (weak supersolutions) and Lemma 3.4 (the classical Hopf lemma).
* L. Rosales, *Generalizing Hopf's boundary point lemma*, Canad. Math. Bull. (2019),
  arXiv:1806.07003 (the divergence-form Hopf lemma for weak supersolutions).
-/

public section

open MeasureTheory Set Filter TopologicalSpace
open scoped Topology

namespace TauCeti.PDE

variable {x₀ x₁ s t δ x : ℝ} {a b c d q Φ k : ℝ → ℝ}

/-- `u ∈ W^{1,2}(x₀, x₁)` is a **weak supersolution** of `(a u' + b u)' + c u' + d u ≤ 0`, in the
sign convention of Gilbarg–Trudinger, Chapter 8: for every `w ∈ W^{1,2}_0(x₀, x₁)` with `w ≥ 0`
almost everywhere, the pairing `(a u' + b u) w' - (c u' + d u) w` is integrable on `(x₀, x₁)`
with `∫ ((a u' + b u) w' - (c u' + d u) w) ≥ 0`.

The integrability is part of the definition, since the Bochner integral of a non-integrable
function is `0`. The coefficients are unconstrained here; for `a ∈ L^∞`, `b ∈ L²`, `c ∈ L²` and
`d ∈ L¹` the pairing is integrable for every `u` and `w`, so the integral inequality alone
suffices (`TauCeti.PDE.IsIntervalWeakSupersolution.of_integral_nonneg`). -/
def IsIntervalWeakSupersolution (a b c d : ℝ → ℝ) (u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2) :
    Prop :=
  ∀ w : W1p0 volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2,
    (∀ᵐ y ∂volume.restrict (Ioo x₀ x₁),
      0 ≤ W1p.value (w : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2) y) →
    IntegrableOn (fun y ↦ (a y * W1p.gradient u y + b y * W1p.value u y) *
        W1p.gradient (w : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2) y -
      (c y * W1p.gradient u y + d y * W1p.value u y) *
        W1p.value (w : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2) y) (Ioo x₀ x₁) ∧
    0 ≤ ∫ y in Ioo x₀ x₁, ((a y * W1p.gradient u y + b y * W1p.value u y) *
        W1p.gradient (w : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2) y -
      (c y * W1p.gradient u y + d y * W1p.value u y) *
        W1p.value (w : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2) y)

/-- Being a weak supersolution, written out as the integrability of the pairing with nonnegative
`w ∈ W^{1,2}_0(x₀, x₁)` and the integral inequality. -/
theorem isIntervalWeakSupersolution_iff {u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2} :
    IsIntervalWeakSupersolution a b c d u ↔
      ∀ w : W1p0 volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2,
        (∀ᵐ y ∂volume.restrict (Ioo x₀ x₁),
          0 ≤ W1p.value (w : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2) y) →
        IntegrableOn (fun y ↦ (a y * W1p.gradient u y + b y * W1p.value u y) *
            W1p.gradient (w : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2) y -
          (c y * W1p.gradient u y + d y * W1p.value u y) *
            W1p.value (w : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2) y) (Ioo x₀ x₁) ∧
        0 ≤ ∫ y in Ioo x₀ x₁, ((a y * W1p.gradient u y + b y * W1p.value u y) *
            W1p.gradient (w : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2) y -
          (c y * W1p.gradient u y + d y * W1p.value u y) *
            W1p.value (w : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2) y) :=
  Iff.rfl

namespace IsIntervalWeakSupersolution

variable {u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2}

/-- The pairing of a weak supersolution with a nonnegative test function is integrable. -/
theorem integrableOn (h : IsIntervalWeakSupersolution a b c d u)
    (w : W1p0 volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2)
    (hw : ∀ᵐ y ∂volume.restrict (Ioo x₀ x₁),
      0 ≤ W1p.value (w : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2) y) :
    IntegrableOn (fun y ↦ (a y * W1p.gradient u y + b y * W1p.value u y) *
        W1p.gradient (w : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2) y -
      (c y * W1p.gradient u y + d y * W1p.value u y) *
        W1p.value (w : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2) y) (Ioo x₀ x₁) :=
  (h w hw).1

/-- The integral inequality defining a weak supersolution. -/
theorem integral_nonneg (h : IsIntervalWeakSupersolution a b c d u)
    (w : W1p0 volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2)
    (hw : ∀ᵐ y ∂volume.restrict (Ioo x₀ x₁),
      0 ≤ W1p.value (w : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2) y) :
    0 ≤ ∫ y in Ioo x₀ x₁, ((a y * W1p.gradient u y + b y * W1p.value u y) *
        W1p.gradient (w : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2) y -
      (c y * W1p.gradient u y + d y * W1p.value u y) *
        W1p.value (w : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2) y) :=
  (h w hw).2

/-- Being a weak supersolution only depends on the coefficients almost everywhere on the
interval. -/
theorem congr_ae (h : IsIntervalWeakSupersolution a b c d u) {a' b' c' d' : ℝ → ℝ}
    (ha : a =ᵐ[volume.restrict (Ioo x₀ x₁)] a') (hb : b =ᵐ[volume.restrict (Ioo x₀ x₁)] b')
    (hc : c =ᵐ[volume.restrict (Ioo x₀ x₁)] c') (hd : d =ᵐ[volume.restrict (Ioo x₀ x₁)] d') :
    IsIntervalWeakSupersolution a' b' c' d' u := fun w hw ↦ by
  refine ⟨(h.integrableOn w hw).congr_fun_ae ?_, (h.integral_nonneg w hw).trans_eq
    (integral_congr_ae ?_)⟩ <;>
  · filter_upwards [ha, hb, hc, hd] with y h₁ h₂ h₃ h₄
    rw [h₁, h₂, h₃, h₄]

/-- The zero function is a weak supersolution. -/
@[simp]
theorem zero : IsIntervalWeakSupersolution a b c d (0 : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2) :=
  fun w _ ↦ by
  have hv : ⇑(W1p.value (0 : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2)) =ᵐ[volume.restrict
      (Ioo x₀ x₁)] 0 := by
    simpa only [← W1p.valueL_apply, map_zero] using Lp.coeFn_zero ℝ 2 _
  have hg : ⇑(W1p.gradient (0 : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2)) =ᵐ[volume.restrict
      (Ioo x₀ x₁)] 0 := by
    simpa only [← W1p.gradientL_apply, map_zero] using Lp.coeFn_zero ℝ 2 _
  refine ⟨integrableOn_zero.congr_fun_ae ?_, (integral_zero ℝ ℝ).ge.trans_eq
    (integral_congr_ae ?_)⟩ <;>
  · filter_upwards [hv, hg] with y h₁ h₂
    simp [h₁, h₂]

/-- A nonnegative multiple of a weak supersolution is a weak supersolution. -/
theorem smul (h : IsIntervalWeakSupersolution a b c d u) {r : ℝ} (hr : 0 ≤ r) :
    IsIntervalWeakSupersolution a b c d (r • u) := fun w hw ↦ by
  have hg : ⇑(W1p.gradient (r • u)) =ᵐ[volume.restrict (Ioo x₀ x₁)] r • ⇑(W1p.gradient u) := by
    rw [show W1p.gradient (r • u) = r • W1p.gradient u by
      simpa only [W1p.gradientL_apply] using map_smul W1p.gradientL r u]
    exact Lp.coeFn_smul r (W1p.gradient u)
  refine ⟨IntegrableOn.congr_fun_ae (Integrable.const_mul (h.integrableOn w hw) r) ?_,
    (mul_nonneg hr (h.integral_nonneg w hw)).trans_eq ?_⟩
  on_goal 2 => rw [← integral_const_mul]; refine integral_congr_ae ?_
  all_goals
    filter_upwards [hg, W1p.value_smul_ae r u] with y h₁ h₂
    simp only [h₁, h₂, Pi.smul_apply, smul_eq_mul]
    ring

/-- The sum of two weak supersolutions is a weak supersolution. -/
theorem add (hu : IsIntervalWeakSupersolution a b c d u)
    {v : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2} (hv : IsIntervalWeakSupersolution a b c d v) :
    IsIntervalWeakSupersolution a b c d (u + v) := fun w hw ↦ by
  have hg : ⇑(W1p.gradient (u + v)) =ᵐ[volume.restrict (Ioo x₀ x₁)]
      ⇑(W1p.gradient u) + ⇑(W1p.gradient v) := by
    rw [show W1p.gradient (u + v) = W1p.gradient u + W1p.gradient v by
      simpa only [W1p.gradientL_apply] using map_add W1p.gradientL u v]
    exact Lp.coeFn_add (W1p.gradient u) (W1p.gradient v)
  refine ⟨((hu.integrableOn w hw).add (hv.integrableOn w hw)).congr_fun_ae ?_,
    (add_nonneg (hu.integral_nonneg w hw) (hv.integral_nonneg w hw)).trans_eq ?_⟩
  on_goal 2 =>
    rw [← integral_add (hu.integrableOn w hw) (hv.integrableOn w hw)]
    refine integral_congr_ae ?_
  all_goals
    filter_upwards [hg, W1p.value_add_ae u v] with y h₁ h₂
    simp only [h₁, h₂, Pi.add_apply]
    ring

/-- **Introduction rule.** For `a ∈ L^∞`, `b ∈ L²`, `c ∈ L²` and `d ∈ L¹` the pairing is
integrable for every `u` and `w`, since `u` is essentially bounded on the interval, so the
integral inequality alone makes `u` a weak supersolution. -/
theorem of_integral_nonneg (ha : MemLp a ⊤ (volume.restrict (Ioo x₀ x₁)))
    (hb : MemLp b 2 (volume.restrict (Ioo x₀ x₁)))
    (hc : MemLp c 2 (volume.restrict (Ioo x₀ x₁))) (hd : IntegrableOn d (Ioo x₀ x₁))
    (h : ∀ w : W1p0 volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2,
      (∀ᵐ y ∂volume.restrict (Ioo x₀ x₁),
        0 ≤ W1p.value (w : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2) y) →
      0 ≤ ∫ y in Ioo x₀ x₁, ((a y * W1p.gradient u y + b y * W1p.value u y) *
          W1p.gradient (w : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2) y -
        (c y * W1p.gradient u y + d y * W1p.value u y) *
          W1p.value (w : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2) y)) :
    IsIntervalWeakSupersolution a b c d u := fun w hw ↦ by
  refine ⟨?_, h w hw⟩
  rcases le_or_gt x₁ x₀ with hx | hx
  · simp [Ioo_eq_empty_of_le hx]
  set v : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2 := (w : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2)
  have hF : MemLp (fun y ↦ a y * W1p.gradient u y + b y * W1p.value u y) 2
      (volume.restrict (Ioo x₀ x₁)) :=
    (ha.fun_mul (Lp.memLp (W1p.gradient u))).add (hb.fun_mul (W1p.memLp_top_value u))
  have hG : Integrable (fun y ↦ c y * W1p.gradient u y + d y * W1p.value u y)
      (volume.restrict (Ioo x₀ x₁)) :=
    (hc.integrable_mul (Lp.memLp (W1p.gradient u))).add
      (hd.mul_bdd (Lp.memLp (W1p.value u)).aestronglyMeasurable (W1p.ae_norm_value_le hx u))
  exact (hF.integrable_mul (Lp.memLp (W1p.gradient v))).sub
    (hG.mul_bdd (Lp.memLp (W1p.value v)).aestronglyMeasurable (W1p.ae_norm_value_le hx v))

end IsIntervalWeakSupersolution

/-- The test inequality `∫ k φ ≤ ∫ Φ φ'` for every absolutely continuous `φ ≥ 0` on `[x₀, x₁]`
with `φ' ∈ L²`, vanishing at `x₀` and `x₁`. -/
private def FluxTestInequality (x₀ x₁ : ℝ) (k Φ : ℝ → ℝ) : Prop :=
  ∀ φ : ℝ → ℝ, AbsolutelyContinuousOnInterval φ x₀ x₁ →
    MemLp (deriv φ) 2 (volume.restrict (Ioo x₀ x₁)) → φ x₀ = 0 → φ x₁ = 0 →
    (∀ y ∈ Ioo x₀ x₁, 0 ≤ φ y) →
    ∫ y in Ioo x₀ x₁, k y * φ y ≤ ∫ y in Ioo x₀ x₁, Φ y * deriv φ y

/-- The integrating factor `t ↦ exp (∫ s in x₀..t, q s)`. -/
private noncomputable def integratingFactor (x₀ : ℝ) (q : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (∫ s in x₀..t, q s)

private theorem integratingFactor_pos (t : ℝ) : 0 < integratingFactor x₀ q t :=
  Real.exp_pos _

private theorem integratingFactor_le (hq : Integrable q) (t : ℝ) :
    integratingFactor x₀ q t ≤ Real.exp (∫ s, |q s|) :=
  Real.exp_le_exp.2 (le_of_abs_le (hq.norm_intervalIntegral_le_integral_norm x₀ t))

private theorem exp_neg_le_integratingFactor (hq : Integrable q) (t : ℝ) :
    Real.exp (-∫ s, |q s|) ≤ integratingFactor x₀ q t :=
  Real.exp_le_exp.2 (neg_le_of_abs_le (hq.norm_intervalIntegral_le_integral_norm x₀ t))

private theorem continuous_integratingFactor (hq : Integrable q) :
    Continuous (integratingFactor x₀ q) :=
  Real.continuous_exp.comp
    (intervalIntegral.continuous_primitive (fun _ _ ↦ hq.intervalIntegrable) x₀)

private theorem ae_hasDerivAt_integratingFactor (hq : Integrable q) :
    ∀ᵐ t, HasDerivAt (integratingFactor x₀ q) (integratingFactor x₀ q t * q t) t := by
  filter_upwards [_root_.LocallyIntegrable.ae_hasDerivAt_integral hq.locallyIntegrable] with t ht
  exact (ht x₀).exp

private theorem absolutelyContinuousOnInterval_integratingFactor (hq : Integrable q)
    (x₁ : ℝ) : AbsolutelyContinuousOnInterval (integratingFactor x₀ q) x₀ x₁ :=
  (hq.intervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral
    left_mem_uIcc).comp_of_contDiffAt fun _ _ ↦ Real.contDiff_exp.contDiffAt

/-- The integrating factor is essentially bounded. -/
private theorem memLp_top_integratingFactor (hq : Integrable q) {μ : Measure ℝ} :
    MemLp (integratingFactor x₀ q) ⊤ μ :=
  memLp_top_of_bound (continuous_integratingFactor hq).aestronglyMeasurable _
    (.of_forall fun y ↦ (Real.norm_of_nonneg (integratingFactor_pos y).le).trans_le
      (integratingFactor_le hq y))

/-- Multiplying by the bounded integrating factor preserves `Lᵖ`. -/
private theorem memLp_integratingFactor_mul (hq : Integrable q) {μ : Measure ℝ}
    {p : ENNReal} {f : ℝ → ℝ} (hf : MemLp f p μ) :
    MemLp (fun y ↦ integratingFactor x₀ q y * f y) p μ :=
  (memLp_top_integratingFactor hq).fun_mul hf

/-- A lower bound `σ > 0` for `m y F` gives the lower bound `σ exp (-∫ |q|)` for `F`. -/
private theorem mul_exp_neg_le_of_le_integratingFactor_mul (hq : Integrable q) {y σ F : ℝ}
    (hσ : 0 < σ) (h : σ ≤ integratingFactor x₀ q y * F) :
    σ * Real.exp (-∫ s, |q s|) ≤ F := by
  have hF : 0 < F := pos_of_mul_pos_right (hσ.trans_le h) (integratingFactor_pos y).le
  calc σ * Real.exp (-∫ s, |q s|) ≤ Real.exp (∫ s, |q s|) * F * Real.exp (-∫ s, |q s|) := by
        gcongr
        exact h.trans (mul_le_mul_of_nonneg_right (integratingFactor_le hq y) hF.le)
    _ = F := by rw [Real.exp_neg]; field_simp

/-- An upper bound `K ≥ 0` for `m y F` gives the upper bound `exp (∫ |q|) K` for `F`. -/
private theorem le_exp_mul_of_integratingFactor_mul_le (hq : Integrable q) {y K F : ℝ}
    (hK : 0 ≤ K) (h : integratingFactor x₀ q y * F ≤ K) :
    F ≤ Real.exp (∫ s, |q s|) * K := by
  rcases le_or_gt F 0 with hF | hF
  · exact hF.trans (by positivity)
  calc F = Real.exp (∫ s, |q s|) * (Real.exp (-∫ s, |q s|) * F) := by
        rw [Real.exp_neg]; field_simp
    _ ≤ Real.exp (∫ s, |q s|) * K := by
        gcongr
        exact (mul_le_mul_of_nonneg_right (exp_neg_le_integratingFactor hq y) hF.le).trans h

/-- Testing `Φ` against the derivative of a difference of two ramps gives the difference of its
averages over `(s, s + δ)` and `(t, t + δ)`. -/
private theorem integral_mul_deriv_ramp_sub (hΦ : IntegrableOn Φ (Ioo x₀ x₁))
    (hs : x₀ ≤ s) (hδ : 0 < δ) (hst : s + δ ≤ t) (ht : t + δ ≤ x₁) :
    ∫ y in Ioo x₀ x₁, Φ y * deriv (ramp s δ - ramp t δ) y =
      (δ⁻¹ * ∫ y in Ioo s (s + δ), Φ y) - δ⁻¹ * ∫ y in Ioo t (t + δ), Φ y := by
  have hint : ∀ z, IntegrableOn (fun y ↦ Φ y * (Ioo z (z + δ)).indicator (fun _ ↦ δ⁻¹) y)
      (Ioo x₀ x₁) := fun z ↦ by
    simp_rw [← indicator_mul_right]
    exact (hΦ.mul_const δ⁻¹).indicator measurableSet_Ioo
  have hind : ∀ z, Ioo z (z + δ) ⊆ Ioo x₀ x₁ →
      ∫ y in Ioo x₀ x₁, Φ y * (Ioo z (z + δ)).indicator (fun _ ↦ δ⁻¹) y =
        δ⁻¹ * ∫ y in Ioo z (z + δ), Φ y := fun z hz ↦ by
    simp_rw [← indicator_mul_right]
    rw [setIntegral_indicator measurableSet_Ioo, inter_eq_right.2 hz, integral_mul_const,
      mul_comm]
  calc ∫ y in Ioo x₀ x₁, Φ y * deriv (ramp s δ - ramp t δ) y
      = ∫ y in Ioo x₀ x₁, (Φ y * (Ioo s (s + δ)).indicator (fun _ ↦ δ⁻¹) y -
          Φ y * (Ioo t (t + δ)).indicator (fun _ ↦ δ⁻¹) y) :=
        integral_congr_ae ((ae_restrict_of_ae
          (deriv_ramp_sub_ramp_ae_eq (s := s) (t := t) hδ hδ)).mono
          fun y hy ↦ by simp only [hy, mul_sub])
    _ = (δ⁻¹ * ∫ y in Ioo s (s + δ), Φ y) - δ⁻¹ * ∫ y in Ioo t (t + δ), Φ y := by
        rw [integral_sub (hint s) (hint t), hind s (Ioo_subset_Ioo hs (by linarith)),
          hind t (Ioo_subset_Ioo (by linarith) ht)]

/-- Since `0 ≤ ramp s δ - ramp t δ ≤ 1` vanishes off `(s, t + δ)`, testing `k` against it costs
at most the mass of `|k|` there. -/
private theorem neg_setIntegral_abs_le_integral_mul_ramp_sub (hk : IntegrableOn k (Ioo x₀ x₁))
    (hs : x₀ ≤ s) (hδ : 0 < δ) (hst : s ≤ t) (ht : t + δ ≤ x₁) :
    -∫ y in Ioo s (t + δ), |k y| ≤ ∫ y in Ioo x₀ x₁, k y * (ramp s δ - ramp t δ) y := by
  have hsub : Ioo s (t + δ) ⊆ Ioo x₀ x₁ := Ioo_subset_Ioo hs ht
  have hneg : ∫ y in Ioo x₀ x₁, -(Ioo s (t + δ)).indicator (fun y ↦ |k y|) y =
      -∫ y in Ioo s (t + δ), |k y| := by
    rw [integral_neg, setIntegral_indicator measurableSet_Ioo, inter_eq_right.2 hsub]
  rw [← hneg]
  refine integral_mono (hk.abs.indicator measurableSet_Ioo).neg
    (hk.mul_bdd (((continuous_ramp s δ).sub (continuous_ramp t δ)).aestronglyMeasurable) (c := 1)
      (.of_forall fun y ↦ by
        rw [Real.norm_eq_abs, abs_le, Pi.sub_apply]
        exact ⟨by linarith [(ramp_sub_ramp_mem_Icc hδ.le hst y).1],
          (ramp_sub_ramp_mem_Icc hδ.le hst y).2⟩)) fun y ↦ ?_
  have h01 := ramp_sub_ramp_mem_Icc hδ.le hst y
  rw [Pi.sub_apply]
  by_cases hy : y ∈ Ioo s (t + δ)
  · rw [indicator_of_mem hy]
    nlinarith [mul_le_mul_of_nonneg_right (neg_abs_le (k y)) h01.1,
      mul_le_mul_of_nonneg_left h01.2 (abs_nonneg (k y))]
  · rw [indicator_of_notMem hy, neg_zero, ramp_sub_ramp_eq_zero_of_notMem hδ hst hy, mul_zero]

/-- The test inequality for the difference of two ramps: averages of `Φ` over `(t, t + δ)`
exceed those over `(s, s + δ)` by at most the mass of `|k|` in between. -/
private theorem ramp_average_le
    (hΦ : IntegrableOn Φ (Ioo x₀ x₁)) (hk : IntegrableOn k (Ioo x₀ x₁))
    (hKI : FluxTestInequality x₀ x₁ k Φ)
    (hs : x₀ ≤ s) (hδ : 0 < δ) (hst : s + δ ≤ t) (ht : t + δ ≤ x₁) :
    δ⁻¹ * ∫ y in Ioo t (t + δ), Φ y ≤
      (δ⁻¹ * ∫ y in Ioo s (s + δ), Φ y) + ∫ y in Ioo s (t + δ), |k y| := by
  have hst' : s ≤ t := by linarith
  have h := hKI (ramp s δ - ramp t δ)
    (((lipschitzWith_ramp s δ).lipschitzOnWith.absolutelyContinuousOnInterval).sub
      ((lipschitzWith_ramp t δ).lipschitzOnWith.absolutelyContinuousOnInterval))
    ((memLp_deriv_ramp_sub_ramp hδ hδ 2).restrict _)
    (ramp_sub_ramp_eq_zero_of_notMem hδ hst' fun h ↦ (not_lt.2 hs) h.1)
    (ramp_sub_ramp_eq_zero_of_notMem hδ hst' fun h ↦ (not_lt.2 ht) h.2)
    fun y _ ↦ (ramp_sub_ramp_mem_Icc hδ.le hst' y).1
  rw [integral_mul_deriv_ramp_sub hΦ hs hδ hst ht] at h
  linarith [neg_setIntegral_abs_le_integral_mul_ramp_sub hk hs hδ hst' ht]

/-- **The flux is almost decreasing.** At two Lebesgue points `s < t` of `Φ`, the inequality of
`ramp_average_le` passes to the limit: `Φ t ≤ Φ s + ∫ y in s..t, |k y|`. -/
private theorem le_add_intervalIntegral_abs
    (hΦ : IntegrableOn Φ (Ioo x₀ x₁)) (hk : IntegrableOn k (Ioo x₀ x₁))
    (hKI : FluxTestInequality x₀ x₁ k Φ)
    (hs : s ∈ Ioo x₀ x₁) (ht : t ∈ Ioo x₀ x₁) (hst : s < t)
    (hPs : HasDerivAt (fun y ↦ ∫ z in x₀..y, Φ z) (Φ s) s)
    (hPt : HasDerivAt (fun y ↦ ∫ z in x₀..y, Φ z) (Φ t) t) :
    Φ t ≤ Φ s + ∫ y in s..t, |k y| := by
  set P : ℝ → ℝ := fun y ↦ ∫ z in x₀..y, Φ z
  set K : ℝ → ℝ := fun y ↦ ∫ z in x₀..y, |k z|
  have hka : IntegrableOn (fun y ↦ |k y|) (Ioo x₀ x₁) := hk.abs
  have hx₀ : x₀ ∈ Icc x₀ x₁ := left_mem_Icc.2 (hs.1.trans hs.2).le
  have hKon : ContinuousOn K (Icc x₀ x₁) :=
    TauCeti.intervalIntegral.continuousOn_primitive_interval_of_integrableOn_Ioo hka hx₀
  have hKcont : ContinuousAt K t := hKon.continuousAt (Icc_mem_nhds ht.1 ht.2)
  have hev : ∀ᶠ δ in 𝓝[>] 0,
      δ⁻¹ * (P (t + δ) - P t) ≤ δ⁻¹ * (P (s + δ) - P s) + (K (t + δ) - K s) := by
    filter_upwards [Ioo_mem_nhdsGT (lt_min (sub_pos.2 hst) (sub_pos.2 ht.2))] with δ hδ
    have hδst : s + δ ≤ t := by linarith [hδ.2.trans_le (min_le_left _ _)]
    have hδt : t + δ ≤ x₁ := by linarith [hδ.2.trans_le (min_le_right _ _)]
    have h := ramp_average_le hΦ hk hKI hs.1.le hδ.1 hδst hδt
    rwa [hΦ.setIntegral_Ioo_eq_sub hx₀ (hs.1.trans hst).le (by linarith [hδ.1]) hδt,
      hΦ.setIntegral_Ioo_eq_sub hx₀ hs.1.le (by linarith [hδ.1]) (by linarith),
      hka.setIntegral_Ioo_eq_sub hx₀ hs.1.le (by linarith [hδ.1]) hδt] at h
  have hlimL : Tendsto (fun δ ↦ δ⁻¹ * (P (t + δ) - P t)) (𝓝[>] 0) (𝓝 (Φ t)) := by
    simpa only [smul_eq_mul] using hPt.tendsto_slope_zero_right
  have hlimR : Tendsto (fun δ ↦ δ⁻¹ * (P (s + δ) - P s) + (K (t + δ) - K s)) (𝓝[>] 0)
      (𝓝 (Φ s + (K t - K s))) := by
    have hs' : Tendsto (fun δ ↦ δ⁻¹ * (P (s + δ) - P s)) (𝓝[>] 0) (𝓝 (Φ s)) := by
      simpa only [smul_eq_mul] using hPs.tendsto_slope_zero_right
    refine hs'.add ((hKcont.tendsto.comp ?_).sub_const _)
    have : Tendsto (fun δ : ℝ ↦ t + δ) (𝓝 0) (𝓝 t) := by
      simpa using (continuous_const_add t).tendsto 0
    exact this.mono_left nhdsWithin_le_nhds
  have h := le_of_tendsto_of_tendsto hlimL hlimR hev
  have hKst : K t - K s = ∫ y in s..t, |k y| := by
    rw [intervalIntegral.integral_of_le hst.le, integral_Ioc_eq_integral_Ioo,
      hka.setIntegral_Ioo_eq_sub hx₀ hs.1.le hst.le ht.2.le]
  linarith

/-- Below a Lebesgue point `s` of `Φ`, the function `Φ` stays almost everywhere above
`Φ s - ∫ y in x₀..s, |k y|`. -/
private theorem ae_sub_le_of_hasDerivAt
    (hΦ : IntegrableOn Φ (Ioo x₀ x₁)) (hk : IntegrableOn k (Ioo x₀ x₁))
    (hKI : FluxTestInequality x₀ x₁ k Φ)
    (hE : ∀ᵐ y, y ∈ Ioo x₀ x₁ → HasDerivAt (fun y ↦ ∫ z in x₀..y, Φ z) (Φ y) y)
    (hs : s ∈ Ioo x₀ x₁) (hPs : HasDerivAt (fun y ↦ ∫ z in x₀..y, Φ z) (Φ s) s) :
    ∀ᵐ y, y ∈ Ioo x₀ s → Φ s - ∫ z in x₀..s, |k z| ≤ Φ y := by
  filter_upwards [hE] with y hy hys
  have hyI : y ∈ Ioo x₀ x₁ := ⟨hys.1, hys.2.trans hs.2⟩
  have h := le_add_intervalIntegral_abs hΦ hk hKI hyI hs hys.2 (hy hyI) hPs
  have hmono : ∫ z in y..s, |k z| ≤ ∫ z in x₀..s, |k z| :=
    intervalIntegral.integral_mono_interval hys.1.le hys.2.le le_rfl
      (.of_forall fun _ ↦ abs_nonneg _)
      (IntegrableOn.intervalIntegrable_of_mem_Icc hk.abs (left_mem_Icc.2 (hs.1.trans hs.2).le)
        ⟨hs.1.le, hs.2.le⟩)
  linarith

/-- For an absolutely continuous `ψ ≥ 0` vanishing at both endpoints, with derivative in `L²`,
the pairing with a weak supersolution is integrable. -/
theorem IsIntervalWeakSupersolution.integrableOn_of_absolutelyContinuousOnInterval
    (hx : x₀ < x₁)
    {u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2}
    (hsuper : IsIntervalWeakSupersolution a b c d u)
    {ψ : ℝ → ℝ} (hψ : AbsolutelyContinuousOnInterval ψ x₀ x₁)
    (hdψ : MemLp (deriv ψ) 2 (volume.restrict (Ioo x₀ x₁))) (hψ₀ : ψ x₀ = 0) (hψ₁ : ψ x₁ = 0)
    (hψnn : ∀ t ∈ Ioo x₀ x₁, 0 ≤ ψ t) :
    IntegrableOn (fun x ↦
      (a x * W1p.gradient u x + b x * W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le x)) *
          deriv ψ x -
        (c x * W1p.gradient u x + d x * W1p.intervalRepresentativeL hx u
          (projIcc x₀ x₁ hx.le x)) * ψ x) (Ioo x₀ x₁) := by
  obtain ⟨w, hw0, hwv, hwg⟩ :=
    hψ.exists_mem_w1p0Submodule_value_gradient_ae_eq hdψ (by norm_num) hψ₀ hψ₁
  have h := hsuper.integrableOn ⟨w, hw0⟩ (by
    filter_upwards [hwv, ae_restrict_mem measurableSet_Ioo] with t ht hmem
    simpa [ht] using hψnn t hmem)
  refine h.congr_fun_ae ?_
  filter_upwards [hwv, hwg, W1p.value_ae_eq_intervalRepresentativeL hx u] with t h1 h2 h3
  rw [h1, h2, h3]

/-- An absolutely continuous `ψ ≥ 0` vanishing at both endpoints, with derivative in `L²`,
is an admissible test function in the weak supersolution inequality. -/
theorem IsIntervalWeakSupersolution.integral_nonneg_of_absolutelyContinuousOnInterval
    (hx : x₀ < x₁)
    {u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2}
    (hsuper : IsIntervalWeakSupersolution a b c d u)
    {ψ : ℝ → ℝ} (hψ : AbsolutelyContinuousOnInterval ψ x₀ x₁)
    (hdψ : MemLp (deriv ψ) 2 (volume.restrict (Ioo x₀ x₁))) (hψ₀ : ψ x₀ = 0) (hψ₁ : ψ x₁ = 0)
    (hψnn : ∀ t ∈ Ioo x₀ x₁, 0 ≤ ψ t) :
    0 ≤ ∫ x in Ioo x₀ x₁,
      ((a x * W1p.gradient u x + b x * W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le x)) *
          deriv ψ x -
        (c x * W1p.gradient u x + d x * W1p.intervalRepresentativeL hx u
          (projIcc x₀ x₁ hx.le x)) * ψ x) := by
  obtain ⟨w, hw0, hwv, hwg⟩ :=
    hψ.exists_mem_w1p0Submodule_value_gradient_ae_eq hdψ (by norm_num) hψ₀ hψ₁
  have h := hsuper.integral_nonneg ⟨w, hw0⟩ (by
    filter_upwards [hwv, ae_restrict_mem measurableSet_Ioo] with t ht hmem
    simpa [ht] using hψnn t hmem)
  refine h.trans_eq (integral_congr_ae ?_)
  filter_upwards [hwv, hwg, W1p.value_ae_eq_intervalRepresentativeL hx u] with t h1 h2 h3
  rw [h1, h2, h3]

/-- The product rule for the integrating factor times an absolutely continuous function. -/
private theorem deriv_integratingFactor_mul_ae (hx : x₀ < x₁) (hq : Integrable q) {φ : ℝ → ℝ}
    (hφ : AbsolutelyContinuousOnInterval φ x₀ x₁) :
    deriv (integratingFactor x₀ q * φ) =ᵐ[volume.restrict (Ioo x₀ x₁)] fun y ↦
      integratingFactor x₀ q y * q y * φ y + integratingFactor x₀ q y * deriv φ y := by
  filter_upwards [ae_restrict_of_ae (ae_hasDerivAt_integratingFactor (x₀ := x₀) hq),
    ae_restrict_of_ae hφ.ae_differentiableAt, ae_restrict_mem measurableSet_Ioo] with y hm hd hy
  have hd' := (hd (by rw [uIcc_of_le hx.le]; exact Ioo_subset_Icc_self hy)).hasDerivAt
  rw [(hm.mul hd').deriv]

/-- The integrating factor times an absolutely continuous function with `L²` derivative again
has `L²` derivative, given `q ∈ L²`. -/
private theorem memLp_deriv_integratingFactor_mul (hx : x₀ < x₁) (hq : Integrable q)
    (hq2 : MemLp q 2 (volume.restrict (Ioo x₀ x₁))) {φ : ℝ → ℝ}
    (hφ : AbsolutelyContinuousOnInterval φ x₀ x₁)
    (hdφ : MemLp (deriv φ) 2 (volume.restrict (Ioo x₀ x₁))) :
    MemLp (deriv (integratingFactor x₀ q * φ)) 2 (volume.restrict (Ioo x₀ x₁)) := by
  have h1 : MemLp (fun y ↦ q y * φ y) 2 (volume.restrict (Ioo x₀ x₁)) :=
    hq2.fun_mul (hφ.continuousOn.memLp_top_restrict_of_subset_isCompact isCompact_uIcc
      measurableSet_Ioo (Ioo_subset_Icc_self.trans Icc_subset_uIcc))
  refine ((memLp_integratingFactor_mul (x₀ := x₀) hq h1).add
    (memLp_integratingFactor_mul (x₀ := x₀) hq hdφ)).ae_eq ?_
  filter_upwards [deriv_integratingFactor_mul_ae hx hq hφ] with y hy
  rw [hy, Pi.add_apply, mul_assoc]

/-- **Testing with the integrating factor.** Write `F = a u' + b u` for the flux and
`m = exp (∫ q)` with `q a = c` on the interval. Testing the supersolution inequality with `m φ`
removes the first-order term: `∫ m (d - q b) u φ ≤ ∫ m F φ'` for every admissible `φ ≥ 0`. -/
private theorem integral_mul_le_integral_mul_deriv (hx : x₀ < x₁)
    {u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2}
    (hsuper : IsIntervalWeakSupersolution a b c d u)
    (hq : Integrable q) (hq2 : MemLp q 2 (volume.restrict (Ioo x₀ x₁)))
    (hqa : ∀ y ∈ Ioo x₀ x₁, q y * a y = c y)
    (hF : MemLp (fun y ↦ a y * W1p.gradient u y +
      b y * W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le y)) 2
      (volume.restrict (Ioo x₀ x₁)))
    (hk : Integrable (fun y ↦ (d y - q y * b y) *
      W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le y)) (volume.restrict (Ioo x₀ x₁)))
    {φ : ℝ → ℝ} (hφ : AbsolutelyContinuousOnInterval φ x₀ x₁)
    (hdφ : MemLp (deriv φ) 2 (volume.restrict (Ioo x₀ x₁))) (hφ₀ : φ x₀ = 0) (hφ₁ : φ x₁ = 0)
    (hφnn : ∀ y ∈ Ioo x₀ x₁, 0 ≤ φ y) :
    ∫ y in Ioo x₀ x₁, integratingFactor x₀ q y * ((d y - q y * b y) *
        W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le y)) * φ y ≤
      ∫ y in Ioo x₀ x₁, integratingFactor x₀ q y * (a y * W1p.gradient u y +
        b y * W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le y)) * deriv φ y := by
  set m := integratingFactor x₀ q
  set v : ℝ → ℝ := fun y ↦ W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le y)
  have hφ' : MemLp φ ⊤ (volume.restrict (Ioo x₀ x₁)) :=
    hφ.continuousOn.memLp_top_restrict_of_subset_isCompact isCompact_uIcc measurableSet_Ioo
      (Ioo_subset_Icc_self.trans Icc_subset_uIcc)
  set ψ : ℝ → ℝ := m * φ
  have hdψ := deriv_integratingFactor_mul_ae hx hq hφ
  have h := hsuper.integral_nonneg_of_absolutelyContinuousOnInterval hx
    ((absolutelyContinuousOnInterval_integratingFactor hq x₁).mul hφ)
    (memLp_deriv_integratingFactor_mul hx hq hq2 hφ hdφ)
    (by simp [hφ₀]) (by simp [hφ₁])
    (fun y hy ↦ mul_nonneg (integratingFactor_pos y).le (hφnn y hy))
  have hcongr : (fun y ↦ (a y * W1p.gradient u y + b y * v y) * deriv ψ y -
      (c y * W1p.gradient u y + d y * v y) * ψ y) =ᵐ[volume.restrict (Ioo x₀ x₁)]
      fun y ↦ m y * (a y * W1p.gradient u y + b y * v y) * deriv φ y -
        m y * ((d y - q y * b y) * v y) * φ y := by
    filter_upwards [hdψ, ae_restrict_mem measurableSet_Ioo] with y hd hy
    rw [hd, ← hqa y hy]
    simp only [ψ, Pi.mul_apply]
    ring
  have hmF : MemLp (fun y ↦ m y * (a y * W1p.gradient u y + b y * v y)) 2
      (volume.restrict (Ioo x₀ x₁)) := memLp_integratingFactor_mul hq hF
  have i1 : Integrable (fun y ↦ m y * (a y * W1p.gradient u y + b y * v y) * deriv φ y)
      (volume.restrict (Ioo x₀ x₁)) := hmF.integrable_mul hdφ
  have i2 : Integrable (fun y ↦ m y * ((d y - q y * b y) * v y) * φ y)
      (volume.restrict (Ioo x₀ x₁)) :=
    (hk.mul_of_top_right (memLp_top_integratingFactor hq)).mul_of_top_left hφ'
  rw [integral_congr_ae hcongr, integral_sub i1 i2] at h
  linarith

/-- If `u` vanishes at `x₀` and its weak gradient is at least `σ` on `(x₀, y)`, then
`(y - x₀) σ ≤ u y`. -/
private theorem mul_le_intervalRepresentativeL_of_le_gradient (hx : x₀ < x₁)
    (u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2)
    (hu₀ : W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le x₀) = 0) {y σ : ℝ}
    (hy : y ∈ Icc x₀ x₁) (hσ : ∀ᵐ r, r ∈ Ioo x₀ y → σ ≤ W1p.gradient u r) :
    (y - x₀) * σ ≤ W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le y) := by
  rw [projIcc_left] at hu₀
  simpa only [projIcc_of_mem hx.le hy, hu₀, sub_zero] using
    W1p.mul_le_intervalRepresentativeL_sub_of_le_gradient hx u
      (s := ⟨x₀, left_mem_Icc.2 hx.le⟩) (t := ⟨y, hy⟩) hy.1 hσ

/-- If `u` vanishes at `x₀` and its weak gradient is at most `σ` on `(x₀, y)`, then
`u y ≤ (y - x₀) σ`. -/
private theorem intervalRepresentativeL_le_mul_of_gradient_le (hx : x₀ < x₁)
    (u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2)
    (hu₀ : W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le x₀) = 0) {y σ : ℝ}
    (hy : y ∈ Icc x₀ x₁) (hσ : ∀ᵐ r, r ∈ Ioo x₀ y → W1p.gradient u r ≤ σ) :
    W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le y) ≤ (y - x₀) * σ := by
  rw [projIcc_left] at hu₀
  simpa only [projIcc_of_mem hx.le hy, hu₀, sub_zero] using
    W1p.intervalRepresentativeL_sub_le_mul_of_gradient_le hx u
      (s := ⟨x₀, left_mem_Icc.2 hx.le⟩) (t := ⟨y, hy⟩) hy.1 hσ

/-- **Positive flux gives linear growth.** If the flux `a u' + b u` is bounded below by `σ > 0`
near `x₀`, where `u` vanishes and `a ≤ Λ`, then `u` grows at least linearly from `x₀`. -/
private theorem exists_pos_mul_le_of_le_flux (hx : x₀ < x₁)
    (u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2) {Λ β σ s : ℝ}
    (ha : ∀ y ∈ Ioo x₀ x₁, 0 < a y) (haΛ : ∀ y ∈ Ioo x₀ x₁, a y ≤ Λ)
    (hb : ∀ y ∈ Ioo x₀ x₁, |b y| ≤ β) (hσ : 0 < σ) (hs : s ∈ Ioo x₀ x₁)
    (hu₀ : W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le x₀) = 0)
    (hlow : ∀ᵐ y, y ∈ Ioo x₀ s →
      σ ≤ a y * W1p.gradient u y + b y * W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le y)) :
    ∃ ε > 0, ∃ δ > 0, ∀ h ∈ Ioo 0 δ,
      ε * h ≤ W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le (x₀ + h)) := by
  have hβ : 0 ≤ β := (abs_nonneg _).trans (hb s hs)
  have hΛ : 0 < Λ := (ha s hs).trans_le (haΛ s hs)
  have hvc := W1p.continuous_intervalRepresentativeL_projIcc hx u
  -- Near `x₀` the term `b u` is at most `σ / 2`.
  obtain ⟨η, hη, hvη⟩ := Metric.continuousAt_iff.1 hvc.continuousAt (σ / (2 * (β + 1)))
    (by positivity)
  refine ⟨σ / (2 * Λ), by positivity, min (s - x₀) η, lt_min (sub_pos.2 hs.1) hη,
    fun h hh ↦ ?_⟩
  have hhs : x₀ + h < s := by linarith [hh.2.trans_le (min_le_left _ _)]
  have hgrad : ∀ᵐ y, y ∈ Ioo x₀ (x₀ + h) → σ / (2 * Λ) ≤ W1p.gradient u y := by
    filter_upwards [hlow] with y hy hyI
    have hyI' : y ∈ Ioo x₀ x₁ := ⟨hyI.1, hyI.2.trans (hhs.trans hs.2)⟩
    have hvy : |W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le y)| <
        σ / (2 * (β + 1)) := by
      have := hvη (x := y) (by
        rw [Real.dist_eq, abs_of_pos (sub_pos.2 hyI.1)]
        linarith [hyI.2, hh.2.trans_le (min_le_right _ _)])
      rwa [Real.dist_eq, hu₀, sub_zero] at this
    have hbv : |b y * W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le y)| ≤ σ / 2 := by
      rw [abs_mul]
      calc |b y| * |W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le y)| ≤
          β * (σ / (2 * (β + 1))) :=
            mul_le_mul (hb y hyI') hvy.le (abs_nonneg _) hβ
        _ ≤ σ / 2 := by
            rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
            nlinarith
    have hag : σ / 2 ≤ a y * W1p.gradient u y := by
      have := hy ⟨hyI.1, hyI.2.trans hhs⟩
      linarith [le_abs_self (b y * W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le y))]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [haΛ y hyI', ha y hyI']
  have hmem : x₀ + h ∈ Icc x₀ x₁ := ⟨by linarith [hh.1], by linarith [hs.2]⟩
  have hle := mul_le_intervalRepresentativeL_of_le_gradient hx u hu₀ hmem hgrad
  rw [add_sub_cancel_left] at hle
  linarith

/-- **A flux controlled by the solution forces it to vanish.** Suppose that `u` vanishes at `x₀`,
that `a ≥ λ > 0` and `|b| ≤ β`, and that on each short interval `(x₀, x₀ + h)` the flux
`a u' + b u` is at most `C U` for every bound `U ≥ 0` of `u` on `[x₀, x₀ + h]`. Then `u` cannot
be positive on the whole interval. -/
private theorem not_forall_pos_of_flux_le (hx : x₀ < x₁)
    (u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2) {lam β C : ℝ} (hlam : 0 < lam)
    (ha : ∀ y ∈ Ioo x₀ x₁, lam ≤ a y) (hb : ∀ y ∈ Ioo x₀ x₁, |b y| ≤ β) (hC : 0 ≤ C)
    (hu₀ : W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le x₀) = 0)
    (hup : ∀ h, 0 < h → h < x₁ - x₀ → ∀ U, 0 ≤ U →
      (∀ y ∈ Icc x₀ (x₀ + h), W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le y) ≤ U) →
      ∀ᵐ y, y ∈ Ioo x₀ (x₀ + h) →
        a y * W1p.gradient u y + b y * W1p.intervalRepresentativeL hx u
          (projIcc x₀ x₁ hx.le y) ≤ C * U) :
    ¬∀ t ∈ Ioo x₀ x₁, 0 < W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le t) := by
  intro hpos
  have hβ : 0 ≤ β := (abs_nonneg _).trans (hb ((x₀ + x₁) / 2) ⟨by linarith, by linarith⟩)
  have hvc := W1p.continuous_intervalRepresentativeL_projIcc hx u
  -- A short interval on which the growth allowed by the flux bound is at most one half.
  set h := min ((x₁ - x₀) / 2) (lam / (2 * (C + β + 1)))
  have hh : 0 < h := lt_min (by linarith) (by positivity)
  have hh₁ : h < x₁ - x₀ := (min_le_left _ _).trans_lt (by linarith)
  have hhC : h * ((C + β) / lam) ≤ 1 / 2 := by
    have : h ≤ lam / (2 * (C + β + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at this
    rw [mul_div_assoc', div_le_iff₀ hlam]
    nlinarith
  -- `U` is the maximum of `u` on `[x₀, x₀ + h]`, attained at `τ`.
  obtain ⟨τ, hτ, hτmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 (by linarith))
    (hvc.continuousOn (s := Icc x₀ (x₀ + h)))
  set U := W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le τ)
  have hUpos : 0 < U :=
    (hpos (x₀ + h) ⟨by linarith, by linarith⟩).trans_le (hτmax ⟨by linarith, le_rfl⟩)
  have hgrad : ∀ᵐ y, y ∈ Ioo x₀ (x₀ + h) → W1p.gradient u y ≤ (C + β) * U / lam := by
    filter_upwards [hup h hh hh₁ U hUpos.le fun y hy ↦ hτmax hy] with y hy hyI
    have hyI' : y ∈ Ioo x₀ x₁ := ⟨hyI.1, hyI.2.trans (by linarith)⟩
    have hvy := hpos y hyI'
    have hvU : W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le y) ≤ U :=
      hτmax (Ioo_subset_Icc_self hyI)
    have hbv : -(β * U) ≤ b y * W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le y) := by
      have := abs_le.1 (hb y hyI')
      nlinarith
    have hag := hy hyI
    rw [le_div_iff₀ hlam]
    rcases le_or_gt (W1p.gradient u y) 0 with hg | hg
    · nlinarith
    · nlinarith [mul_le_mul_of_nonneg_left (ha y hyI') hg.le]
  have hmem : τ ∈ Icc x₀ x₁ := ⟨hτ.1, hτ.2.trans (by linarith)⟩
  have hle : U ≤ (τ - x₀) * ((C + β) * U / lam) :=
    intervalRepresentativeL_le_mul_of_gradient_le hx u hu₀ hmem
      (hgrad.mono fun y hy hyI ↦ hy ⟨hyI.1, hyI.2.trans_le hτ.2⟩)
  have : (τ - x₀) * ((C + β) * U / lam) ≤ U / 2 := by
    calc (τ - x₀) * ((C + β) * U / lam) ≤ h * ((C + β) * U / lam) := by
          gcongr
          linarith [hτ.2]
      _ = h * ((C + β) / lam) * U := by ring
      _ ≤ 1 / 2 * U := by gcongr
      _ = U / 2 := by ring
  linarith

/-- The mass of `|m (d - q b) u|` on `(x₀, y)` is at most `exp L · U · ∫ |d - q b|` when
`0 ≤ u ≤ U` there. -/
private theorem intervalIntegral_abs_le (hx : x₀ < x₁)
    (u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2) (hq : Integrable q)
    (he : IntegrableOn (fun y ↦ d y - q y * b y) (Ioo x₀ x₁)) {y U : ℝ}
    (hy : y ∈ Ioo x₀ x₁)
    (hU : ∀ z ∈ Icc x₀ y, |W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le z)| ≤ U) :
    ∫ z in x₀..y, |integratingFactor x₀ q z * ((d z - q z * b z) *
        W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le z))| ≤
      Real.exp (∫ s, |q s|) * U * ∫ z in Ioo x₀ x₁, |d z - q z * b z| := by
  set L := ∫ s, |q s|
  have hU0 : 0 ≤ U := (abs_nonneg _).trans (hU x₀ (left_mem_Icc.2 hy.1.le))
  have hpt : ∀ z ∈ Icc x₀ y, |integratingFactor x₀ q z * ((d z - q z * b z) *
      W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le z))| ≤
        Real.exp L * U * |d z - q z * b z| := fun z hz ↦ by
    rw [abs_mul, abs_mul, abs_of_pos (integratingFactor_pos z)]
    calc integratingFactor x₀ q z * (|d z - q z * b z| *
          |W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le z)|)
        ≤ Real.exp L * (|d z - q z * b z| * U) := by
          gcongr
          exacts [integratingFactor_le hq z, hU z hz]
      _ = Real.exp L * U * |d z - q z * b z| := by ring
  calc ∫ z in x₀..y, |integratingFactor x₀ q z * ((d z - q z * b z) *
        W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le z))|
      = ∫ z in Ioc x₀ y, |integratingFactor x₀ q z * ((d z - q z * b z) *
        W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le z))| :=
        intervalIntegral.integral_of_le hy.1.le
    _ ≤ ∫ z in Ioc x₀ y, Real.exp L * U * |d z - q z * b z| :=
        integral_mono_of_nonneg (.of_forall fun _ ↦ abs_nonneg _)
          ((he.mono_set (Ioc_subset_Ioo_right hy.2)).abs.const_mul (Real.exp L * U))
          ((ae_restrict_mem measurableSet_Ioc).mono fun z hz ↦ hpt z (Ioc_subset_Icc_self hz))
    _ = Real.exp L * U * ∫ z in Ioc x₀ y, |d z - q z * b z| := integral_const_mul _ _
    _ ≤ Real.exp L * U * ∫ z in Ioo x₀ x₁, |d z - q z * b z| :=
        mul_le_mul_of_nonneg_left (setIntegral_mono_set he.abs
          (.of_forall fun _ ↦ abs_nonneg _) (ae_of_all _ (Ioc_subset_Ioo_right hy.2)))
          (by positivity)

/-- The Hopf lemma for a weak supersolution, given an integrating factor `q` with `q a = c`. -/
private theorem exists_pos_mul_le_of_integratingFactor (hx : x₀ < x₁)
    (u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2) {lam Λ β : ℝ} (hlam : 0 < lam)
    (ha : ∀ y ∈ Ioo x₀ x₁, lam ≤ a y) (haΛ : ∀ y ∈ Ioo x₀ x₁, a y ≤ Λ)
    (hb : ∀ y ∈ Ioo x₀ x₁, |b y| ≤ β)
    (hsuper : IsIntervalWeakSupersolution a b c d u)
    (hq : Integrable q) (hq2 : MemLp q 2 (volume.restrict (Ioo x₀ x₁)))
    (hqa : ∀ y ∈ Ioo x₀ x₁, q y * a y = c y)
    (hF : MemLp (fun y ↦ a y * W1p.gradient u y +
      b y * W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le y)) 2
      (volume.restrict (Ioo x₀ x₁)))
    (he : IntegrableOn (fun y ↦ d y - q y * b y) (Ioo x₀ x₁))
    (hu₀ : W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le x₀) = 0)
    (hpos : ∀ t ∈ Ioo x₀ x₁, 0 < W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le t)) :
    ∃ ε > 0, ∃ δ > 0, ∀ h ∈ Ioo 0 δ,
      ε * h ≤ W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le (x₀ + h)) := by
  set L := ∫ s, |q s|
  -- The weighted flux `Φ = m (a u' + b u)` and the weighted zeroth-order term `k`.
  set Φ : ℝ → ℝ := fun y ↦ integratingFactor x₀ q y * (a y * W1p.gradient u y +
    b y * W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le y))
  set k : ℝ → ℝ := fun y ↦ integratingFactor x₀ q y * ((d y - q y * b y) *
    W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le y))
  have hvb : ∀ y, ‖W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le y)‖ ≤
      ‖W1p.intervalRepresentativeL hx u‖ := fun y ↦
    (W1p.intervalRepresentativeL hx u).norm_coe_le_norm _
  have hk1 : Integrable (fun y ↦ (d y - q y * b y) *
      W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le y)) (volume.restrict (Ioo x₀ x₁)) :=
    he.mul_bdd (W1p.continuous_intervalRepresentativeL_projIcc hx u).aestronglyMeasurable
      (.of_forall hvb)
  have hΦi : IntegrableOn Φ (Ioo x₀ x₁) :=
    (memLp_integratingFactor_mul hq hF).integrable (by norm_num)
  have hki : IntegrableOn k (Ioo x₀ x₁) := hk1.mul_of_top_right (memLp_top_integratingFactor hq)
  have hKI : FluxTestInequality x₀ x₁ k Φ := fun _ h₁ h₂ h₃ h₄ h₅ ↦
    integral_mul_le_integral_mul_deriv hx hsuper hq hq2 hqa hF hk1 h₁ h₂ h₃ h₄ h₅
  have hE : ∀ᵐ y, y ∈ Ioo x₀ x₁ → HasDerivAt (fun y ↦ ∫ z in x₀..y, Φ z) (Φ y) y := by
    filter_upwards [((intervalIntegrable_iff_integrableOn_Ioo_of_le hx.le).2
      hΦi).ae_hasDerivAt_integral] with y hy hyI
    exact hy (by rw [uIcc_of_le hx.le]; exact Ioo_subset_Icc_self hyI) x₀ left_mem_uIcc
  by_cases hA : ∃ s ∈ Ioo x₀ x₁,
      HasDerivAt (fun y ↦ ∫ z in x₀..y, Φ z) (Φ s) s ∧ ∫ z in x₀..s, |k z| < Φ s
  · -- The flux has a positive limit at `x₀`: `u` grows linearly.
    obtain ⟨s, hs, hPs, hlt⟩ := hA
    refine exists_pos_mul_le_of_le_flux hx u (fun y hy ↦ hlam.trans_le (ha y hy)) haΛ hb
      (σ := (Φ s - ∫ z in x₀..s, |k z|) * Real.exp (-L))
      (mul_pos (sub_pos.2 hlt) (Real.exp_pos _)) hs hu₀ ?_
    filter_upwards [ae_sub_le_of_hasDerivAt hΦi hki hKI hE hs hPs] with y hy hys
    exact mul_exp_neg_le_of_le_integratingFactor_mul hq (sub_pos.2 hlt) (hy hys)
  · -- The flux has a nonpositive limit at `x₀`: `u` vanishes near `x₀`.
    push Not at hA
    refine absurd hpos (not_forall_pos_of_flux_le hx u hlam ha hb
      (C := Real.exp L * Real.exp L * ∫ z in Ioo x₀ x₁, |d z - q z * b z|)
      (by positivity) hu₀ fun h _ hh₁ U hU hvU ↦ ?_)
    filter_upwards [hE] with y hy hyh
    have hyI : y ∈ Ioo x₀ x₁ := ⟨hyh.1, hyh.2.trans (by linarith)⟩
    have hKU := intervalIntegral_abs_le hx u hq he hyI (U := U) fun z hz ↦ by
      have hz0 : 0 ≤ W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le z) := by
        rcases eq_or_lt_of_le hz.1 with rfl | hz'
        · exact hu₀.ge
        · exact (hpos z ⟨hz', hz.2.trans_lt hyI.2⟩).le
      rw [abs_of_nonneg hz0]
      exact hvU z ⟨hz.1, hz.2.trans hyh.2.le⟩
    exact (le_exp_mul_of_integratingFactor_mul_le hq (by positivity)
      ((hA y hyI (hy hyI)).trans hKU)).trans_eq (by ring)

/-- The Hopf lemma for a weak supersolution whose coefficient bounds hold at every point of the
interval. -/
private theorem exists_pos_mul_le_of_forall_bounds (hx : x₀ < x₁)
    (u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2) {lam Λ β : ℝ} (hlam : 0 < lam)
    (ha : ∀ y ∈ Ioo x₀ x₁, lam ≤ a y) (haΛ : ∀ y ∈ Ioo x₀ x₁, a y ≤ Λ)
    (ham : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (hb : ∀ y ∈ Ioo x₀ x₁, |b y| ≤ β) (hbm : AEStronglyMeasurable b (volume.restrict (Ioo x₀ x₁)))
    (hc : MemLp c 2 (volume.restrict (Ioo x₀ x₁))) (hd : IntegrableOn d (Ioo x₀ x₁))
    (hsuper : IsIntervalWeakSupersolution a b c d u)
    (hu₀ : W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le x₀) = 0)
    (hpos : ∀ t ∈ Ioo x₀ x₁, 0 < W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le t)) :
    ∃ ε > 0, ∃ δ > 0, ∀ h ∈ Ioo 0 δ,
      ε * h ≤ W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le (x₀ + h)) := by
  have hIoo : ∀ᵐ y ∂volume.restrict (Ioo x₀ x₁), y ∈ Ioo x₀ x₁ :=
    ae_restrict_mem measurableSet_Ioo
  -- The integrating factor is built from `q = c / a`, extended by zero off the interval.
  have hca : MemLp (fun y ↦ c y / a y) 2 (volume.restrict (Ioo x₀ x₁)) := by
    refine hc.of_le_mul (c := lam⁻¹)
      (hc.aestronglyMeasurable.div₀ ham)
      (hIoo.mono fun y hy ↦ ?_)
    rw [norm_div, Real.norm_of_nonneg (hlam.le.trans (ha y hy)), div_eq_inv_mul]
    gcongr
    exact ha y hy
  have hq2 : MemLp ((Ioo x₀ x₁).indicator fun y ↦ c y / a y) 2 (volume.restrict (Ioo x₀ x₁)) :=
    hca.ae_eq (indicator_ae_eq_restrict measurableSet_Ioo.nullMeasurableSet).symm
  have hgrad : MemLp (fun y ↦ a y * W1p.gradient u y) 2 (volume.restrict (Ioo x₀ x₁)) :=
    (memLp_top_of_bound ham Λ (hIoo.mono fun y hy ↦
      (Real.norm_of_nonneg (hlam.le.trans (ha y hy))).trans_le (haΛ y hy))).fun_mul
      (Lp.memLp (W1p.gradient u))
  have hbv : MemLp (fun y ↦ b y * W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le y)) 2
      (volume.restrict (Ioo x₀ x₁)) := by
    refine MemLp.of_bound
      (hbm.mul (W1p.continuous_intervalRepresentativeL_projIcc hx u).aestronglyMeasurable)
      (β * ‖W1p.intervalRepresentativeL hx u‖)
      (hIoo.mono fun y hy ↦ ?_)
    rw [norm_mul]
    exact mul_le_mul (hb y hy) ((W1p.intervalRepresentativeL hx u).norm_coe_le_norm _)
      (norm_nonneg _) ((abs_nonneg _).trans (hb y hy))
  refine exists_pos_mul_le_of_integratingFactor hx u hlam ha haΛ hb hsuper
    ((integrable_indicator_iff measurableSet_Ioo).2 (hca.integrable (by norm_num))) hq2
    (fun y hy ↦ ?_) (hgrad.add hbv) (hd.sub ?_) hu₀ hpos
  · rw [indicator_of_mem hy, div_mul_cancel₀ _ (hlam.trans_le (ha y hy)).ne']
  · exact (hq2.integrable (by norm_num)).mul_bdd hbm (hIoo.mono fun y hy ↦ hb y hy)

/-- **Hopf's boundary-point lemma for weak supersolutions on an interval.** Let
`L u = (a u' + b u)' + c u' + d u` on `(x₀, x₁)` with `λ ≤ a ≤ Λ`, `λ > 0` and `|b| ≤ β` almost
everywhere, `a` and `b` measurable, `c ∈ L²` and `d ∈ L¹`, and let `u ∈ W^{1,2}(x₀, x₁)` be a weak
supersolution, `L u ≤ 0`: `∫ ((a u' + b u) w' - (c u' + d u) w) ≥ 0` for every
`w ∈ W^{1,2}_0(x₀, x₁)` with `w ≥ 0`. If the continuous representative of `u` vanishes at `x₀` and
is positive on `(x₀, x₁)`, then it leaves `x₀` at a positive linear rate: `ε h ≤ u (x₀ + h)` for
some `ε > 0` and all small `h > 0`. No sign condition is imposed on `b`, `c` or `d`, and no
continuity on `a` or `b`. -/
theorem IsIntervalWeakSupersolution.exists_pos_mul_le_intervalRepresentativeL
    (hx : x₀ < x₁) {u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2} {lam Λ β : ℝ} (hlam : 0 < lam)
    (ha : ∀ᵐ y ∂volume.restrict (Ioo x₀ x₁), lam ≤ a y)
    (haΛ : ∀ᵐ y ∂volume.restrict (Ioo x₀ x₁), a y ≤ Λ)
    (ham : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (hb : ∀ᵐ y ∂volume.restrict (Ioo x₀ x₁), |b y| ≤ β)
    (hbm : AEStronglyMeasurable b (volume.restrict (Ioo x₀ x₁)))
    (hc : MemLp c 2 (volume.restrict (Ioo x₀ x₁))) (hd : IntegrableOn d (Ioo x₀ x₁))
    (hsuper : IsIntervalWeakSupersolution a b c d u)
    (hu₀ : W1p.intervalRepresentativeL hx u ⟨x₀, left_mem_Icc.2 hx.le⟩ = 0)
    (hpos : ∀ t ∈ Ioo x₀ x₁, 0 < W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le t)) :
    ∃ ε > 0, ∃ δ > 0, ∀ h ∈ Ioo 0 δ,
      ε * h ≤ W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le (x₀ + h)) := by
  -- Redefine `a` and `b` on the exceptional null set so that their bounds hold everywhere; this
  -- changes neither their measurability nor the weak supersolution inequality.
  have : (ae (volume.restrict (Ioo x₀ x₁))).NeBot := ae_restrict_neBot.2 (by
    rw [Real.volume_Ioo]
    exact (ENNReal.ofReal_pos.2 (sub_pos.2 hx)).ne')
  have haI : ∀ᵐ y ∂volume.restrict (Ioo x₀ x₁), a y ∈ Icc lam Λ := by
    filter_upwards [ha, haΛ] with y h₁ h₂ using ⟨h₁, h₂⟩
  obtain ⟨a', -, ha', haa⟩ := ham.aemeasurable.exists_ae_eq_range_subset haI
    (haI.exists.elim fun y₀ hy₀ ↦ ⟨a y₀, hy₀⟩)
  obtain ⟨b', -, hb', hbb⟩ := hbm.aemeasurable.exists_ae_eq_range_subset (t := {r | |r| ≤ β}) hb
    (hb.exists.elim fun y₀ hy₀ ↦ ⟨b y₀, hy₀⟩)
  refine exists_pos_mul_le_of_forall_bounds hx u hlam (fun y _ ↦ (ha' (mem_range_self y)).1)
    (fun y _ ↦ (ha' (mem_range_self y)).2) (ham.congr haa) (fun y _ ↦ hb' (mem_range_self y))
    (hbm.congr hbb) hc hd (hsuper.congr_ae haa hbb (ae_eq_refl c) (ae_eq_refl d))
    (by rwa [projIcc_left]) hpos

/-- **Hopf's boundary-point lemma for weak supersolutions on an interval**, derivative form: under
the hypotheses of `IsIntervalWeakSupersolution.exists_pos_mul_le_intervalRepresentativeL`, a right
derivative of the continuous representative at `x₀`, if it exists, is positive. -/
theorem IsIntervalWeakSupersolution.pos_of_hasDerivWithinAt_intervalRepresentativeL
    (hx : x₀ < x₁) {u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ 2} {lam Λ β : ℝ} (hlam : 0 < lam)
    (ha : ∀ᵐ y ∂volume.restrict (Ioo x₀ x₁), lam ≤ a y)
    (haΛ : ∀ᵐ y ∂volume.restrict (Ioo x₀ x₁), a y ≤ Λ)
    (ham : AEStronglyMeasurable a (volume.restrict (Ioo x₀ x₁)))
    (hb : ∀ᵐ y ∂volume.restrict (Ioo x₀ x₁), |b y| ≤ β)
    (hbm : AEStronglyMeasurable b (volume.restrict (Ioo x₀ x₁)))
    (hc : MemLp c 2 (volume.restrict (Ioo x₀ x₁))) (hd : IntegrableOn d (Ioo x₀ x₁))
    (hsuper : IsIntervalWeakSupersolution a b c d u)
    (hu₀ : W1p.intervalRepresentativeL hx u ⟨x₀, left_mem_Icc.2 hx.le⟩ = 0)
    (hpos : ∀ t ∈ Ioo x₀ x₁, 0 < W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le t))
    {u' : ℝ}
    (hd' : HasDerivWithinAt (fun t ↦ W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le t))
      u' (Ici x₀) x₀) :
    0 < u' := by
  obtain ⟨ε, hε, δ, hδ, h⟩ := hsuper.exists_pos_mul_le_intervalRepresentativeL hx hlam ha haΛ
    ham hb hbm hc hd hu₀ hpos
  have hslope := (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl x₀)).mp
    (hasDerivWithinAt_Ioi_iff_Ici.mpr hd')
  refine hε.trans_le (ge_of_tendsto hslope ?_)
  filter_upwards [Ioo_mem_nhdsGT (lt_add_of_pos_right x₀ hδ)] with t ht
  have h' := h (t - x₀) ⟨sub_pos.2 ht.1, by linarith [ht.2]⟩
  rw [add_sub_cancel] at h'
  rw [slope_def_field, projIcc_left, hu₀, sub_zero, le_div_iff₀ (sub_pos.2 ht.1)]
  exact h'

end TauCeti.PDE
