/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import TauCeti.Analysis.Sobolev.W1p.Interval.Representative
public import TauCeti.Analysis.Sobolev.W1p.Zero
public import TauCeti.Analysis.Sobolev.Wkp.Basic
import TauCeti.Analysis.PDE.DirichletProblem.Interval
import TauCeti.Analysis.PDE.Regularity.Hessian.Interval
import TauCeti.Analysis.PDE.Regularity.Interval
import TauCeti.Analysis.Sobolev.WeakDeriv.Interval

/-!
# A jump in the datum stops elliptic regularity

Interior elliptic regularity gains two derivatives over the datum: for `-Δu = f` with
`f ∈ H^{k-1}` the solution lies in `H^{k+1}`, while a datum `div F` with `F ∈ L²` only lies in
`H⁻¹` and gives no second derivatives. This file shows, on an interval, that neither gain can be
improved when the datum has a jump. Let `x₀ < c < x₁`, and let a function on `(x₀, x₁)` be almost
everywhere equal to a constant `y₀` on `(x₀, c)` and to a different constant `y₁` on `(c, x₁)`.

* If `f` is such a function and `u ∈ W^{2,p}(x₀, x₁)` solves `-u'' = f`, then `u` is not in
  `W^{3,p}(x₀, x₁)`
  (`TauCeti.PDE.not_exists_wkp_three_lowerOrder_eq_of_neg_iteratedGradient_eq`).
* If `F` is such a function and `u ∈ W^{1,p}(x₀, x₁)` solves `-u'' = F'` in the sense of
  distributions, then `u` is not in `W^{2,p}(x₀, x₁)`
  (`TauCeti.PDE.not_exists_wkp_two_firstOrder_eq_of_forall_integral_gradient_mul_deriv_eq`).

Both hold for every `1 ≤ p ≤ ∞` and need no boundary condition. In the first case `u''` is `-f`,
and in the second the first integral of the equation makes `u'` equal to a constant minus `F`. In
both cases a derivative of `u` would inherit the jump, and a weakly differentiable function has
no jump (`TauCeti.HasWeakLineDerivOn.eq_of_ae_eq_const_Ioo`).

The two statements are applied to the indicator function `1_{(0, 1/2)}` on `(0, 1)`, with zero
boundary values:

* the Dirichlet problem `-u'' = 1_{(0, 1/2)}` has a solution in `W^{2,p}(0, 1)` for every
  `1 ≤ p < ∞`, and it does not lie in `W^{3,p}(0, 1)`
  (`TauCeti.PDE.exists_neg_iteratedGradient_eq_indicator_Ioo_and_not_exists_wkp_three`);
* the Dirichlet problem `-u'' = (1_{(0, 1/2)})'` has a solution in `W^{1,p}(0, 1)` for every
  `1 ≤ p ≤ ∞`, and it does not lie in `W^{2,p}(0, 1)`
  (`TauCeti.PDE.exists_forall_integral_gradient_mul_deriv_eq_indicator_Ioo_and_not_exists_wkp_two`).

So the `Hᵏ` bootstrap with a datum in `H^{k-1}` stops exactly at `H²` for this datum, and a
divergence datum `F'` with `F ∈ L²` gives no `H²` regularity.

## References

* L. C. Evans, *Partial Differential Equations*, §6.3.1, Theorems 1 and 2 (interior `H²` and
  `Hᵏ` regularity).
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Section 8.4 (one-dimensional boundary value problems).
-/

public section

open MeasureTheory Set Filter TopologicalSpace
open scoped ENNReal Distributions

namespace TauCeti.PDE

variable {x₀ x₁ c : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **A jump in the datum stops the regularity of `-u'' = f` at `W^{2,p}`.** Let
`x₀ < c < x₁`, and let `f` be almost everywhere equal to `y₀` on `(x₀, c)` and to `y₁ ≠ y₀` on
`(c, x₁)`. If `u ∈ W^{2,p}(x₀, x₁)` solves `-u'' = f` almost everywhere, where `u''` is the weak
Hessian in the direction `1`, then `u` is not the second-order part of any element of
`W^{3,p}(x₀, x₁)`. -/
theorem not_exists_wkp_three_lowerOrder_eq_of_neg_iteratedGradient_eq (hc₀ : x₀ < c)
    (hc₁ : c < x₁) {f : ℝ → ℝ} {y₀ y₁ : ℝ} (hy : y₀ ≠ y₁)
    (hf₀ : ∀ᵐ t ∂volume.restrict (Ioo x₀ c), f t = y₀)
    (hf₁ : ∀ᵐ t ∂volume.restrict (Ioo c x₁), f t = y₁)
    {u : Wkp volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p 2}
    (hu : ∀ᵐ t ∂volume.restrict (Ioo x₀ x₁), -Wkp.iteratedGradient 1 u t 1 = f t) :
    ¬∃ v : Wkp volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p 3, Wkp.lowerOrder 2 v = u := by
  rintro ⟨v, rfl⟩
  -- The weak Hessian of `u` in the direction `1` is weakly differentiable, but equals `-f`.
  have hw := ((Wkp.hasWeakFDerivOn_iteratedGradient 1 v).hasWeakLineDerivOn 1).clm_comp
    (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ))
  refine hy (neg_injective (hw.eq_of_ae_eq_const_Ioo hc₀ hc₁ ?_ ?_))
  · filter_upwards [ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_right hc₁.le) hu,
      hf₀] with t ht hft
    rw [← hft, ← ht, neg_neg, ContinuousLinearMap.apply_apply]
  · filter_upwards [ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_left hc₀.le) hu,
      hf₁] with t ht hft
    rw [← hft, ← ht, neg_neg, ContinuousLinearMap.apply_apply]

/-- **A jump in a divergence datum prevents `W^{2,p}` regularity.** Let `x₀ < c < x₁`, and let
`F` be almost everywhere equal to `y₀` on `(x₀, c)` and to `y₁ ≠ y₀` on `(c, x₁)`. If
`u ∈ W^{1,p}(x₀, x₁)` solves `-u'' = F'` in the sense of distributions, that is
`∫ u' φ' = -∫ F φ'` for every test function `φ` on `(x₀, x₁)`, then `u` is not the first-order
part of any element of `W^{2,p}(x₀, x₁)`. -/
theorem not_exists_wkp_two_firstOrder_eq_of_forall_integral_gradient_mul_deriv_eq (hc₀ : x₀ < c)
    (hc₁ : c < x₁) {F : ℝ → ℝ} {y₀ y₁ : ℝ} (hy : y₀ ≠ y₁)
    (hF₀ : ∀ᵐ t ∂volume.restrict (Ioo x₀ c), F t = y₀)
    (hF₁ : ∀ᵐ t ∂volume.restrict (Ioo c x₁), F t = y₁)
    {u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p}
    (hu : ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
      ∫ t in Ioo x₀ x₁, W1p.gradient u t * deriv φ t = -∫ t in Ioo x₀ x₁, F t * deriv φ t) :
    ¬∃ v : Wkp volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p 2, Wkp.firstOrder 1 v = u := by
  rintro ⟨v, rfl⟩
  -- `F` is integrable, being almost everywhere constant on each side of `c`.
  have hFi : IntegrableOn F (Ioo x₀ x₁) := by
    have h₀ : IntegrableOn F (Ioo x₀ c) :=
      (integrableOn_const measure_Ioo_lt_top.ne).congr_fun_ae (hF₀.mono fun _ ht => ht.symm)
    have h₁ : IntegrableOn F (Ico c x₁) := (integrableOn_Ico_iff_integrableOn_Ioo (f := F)).2
      ((integrableOn_const measure_Ioo_lt_top.ne).congr_fun_ae (hF₁.mono fun _ ht => ht.symm))
    exact (h₀.union h₁).mono_set Ioo_subset_Ioo_union_Ico
  -- The first integral of the equation: `u' + F` is almost everywhere a constant `k`.
  obtain ⟨k, hk⟩ := exists_ae_mul_gradient_add_eq_sub_intervalIntegral (a := fun _ => 1)
    (f := 0) (F := F) aestronglyMeasurable_const (M := 1) (by simp) integrableOn_zero hFi
    fun φ => by simpa using hu φ
  -- So `u' = k - F` jumps at `c`, although it is weakly differentiable.
  have hw := Wkp.hasWeakLineDerivOn_gradient_lowerOrder v
  refine hy (sub_right_injective (hw.eq_of_ae_eq_const_Ioo (y₀ := k - y₀) (y₁ := k - y₁) hc₀ hc₁
    ?_ ?_))
  · filter_upwards [ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_right hc₁.le) hk,
      hF₀] with t ht hFt
    simp only [one_mul, Pi.zero_apply, intervalIntegral.integral_zero, sub_zero] at ht
    rw [← hFt, ← ht, add_sub_cancel_right]
  · filter_upwards [ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_left hc₀.le) hk,
      hF₁] with t ht hFt
    simp only [one_mul, Pi.zero_apply, intervalIntegral.integral_zero, sub_zero] at ht
    rw [← hFt, ← ht, add_sub_cancel_right]

/-- The indicator of `(0, 1/2)` is `0` almost everywhere on `(1/2, 1)`. -/
private theorem ae_indicator_Ioo_eq_zero :
    ∀ᵐ t ∂volume.restrict (Ioo (1 / 2 : ℝ) 1), (Ioo (0 : ℝ) (1 / 2)).indicator 1 t = (0 : ℝ) :=
  ae_restrict_of_ae_restrict_of_subset
    (t := (Ioo (0 : ℝ) (1 / 2))ᶜ) (fun _ ht h => lt_asymm h.2 ht.1)
    (indicator_ae_eq_restrict_compl (f := (1 : ℝ → ℝ)) measurableSet_Ioo.nullMeasurableSet)

omit [Fact (1 ≤ p)] in
/-- The indicator of `(0, 1/2)` lies in `Lᵖ(0, 1)`. -/
private theorem memLp_indicator_Ioo_one_half :
    MemLp ((Ioo (0 : ℝ) (1 / 2)).indicator (1 : ℝ → ℝ)) p (volume.restrict (Ioo (0 : ℝ) 1)) :=
  memLp_indicator_const (μ := volume.restrict (Ioo (0 : ℝ) 1)) p
    (measurableSet_Ioo (a := (0 : ℝ)) (b := 1 / 2)).nullMeasurableSet (1 : ℝ)
    (Or.inr (measure_ne_top _ _))

/-- **The `Hᵏ` bootstrap stops at `H²` for a datum with a jump.** For `1 ≤ p < ∞`, the Dirichlet
problem `-u'' = 1_{(0, 1/2)}` on `(0, 1)` with zero boundary values has a solution
`u ∈ W^{2,p}(0, 1)`, and `u` does not lie in `W^{3,p}(0, 1)`: its second derivative jumps at
`1/2`. -/
theorem exists_neg_iteratedGradient_eq_indicator_Ioo_and_not_exists_wkp_three (hp : p ≠ ⊤) :
    ∃ u : Wkp volume ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩ p 2,
      Wkp.firstOrder 1 u ∈ w1p0Submodule volume ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩ p ∧
      (∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1),
        -Wkp.iteratedGradient 1 u t 1 = (Ioo (0 : ℝ) (1 / 2)).indicator 1 t) ∧
      ¬∃ v : Wkp volume ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩ p 3, Wkp.lowerOrder 2 v = u := by
  have hf := memLp_indicator_Ioo_one_half (p := p)
  obtain ⟨u, ⟨hu0, hu⟩, -⟩ :=
    existsUnique_firstOrder_mem_w1p0Submodule_and_neg_mul_iteratedGradient_eq_of_Ioo hp
      zero_lt_one aestronglyMeasurable_const zero_lt_one (ae_of_all _ fun _ => le_rfl)
      hf.toLp
  have hu' : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1),
      -Wkp.iteratedGradient 1 u t 1 = (Ioo (0 : ℝ) (1 / 2)).indicator 1 t := by
    filter_upwards [hu, hf.coeFn_toLp] with t ht hft
    rw [← hft, ← ht, one_mul]
  refine ⟨u, hu0, hu', not_exists_wkp_three_lowerOrder_eq_of_neg_iteratedGradient_eq
    (by norm_num) (by norm_num) one_ne_zero
    (indicator_ae_eq_restrict (f := (1 : ℝ → ℝ)) measurableSet_Ioo.nullMeasurableSet)
    ae_indicator_Ioo_eq_zero hu'⟩

/-- **A divergence datum with a jump gives no `H²` regularity.** For `1 ≤ p ≤ ∞`, the Dirichlet
problem `-u'' = (1_{(0, 1/2)})'` on `(0, 1)` with zero boundary values has a solution
`u ∈ W^{1,p}(0, 1)`, a weak solution in the sense `∫ u' φ' = -∫ 1_{(0, 1/2)} φ'` for every test
function `φ`, and `u` does not lie in `W^{2,p}(0, 1)`: its derivative jumps at `1/2`. -/
theorem exists_forall_integral_gradient_mul_deriv_eq_indicator_Ioo_and_not_exists_wkp_two :
    ∃ u : W1p volume ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩ p,
      W1p.intervalTraceL zero_lt_one u = (0, 0) ∧
      (∀ φ : 𝓓(⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩, ℝ),
        ∫ t in Ioo (0 : ℝ) 1, W1p.gradient u t * deriv φ t =
          -∫ t in Ioo (0 : ℝ) 1, (Ioo (0 : ℝ) (1 / 2)).indicator 1 t * deriv φ t) ∧
      ¬∃ v : Wkp volume ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩ p 2, Wkp.firstOrder 1 v = u := by
  have hF := memLp_indicator_Ioo_one_half (p := p)
  obtain ⟨u, hu0, hu⟩ := exists_intervalTraceL_eq_and_forall_integral_mul_gradient_eq
    zero_lt_one zero_lt_one (a := fun _ => 1) aestronglyMeasurable_const
    (ae_of_all _ fun _ => le_rfl) (f := 0) integrableOn_zero hF 0 0
  have hu' : ∀ φ : 𝓓(⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩, ℝ),
      ∫ t in Ioo (0 : ℝ) 1, W1p.gradient u t * deriv φ t =
        -∫ t in Ioo (0 : ℝ) 1, (Ioo (0 : ℝ) (1 / 2)).indicator 1 t * deriv φ t := fun φ => by
    simpa using hu φ
  refine ⟨u, hu0, hu', not_exists_wkp_two_firstOrder_eq_of_forall_integral_gradient_mul_deriv_eq
    (by norm_num) (by norm_num) one_ne_zero
    (indicator_ae_eq_restrict (f := (1 : ℝ → ℝ)) measurableSet_Ioo.nullMeasurableSet)
    ae_indicator_Ioo_eq_zero hu'⟩

end TauCeti.PDE
