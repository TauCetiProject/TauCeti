/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Interval.OneEndpoint
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.W1p
import TauCeti.Analysis.Sobolev.W1p.Interval.AbsolutelyContinuous
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# The mixed and Neumann problems for `-u''` on an interval

On a bounded interval `(a, b)` of the real line, the energy form of `-u''` is `∫_a^b u' v'`, and
the boundary of `(a, b)` is the two endpoints, on which surface measure is counting measure. For
`f ∈ L¹(a, b)` and boundary data `h₀, h₁ ∈ ℝ`, the weak form of the **Neumann problem**

`-u'' = f` in `(a, b)`, `-u'(a) = h₀`, `u'(b) = h₁`

asks for `u ∈ H¹(a, b)` with

`∫_a^b u' v' = ∫_a^b f v + h₀ v(a) + h₁ v(b)` for every `v ∈ H¹(a, b)`,

where `v(a)` and `v(b)` are the endpoint values of the continuous representative
(`TauCeti.W1p.intervalTraceL`). The data `h₀, h₁` are the outward conormal derivatives: the outward
normal is `-1` at `a` and `+1` at `b`. The weak form of the **mixed problem**, with the Dirichlet
condition `u(a) = 0` on the boundary part `Γ = {a}` and the Neumann condition `u'(b) = h₁` on the
rest of the boundary, asks for `u ∈ H¹_Γ(a, b)` with

`∫_a^b u' v' = ∫_a^b f v + h₁ v(b)` for every `v ∈ H¹_Γ(a, b)`,

where `H¹_Γ(a, b)` is the space `TauCeti.w1pVanishingOnSubmodule` of Sobolev functions vanishing on
`Γ`. On an interval both problems are solved explicitly, through the flux `u'`.

* **The Neumann problem** has a weak solution exactly when the datum annihilates the constants,
  `∫_a^b f + h₀ + h₁ = 0`
  (`TauCeti.PDE.exists_forall_setIntegral_gradient_mul_gradient_eq_iff_Ioo`), as testing with
  `v = 1` shows. Its weak solutions are then exactly the functions
  `C - ∫_a^x (h₀ + ∫_a^s f) ds`, `C ∈ ℝ`
  (`TauCeti.PDE.forall_setIntegral_gradient_mul_gradient_eq_iff_Ioo`): unique up to an additive
  constant.
* **The mixed problem** has exactly one weak solution, `∫_a^x (h₁ + ∫_s^b f) ds`
  (`TauCeti.PDE.mem_w1pVanishingOnSubmodule_and_forall_setIntegral_gradient_mul_gradient_eq_iff_Ioo`
  and `TauCeti.PDE.existsUnique_mem_w1pVanishingOnSubmodule_and_forall_setIntegral_eq_Ioo`).

In both cases the flux `F = u'` of the explicit solution is `c - ∫_a^x f` for a constant `c`, and
integration by parts against `F` gives `∫_a^b F v' = F(b) v(b) - F(a) v(a) + ∫_a^b f v`; the
boundary conditions fix `c`. Uniqueness comes from testing the equation of the difference `w` of two
solutions with `w` itself: `∫_a^b w'² = 0`, so `w` is constant, and in the mixed problem `w(a) = 0`.

On `(0, 1)` with `f = 1` this gives the standard examples:

* the mixed problem `-u'' = 1`, `u(0) = 0`, `u'(1) = 0` has the unique weak solution `x - x²/2`
  (`TauCeti.PDE.mem_w1pVanishingOnSubmodule_and_forall_setIntegral_eq_iff_Ioo_zero_one`);
* the Neumann problem `-u'' = 1` with `h₀ = h₁ = 0` has no weak solution, since `∫_0^1 1 = 1 ≠ 0`
  (`TauCeti.PDE.not_exists_forall_setIntegral_gradient_mul_gradient_eq_Ioo_zero_one`);
* with `h₀ = 0` and `h₁ = -1` the compatibility condition holds, and the weak solutions are exactly
  `C - x²/2`
  (`TauCeti.PDE.forall_setIntegral_gradient_mul_gradient_eq_sub_iff_Ioo_zero_one`).

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, §8.4,
  Example 5 (a mixed condition in one dimension), and Problem 47, part B (the Neumann problem on an
  interval and its compatibility condition).
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal InnerProductSpace

namespace TauCeti.PDE

variable {a b : ℝ}

local instance : IsFiniteMeasure (volume.restrict
    ((⟨Ioo a b, isOpen_Ioo⟩ : Opens ℝ) : Set ℝ)) := ⟨by simp⟩

/-! ### The Dirichlet form on an interval -/

/-- On an interval, the Dirichlet form `∫ u' v'` is the `L²` inner product of the weak
gradients. -/
private theorem setIntegral_gradient_mul_gradient_eq_inner
    (u v : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2) :
    ∫ t in Ioo a b, W1p.gradient u t * W1p.gradient v t =
      ⟪W1p.gradient u, W1p.gradient v⟫_ℝ := by
  rw [L2.inner_def]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp [mul_comm]

/-- The Dirichlet form is additive in its left argument up to subtraction. -/
private theorem setIntegral_gradient_sub_mul_gradient
    (u u' v : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2) :
    ∫ t in Ioo a b, W1p.gradient (u - u') t * W1p.gradient v t =
      (∫ t in Ioo a b, W1p.gradient u t * W1p.gradient v t) -
        ∫ t in Ioo a b, W1p.gradient u' t * W1p.gradient v t := by
  rw [setIntegral_gradient_mul_gradient_eq_inner, setIntegral_gradient_mul_gradient_eq_inner,
    setIntegral_gradient_mul_gradient_eq_inner, W1p.gradient_sub, inner_sub_left]

/-- **Zero energy, constant function.** If `∫ w'² = 0`, the continuous representative of `w` is
constant on `[a, b]`, equal to its value at `a`. -/
private theorem intervalRepresentativeL_eq_of_setIntegral_gradient_mul_self_eq_zero
    (hab : a < b) {w : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2}
    (hw : ∫ t in Ioo a b, W1p.gradient w t * W1p.gradient w t = 0) (t : Icc a b) :
    W1p.intervalRepresentativeL hab w t = (W1p.intervalTraceL hab w).1 := by
  rw [setIntegral_gradient_mul_gradient_eq_inner, real_inner_self_eq_norm_sq, sq_eq_zero_iff,
    norm_eq_zero] at hw
  obtain ⟨c, rfl⟩ := W1p.exists_eq_const_of_gradient_eq_zero isPreconnected_Ioo hw
  simp [W1p.intervalRepresentativeL_const]

/-! ### The explicit solution -/

/-- **Integration by parts against a flux.** For `f ∈ L¹(a, b)`, a constant `c` and
`v ∈ W^{1,q}(a, b)`, the flux `F(x) = c - ∫_a^x f` satisfies
`∫_a^b F v' = F(b) v(b) - F(a) v(a) + ∫_a^b f v`. -/
private theorem setIntegral_sub_intervalIntegral_mul_gradient_eq {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hab : a < b) {f : ℝ → ℝ} (hf : IntegrableOn f (Ioo a b)) (c : ℝ)
    (v : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ q) :
    ∫ t in Ioo a b, (c - ∫ s in a..t, f s) * W1p.gradient v t =
      (c - ∫ t in Ioo a b, f t) * (W1p.intervalTraceL hab v).2 -
        c * (W1p.intervalTraceL hab v).1 + ∫ t in Ioo a b, f t * W1p.value v t := by
  -- The flux is the representative of a `W^{1,1}` class with weak gradient `-f`.
  obtain ⟨w, hw, hgw⟩ := W1p.exists_intervalRepresentativeL_eq_and_gradient_ae_eq (p := 1) hab
    (left_mem_Icc.2 hab.le) c (memLp_one_iff_integrable.2 hf).neg
  have hrep (t : Icc a b) : W1p.intervalRepresentativeL hab w t = c - ∫ s in a..(t : ℝ), f s := by
    rw [hw]
    simp only [Pi.neg_apply, intervalIntegral.integral_neg, sub_eq_add_neg]
  have h := W1p.integral_intervalRepresentativeL_mul_gradient_eq_sub hab w v
  rw [intervalIntegral.integral_of_le hab.le, intervalIntegral.integral_of_le hab.le,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo] at h
  have h1 : ∫ t in Ioo a b, W1p.intervalRepresentativeL hab w (projIcc a b hab.le t) *
      W1p.gradient v t = ∫ t in Ioo a b, (c - ∫ s in a..t, f s) * W1p.gradient v t := by
    refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    rw [projIcc_of_mem hab.le (Ioo_subset_Icc_self ht), hrep]
  have h2 : ∫ t in Ioo a b, W1p.gradient w t *
      W1p.intervalRepresentativeL hab v (projIcc a b hab.le t) =
        -∫ t in Ioo a b, f t * W1p.value v t := by
    rw [← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [hgw, W1p.value_ae_eq_intervalRepresentativeL hab v] with t hgt hvt
    rw [hgt, ← hvt, Pi.neg_apply, neg_mul]
  have hb : ∫ s in a..b, f s = ∫ t in Ioo a b, f t := by
    rw [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo]
  rw [h1, h2, W1p.intervalTraceL_apply, W1p.intervalTraceL_apply, hrep, hrep] at h
  simp only [intervalIntegral.integral_same, sub_zero, hb] at h
  rw [h, W1p.intervalTraceL_apply]
  ring

/-- The flux `x ↦ c - ∫_a^x f` of an integrable `f` lies in `L²(a, b)`: it is continuous on
`[a, b]`. -/
private theorem memLp_sub_intervalIntegral (hab : a < b) {f : ℝ → ℝ}
    (hf : IntegrableOn f (Ioo a b)) (c : ℝ) :
    MemLp (fun t => c - ∫ s in a..t, f s) 2 (volume.restrict (Ioo a b)) := by
  have hcont : ContinuousOn (fun t => c - ∫ s in a..t, f s) (Icc a b) := by
    refine continuousOn_const.sub ?_
    rw [← uIcc_of_le hab.le]
    exact intervalIntegral.continuousOn_primitive_interval
      (by rwa [uIcc_of_le hab.le, integrableOn_Icc_iff_integrableOn_Ioo])
  exact hcont.memLp_restrict_of_subset_isCompact isCompact_Icc measurableSet_Ioo
    Ioo_subset_Icc_self 2

/-- **The explicit solution.** For constants `C` and `c`, the function
`C + ∫_a^x (c - ∫_a^s f) ds` is the representative of a class `u ∈ H¹(a, b)` with flux
`u' = c - ∫_a^x f`, so that `∫_a^b u' v' = (c - ∫_a^b f) v(b) - c v(a) + ∫_a^b f v` for every
`v ∈ H¹(a, b)`. -/
private theorem exists_intervalRepresentativeL_eq_and_forall_setIntegral_eq (hab : a < b)
    {f : ℝ → ℝ} (hf : IntegrableOn f (Ioo a b)) (C c : ℝ) :
    ∃ u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2,
      (∀ t : Icc a b, W1p.intervalRepresentativeL hab u t =
        C + ∫ s in a..(t : ℝ), (c - ∫ r in a..s, f r)) ∧
      ∀ v : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2,
        ∫ t in Ioo a b, W1p.gradient u t * W1p.gradient v t =
          (c - ∫ t in Ioo a b, f t) * (W1p.intervalTraceL hab v).2 -
            c * (W1p.intervalTraceL hab v).1 + ∫ t in Ioo a b, f t * W1p.value v t := by
  obtain ⟨u, hu, hgu⟩ := W1p.exists_intervalRepresentativeL_eq_and_gradient_ae_eq hab
    (left_mem_Icc.2 hab.le) C (memLp_sub_intervalIntegral hab hf c)
  refine ⟨u, hu, fun v => ?_⟩
  rw [← setIntegral_sub_intervalIntegral_mul_gradient_eq hab hf c v]
  refine integral_congr_ae ?_
  filter_upwards [hgu] with t ht
  rw [ht]

/-! ### The Neumann problem -/

/-- **The compatibility condition of the Neumann problem on an interval.** For `f ∈ L¹(a, b)` and
boundary data `h₀, h₁`, the weak Neumann problem
`∫_a^b u' v' = ∫_a^b f v + h₀ v(a) + h₁ v(b)` for every `v ∈ H¹(a, b)` has a solution
`u ∈ H¹(a, b)` exactly when `∫_a^b f + h₀ + h₁ = 0`. -/
theorem exists_forall_setIntegral_gradient_mul_gradient_eq_iff_Ioo (hab : a < b) {f : ℝ → ℝ}
    (hf : IntegrableOn f (Ioo a b)) (h₀ h₁ : ℝ) :
    (∃ u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2, ∀ v : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2,
      ∫ t in Ioo a b, W1p.gradient u t * W1p.gradient v t =
        (∫ t in Ioo a b, f t * W1p.value v t) + h₀ * (W1p.intervalTraceL hab v).1 +
          h₁ * (W1p.intervalTraceL hab v).2) ↔
      (∫ t in Ioo a b, f t) + h₀ + h₁ = 0 := by
  constructor
  · -- Test with the constant `1`, whose gradient vanishes.
    rintro ⟨u, hu⟩
    have h := hu (W1p.const 1)
    have hl : ∫ t in Ioo a b, W1p.gradient u t * W1p.gradient (W1p.const 1 :
        W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2) t = 0 := by
      rw [W1p.gradient_const]
      refine (integral_congr_ae ?_).trans (integral_zero _ ℝ)
      filter_upwards [Lp.coeFn_zero ℝ 2 (volume.restrict (Ioo a b))] with t ht
      rw [ht, Pi.zero_apply, mul_zero]
    have hr : ∫ t in Ioo a b, f t * W1p.value (W1p.const 1 :
        W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2) t = ∫ t in Ioo a b, f t := by
      refine integral_congr_ae ?_
      filter_upwards [W1p.value_const_ae (mu := volume) (Omega := ⟨Ioo a b, isOpen_Ioo⟩)
        (p := 2) 1] with t ht
      rw [ht, mul_one]
    simp only [hl, hr, W1p.intervalTraceL_apply, W1p.intervalRepresentativeL_const,
      ContinuousMap.const_apply, mul_one] at h
    linarith
  · -- The flux `-h₀ - ∫_a^x f` has the right boundary values.
    intro hc
    obtain ⟨u, -, hu⟩ := exists_intervalRepresentativeL_eq_and_forall_setIntegral_eq hab hf 0 (-h₀)
    refine ⟨u, fun v => ?_⟩
    rw [hu, show -h₀ - ∫ t in Ioo a b, f t = h₁ by linarith]
    ring

/-- **The weak solutions of the Neumann problem on an interval.** Under the compatibility condition
`∫_a^b f + h₀ + h₁ = 0`, a class `u ∈ H¹(a, b)` solves the weak Neumann problem
`∫_a^b u' v' = ∫_a^b f v + h₀ v(a) + h₁ v(b)` for every `v ∈ H¹(a, b)` exactly when its continuous
representative is `C - ∫_a^x (h₀ + ∫_a^s f) ds` for a constant `C`: the solution is unique up to an
additive constant. -/
theorem forall_setIntegral_gradient_mul_gradient_eq_iff_Ioo (hab : a < b) {f : ℝ → ℝ}
    (hf : IntegrableOn f (Ioo a b)) {h₀ h₁ : ℝ} (hc : (∫ t in Ioo a b, f t) + h₀ + h₁ = 0)
    (u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2) :
    (∀ v : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2,
      ∫ t in Ioo a b, W1p.gradient u t * W1p.gradient v t =
        (∫ t in Ioo a b, f t * W1p.value v t) + h₀ * (W1p.intervalTraceL hab v).1 +
          h₁ * (W1p.intervalTraceL hab v).2) ↔
      ∃ C : ℝ, ∀ t : Icc a b, W1p.intervalRepresentativeL hab u t =
        C - ∫ s in a..(t : ℝ), (h₀ + ∫ r in a..s, f r) := by
  have hflux (C : ℝ) (t : ℝ) : C + ∫ s in a..t, (-h₀ - ∫ r in a..s, f r) =
      C - ∫ s in a..t, (h₀ + ∫ r in a..s, f r) := by
    rw [sub_eq_add_neg, ← intervalIntegral.integral_neg]
    congr 2
    ext s
    ring
  have hRHS : h₁ = -h₀ - ∫ t in Ioo a b, f t := by linarith
  constructor
  · -- The difference with the explicit solution has zero energy.
    intro hu
    obtain ⟨u₀, hu₀, hu₀v⟩ :=
      exists_intervalRepresentativeL_eq_and_forall_setIntegral_eq hab hf 0 (-h₀)
    have hw := intervalRepresentativeL_eq_of_setIntegral_gradient_mul_self_eq_zero hab
      (w := u - u₀) (by rw [setIntegral_gradient_sub_mul_gradient, hu, hu₀v, hRHS]; ring)
    refine ⟨(W1p.intervalTraceL hab (u - u₀)).1, fun t => ?_⟩
    have ht := hw t
    rw [map_sub, ContinuousMap.sub_apply, hu₀] at ht
    rw [← hflux]
    linarith
  · -- A representative of this form is that of the explicit solution with constant `C`.
    rintro ⟨C, hC⟩
    obtain ⟨u₁, hu₁, hu₁v⟩ :=
      exists_intervalRepresentativeL_eq_and_forall_setIntegral_eq hab hf C (-h₀)
    obtain rfl : u = u₁ := W1p.intervalRepresentativeL_injective hab
      (ContinuousMap.ext fun t => by rw [hC, hu₁, hflux])
    intro v
    rw [hu₁v, ← hRHS]
    ring

/-! ### The mixed problem -/

/-- The flux of the mixed problem, `h₁ + ∫_x^b f`, is `(h₁ + ∫_a^b f) - ∫_a^x f` on `[a, b]`, so
the explicit solution `∫_a^x (h₁ + ∫_s^b f) ds` is a primitive of a flux of this form. -/
private theorem intervalIntegral_sub_intervalIntegral_eq (hab : a < b) {f : ℝ → ℝ}
    (hf : IntegrableOn f (Ioo a b)) (h₁ : ℝ) (t : Icc a b) :
    ∫ s in a..(t : ℝ), ((h₁ + ∫ r in Ioo a b, f r) - ∫ r in a..s, f r) =
      ∫ s in a..(t : ℝ), (h₁ + ∫ r in s..b, f r) := by
  have hfab : IntervalIntegrable f volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 hf
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le t.property.1] at hs
  have hfas : IntervalIntegrable f volume a s :=
    hfab.mono_set (uIcc_subset_uIcc_left (by
      rw [uIcc_of_le hab.le]
      exact ⟨hs.1, hs.2.trans t.property.2⟩))
  rw [← intervalIntegral.integral_interval_sub_left hfab hfas,
    intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo]
  ring

/-- **The weak solution of the mixed problem on an interval.** For `f ∈ L¹(a, b)`, a Neumann datum
`h₁` at `b` and the Dirichlet condition on `Γ = {a}`, a class `u ∈ H¹(a, b)` lies in
`H¹_Γ(a, b)` and satisfies `∫_a^b u' v' = ∫_a^b f v + h₁ v(b)` for every `v ∈ H¹_Γ(a, b)` exactly
when its continuous representative is `∫_a^x (h₁ + ∫_s^b f) ds`. -/
theorem mem_w1pVanishingOnSubmodule_and_forall_setIntegral_gradient_mul_gradient_eq_iff_Ioo
    (hab : a < b) {f : ℝ → ℝ} (hf : IntegrableOn f (Ioo a b)) (h₁ : ℝ)
    (u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2) :
    (u ∈ w1pVanishingOnSubmodule volume ⟨Ioo a b, isOpen_Ioo⟩ 2 {a} ∧
      ∀ v ∈ w1pVanishingOnSubmodule volume ⟨Ioo a b, isOpen_Ioo⟩ 2 {a},
        ∫ t in Ioo a b, W1p.gradient u t * W1p.gradient v t =
          (∫ t in Ioo a b, f t * W1p.value v t) + h₁ * (W1p.intervalTraceL hab v).2) ↔
      ∀ t : Icc a b, W1p.intervalRepresentativeL hab u t =
        ∫ s in a..(t : ℝ), (h₁ + ∫ r in s..b, f r) := by
  set c := h₁ + ∫ t in Ioo a b, f t
  have hflux (t : Icc a b) : 0 + ∫ s in a..(t : ℝ), (c - ∫ r in a..s, f r) =
      ∫ s in a..(t : ℝ), (h₁ + ∫ r in s..b, f r) := by
    rw [zero_add, intervalIntegral_sub_intervalIntegral_eq hab hf h₁ t]
  obtain ⟨u₀, hu₀, hu₀v⟩ := exists_intervalRepresentativeL_eq_and_forall_setIntegral_eq hab hf 0 c
  have hmem : u₀ ∈ w1pVanishingOnSubmodule volume ⟨Ioo a b, isOpen_Ioo⟩ 2 {a} := by
    rw [W1p.mem_w1pVanishingOnSubmodule_singleton_iff_intervalTraceL_fst_eq_zero
      (by norm_num) hab, W1p.intervalTraceL_apply, hu₀]
    simp
  -- On `H¹_Γ(a, b)` the explicit solution satisfies the mixed equation.
  have hsol (v) (hv : v ∈ w1pVanishingOnSubmodule volume ⟨Ioo a b, isOpen_Ioo⟩ 2 {a}) :
      ∫ t in Ioo a b, W1p.gradient u₀ t * W1p.gradient v t =
        (∫ t in Ioo a b, f t * W1p.value v t) + h₁ * (W1p.intervalTraceL hab v).2 := by
    rw [hu₀v, W1p.intervalTraceL_fst_eq_zero_of_mem_w1pVanishingOnSubmodule_singleton hab hv]
    ring
  constructor
  · -- The difference with the explicit solution has zero energy and vanishes at `a`.
    rintro ⟨hu, huv⟩
    have hwmem := (w1pVanishingOnSubmodule volume ⟨Ioo a b, isOpen_Ioo⟩ 2 {a}).toSubmodule.sub_mem
      hu hmem
    have hw := intervalRepresentativeL_eq_of_setIntegral_gradient_mul_self_eq_zero hab
      (w := u - u₀) (by rw [setIntegral_gradient_sub_mul_gradient, huv _ hwmem, hsol _ hwmem,
        sub_self])
    intro t
    have ht := hw t
    rw [W1p.intervalTraceL_fst_eq_zero_of_mem_w1pVanishingOnSubmodule_singleton hab hwmem,
      map_sub, ContinuousMap.sub_apply, sub_eq_zero, hu₀ t, hflux] at ht
    exact ht
  · -- A representative of this form is that of the explicit solution.
    intro hu
    obtain rfl : u = u₀ := W1p.intervalRepresentativeL_injective hab
      (ContinuousMap.ext fun t => by rw [hu, hu₀, hflux])
    exact ⟨hmem, hsol⟩

/-- **Existence and uniqueness for the mixed problem on an interval.** For `f ∈ L¹(a, b)` and a
Neumann datum `h₁` at `b`, there is exactly one `u ∈ H¹_Γ(a, b)`, `Γ = {a}`, with
`∫_a^b u' v' = ∫_a^b f v + h₁ v(b)` for every `v ∈ H¹_Γ(a, b)`. -/
theorem existsUnique_mem_w1pVanishingOnSubmodule_and_forall_setIntegral_eq_Ioo
    (hab : a < b) {f : ℝ → ℝ} (hf : IntegrableOn f (Ioo a b)) (h₁ : ℝ) :
    ∃! u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2,
      u ∈ w1pVanishingOnSubmodule volume ⟨Ioo a b, isOpen_Ioo⟩ 2 {a} ∧
        ∀ v ∈ w1pVanishingOnSubmodule volume ⟨Ioo a b, isOpen_Ioo⟩ 2 {a},
          ∫ t in Ioo a b, W1p.gradient u t * W1p.gradient v t =
            (∫ t in Ioo a b, f t * W1p.value v t) + h₁ * (W1p.intervalTraceL hab v).2 := by
  simp_rw [mem_w1pVanishingOnSubmodule_and_forall_setIntegral_gradient_mul_gradient_eq_iff_Ioo
    hab hf h₁]
  obtain ⟨u, hu, -⟩ := exists_intervalRepresentativeL_eq_and_forall_setIntegral_eq hab hf 0
    (h₁ + ∫ t in Ioo a b, f t)
  refine ⟨u, fun t => ?_, fun u' hu' => W1p.intervalRepresentativeL_injective hab
    (ContinuousMap.ext fun t => ?_)⟩
  · rw [hu, zero_add, intervalIntegral_sub_intervalIntegral_eq hab hf h₁ t]
  · rw [hu', hu, zero_add, intervalIntegral_sub_intervalIntegral_eq hab hf h₁ t]

/-! ### The examples on `(0, 1)` -/

/-- **The mixed problem `-u'' = 1`, `u(0) = 0`, `u'(1) = 0` on `(0, 1)`.** A class `u ∈ H¹(0, 1)`
lies in `H¹_{{0}}(0, 1)` and satisfies `∫_0^1 u' v' = ∫_0^1 v` for every `v ∈ H¹_{{0}}(0, 1)`
exactly when it is `x - x²/2`. -/
theorem mem_w1pVanishingOnSubmodule_and_forall_setIntegral_eq_iff_Ioo_zero_one
    (u : W1p volume ⟨Ioo 0 1, isOpen_Ioo⟩ 2) :
    (u ∈ w1pVanishingOnSubmodule volume ⟨Ioo 0 1, isOpen_Ioo⟩ 2 {0} ∧
      ∀ v ∈ w1pVanishingOnSubmodule volume ⟨Ioo 0 1, isOpen_Ioo⟩ 2 {0},
        ∫ t in Ioo 0 1, W1p.gradient u t * W1p.gradient v t = ∫ t in Ioo 0 1, W1p.value v t) ↔
      ∀ t : Icc (0 : ℝ) 1, W1p.intervalRepresentativeL zero_lt_one u t = t - t ^ 2 / 2 := by
  have h := mem_w1pVanishingOnSubmodule_and_forall_setIntegral_gradient_mul_gradient_eq_iff_Ioo
    zero_lt_one (f := fun _ => 1) (integrableOn_const measure_Ioo_lt_top.ne) 0 u
  simp only [one_mul, zero_mul, add_zero, zero_add, intervalIntegral.integral_const, smul_eq_mul,
    mul_one, integral_id, intervalIntegral.integral_sub intervalIntegrable_const
      intervalIntegral.intervalIntegrable_id] at h
  rw [h]
  refine forall_congr' fun t => ?_
  ring_nf

/-- **The Neumann problem `-u'' = 1` with zero Neumann data on `(0, 1)` has no weak solution**:
the datum does not annihilate the constants, since `∫_0^1 1 = 1 ≠ 0`. -/
theorem not_exists_forall_setIntegral_gradient_mul_gradient_eq_Ioo_zero_one :
    ¬∃ u : W1p volume ⟨Ioo 0 1, isOpen_Ioo⟩ 2, ∀ v : W1p volume ⟨Ioo 0 1, isOpen_Ioo⟩ 2,
      ∫ t in Ioo 0 1, W1p.gradient u t * W1p.gradient v t = ∫ t in Ioo 0 1, W1p.value v t := by
  have h := exists_forall_setIntegral_gradient_mul_gradient_eq_iff_Ioo zero_lt_one
    (f := fun _ => 1) (integrableOn_const measure_Ioo_lt_top.ne) 0 0
  simp only [one_mul, zero_mul, add_zero, setIntegral_const, Real.volume_real_Ioo, sub_zero,
    smul_eq_mul, mul_one] at h
  rw [h]
  norm_num

/-- **The Neumann problem `-u'' = 1`, `-u'(0) = 0`, `u'(1) = -1` on `(0, 1)`.** The compatibility
condition `∫_0^1 1 + 0 + (-1) = 0` holds, and a class `u ∈ H¹(0, 1)` satisfies
`∫_0^1 u' v' = ∫_0^1 v - v(1)` for every `v ∈ H¹(0, 1)` exactly when it is `C - x²/2` for a
constant `C`. -/
theorem forall_setIntegral_gradient_mul_gradient_eq_sub_iff_Ioo_zero_one
    (u : W1p volume ⟨Ioo 0 1, isOpen_Ioo⟩ 2) :
    (∀ v : W1p volume ⟨Ioo 0 1, isOpen_Ioo⟩ 2,
      ∫ t in Ioo 0 1, W1p.gradient u t * W1p.gradient v t =
        (∫ t in Ioo 0 1, W1p.value v t) - (W1p.intervalTraceL zero_lt_one v).2) ↔
      ∃ C : ℝ, ∀ t : Icc (0 : ℝ) 1,
        W1p.intervalRepresentativeL zero_lt_one u t = C - t ^ 2 / 2 := by
  have h := forall_setIntegral_gradient_mul_gradient_eq_iff_Ioo zero_lt_one
    (f := fun _ => 1) (integrableOn_const measure_Ioo_lt_top.ne) (h₀ := 0) (h₁ := -1) (by simp) u
  simp only [one_mul, zero_mul, add_zero, zero_add, intervalIntegral.integral_const, smul_eq_mul,
    mul_one, sub_zero, neg_one_mul, ← sub_eq_add_neg, integral_id] at h
  rw [h]
  refine exists_congr fun C => forall_congr' fun t => ?_
  ring_nf

end TauCeti.PDE
