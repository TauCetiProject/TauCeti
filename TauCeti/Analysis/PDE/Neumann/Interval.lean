/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Interval.Representative
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Analysis.Sobolev.W1p.Interval.AbsolutelyContinuous
import TauCeti.Analysis.Sobolev.W1p.Interval.Energy

/-!
# The Neumann problem for `-u''` on an interval

On a bounded interval `(a, b)` of the real line, the energy form of `-u''` is `∫_a^b u' v'`, and
the boundary of `(a, b)` is the two endpoints, on which surface measure is counting measure. For
`f ∈ L¹(a, b)` and boundary data `h₀, h₁ ∈ ℝ`, the weak form of the **Neumann problem**

`-u'' = f` in `(a, b)`, `-u'(a) = h₀`, `u'(b) = h₁`

asks for `u ∈ H¹(a, b)` with

`∫_a^b u' v' = ∫_a^b f v + h₀ v(a) + h₁ v(b)` for every `v ∈ H¹(a, b)`,

where `v(a)` and `v(b)` are the endpoint values of the continuous representative
(`TauCeti.W1p.intervalTraceL`). The data `h₀, h₁` are the outward conormal derivatives: the outward
normal is `-1` at `a` and `+1` at `b`. On an interval the problem is solved explicitly, through the
flux `u'`.

* The problem has a weak solution exactly when the datum annihilates the constants,
  `∫_a^b f + h₀ + h₁ = 0`
  (`TauCeti.PDE.exists_forall_setIntegral_gradient_mul_gradient_eq_iff_Ioo`), as testing with
  `v = 1` shows.
* Its weak solutions are then exactly the functions `C - ∫_a^x (h₀ + ∫_a^s f) ds`, `C ∈ ℝ`
  (`TauCeti.PDE.forall_setIntegral_gradient_mul_gradient_eq_iff_Ioo`): unique up to an additive
  constant.

The flux `-h₀ - ∫_a^x f` of the explicit solution has the prescribed boundary values
(`TauCeti.W1p.exists_intervalRepresentativeL_eq_and_forall_setIntegral_gradient_mul_gradient_eq`).
Uniqueness comes from testing the equation of the difference `w` of two solutions with `w` itself:
`∫_a^b w'² = 0`, so `w` is constant.

On `(0, 1)` with `f = 1` this gives the standard examples:

* with `h₀ = h₁ = 0` there is no weak solution, since `∫_0^1 1 = 1 ≠ 0`
  (`TauCeti.PDE.not_exists_forall_setIntegral_gradient_mul_gradient_eq_Ioo_zero_one`);
* with `h₀ = 0` and `h₁ = -1` the compatibility condition holds, and the weak solutions are exactly
  `C - x²/2`
  (`TauCeti.PDE.forall_setIntegral_gradient_mul_gradient_eq_sub_iff_Ioo_zero_one`).

The mixed problem on an interval is in `TauCeti/Analysis/PDE/MixedProblem/Interval.lean`.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Problem 47,
  part B (the Neumann problem on an interval and its compatibility condition).
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace

namespace TauCeti.PDE

variable {a b : ℝ}

local instance : IsFiniteMeasure (volume.restrict
    ((⟨Ioo a b, isOpen_Ioo⟩ : Opens ℝ) : Set ℝ)) := ⟨by simp⟩

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
    obtain ⟨u, -, hu⟩ :=
      W1p.exists_intervalRepresentativeL_eq_and_forall_setIntegral_gradient_mul_gradient_eq
        (p := 2) (q := 2) hab hf 0 (-h₀)
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
      W1p.exists_intervalRepresentativeL_eq_and_forall_setIntegral_gradient_mul_gradient_eq
        (p := 2) (q := 2) hab hf 0 (-h₀)
    have hsub := W1p.setIntegral_gradient_sub_mul_gradient u u₀ (u - u₀)
    simp only [Opens.coe_mk] at hsub
    have hw := W1p.intervalRepresentativeL_eq_of_setIntegral_gradient_mul_self_eq_zero hab
      (w := u - u₀) (by rw [hsub, hu, hu₀v, hRHS]; ring)
    refine ⟨(W1p.intervalTraceL hab (u - u₀)).1, fun t => ?_⟩
    have ht := hw t
    rw [map_sub, ContinuousMap.sub_apply, hu₀] at ht
    rw [← hflux]
    linarith
  · -- A representative of this form is that of the explicit solution with constant `C`.
    rintro ⟨C, hC⟩
    obtain ⟨u₁, hu₁, hu₁v⟩ :=
      W1p.exists_intervalRepresentativeL_eq_and_forall_setIntegral_gradient_mul_gradient_eq
        (p := 2) (q := 2) hab hf C (-h₀)
    obtain rfl : u = u₁ := W1p.intervalRepresentativeL_injective hab
      (ContinuousMap.ext fun t => by rw [hC, hu₁, hflux])
    intro v
    rw [hu₁v, ← hRHS]
    ring

/-! ### The examples on `(0, 1)` -/

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
