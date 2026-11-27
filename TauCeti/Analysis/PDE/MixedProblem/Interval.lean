/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Interval.OneEndpoint
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Analysis.Sobolev.W1p.Interval.AbsolutelyContinuous
import TauCeti.Analysis.Sobolev.W1p.Interval.Energy

/-!
# The mixed problem for `-u''` on an interval

On a bounded interval `(a, b)` of the real line, the energy form of `-u''` is `∫_a^b u' v'`, and
the boundary of `(a, b)` is the two endpoints, on which surface measure is counting measure. For
`f ∈ L¹(a, b)` and a boundary datum `h₁ ∈ ℝ`, the weak form of the **mixed problem**, with the
Dirichlet condition `u(a) = 0` on the boundary part `Γ = {a}` and the Neumann condition
`u'(b) = h₁` on the rest of the boundary, asks for `u ∈ H¹_Γ(a, b)` with

`∫_a^b u' v' = ∫_a^b f v + h₁ v(b)` for every `v ∈ H¹_Γ(a, b)`,

where `H¹_Γ(a, b)` is the space `TauCeti.w1pVanishingOnSubmodule` of Sobolev functions vanishing on
`Γ` and `v(b)` is the endpoint value of the continuous representative
(`TauCeti.W1p.intervalTraceL`). The problem has exactly one weak solution,
`∫_a^x (h₁ + ∫_s^b f) ds`
(`TauCeti.PDE.mem_w1pVanishingOnSubmodule_and_forall_setIntegral_gradient_mul_gradient_eq_iff_Ioo`
and `TauCeti.PDE.existsUnique_mem_w1pVanishingOnSubmodule_and_forall_setIntegral_eq_Ioo`).

The flux `u' = h₁ + ∫_x^b f` of the explicit solution is `c - ∫_a^x f` for a constant `c`, and
integration by parts against it gives `∫_a^b u' v' = u'(b) v(b) - u'(a) v(a) + ∫_a^b f v`
(`TauCeti.W1p.exists_intervalRepresentativeL_eq_and_forall_setIntegral_gradient_mul_gradient_eq`),
where `v(a) = 0` on `H¹_Γ(a, b)`. Uniqueness comes from testing the equation of the difference `w`
of two solutions with `w` itself: `∫_a^b w'² = 0`, so `w` is constant, and `w(a) = 0`.

On `(0, 1)` with `f = 1` and `h₁ = 0` this gives the standard example: the mixed problem
`-u'' = 1`, `u(0) = 0`, `u'(1) = 0` has the unique weak solution `x - x²/2`
(`TauCeti.PDE.mem_w1pVanishingOnSubmodule_and_forall_setIntegral_eq_iff_Ioo_zero_one`).

The Neumann problem on an interval is in `TauCeti/Analysis/PDE/Neumann/Interval.lean`.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, §8.4,
  Example 5 (a mixed condition in one dimension).
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace

namespace TauCeti.PDE

variable {a b : ℝ}

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
  obtain ⟨u₀, hu₀, hu₀v⟩ :=
    W1p.exists_intervalRepresentativeL_eq_and_forall_setIntegral_gradient_mul_gradient_eq
      (p := 2) (q := 2) hab hf 0 c
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
    have hsub := W1p.setIntegral_gradient_sub_mul_gradient u u₀ (u - u₀)
    simp only [Opens.coe_mk] at hsub
    have hw := W1p.intervalRepresentativeL_eq_of_setIntegral_gradient_mul_self_eq_zero hab
      (w := u - u₀) (by rw [hsub, huv _ hwmem, hsol _ hwmem, sub_self])
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
  obtain ⟨u, hu, -⟩ :=
    W1p.exists_intervalRepresentativeL_eq_and_forall_setIntegral_gradient_mul_gradient_eq
      (p := 2) (q := 2) hab hf 0 (h₁ + ∫ t in Ioo a b, f t)
  refine ⟨u, fun t => ?_, fun u' hu' => W1p.intervalRepresentativeL_injective hab
    (ContinuousMap.ext fun t => ?_)⟩
  · rw [hu, zero_add, intervalIntegral_sub_intervalIntegral_eq hab hf h₁ t]
  · rw [hu', hu, zero_add, intervalIntegral_sub_intervalIntegral_eq hab hf h₁ t]

/-! ### The example on `(0, 1)` -/

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

end TauCeti.PDE
