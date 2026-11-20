/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Interval.Representative
public import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Topology.Order.IntermediateValue
import TauCeti.Analysis.PDE.DirichletProblem.Interval
import TauCeti.Analysis.PDE.Regularity.Interval
import TauCeti.Analysis.Sobolev.W1p.Interval.AbsolutelyContinuous

/-!
# The Kirchhoff transformation of quasilinear equations on an interval

On a bounded interval `(x₀, x₁)` consider the quasilinear Dirichlet problem

`-(A(u) u')' = f + F'` in `(x₀, x₁)`, `u(x₀) = g₀`, `u(x₁) = g₁`,

whose coefficient `A` depends on the solution `u` alone, not on the position. A solution is
`u ∈ W^{1,p}(x₀, x₁)` whose continuous representative `ū` takes the boundary values and satisfies

`∫ A(ū t) u' φ' = ∫ f φ - ∫ F φ'` for every test function `φ ∈ C_c^∞(x₀, x₁)`.

For continuous `A` with antiderivative `Φ`, the **Kirchhoff transformation** `w = Φ(u)` turns this
problem into the linear problem `-w'' = f + F'` with boundary values `Φ(g₀)` and `Φ(g₁)`: by the
chain rule `w' = A(u) u'`, so the two weak formulations coincide
(`TauCeti.PDE.exists_intervalRepresentativeL_eq_comp_and_forall_setIntegral_eq`). When `A > 0`, the
antiderivative `Φ` is strictly increasing, and when it is also onto, `u = Φ⁻¹(w)` transforms
solutions back (`TauCeti.PDE.exists_comp_intervalRepresentativeL_eq_and_forall_setIntegral_eq`).

Since the linear problem has exactly one solution, so does the quasilinear one:

* for continuous `A > 0` and integrable `f`, `F`, two solutions with the same boundary values
  coincide (`TauCeti.PDE.eq_of_intervalTraceL_eq_of_forall_setIntegral_eq`);
* for continuous `A ≥ λ > 0`, `f ∈ L¹` and `F ∈ Lᵖ`, the problem has exactly one solution
  (`TauCeti.PDE.existsUnique_intervalTraceL_eq_and_forall_setIntegral_eq`). No upper bound on `A`
  is needed.

For a coefficient `A(x, u)` depending also on the position, existence holds by Schauder's
fixed-point theorem (`TauCeti.PDE.exists_intervalTraceL_eq_and_forall_setIntegral_eq`), but the
substitution is not available and uniqueness is not claimed.

## References

* G. Kirchhoff, *Vorlesungen über die Theorie der Wärme*, Leipzig, 1894 (the substitution, for
  heat conduction with a temperature-dependent conductivity).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Chapter 11 (the quasilinear Dirichlet problem).
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Section 8.4 (one-dimensional boundary value problems).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Distributions

namespace TauCeti.PDE

variable {x₀ x₁ : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {A Φ f F : ℝ → ℝ}

/-- **The Kirchhoff transformation.** Let `A` be continuous with antiderivative `Φ`, and let
`u ∈ W^{1,p}(x₀, x₁)`, with continuous representative `ū`, solve `-(A(u) u')' = f + F'` in the sense
of distributions on `(x₀, x₁)`. Then `Φ ∘ ū` is the continuous representative of a solution
`w ∈ W^{1,p}(x₀, x₁)` of the linear equation `-w'' = f + F'`. -/
theorem exists_intervalRepresentativeL_eq_comp_and_forall_setIntegral_eq (hx : x₀ < x₁)
    (hA : Continuous A) (hΦ : ∀ y, HasDerivAt Φ (A y) y)
    {u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p}
    (hu : ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
      ∫ t in Ioo x₀ x₁, A (W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le t)) *
          W1p.gradient u t * deriv φ t =
        (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t) :
    ∃ w : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p,
      (∀ t : Icc x₀ x₁,
        W1p.intervalRepresentativeL hx w t = Φ (W1p.intervalRepresentativeL hx u t)) ∧
      ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
        ∫ t in Ioo x₀ x₁, W1p.gradient w t * deriv φ t =
          (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t := by
  obtain ⟨w, hrep, hgrad⟩ := W1p.exists_intervalRepresentativeL_eq_comp_and_gradient_ae_eq hx
    (contDiff_one_iff_deriv.2 ⟨fun y => (hΦ y).differentiableAt,
      (funext fun y => (hΦ y).deriv : deriv Φ = A) ▸ hA⟩) u
  refine ⟨w, hrep, fun φ => ?_⟩
  rw [← hu φ]
  -- By the chain rule `w' = A(ū) u'`.
  refine integral_congr_ae (hgrad.mono fun t ht => ?_)
  dsimp only at ht ⊢
  rw [ht, (hΦ _).deriv]

/-- **The inverse Kirchhoff transformation.** Let `A > 0` be continuous with an antiderivative `Φ`
that is onto `ℝ`, and let `w ∈ W^{1,p}(x₀, x₁)`, with continuous representative `W`, solve the
linear equation `-w'' = f + F'` in the sense of distributions on `(x₀, x₁)`. Then `Φ⁻¹ ∘ W` is the
continuous representative of a solution `u ∈ W^{1,p}(x₀, x₁)` of `-(A(u) u')' = f + F'`. -/
theorem exists_comp_intervalRepresentativeL_eq_and_forall_setIntegral_eq (hx : x₀ < x₁)
    (hA : Continuous A) (hA0 : ∀ y, 0 < A y) (hΦ : ∀ y, HasDerivAt Φ (A y) y)
    (hΦs : Function.Surjective Φ) {w : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p}
    (hw : ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
      ∫ t in Ioo x₀ x₁, W1p.gradient w t * deriv φ t =
        (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t) :
    ∃ u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p,
      (∀ t : Icc x₀ x₁,
        Φ (W1p.intervalRepresentativeL hx u t) = W1p.intervalRepresentativeL hx w t) ∧
      ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
        ∫ t in Ioo x₀ x₁, A (W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le t)) *
            W1p.gradient u t * deriv φ t =
          (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t := by
  -- `Φ` is an order isomorphism of `ℝ`, whose inverse `ψ` has derivative `A(ψ)⁻¹`.
  set e : ℝ ≃o ℝ := StrictMono.orderIsoOfSurjective Φ (strictMono_of_hasDerivAt_pos hΦ hA0) hΦs
  have he : ∀ y, Φ (e.symm y) = y := e.apply_symm_apply
  have hψ : ∀ y, HasDerivAt e.symm (A (e.symm y))⁻¹ y := fun y =>
    HasDerivAt.of_local_left_inverse e.symm.continuous.continuousAt (hΦ _) (hA0 _).ne'
      (Eventually.of_forall he)
  obtain ⟨u, hrep, hgrad⟩ := W1p.exists_intervalRepresentativeL_eq_comp_and_gradient_ae_eq hx
    (contDiff_one_iff_deriv.2 ⟨fun y => (hψ y).differentiableAt,
      (funext fun y => (hψ y).deriv : deriv e.symm = fun y => (A (e.symm y))⁻¹) ▸
        (hA.comp e.symm.continuous).inv₀ fun y => (hA0 _).ne'⟩) w
  refine ⟨u, fun t => by rw [hrep, he], fun φ => ?_⟩
  rw [← hw φ]
  -- By the chain rule `A(ū) u' = A(ψ(W)) A(ψ(W))⁻¹ w' = w'`.
  refine integral_congr_ae (hgrad.mono fun t ht => ?_)
  dsimp only at ht ⊢
  rw [ht, (hψ _).deriv, hrep, ← mul_assoc, mul_inv_cancel₀ (hA0 _).ne', one_mul]

/-- Uniqueness for the linear problem `-w'' = f + F'`: two solutions with the same endpoint values
coincide. -/
private theorem eq_of_intervalTraceL_eq_of_forall_setIntegral_gradient_mul_eq (hx : x₀ < x₁)
    (hf : IntegrableOn f (Ioo x₀ x₁)) (hF : IntegrableOn F (Ioo x₀ x₁))
    {w₁ w₂ : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p}
    (htr : W1p.intervalTraceL hx w₁ = W1p.intervalTraceL hx w₂)
    (hw₁ : ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
      ∫ t in Ioo x₀ x₁, W1p.gradient w₁ t * deriv φ t =
        (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t)
    (hw₂ : ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
      ∫ t in Ioo x₀ x₁, W1p.gradient w₂ t * deriv φ t =
        (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t) :
    w₁ = w₂ := by
  -- The first integrals `wᵢ' + F = kᵢ - ∫_{x₀}^t f`.
  obtain ⟨k₁, hk₁⟩ := exists_ae_mul_gradient_add_eq_sub_intervalIntegral (a := fun _ => 1)
    aestronglyMeasurable_const (M := 1) (by simp) hf hF (u := w₁)
    (by simpa only [one_mul] using hw₁)
  obtain ⟨k₂, hk₂⟩ := exists_ae_mul_gradient_add_eq_sub_intervalIntegral (a := fun _ => 1)
    aestronglyMeasurable_const (M := 1) (by simp) hf hF (u := w₂)
    (by simpa only [one_mul] using hw₂)
  -- So `z = w₁ - w₂` has constant gradient `k₁ - k₂`, and it vanishes at both endpoints.
  have hz : ∀ᵐ r ∂volume.restrict (Ioo x₀ x₁), W1p.gradient (w₁ - w₂) r = k₁ - k₂ := by
    filter_upwards [hk₁, hk₂, Lp.coeFn_sub (W1p.gradient w₁) (W1p.gradient w₂)] with r h₁ h₂ h
    rw [W1p.gradient_sub, h, Pi.sub_apply]
    linarith
  -- On every `(s, t) ⊆ (x₀, x₁)`, `z` increases by `(t - s) (k₁ - k₂)`.
  have hlin : ∀ s t : Icc x₀ x₁, (s : ℝ) ≤ t →
      W1p.intervalRepresentativeL hx (w₁ - w₂) t - W1p.intervalRepresentativeL hx (w₁ - w₂) s =
        ((t : ℝ) - s) * (k₁ - k₂) := fun s t hst =>
    W1p.intervalRepresentativeL_sub_eq_mul_of_gradient_eq hx _ hst
      (((ae_restrict_iff' measurableSet_Ioo).1 hz).mono fun _ hr hrI =>
        hr ⟨s.2.1.trans_lt hrI.1, hrI.2.trans_le t.2.2⟩)
  set x₀' : Icc x₀ x₁ := ⟨x₀, left_mem_Icc.2 hx.le⟩
  have hrep : ∀ t, W1p.intervalRepresentativeL hx (w₁ - w₂) t =
      W1p.intervalRepresentativeL hx w₁ t - W1p.intervalRepresentativeL hx w₂ t := fun t => by
    rw [map_sub, ContinuousMap.sub_apply]
  rw [W1p.intervalTraceL_apply, W1p.intervalTraceL_apply, Prod.mk.injEq] at htr
  have h0 : W1p.intervalRepresentativeL hx (w₁ - w₂) x₀' = 0 := by rw [hrep, htr.1, sub_self]
  -- The two zero endpoint values force `k₁ = k₂`, so `z` is constant, hence zero.
  have hk : k₁ - k₂ = 0 := by
    have h := hlin x₀' ⟨x₁, right_mem_Icc.2 hx.le⟩ hx.le
    rw [hrep, htr.2, sub_self, h0, sub_self, eq_comm] at h
    exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hx.ne')
  rw [← sub_eq_zero]
  apply W1p.intervalRepresentativeL_injective hx
  ext t
  have h := hlin x₀' t t.2.1
  rw [hk, mul_zero, h0, sub_zero] at h
  rw [h, map_zero, ContinuousMap.zero_apply]

/-- **Uniqueness for the quasilinear Dirichlet problem** `-(A(u) u')' = f + F'` on an interval,
for a continuous coefficient `A > 0` depending on the solution alone: two solutions
`u, v ∈ W^{1,p}(x₀, x₁)` with the same endpoint values coincide. No bound on `A` is needed. -/
theorem eq_of_intervalTraceL_eq_of_forall_setIntegral_eq (hx : x₀ < x₁) (hA : Continuous A)
    (hA0 : ∀ y, 0 < A y) (hf : IntegrableOn f (Ioo x₀ x₁)) (hF : IntegrableOn F (Ioo x₀ x₁))
    {u v : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p}
    (htr : W1p.intervalTraceL hx u = W1p.intervalTraceL hx v)
    (hu : ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
      ∫ t in Ioo x₀ x₁, A (W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le t)) *
          W1p.gradient u t * deriv φ t =
        (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t)
    (hv : ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
      ∫ t in Ioo x₀ x₁, A (W1p.intervalRepresentativeL hx v (projIcc x₀ x₁ hx.le t)) *
          W1p.gradient v t * deriv φ t =
        (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t) :
    u = v := by
  -- The Kirchhoff transforms of the representatives of `u` and `v` solve the same linear problem.
  have hΦ : ∀ y, HasDerivAt (fun y => ∫ s in (0 : ℝ)..y, A s) (A y) y := fun y =>
    (hA.integral_hasStrictDerivAt 0 y).hasDerivAt
  obtain ⟨w₁, hw₁r, hw₁⟩ := exists_intervalRepresentativeL_eq_comp_and_forall_setIntegral_eq hx hA
    hΦ hu
  obtain ⟨w₂, hw₂r, hw₂⟩ := exists_intervalRepresentativeL_eq_comp_and_forall_setIntegral_eq hx hA
    hΦ hv
  have hw : w₁ = w₂ := by
    refine eq_of_intervalTraceL_eq_of_forall_setIntegral_gradient_mul_eq hx hf hF ?_ hw₁ hw₂
    rw [W1p.intervalTraceL_apply, W1p.intervalTraceL_apply, Prod.mk.injEq] at htr ⊢
    rw [hw₁r, hw₁r, hw₂r, hw₂r, htr.1, htr.2]
    exact ⟨rfl, rfl⟩
  -- The antiderivative of `A > 0` is injective.
  apply W1p.intervalRepresentativeL_injective hx
  ext t
  exact (strictMono_of_hasDerivAt_pos hΦ hA0).injective (by rw [← hw₁r, ← hw₂r, hw])

/-- **Well-posedness of the quasilinear Dirichlet problem** `-(A(u) u')' = f + F'` on an interval,
for a continuous coefficient `A ≥ λ > 0` depending on the solution alone. Let `f ∈ L¹(x₀, x₁)` and
`F ∈ Lᵖ(x₀, x₁)` with `1 ≤ p ≤ ∞`. For all `g₀, g₁` there is exactly one `u ∈ W^{1,p}(x₀, x₁)` whose
continuous representative `ū` takes the boundary values `ū x₀ = g₀`, `ū x₁ = g₁`, and which solves
the equation weakly:

`∫ A(ū t) u' φ' = ∫ f φ - ∫ F φ'` for every `φ ∈ C_c^∞(x₀, x₁)`.

Unlike the existence theorem for coefficients `A(x, u)`
(`TauCeti.PDE.exists_intervalTraceL_eq_and_forall_setIntegral_eq`), no upper bound on `A` is
needed. -/
theorem existsUnique_intervalTraceL_eq_and_forall_setIntegral_eq (hx : x₀ < x₁) {lam : ℝ}
    (hlam : 0 < lam) (hA : Continuous A) (hAl : ∀ y, lam ≤ A y) (hf : IntegrableOn f (Ioo x₀ x₁))
    (hF : MemLp F p (volume.restrict (Ioo x₀ x₁))) (g₀ g₁ : ℝ) :
    ∃! u : W1p volume ⟨Ioo x₀ x₁, isOpen_Ioo⟩ p,
      W1p.intervalTraceL hx u = (g₀, g₁) ∧
      ∀ φ : 𝓓(⟨Ioo x₀ x₁, isOpen_Ioo⟩, ℝ),
        ∫ t in Ioo x₀ x₁, A (W1p.intervalRepresentativeL hx u (projIcc x₀ x₁ hx.le t)) *
            W1p.gradient u t * deriv φ t =
          (∫ t in Ioo x₀ x₁, f t * φ t) - ∫ t in Ioo x₀ x₁, F t * deriv φ t := by
  set Φ : ℝ → ℝ := fun y => ∫ s in (0 : ℝ)..y, A s
  have hΦ : ∀ y, HasDerivAt Φ (A y) y := fun y => (hA.integral_hasStrictDerivAt 0 y).hasDerivAt
  have hA0 : ∀ y, 0 < A y := fun y => hlam.trans_le (hAl y)
  -- `Φ` is onto: `Φ - λ id` is monotone and vanishes at `0`, so `Φ y` lies beyond `λ y`.
  have hmono : Monotone fun y => Φ y - lam * y :=
    monotone_of_hasDerivAt_nonneg (fun y => (hΦ y).sub ((hasDerivAt_id y).const_mul lam))
      fun y => by simpa using hAl y
  have hΦ0 : Φ 0 = 0 := intervalIntegral.integral_same
  have hΦs : Function.Surjective Φ := by
    refine (continuous_iff_continuousAt.2 fun y => (hΦ y).continuousAt).surjective
      (tendsto_atTop_mono' _ ?_ (tendsto_id.const_mul_atTop hlam))
      (tendsto_atBot_mono' _ ?_ (tendsto_id.const_mul_atBot hlam))
    · filter_upwards [eventually_ge_atTop 0] with y hy
      simpa [hΦ0] using hmono hy
    · filter_upwards [eventually_le_atBot 0] with y hy
      simpa [hΦ0] using hmono hy
  -- Solve the linear problem `-w'' = f + F'` with boundary values `Φ(g₀)`, `Φ(g₁)` and transform
  -- back.
  obtain ⟨w, hwtr, hw⟩ := exists_intervalTraceL_eq_and_forall_integral_mul_gradient_eq
    (a := fun _ => 1) hx one_pos aestronglyMeasurable_const (ae_of_all _ fun _ => le_rfl) hf hF
    (Φ g₀) (Φ g₁)
  obtain ⟨u, hu, hweak⟩ := exists_comp_intervalRepresentativeL_eq_and_forall_setIntegral_eq hx hA
    hA0 hΦ hΦs (w := w) (by simpa only [one_mul] using hw)
  have hutr : W1p.intervalTraceL hx u = (g₀, g₁) := by
    rw [W1p.intervalTraceL_apply] at hwtr ⊢
    rw [← hu, ← hu, Prod.mk.injEq] at hwtr
    have hinj := (strictMono_of_hasDerivAt_pos hΦ hA0).injective
    rw [hinj hwtr.1, hinj hwtr.2]
  exact ⟨u, ⟨hutr, hweak⟩, fun v hv => eq_of_intervalTraceL_eq_of_forall_setIntegral_eq hx hA hA0
    hf (hF.integrable Fact.out) (hv.1.trans hutr.symm) hv.2 hweak⟩

end TauCeti.PDE
