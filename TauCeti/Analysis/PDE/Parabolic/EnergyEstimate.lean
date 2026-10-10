/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.GelfandTriple
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Analysis.ODE.Gronwall
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The energy estimate and uniqueness for linear parabolic equations

Let `V ↪ H ↪ V*` be a Gelfand triple, given by a continuous linear map `ι : V →L[ℝ] H` from a
Banach space into a real inner product space (`ContinuousLinearMap.gelfandDual`). An abstract
linear parabolic equation on a time interval `(a, b)` is

`u' + A(t) u = f`,

where `A(t) : V →L[ℝ] V*` is a family of bounded operators, `f ∈ L²(a, b; V*)`, and a weak
solution is a `u ∈ L²(a, b; V)` whose image `ι.gelfandDual ∘ ι ∘ u` in `V*` has a weak time
derivative `u' ∈ L²(a, b; V*)` satisfying the equation for almost every `t`. By
`TauCeti.HasWeakLineDerivOn.exists_continuousOn_ae_eq_of_gelfandDual`, `ι ∘ u` then has a
representative `w` continuous on `[a, b]`, which gives meaning to the initial value `w a`.

For `L = -∂ⱼ(aⁱʲ(x, t) ∂ᵢ ·) + …` on a domain `Ω`, the triple is `H¹₀(Ω) ↪ L²(Ω) ↪ H⁻¹(Ω)` and
`A(t)` is the energy form of `L` at time `t`.

Assume that `A(t)` satisfies **Gårding's inequality** `α ‖v‖² - β ‖ι v‖² ≤ A(t) v v` for some
`α > 0` and `β ≥ 0`. The energy identity `d/dt ‖w‖² = 2 u'(u) = 2 f(u) - 2 A(t) u u`, Young's
inequality `2 f(u) ≤ α⁻¹ ‖f‖² + α ‖u‖²` and Grönwall's inequality give the **energy estimate**

`‖w t‖² + α ∫ₐᵗ ‖u‖² ≤ exp (2 β (t - a)) (‖w a‖² + α⁻¹ ∫ₐᵗ ‖f‖²)`

for every `t ∈ [a, b]` (`TauCeti.HasWeakLineDerivOn.norm_sq_add_mul_integral_le_of_gelfandDual`).
Applied to the difference of two solutions, it shows that a weak solution is determined by its
initial value and the right-hand side: their continuous representatives agree on `[a, b]`
(`TauCeti.HasWeakLineDerivOn.eqOn_of_gelfandDual`), and the solutions themselves agree almost
everywhere on `(a, b)` (`TauCeti.HasWeakLineDerivOn.ae_eq_of_gelfandDual`), even when `ι` is not
injective.

No measurability of `t ↦ A(t)` is assumed: the equation and the integrability of `u'(u)` and
`f(u)` already make `t ↦ A(t) u(t) u(t)` integrable.

## Main declarations

* `TauCeti.HasWeakLineDerivOn.norm_sq_add_mul_integral_le_of_gelfandDual`: the energy estimate.
* `TauCeti.HasWeakLineDerivOn.eqOn_of_gelfandDual`: two weak solutions with the same initial
  value have the same continuous representative.
* `TauCeti.HasWeakLineDerivOn.ae_eq_of_gelfandDual`: two weak solutions with the same initial
  value agree almost everywhere.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §7.1.2, Theorem 2 and Theorem 4.
* E. Zeidler, *Nonlinear Functional Analysis and its Applications II/A*, Chapter 23.
-/

public section

open MeasureTheory Filter Set Real

namespace TauCeti

variable {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] {ι : V →L[ℝ] H} {A : ℝ → V →L[ℝ] StrongDual ℝ V}
  {a b α β : ℝ} {u : ℝ → V} {u' f : ℝ → StrongDual ℝ V} {w : ℝ → H}

/-- The pointwise energy balance: if `B` satisfies Gårding's inequality and `d + B x = g`, then
`2 d x ≤ α⁻¹ ‖g‖² - α ‖x‖² + 2 β ‖ι x‖²`, by Young's inequality `2 g x ≤ α⁻¹ ‖g‖² + α ‖x‖²`. -/
private theorem two_mul_apply_le {B : V →L[ℝ] StrongDual ℝ V} {x : V} {d g : StrongDual ℝ V}
    (hα : 0 < α) (hB : ∀ v, α * ‖v‖ ^ 2 - β * ‖ι v‖ ^ 2 ≤ B v v) (heq : d + B x = g) :
    2 * d x ≤ α⁻¹ * ‖g‖ ^ 2 - α * ‖x‖ ^ 2 + 2 * β * ‖ι x‖ ^ 2 := by
  have hdx : d x = g x - B x x := by
    rw [← heq, add_apply, add_sub_cancel_right]
  have hgx : g x ≤ ‖g‖ * ‖x‖ := (le_abs_self _).trans <| by
    simpa only [Real.norm_eq_abs] using g.le_opNorm x
  have hyoung : 0 ≤ α⁻¹ * (‖g‖ - α * ‖x‖) ^ 2 := by positivity
  have hαα : α⁻¹ * α = 1 := inv_mul_cancel₀ hα.ne'
  rw [hdx]
  nlinarith [hB x, hgx, hyoung, hαα]

variable [CompleteSpace V]

/-- **The energy estimate for linear parabolic equations.** Let `ι : V →L[ℝ] H` define a Gelfand
triple, and let `A(t)` satisfy Gårding's inequality `α ‖v‖² - β ‖ι v‖² ≤ A(t) v v` with `α > 0`
and `β ≥ 0` for almost every `t ∈ (a, b)`. Let `u ∈ L²(a, b; V)` be such that
`t ↦ ι.gelfandDual (ι (u t))` has weak derivative `u' ∈ L²(a, b; V*)` with `u' + A(t) u = f` almost
everywhere on `(a, b)`, for some `f ∈ L²(a, b; V*)`, and let `w` be continuous on `[a, b]` and equal
to `ι ∘ u` almost everywhere on `(a, b)`. Then for every `t ∈ [a, b]`,
`‖w t‖² + α ∫ₐᵗ ‖u‖² ≤ exp (2 β (t - a)) (‖w a‖² + α⁻¹ ∫ₐᵗ ‖f‖²)`. -/
theorem HasWeakLineDerivOn.norm_sq_add_mul_integral_le_of_gelfandDual
    (h : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ (fun t ↦ ι.gelfandDual (ι (u t))) u' 1)
    (hu : MemLp u 2 (volume.restrict (Ioo a b))) (hu' : MemLp u' 2 (volume.restrict (Ioo a b)))
    (hf : MemLp f 2 (volume.restrict (Ioo a b))) (hα : 0 < α) (hβ : 0 ≤ β)
    (hA : ∀ᵐ t ∂volume.restrict (Ioo a b), ∀ v, α * ‖v‖ ^ 2 - β * ‖ι v‖ ^ 2 ≤ A t v v)
    (heq : ∀ᵐ t ∂volume.restrict (Ioo a b), u' t + A t (u t) = f t)
    (hw : ContinuousOn w (Icc a b)) (hae : (fun t ↦ ι (u t)) =ᵐ[volume.restrict (Ioo a b)] w)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ‖w t‖ ^ 2 + α * ∫ s in a..t, ‖u s‖ ^ 2 ≤
      exp (2 * β * (t - a)) * (‖w a‖ ^ 2 + α⁻¹ * ∫ s in a..t, ‖f s‖ ^ 2) := by
  have hab : a ≤ b := ht.1.trans ht.2
  have ha : a ∈ Icc a b := left_mem_Icc.2 hab
  -- Integrability of the terms of the energy balance on `(a, b)`.
  have hp : IntegrableOn (fun r ↦ 2 * u' r (u r)) (Ioo a b) :=
    (memLp_one_iff_integrable.1
      ((ContinuousLinearMap.id ℝ (StrongDual ℝ V)).memLp_of_bilin 1 hu' hu)).const_mul 2
  have hu2 : IntegrableOn (fun r ↦ ‖u r‖ ^ 2) (Ioo a b) :=
    (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).1 hu
  have hf2 : IntegrableOn (fun r ↦ ‖f r‖ ^ 2) (Ioo a b) :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf
  have hφ : ContinuousOn (fun r ↦ ‖w r‖ ^ 2) (Icc a b) := hw.norm.pow 2
  have hφi : IntegrableOn (fun r ↦ ‖w r‖ ^ 2) (Ioo a b) :=
    hφ.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  -- Pointwise, `2 u'(u) ≤ α⁻¹ ‖f‖² - α ‖u‖² + 2 β ‖w‖²`, by the equation, Gårding and Young.
  have hpt : ∀ᵐ r ∂volume.restrict (Ioo a b),
      2 * u' r (u r) ≤ α⁻¹ * ‖f r‖ ^ 2 - α * ‖u r‖ ^ 2 + 2 * β * ‖w r‖ ^ 2 := by
    filter_upwards [hA, heq, hae] with r hAr heqr haer
    simpa only [haer] using two_mul_apply_le hα hAr heqr
  -- Integrating, `χ s = ‖w s‖² + α ∫ₐˢ ‖u‖²` satisfies `χ s ≤ ‖w a‖² + α⁻¹ ∫ₐᵗ ‖f‖² + 2 β ∫ₐˢ χ`
  -- on `[a, t]`.
  set χ : ℝ → ℝ := fun s ↦ ‖w s‖ ^ 2 + α * ∫ r in a..s, ‖u r‖ ^ 2 with hχ_def
  have hU : ContinuousOn (fun s ↦ ∫ r in a..s, ‖u r‖ ^ 2) (Icc a b) := by
    have hU2 : IntegrableOn (fun r ↦ ‖u r‖ ^ 2) (uIcc a b) := by
      rw [uIcc_of_le hab]
      exact (integrableOn_Icc_iff_integrableOn_Ioo (f := fun r ↦ ‖u r‖ ^ 2)).2 hu2
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume) hU2
    rwa [uIcc_of_le hab] at this
  have hχ : ContinuousOn χ (Icc a b) := hφ.add (hU.const_smul α)
  have hU0 (s : ℝ) (hs : a ≤ s) : 0 ≤ ∫ r in a..s, ‖u r‖ ^ 2 :=
    intervalIntegral.integral_nonneg hs fun _ _ ↦ by positivity
  have htb : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
  have hbound : ∀ s ∈ Icc a t,
      χ s ≤ (‖w a‖ ^ 2 + α⁻¹ * ∫ r in a..t, ‖f r‖ ^ 2) + 2 * β * ∫ r in a..s, χ r := by
    intro s hs
    have hsb : s ∈ Icc a b := htb hs
    have hsub : Ioo a s ⊆ Ioo a b := Ioo_subset_Ioo_right hsb.2
    have hφs := hφi.intervalIntegrable_of_mem_Icc ha hsb
    have hfs := hf2.intervalIntegrable_of_mem_Icc ha hsb
    have hus := hu2.intervalIntegrable_of_mem_Icc ha hsb
    -- the energy identity, then the pointwise bound integrated over `(a, s)`
    have hid : ‖w s‖ ^ 2 - ‖w a‖ ^ 2 = ∫ r in a..s, 2 * u' r (u r) := by
      rw [h.norm_sq_sub_norm_sq_eq_of_gelfandDual hu hu' hw hae ha hsb,
        intervalIntegral.integral_const_mul]
    have hint : ∫ r in a..s, 2 * u' r (u r) ≤
        ∫ r in a..s, (α⁻¹ * ‖f r‖ ^ 2 - α * ‖u r‖ ^ 2 + 2 * β * ‖w r‖ ^ 2) := by
      rw [intervalIntegral.integral_of_le hs.1, intervalIntegral.integral_of_le hs.1,
        integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
      exact setIntegral_mono_ae_restrict (hp.mono_set hsub)
        (IntegrableOn.mono_set (((hf2.const_mul α⁻¹).sub (hu2.const_mul α)).add
          (hφi.const_mul (2 * β))) hsub)
        (ae_restrict_of_ae_restrict_of_subset hsub hpt)
    have hsplit : ∫ r in a..s, (α⁻¹ * ‖f r‖ ^ 2 - α * ‖u r‖ ^ 2 + 2 * β * ‖w r‖ ^ 2) =
        α⁻¹ * (∫ r in a..s, ‖f r‖ ^ 2) - α * (∫ r in a..s, ‖u r‖ ^ 2) +
          2 * β * ∫ r in a..s, ‖w r‖ ^ 2 := by
      rw [intervalIntegral.integral_add ((hfs.const_mul α⁻¹).sub (hus.const_mul α))
        (hφs.const_mul (2 * β)), intervalIntegral.integral_sub (hfs.const_mul α⁻¹)
        (hus.const_mul α)]
      simp only [intervalIntegral.integral_const_mul]
    -- `∫ₐˢ ‖f‖² ≤ ∫ₐᵗ ‖f‖²` and `∫ₐˢ ‖w‖² ≤ ∫ₐˢ χ`
    have hfmono : ∫ r in a..s, ‖f r‖ ^ 2 ≤ ∫ r in a..t, ‖f r‖ ^ 2 :=
      intervalIntegral.integral_mono_interval le_rfl hs.1 hs.2
        (Eventually.of_forall fun _ ↦ by positivity) (hf2.intervalIntegrable_of_mem_Icc ha ht)
    have hχmono : ∫ r in a..s, ‖w r‖ ^ 2 ≤ ∫ r in a..s, χ r :=
      intervalIntegral.integral_mono_on hs.1 hφs
        (ContinuousOn.intervalIntegrable_of_Icc hs.1 (hχ.mono (Icc_subset_Icc_right hsb.2)))
        fun r hr ↦ le_add_of_nonneg_right (mul_nonneg hα.le (hU0 r hr.1))
    have hα' : 0 ≤ α⁻¹ := inv_nonneg.2 hα.le
    have hχs : χ s = ‖w s‖ ^ 2 + α * ∫ r in a..s, ‖u r‖ ^ 2 := rfl
    rw [hχs]
    nlinarith [mul_le_mul_of_nonneg_left hfmono hα', mul_le_mul_of_nonneg_left hχmono
      (by positivity : 0 ≤ 2 * β)]
  have := le_mul_exp_of_le_add_mul_integral (hχ.mono htb) (by positivity) hbound t
    (right_mem_Icc.2 ht.1)
  simpa only [hχ_def, mul_comm (exp _)] using this

/-- The energy estimate for the difference of two weak solutions with the same initial value and
right-hand side: `‖w₁ t - w₂ t‖² + α ∫ₐᵗ ‖u₁ - u₂‖² ≤ 0` on `[a, b]`. -/
private theorem norm_sq_add_mul_integral_sub_nonpos {u₁ u₂ : ℝ → V}
    {u₁' u₂' : ℝ → StrongDual ℝ V} {w₁ w₂ : ℝ → H}
    (h₁ : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ (fun t ↦ ι.gelfandDual (ι (u₁ t))) u₁' 1)
    (h₂ : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ (fun t ↦ ι.gelfandDual (ι (u₂ t))) u₂' 1)
    (hu₁ : MemLp u₁ 2 (volume.restrict (Ioo a b))) (hu₁' : MemLp u₁' 2 (volume.restrict (Ioo a b)))
    (hu₂ : MemLp u₂ 2 (volume.restrict (Ioo a b))) (hu₂' : MemLp u₂' 2 (volume.restrict (Ioo a b)))
    (hα : 0 < α) (hβ : 0 ≤ β)
    (hA : ∀ᵐ t ∂volume.restrict (Ioo a b), ∀ v, α * ‖v‖ ^ 2 - β * ‖ι v‖ ^ 2 ≤ A t v v)
    (heq₁ : ∀ᵐ t ∂volume.restrict (Ioo a b), u₁' t + A t (u₁ t) = f t)
    (heq₂ : ∀ᵐ t ∂volume.restrict (Ioo a b), u₂' t + A t (u₂ t) = f t)
    (hw₁ : ContinuousOn w₁ (Icc a b)) (hae₁ : (fun t ↦ ι (u₁ t)) =ᵐ[volume.restrict (Ioo a b)] w₁)
    (hw₂ : ContinuousOn w₂ (Icc a b)) (hae₂ : (fun t ↦ ι (u₂ t)) =ᵐ[volume.restrict (Ioo a b)] w₂)
    (h₀ : w₁ a = w₂ a) {t : ℝ} (ht : t ∈ Icc a b) :
    ‖w₁ t - w₂ t‖ ^ 2 + α * ∫ s in a..t, ‖u₁ s - u₂ s‖ ^ 2 ≤ 0 := by
  -- `u₁ - u₂` solves the homogeneous equation with zero initial value.
  have hd : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩
      (fun t ↦ ι.gelfandDual (ι ((u₁ - u₂) t))) (u₁' - u₂') 1 := by
    have e : (fun t ↦ ι.gelfandDual (ι ((u₁ - u₂) t))) =
        (fun t ↦ ι.gelfandDual (ι (u₁ t))) - fun t ↦ ι.gelfandDual (ι (u₂ t)) := by
      ext1 t
      simp only [Pi.sub_apply, map_sub]
    rw [e]
    exact h₁.sub h₂
  have heq : ∀ᵐ t ∂volume.restrict (Ioo a b),
      (u₁' - u₂') t + A t ((u₁ - u₂) t) = (0 : ℝ → StrongDual ℝ V) t := by
    filter_upwards [heq₁, heq₂] with t e₁ e₂
    rw [Pi.sub_apply, Pi.sub_apply, map_sub, Pi.zero_apply]
    calc u₁' t - u₂' t + (A t (u₁ t) - A t (u₂ t))
        = (u₁' t + A t (u₁ t)) - (u₂' t + A t (u₂ t)) := by abel
      _ = 0 := by rw [e₁, e₂, sub_self]
  have hae : (fun t ↦ ι ((u₁ - u₂) t)) =ᵐ[volume.restrict (Ioo a b)] w₁ - w₂ := by
    filter_upwards [hae₁, hae₂] with t e₁ e₂
    rw [Pi.sub_apply, map_sub, e₁, e₂, Pi.sub_apply]
  have := hd.norm_sq_add_mul_integral_le_of_gelfandDual (hu₁.sub hu₂) (hu₁'.sub hu₂')
    (MemLp.zero (ε := StrongDual ℝ V)) hα hβ hA heq (hw₁.sub hw₂) hae ht
  simp only [Pi.sub_apply, Pi.zero_apply, h₀, sub_self, norm_zero] at this
  simpa using this

/-- **Uniqueness for linear parabolic equations: continuous representatives.** Let `ι : V →L[ℝ] H`
define a Gelfand triple, and let `A(t)` satisfy Gårding's inequality
`α ‖v‖² - β ‖ι v‖² ≤ A(t) v v` with `α > 0` and `β ≥ 0` for almost every `t ∈ (a, b)`. If `u₁` and
`u₂` are weak solutions in `L²(a, b; V)` of `u' + A(t) u = f` on `(a, b)`, and their continuous
representatives `w₁`, `w₂` on `[a, b]` have the same initial value `w₁ a = w₂ a`, then `w₁ = w₂` on
`[a, b]`. -/
theorem HasWeakLineDerivOn.eqOn_of_gelfandDual {u₁ u₂ : ℝ → V} {u₁' u₂' : ℝ → StrongDual ℝ V}
    {w₁ w₂ : ℝ → H}
    (h₁ : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ (fun t ↦ ι.gelfandDual (ι (u₁ t))) u₁' 1)
    (h₂ : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ (fun t ↦ ι.gelfandDual (ι (u₂ t))) u₂' 1)
    (hu₁ : MemLp u₁ 2 (volume.restrict (Ioo a b))) (hu₁' : MemLp u₁' 2 (volume.restrict (Ioo a b)))
    (hu₂ : MemLp u₂ 2 (volume.restrict (Ioo a b))) (hu₂' : MemLp u₂' 2 (volume.restrict (Ioo a b)))
    (hα : 0 < α) (hβ : 0 ≤ β)
    (hA : ∀ᵐ t ∂volume.restrict (Ioo a b), ∀ v, α * ‖v‖ ^ 2 - β * ‖ι v‖ ^ 2 ≤ A t v v)
    (heq₁ : ∀ᵐ t ∂volume.restrict (Ioo a b), u₁' t + A t (u₁ t) = f t)
    (heq₂ : ∀ᵐ t ∂volume.restrict (Ioo a b), u₂' t + A t (u₂ t) = f t)
    (hw₁ : ContinuousOn w₁ (Icc a b)) (hae₁ : (fun t ↦ ι (u₁ t)) =ᵐ[volume.restrict (Ioo a b)] w₁)
    (hw₂ : ContinuousOn w₂ (Icc a b)) (hae₂ : (fun t ↦ ι (u₂ t)) =ᵐ[volume.restrict (Ioo a b)] w₂)
    (h₀ : w₁ a = w₂ a) :
    EqOn w₁ w₂ (Icc a b) := by
  intro t ht
  have hle := norm_sq_add_mul_integral_sub_nonpos h₁ h₂ hu₁ hu₁' hu₂ hu₂' hα hβ hA heq₁ heq₂ hw₁
    hae₁ hw₂ hae₂ h₀ ht
  have hint : 0 ≤ α * ∫ s in a..t, ‖u₁ s - u₂ s‖ ^ 2 :=
    mul_nonneg hα.le (intervalIntegral.integral_nonneg ht.1 fun _ _ ↦ by positivity)
  have : ‖w₁ t - w₂ t‖ ^ 2 = 0 := le_antisymm (by linarith) (by positivity)
  simpa [sub_eq_zero] using this

/-- **Uniqueness for linear parabolic equations.** Let `ι : V →L[ℝ] H` define a Gelfand triple, and
let `A(t)` satisfy Gårding's inequality `α ‖v‖² - β ‖ι v‖² ≤ A(t) v v` with `α > 0` and `β ≥ 0` for
almost every `t ∈ (a, b)`. If `u₁` and `u₂` are weak solutions in `L²(a, b; V)` of
`u' + A(t) u = f` on `(a, b)`, and their continuous representatives `w₁`, `w₂` on `[a, b]` have the
same initial value `w₁ a = w₂ a`, then `u₁ = u₂` almost everywhere on `(a, b)`. This holds even when
`ι` is not injective. -/
theorem HasWeakLineDerivOn.ae_eq_of_gelfandDual {u₁ u₂ : ℝ → V} {u₁' u₂' : ℝ → StrongDual ℝ V}
    {w₁ w₂ : ℝ → H}
    (h₁ : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ (fun t ↦ ι.gelfandDual (ι (u₁ t))) u₁' 1)
    (h₂ : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ (fun t ↦ ι.gelfandDual (ι (u₂ t))) u₂' 1)
    (hu₁ : MemLp u₁ 2 (volume.restrict (Ioo a b))) (hu₁' : MemLp u₁' 2 (volume.restrict (Ioo a b)))
    (hu₂ : MemLp u₂ 2 (volume.restrict (Ioo a b))) (hu₂' : MemLp u₂' 2 (volume.restrict (Ioo a b)))
    (hα : 0 < α) (hβ : 0 ≤ β)
    (hA : ∀ᵐ t ∂volume.restrict (Ioo a b), ∀ v, α * ‖v‖ ^ 2 - β * ‖ι v‖ ^ 2 ≤ A t v v)
    (heq₁ : ∀ᵐ t ∂volume.restrict (Ioo a b), u₁' t + A t (u₁ t) = f t)
    (heq₂ : ∀ᵐ t ∂volume.restrict (Ioo a b), u₂' t + A t (u₂ t) = f t)
    (hw₁ : ContinuousOn w₁ (Icc a b)) (hae₁ : (fun t ↦ ι (u₁ t)) =ᵐ[volume.restrict (Ioo a b)] w₁)
    (hw₂ : ContinuousOn w₂ (Icc a b)) (hae₂ : (fun t ↦ ι (u₂ t)) =ᵐ[volume.restrict (Ioo a b)] w₂)
    (h₀ : w₁ a = w₂ a) :
    u₁ =ᵐ[volume.restrict (Ioo a b)] u₂ := by
  rcases lt_or_ge b a with hba | hab
  · simp [Ioo_eq_empty_of_le hba.le, EventuallyEq]
  have hle := norm_sq_add_mul_integral_sub_nonpos h₁ h₂ hu₁ hu₁' hu₂ hu₂' hα hβ hA heq₁ heq₂ hw₁
    hae₁ hw₂ hae₂ h₀ (right_mem_Icc.2 hab)
  -- `∫ₐᵇ ‖u₁ - u₂‖² = 0`, so `u₁ - u₂` vanishes almost everywhere on `(a, b)`.
  have hint : IntegrableOn (fun s ↦ ‖u₁ s - u₂ s‖ ^ 2) (Ioo a b) :=
    (memLp_two_iff_integrable_sq_norm (hu₁.sub hu₂).aestronglyMeasurable).1 (hu₁.sub hu₂)
  have hnn : 0 ≤ ∫ s in a..b, ‖u₁ s - u₂ s‖ ^ 2 :=
    intervalIntegral.integral_nonneg hab fun _ _ ↦ by positivity
  have hzero : ∫ s in Ioo a b, ‖u₁ s - u₂ s‖ ^ 2 = 0 := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab]
    nlinarith [sq_nonneg ‖w₁ b - w₂ b‖]
  filter_upwards [(setIntegral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall fun _ ↦ by positivity) hint).1 hzero] with s hs
  simpa [sub_eq_zero] using hs

end TauCeti
