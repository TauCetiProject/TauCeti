/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Comp

/-!
# The integral Grönwall inequality with an integrable kernel

Let `β ≥ 0` be integrable on `[a, b]` and let `u` satisfy `u s ≤ α + ∫ₐˢ β u` at almost every
`s ∈ [a, b]`, with `β u` integrable there. Then `u t ≤ α exp (∫ₐᵗ β)` at every `t ∈ [a, b]` where
the inequality itself holds (`TauCeti.le_mul_exp_integral_of_le_add_integral_mul`); in particular
at every `t ∈ [a, b]` if it holds everywhere there. The backward form, with `∫ₜᵇ` in place of
`∫ₐᵗ`, is `TauCeti.le_mul_exp_integral_of_le_add_integral_mul_rev`. The kernel need not be
bounded, nor `u` continuous. The constant-kernel case `β ≡ K`, with the closed form
`α exp (K (t - a))`, is `TauCeti.le_mul_exp_of_le_add_mul_integral`.

The sign of the kernel matters: `u ≡ 1/2`, `β ≡ -1` and `α = 1` satisfy the hypothesis on
`[0, 1]`, yet `1/2 > e^{-1}`.

This is the estimate behind uniqueness and the bounds for linear Carathéodory systems.

## References

* E. A. Coddington, N. Levinson, *Theory of Ordinary Differential Equations*, Chapter 1.
-/

public section

open Set MeasureTheory Real

namespace TauCeti

/-- **Grönwall's inequality with an integrable kernel.** Let `β` be integrable and almost
everywhere nonnegative on `[a, b]`, and let `u` be such that `β u` is integrable on `[a, b]`. If
`u s ≤ α + ∫ₐˢ β u` for almost every `s ∈ [a, b]`, then `u t ≤ α exp (∫ₐᵗ β)` at every
`t ∈ [a, b]` where `u t ≤ α + ∫ₐᵗ β u` holds; in particular at every `t ∈ [a, b]` if the hypothesis
holds everywhere there. -/
theorem le_mul_exp_integral_of_le_add_integral_mul {u β : ℝ → ℝ} {a b α t : ℝ}
    (hβ : IntegrableOn β (Icc a b)) (hβ₀ : ∀ᵐ s ∂volume.restrict (Icc a b), 0 ≤ β s)
    (hβu : IntegrableOn (fun s ↦ β s * u s) (Icc a b))
    (h : ∀ᵐ s ∂volume.restrict (Icc a b), u s ≤ α + ∫ r in a..s, β r * u r)
    (ht : t ∈ Icc a b) (hut : u t ≤ α + ∫ s in a..t, β s * u s) :
    u t ≤ α * exp (∫ s in a..t, β s) := by
  -- Integrating factor: with `v t = ∫ₐᵗ β u` and `B t = ∫ₐᵗ β`, the product `(α + v) e^{-B}` is
  -- absolutely continuous on `[a, t]` with derivative `β e^{-B} (u - α - v) ≤ 0` almost
  -- everywhere, so it is at most its value `α` at `a`.
  set B : ℝ → ℝ := fun x ↦ ∫ s in a..x, β s
  set v : ℝ → ℝ := fun x ↦ ∫ s in a..x, β s * u s
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
  have hβi : IntervalIntegrable β volume a t :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ht.1).2 (hβ.mono_set hsub)
  have hβui : IntervalIntegrable (fun s ↦ β s * u s) volume a t :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ht.1).2 (hβu.mono_set hsub)
  have hBAC : AbsolutelyContinuousOnInterval B a t :=
    hβi.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hvAC : AbsolutelyContinuousOnInterval v a t :=
    hβui.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hEAC : AbsolutelyContinuousOnInterval (fun x ↦ exp (-B x)) a t :=
    hBAC.neg.comp_of_contDiffAt (φ := exp) fun _ _ ↦ contDiff_exp.contDiffAt
  have hgAC : AbsolutelyContinuousOnInterval (fun x ↦ (α + v x) * exp (-B x)) a t :=
    ((LipschitzWith.const α).lipschitzOnWith.absolutelyContinuousOnInterval.add hvAC).fun_mul
      hEAC
  -- Its derivative `β e^{-B} (u - α - v)` is almost everywhere nonpositive on `[a, t]`.
  have hβ₀' : ∀ᵐ x, x ∈ Icc a b → 0 ≤ β x := (ae_restrict_iff' measurableSet_Icc).1 hβ₀
  have h' : ∀ᵐ x, x ∈ Icc a b → u x ≤ α + v x := (ae_restrict_iff' measurableSet_Icc).1 h
  have hderiv : (fun x ↦ deriv (fun x ↦ (α + v x) * exp (-B x)) x)
      ≤ᵐ[volume.restrict (Icc a t)] fun _ ↦ 0 := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hβi.ae_hasDerivAt_integral, hβui.ae_hasDerivAt_integral, hβ₀', h']
      with x hB hv hx₀ hxu hx
    have hx' : x ∈ uIcc a t := by rwa [uIcc_of_le ht.1]
    have hd : HasDerivAt (fun y ↦ (α + v y) * exp (-B y))
        ((0 + β x * u x) * exp (-B x) + (α + v x) * (exp (-B x) * -β x)) x :=
      ((hasDerivAt_const x α).add (hv hx' a left_mem_uIcc)).mul
        (hB hx' a left_mem_uIcc).neg.exp
    rw [hd.deriv]
    nlinarith [mul_nonneg (mul_nonneg (hx₀ (hsub hx)) (exp_pos (-B x)).le)
      (sub_nonneg.2 (hxu (hsub hx)))]
  have hle := intervalIntegral.integral_mono_ae_restrict ht.1 hgAC.intervalIntegrable_deriv
    intervalIntegrable_const hderiv
  rw [hgAC.integral_deriv_eq_sub, intervalIntegral.integral_const, smul_zero] at hle
  simp only [B, v, intervalIntegral.integral_same, neg_zero, exp_zero, add_zero, mul_one,
    sub_nonpos] at hle hut ⊢
  rw [exp_neg, ← div_eq_mul_inv, div_le_iff₀ (exp_pos _)] at hle
  linarith

/-- **Grönwall's inequality with an integrable kernel, backward form.** Let `β` be integrable and
almost everywhere nonnegative on `[a, b]`, and let `u` be such that `β u` is integrable on
`[a, b]`. If `u s ≤ α + ∫ₛᵇ β u` for almost every `s ∈ [a, b]`, then `u t ≤ α exp (∫ₜᵇ β)` at
every `t ∈ [a, b]` where `u t ≤ α + ∫ₜᵇ β u` holds; in particular at every `t ∈ [a, b]` if the
hypothesis holds everywhere there. -/
theorem le_mul_exp_integral_of_le_add_integral_mul_rev {u β : ℝ → ℝ} {a b α t : ℝ}
    (hβ : IntegrableOn β (Icc a b)) (hβ₀ : ∀ᵐ s ∂volume.restrict (Icc a b), 0 ≤ β s)
    (hβu : IntegrableOn (fun s ↦ β s * u s) (Icc a b))
    (h : ∀ᵐ s ∂volume.restrict (Icc a b), u s ≤ α + ∫ r in s..b, β r * u r)
    (ht : t ∈ Icc a b) (hut : u t ≤ α + ∫ s in t..b, β s * u s) :
    u t ≤ α * exp (∫ s in t..b, β s) := by
  -- Reflect `[a, b]` to `[-b, -a]` and apply the forward form to `u ∘ neg` and `β ∘ neg`.
  have hmp := Measure.measurePreserving_neg (volume : Measure ℝ)
  have hpre : Neg.neg ⁻¹' Icc a b = Icc (-b) (-a) := by simp [neg_preimage, neg_Icc]
  have hneg {f : ℝ → ℝ} (hf : IntegrableOn f (Icc a b)) :
      IntegrableOn (fun s ↦ f (-s)) (Icc (-b) (-a)) := by
    rw [← hpre]
    exact (hmp.integrableOn_comp_preimage (measurableEmbedding_neg)).2 hf
  have hae {p : ℝ → Prop} (hp : ∀ᵐ s ∂volume.restrict (Icc a b), p s) :
      ∀ᵐ s ∂volume.restrict (Icc (-b) (-a)), p (-s) := by
    rw [ae_restrict_iff' measurableSet_Icc] at hp ⊢
    filter_upwards [hmp.quasiMeasurePreserving.ae hp] with s hs hs'
    exact hs ⟨le_neg.1 hs'.2, neg_le.1 hs'.1⟩
  have key := le_mul_exp_integral_of_le_add_integral_mul (u := fun s ↦ u (-s))
    (β := fun s ↦ β (-s)) (α := α) (hneg hβ) (hae hβ₀) (hneg hβu)
    ((hae h).mono fun s hs ↦ by
      simpa [intervalIntegral.integral_comp_neg (fun s ↦ β s * u s)] using hs)
    ⟨neg_le_neg ht.2, neg_le_neg ht.1⟩
    (by simpa [intervalIntegral.integral_comp_neg (fun s ↦ β s * u s)] using hut)
  simpa [intervalIntegral.integral_comp_neg β] using key

end TauCeti
