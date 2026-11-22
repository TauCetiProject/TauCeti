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
bounded, nor `u` continuous.

Energy estimates for evolution equations produce such a recurrence with a constant kernel
`K ≥ 0`. For an integrable `φ` with `φ s ≤ c + K ∫ₐˢ φ` at almost every `s ∈ [a, b]`, the bound
takes the closed form `φ t ≤ c exp (K (t - a))` (`TauCeti.le_mul_exp_of_le_add_mul_integral`).
This corollary asks `φ` itself to be integrable. The forward form needs only `K φ` integrable,
which is weaker when `K = 0`.

The sign of the kernel matters: `u ≡ 1/2`, `β ≡ -1` and `α = 1` satisfy the hypothesis on
`[0, 1]`, yet `1/2 > e^{-1}`.

This is the estimate behind uniqueness and the bounds for linear Carathéodory systems.

## References

* E. A. Coddington, N. Levinson, *Theory of Ordinary Differential Equations*, Chapter 1.
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Appendix B.2.
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
  have hderiv : (fun x ↦ deriv (fun x ↦ (α + v x) * exp (-B x)) x)
      ≤ᵐ[volume.restrict (Icc a t)] fun _ ↦ 0 := by
    filter_upwards [ae_restrict_of_ae hβi.ae_hasDerivAt_integral,
      ae_restrict_of_ae hβui.ae_hasDerivAt_integral,
      ae_restrict_of_ae_restrict_of_subset hsub (hβ₀.and h), ae_restrict_mem measurableSet_Icc]
      with x hB hv ⟨hx₀, hxu⟩ hx
    have hx' : x ∈ uIcc a t := by rwa [uIcc_of_le ht.1]
    have hd : HasDerivAt (fun y ↦ (α + v y) * exp (-B y))
        ((0 + β x * u x) * exp (-B x) + (α + v x) * (exp (-B x) * -β x)) x :=
      ((hasDerivAt_const x α).add (hv hx' a left_mem_uIcc)).mul
        (hB hx' a left_mem_uIcc).neg.exp
    rw [hd.deriv]
    nlinarith [mul_nonneg (mul_nonneg hx₀ (exp_pos (-B x)).le)
      (sub_nonneg.2 (show u x ≤ α + v x from hxu))]
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
  -- Reflect `[a, b]` to `[-b, -a]` and apply the forward form to `u ∘ neg` and `β ∘ neg`. One
  -- measure-preserving negation between the restricted measures transports both the
  -- integrability and the almost-everywhere hypotheses.
  have hpre : Neg.neg ⁻¹' Icc a b = Icc (-b) (-a) := by simp [neg_preimage, neg_Icc]
  have hmp : MeasurePreserving Neg.neg (volume.restrict (Icc (-b) (-a)))
      (volume.restrict (Icc a b)) := by
    rw [← hpre]
    exact (Measure.measurePreserving_neg (volume : Measure ℝ)).restrict_preimage
      measurableSet_Icc
  have key := le_mul_exp_integral_of_le_add_integral_mul (u := fun s ↦ u (-s))
    (β := fun s ↦ β (-s)) (α := α) ((hmp.integrable_comp_emb measurableEmbedding_neg).2 hβ)
    (hmp.quasiMeasurePreserving.ae hβ₀) ((hmp.integrable_comp_emb measurableEmbedding_neg).2 hβu)
    ((hmp.quasiMeasurePreserving.ae h).mono fun s hs ↦ by
      simpa [intervalIntegral.integral_comp_neg (fun s ↦ β s * u s)] using hs)
    ⟨neg_le_neg ht.2, neg_le_neg ht.1⟩
    (by simpa [intervalIntegral.integral_comp_neg (fun s ↦ β s * u s)] using hut)
  simpa [intervalIntegral.integral_comp_neg β] using key

/-- **Grönwall's inequality with a constant kernel.** Let `φ` be integrable on `[a, b]` and
`0 ≤ K`, with `φ s ≤ c + K ∫ₐˢ φ` for almost every `s ∈ [a, b]`. Then `φ t ≤ c exp (K (t - a))`
at every `t ∈ [a, b]` where `φ t ≤ c + K ∫ₐᵗ φ` holds; in particular at every `t ∈ [a, b]` if the
hypothesis holds everywhere there, and at almost every `t ∈ [a, b]` in general. -/
theorem le_mul_exp_of_le_add_mul_integral {φ : ℝ → ℝ} {a b c K t : ℝ}
    (hφ : IntegrableOn φ (Icc a b)) (hK : 0 ≤ K)
    (h : ∀ᵐ s ∂volume.restrict (Icc a b), φ s ≤ c + K * ∫ r in a..s, φ r)
    (ht : t ∈ Icc a b) (hφt : φ t ≤ c + K * ∫ s in a..t, φ s) :
    φ t ≤ c * exp (K * (t - a)) := by
  -- Apply the integrable-kernel inequality to the constant kernel `K`, which integrates to
  -- `∫ₐᵗ K = (t - a) K`.
  have hgr := le_mul_exp_integral_of_le_add_integral_mul (integrableOn_const measure_Icc_lt_top.ne)
    (.of_forall fun _ ↦ hK) (hφ.const_mul K)
    (by simpa only [intervalIntegral.integral_const_mul] using h) ht
    (by rwa [intervalIntegral.integral_const_mul])
  rwa [intervalIntegral.integral_const, smul_eq_mul, mul_comm (t - a)] at hgr

end TauCeti
