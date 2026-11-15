/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The scalar Łojasiewicz differential inequality

Let `e ≥ 0` have derivative `-g²` on `[a, b]`, and suppose `c e ^ θ ≤ g` with `c > 0` and
`θ < 1`. Then, with `K = c (1 - θ)`,

`∫_a^b g ≤ (e(a) ^ (1 - θ) - e(b) ^ (1 - θ)) / K`,

and any curve whose speed is at most `g` moves by at most the same amount during `[a, b]`.
This is the scalar core of Łojasiewicz's finite-length argument for gradient trajectories: there
`e` is the excess of the function over a critical value and `g` the norm of its gradient. Nothing
here refers to gradients or to the norm in which `g` is measured; the gradient-flow
specialization lives in `TauCeti.Analysis.Calculus.Morse.Lojasiewicz`.

## The argument

The **Łojasiewicz potential** `Φ(t) = -e(t) ^ (1 - θ) / K` has right derivative
`e ^ (-θ) g² / c`, which is at least `g`: where `e > 0` this is the chain rule together with the
inequality `c e ^ θ ≤ g`, and once `e` vanishes it stays zero, since `e` is antitone and
nonnegative, so that both `Φ` and `g` vanish from then on. A function whose right derivative
dominates `g` grows at least by the integral of `g`, and dominates the displacement of any curve
with speed at most `g`.

## Main results

* `TauCeti.antitoneOn_of_hasDerivWithinAt_neg_sq`: a function with derivative `-g²` is antitone.
* `TauCeti.sq_eq_zero_of_hasDerivWithinAt_neg_sq`: once such a nonnegative function vanishes, it
  stays zero, and `g` vanishes there.
* `TauCeti.integral_le_rpow_sub_rpow_of_lojasiewicz`: the scalar finite-length bound.
* `TauCeti.norm_sub_le_rpow_sub_rpow_of_lojasiewicz`: the scalar displacement bound for a curve
  whose speed is at most `g`.

## References

* S. Łojasiewicz, *Une propriété topologique des sous-ensembles analytiques réels*, Les Équations
  aux Dérivées Partielles, CNRS, Paris, 1963, 87–89.
* E. Lerman, *Gradient flow of the norm squared of a moment map*, Enseign. Math. 51 (2005),
  117–127, arXiv:math/0410568, proof of Theorem 1.1.
-/

public section

open Filter MeasureTheory Set
open scoped Topology

namespace TauCeti

variable {e g : ℝ → ℝ} {a b c θ : ℝ}

/-- A function with derivative `-g²` on `[a, b]` is antitone there. -/
theorem antitoneOn_of_hasDerivWithinAt_neg_sq
    (he : ∀ t ∈ Icc a b, HasDerivWithinAt e (-g t ^ 2) (Icc a b) t) :
    AntitoneOn e (Icc a b) :=
  antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b)
    (fun t ht ↦ (he t ht).continuousWithinAt)
    (fun t ht ↦ (he t (interior_subset ht)).mono interior_subset)
    (fun _ _ ↦ neg_nonpos.mpr (sq_nonneg _))

/-- Where a nonnegative function with derivative `-g²` on `[a, b]` vanishes, before the end of the
interval, so does `g`: the function stays zero from then on. -/
theorem sq_eq_zero_of_hasDerivWithinAt_neg_sq
    (he : ∀ t ∈ Icc a b, HasDerivWithinAt e (-g t ^ 2) (Icc a b) t)
    (he₀ : ∀ t ∈ Icc a b, 0 ≤ e t) {t : ℝ} (ht : t ∈ Ico a b) (hzero : e t = 0) :
    g t ^ 2 = 0 ∧ e =ᶠ[𝓝[≥] t] fun _ ↦ 0 := by
  have hmem : Ico t b ∈ 𝓝[≥] t := Ico_mem_nhdsGE ht.2
  have hsub : Ico t b ⊆ Icc a b := fun u hu ↦ ⟨ht.1.trans hu.1, hu.2.le⟩
  have heq : e =ᶠ[𝓝[≥] t] fun _ ↦ 0 := by
    filter_upwards [hmem] with u hu
    exact le_antisymm (hzero ▸ antitoneOn_of_hasDerivWithinAt_neg_sq he
      (Ico_subset_Icc_self ht) (hsub hu) hu.1) (he₀ u (hsub hu))
  refine ⟨?_, heq⟩
  have hd₁ := (he t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
    (mem_of_superset hmem hsub)
  have hd₂ : HasDerivWithinAt e 0 (Ici t) t :=
    (hasDerivWithinAt_const t (Ici t) (0 : ℝ)).congr_of_eventuallyEq heq hzero
  exact neg_eq_zero.mp ((uniqueDiffWithinAt_Ici t).eq_deriv _ hd₁ hd₂)

/-- The right derivative of the **Łojasiewicz potential** `-e ^ (1 - θ) / (c (1 - θ))`. -/
private theorem hasDerivWithinAt_lojasiewiczPotential (hθ : θ < 1)
    (he : ∀ t ∈ Icc a b, HasDerivWithinAt e (-g t ^ 2) (Icc a b) t)
    (he₀ : ∀ t ∈ Icc a b, 0 ≤ e t) {t : ℝ} (ht : t ∈ Ico a b) :
    HasDerivWithinAt (fun u ↦ -e u ^ (1 - θ) / (c * (1 - θ))) (e t ^ (-θ) * g t ^ 2 / c)
      (Ici t) t := by
  have hp : (1 - θ) ≠ 0 := (sub_pos.mpr hθ).ne'
  rcases (he₀ t (Ico_subset_Icc_self ht)).lt_or_eq with hpos | hzero
  · have hd := (he t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (mem_of_superset (Ico_mem_nhdsGE ht.2) fun u hu ↦ ⟨ht.1.trans hu.1, hu.2.le⟩)
    convert ((hd.rpow_const (p := 1 - θ) (Or.inl hpos.ne')).neg.div_const (c * (1 - θ)))
      using 1
    rw [sub_sub_cancel_left]
    field_simp
  · obtain ⟨hg, heq⟩ := sq_eq_zero_of_hasDerivWithinAt_neg_sq he he₀ ht hzero.symm
    rw [hg, mul_zero, zero_div]
    refine (hasDerivWithinAt_const t (Ici t) (0 : ℝ)).congr_of_eventuallyEq ?_ ?_
    · filter_upwards [heq] with u hu
      simp [hu, Real.zero_rpow hp]
    · simp [← hzero, Real.zero_rpow hp]

/-- The right derivative of the Łojasiewicz potential dominates `g`. -/
private theorem le_lojasiewiczPotential_deriv (hc : 0 < c)
    (he : ∀ t ∈ Icc a b, HasDerivWithinAt e (-g t ^ 2) (Icc a b) t)
    (he₀ : ∀ t ∈ Icc a b, 0 ≤ e t) (hL : ∀ t ∈ Ico a b, c * e t ^ θ ≤ g t) {t : ℝ}
    (ht : t ∈ Ico a b) :
    g t ≤ e t ^ (-θ) * g t ^ 2 / c := by
  rcases (he₀ t (Ico_subset_Icc_self ht)).lt_or_eq with hpos | hzero
  · have hpow : 0 < e t ^ θ := Real.rpow_pos_of_pos hpos θ
    have hg : 0 < g t := (mul_pos hc hpow).trans_le (hL t ht)
    rw [Real.rpow_neg hpos.le, le_div_iff₀ hc, inv_mul_eq_div, le_div_iff₀ hpow]
    nlinarith [mul_le_mul_of_nonneg_left (hL t ht) hg.le]
  · have hg := (sq_eq_zero_of_hasDerivWithinAt_neg_sq he he₀ ht hzero.symm).1
    rw [hg, pow_eq_zero_iff two_ne_zero |>.mp hg]
    simp

/-- The Łojasiewicz potential is continuous on `[a, b]`. -/
private theorem continuousOn_lojasiewiczPotential (hθ : θ < 1)
    (he : ∀ t ∈ Icc a b, HasDerivWithinAt e (-g t ^ 2) (Icc a b) t) :
    ContinuousOn (fun u ↦ -e u ^ (1 - θ) / (c * (1 - θ))) (Icc a b) :=
  ((ContinuousOn.rpow_const (fun t ht ↦ (he t ht).continuousWithinAt)
    fun _ _ ↦ Or.inr (sub_pos.mpr hθ).le).neg).div_const _

/-- **The scalar Łojasiewicz finite-length bound.** Let `e ≥ 0` have derivative `-g²` on
`[a, b]`, and suppose `c e ^ θ ≤ g` with `c > 0` and `θ < 1`. Then
`∫_a^b g ≤ (e(a) ^ (1 - θ) - e(b) ^ (1 - θ)) / (c (1 - θ))`.

For a negative gradient trajectory, `e` is the excess of `f` over a critical value and `g` the norm
of the gradient. No integrability of `g` is assumed: when `g` is not integrable its integral is
`0`, and the right side is nonnegative. -/
theorem integral_le_rpow_sub_rpow_of_lojasiewicz (hab : a ≤ b) (hc : 0 < c) (hθ : θ < 1)
    (he : ∀ t ∈ Icc a b, HasDerivWithinAt e (-g t ^ 2) (Icc a b) t)
    (he₀ : ∀ t ∈ Icc a b, 0 ≤ e t) (hL : ∀ t ∈ Ico a b, c * e t ^ θ ≤ g t) :
    ∫ t in a..b, g t ≤ (e a ^ (1 - θ) - e b ^ (1 - θ)) / (c * (1 - θ)) := by
  by_cases hint : IntegrableOn g (Icc a b)
  · calc ∫ t in a..b, g t
        ≤ -e b ^ (1 - θ) / (c * (1 - θ)) - -e a ^ (1 - θ) / (c * (1 - θ)) :=
          intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hab
            (continuousOn_lojasiewiczPotential hθ he)
            (fun t ht ↦ (hasDerivWithinAt_lojasiewiczPotential hθ he he₀
              (Ioo_subset_Ico_self ht)).mono Ioi_subset_Ici_self) hint
            fun t ht ↦ le_lojasiewiczPotential_deriv hc he he₀ hL (Ioo_subset_Ico_self ht)
      _ = (e a ^ (1 - θ) - e b ^ (1 - θ)) / (c * (1 - θ)) := by ring
  · rw [intervalIntegral.integral_undef fun h ↦ hint
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp h)]
    refine div_nonneg (sub_nonneg.mpr (Real.rpow_le_rpow (he₀ b (right_mem_Icc.mpr hab))
      (antitoneOn_of_hasDerivWithinAt_neg_sq he (left_mem_Icc.mpr hab)
        (right_mem_Icc.mpr hab) hab) (sub_pos.mpr hθ).le))
      (mul_pos hc (sub_pos.mpr hθ)).le

/-- **The scalar Łojasiewicz displacement bound.** Let `e ≥ 0` have derivative `-g²` on `[a, b]`,
and suppose `c e ^ θ ≤ g` with `c > 0` and `θ < 1`. A curve `x` whose velocity has norm at most
`g` moves by at most `(e(a) ^ (1 - θ) - e(b) ^ (1 - θ)) / (c (1 - θ))` during `[a, b]`. -/
theorem norm_sub_le_rpow_sub_rpow_of_lojasiewicz {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {x x' : ℝ → F} (hab : a ≤ b) (hc : 0 < c) (hθ : θ < 1)
    (he : ∀ t ∈ Icc a b, HasDerivWithinAt e (-g t ^ 2) (Icc a b) t)
    (he₀ : ∀ t ∈ Icc a b, 0 ≤ e t) (hL : ∀ t ∈ Ico a b, c * e t ^ θ ≤ g t)
    (hx : ∀ t ∈ Icc a b, HasDerivWithinAt x (x' t) (Icc a b) t)
    (hx' : ∀ t ∈ Ico a b, ‖x' t‖ ≤ g t) :
    ‖x b - x a‖ ≤ (e a ^ (1 - θ) - e b ^ (1 - θ)) / (c * (1 - θ)) := by
  set Φ : ℝ → ℝ := fun u ↦ -e u ^ (1 - θ) / (c * (1 - θ)) with hΦ
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary'
    (f := fun u ↦ x u - x a) (f' := x') (B := fun u ↦ Φ u - Φ a)
    (B' := fun t ↦ e t ^ (-θ) * g t ^ 2 / c)
    (ContinuousOn.sub (fun t ht ↦ (hx t ht).continuousWithinAt) continuousOn_const)
    (fun t ht ↦ ((hx t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (mem_of_superset (Ico_mem_nhdsGE ht.2) fun u hu ↦ ⟨ht.1.trans hu.1, hu.2.le⟩)).sub_const
        (x a))
    (by simp) ((continuousOn_lojasiewiczPotential hθ he).sub continuousOn_const)
    (fun t ht ↦ (hasDerivWithinAt_lojasiewiczPotential hθ he he₀ ht).sub_const (Φ a))
    (fun t ht ↦ (hx' t ht).trans (le_lojasiewiczPotential_deriv hc he he₀ hL ht))
    (right_mem_Icc.mpr hab)
  refine key.trans (le_of_eq ?_)
  simp only [hΦ]
  ring


end TauCeti
