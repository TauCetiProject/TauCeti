/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Restriction
public import TauCeti.Analysis.PDE.Parabolic.Holder.Schauder
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Topology.EMetricSpace.Lipschitz
import TauCeti.Topology.MetricSpace.Holder

/-!
# The weighted interior estimate for parabolic operators with Hölder coefficients

On `ℝⁿ = EuclideanSpace ℝ ι` and the slab `ℝⁿ × [0, T]`, let

`P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u`

have coefficients in the bounded parabolic Hölder space `C_b^{α,α/2}`, `0 < α < 1`, with `a`
uniformly elliptic. The global Schauder estimate
(`TauCeti.ParabolicC2HolderSpace.exists_norm_le_euclideanParabolicOperatorL`) bounds the order-two
norm `‖u‖_{2+α,par}` by `‖P u‖_{α,par}` and the `C_b^{2,α}` norm of the initial slice. This file
proves that away from the initial time the supremum of the initial slice suffices, at the price
of a weight: there is a constant `C`, depending only on `n`, `α`, the ellipticity constants, a
bound on the Hölder norms of the coefficients and a bound on the horizon `T`, such that

`δ^(1 + α/2) ‖u‖_{2+α,par; [δ, T]} ≤ C (sup |u(·, 0)| + ‖P u‖_{α,par})`

for every `u ∈ C_b^{2+α,1+α/2}` and every `0 < δ < T`
(`TauCeti.ParabolicC2HolderSpace.exists_rpow_mul_norm_restrictL_le`). The weight `δ^(1 + α/2)`
matches the parabolic order of the space: for merely bounded initial data, the parabolic Hölder
seminorm of the spatial Hessian on `[δ, T]` is of order `δ^(-1 - α/2)`. This estimate, uniform over
the closed-slab solutions, is what passes to limits of solutions with smooth data when the initial
data are only bounded and uniformly continuous.

## The argument

Let `χ(t) = ψ(2 t / δ - 1)` with `ψ` Mathlib's smooth transition, so that `χ` vanishes for
`t ≤ δ/2` and equals one for `t ≥ δ`, with `|χ'| ≤ A/δ` and `[χ']_{α,par} ≤ B δ^(-1 - α/2)`. The
map `χ u` has vanishing initial slice and agrees with `u` on `[δ, T]`, and `P (χ u) = χ P u + χ' u`
because `χ` has no spatial derivatives
(`TauCeti.ParabolicC2HolderSpace.parabolicOperatorL_mul_of_spatialFDerivL_eq_zero`). The
Schauder estimate applied to `χ u` bounds `‖u‖_{2+α,par; [δ, T]}` by the `C_b^{α,α/2}` norm of
`χ P u + χ' u`. Since `χ'` vanishes up to time `δ/4`, the norm of `χ' u` is controlled on
`[δ/4, T]` (`TauCeti.HolderSpace.norm_le_norm_compLipschitzL_inclusion_of_eq_zero`), where the
scale-invariant interpolation inequality at the time step `τ δ`
(`TauCeti.ParabolicC2HolderSpace.norm_valueHolderL_le_add_mul`) bounds the parabolic Hölder norm
of `u` by a multiple of `(τ δ)^(-α/2) sup |u|` plus `2 τ δ ‖u‖_{2+α,par; [δ/4, T]}`. After
multiplication by `δ^(1 + α/2)`, the last term is a multiple of `τ` times the weighted norm at
`δ/4`; for `τ` small it is absorbed into the supremum over `δ` of the weighted norms, which is
finite because `u` lies in the closed-slab space. Finally the comparison principle bounds
`sup |u|` by `sup |u(·, 0)|` and `‖P u‖`.

## Main declarations

* `TauCeti.ParabolicC2HolderSpace.exists_rpow_mul_norm_restrictL_le`: the weighted interior
  estimate.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 4
  (the Cauchy problem with bounded uniformly continuous initial data).
-/

public section
noncomputable section

namespace TauCeti

open Set ParabolicSpaceTime
open scoped NNReal ENNReal BoundedContinuousFunction

namespace ParabolicC2HolderSpace

/-! ### The weighted interior estimate -/

section Weighted

variable {α : ℝ≥0}

/-- **The time cutoff.** For `δ > 0` there is a map `χ` of time alone, vanishing together with its
time derivative up to time `δ/4` and equal to one from time `δ` on, with `0 ≤ χ ≤ 1`,
`|χ'| ≤ A / δ` and `δ^(1 + α/2) [χ']_{α,par} ≤ B` for constants `A`, `B` independent of `δ`. It is
`t ↦ ψ(2 t / δ - 1)` for Mathlib's smooth transition `ψ`. -/
private theorem exists_timeCutoff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hα : α ≤ 1) :
    ∃ A B : ℝ≥0, ∀ {T : ℝ} (hT : 0 < T) {δ : ℝ}, 0 < δ →
      ∃ χ : ParabolicC2HolderSpace α E ℝ hT,
        spatialFDerivL χ = 0 ∧
        (∀ p : slab (E := E) 0 T, (p : ParabolicSpaceTime E).time ≤ δ / 4 →
          χ p = 0 ∧ timeDerivL χ p = 0) ∧
        (∀ p : slab (E := E) 0 T, δ ≤ (p : ParabolicSpaceTime E).time → χ p = 1) ∧
        ‖χ‖ ≤ 1 + A / δ + nnHolderNorm α (timeDerivL χ : slab (E := E) 0 T → ℝ) ∧
        (∀ p, ‖timeDerivL χ p‖ ≤ A / δ) ∧
        δ ^ (1 + (α : ℝ) / 2) * nnHolderNorm α (timeDerivL χ : slab (E := E) 0 T → ℝ) ≤ B := by
  obtain ⟨L₁, hL₁⟩ := Real.smoothTransition.exists_forall_norm_deriv_le
  obtain ⟨L₂, hL₂⟩ := Real.smoothTransition.exists_forall_norm_deriv_deriv_le
  have hL₁₀ : 0 ≤ L₁ := (norm_nonneg _).trans (hL₁ 0)
  have hL₂₀ : 0 ≤ L₂ := (norm_nonneg _).trans (hL₂ 0)
  lift L₁ to ℝ≥0 using hL₁₀
  lift L₂ to ℝ≥0 using hL₂₀
  refine ⟨2 * L₁, 4 * L₂ + 4 * L₁, fun {T} hT {δ} hδ ↦ ?_⟩
  set φ : ℝ → ℝ := fun t ↦ Real.smoothTransition (2 * t / δ - 1)
  have hφ : ContDiff ℝ 1 φ := Real.smoothTransition.contDiff.comp (by fun_prop)
  have hφ' (t : ℝ) : deriv φ t = deriv Real.smoothTransition (2 * t / δ - 1) * (2 / δ) := by
    have h := HasDerivAt.smoothTransition
      ((((hasDerivAt_id t).const_mul 2).div_const δ).sub_const 1)
    rw [mul_one] at h
    exact h.deriv
  -- `φ'` is bounded by `2 L₁ / δ` and Lipschitz with constant `4 L₂ / δ²`.
  have hbd (t : ℝ) : ‖deriv φ t‖ ≤ 2 * L₁ / δ := by
    rw [hφ', norm_mul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2 / δ)]
    calc _ ≤ (L₁ : ℝ) * (2 / δ) := by gcongr; exact hL₁ _
      _ = _ := by ring
  have hlip : LipschitzWith L₂ (deriv Real.smoothTransition) :=
    lipschitzWith_of_nnNorm_deriv_le
      (Real.smoothTransition.contDiff (n := 2)).differentiable_deriv_two fun x ↦ by
        rw [← NNReal.coe_le_coe, coe_nnNorm]
        exact hL₂ x
  -- Interpolating between the two bounds at the scale `δ` gives the `(α/2)`-Hölder bound.
  obtain ⟨δ', hδ'⟩ : ∃ δ' : ℝ≥0, (δ' : ℝ) = δ := ⟨⟨δ, hδ.le⟩, rfl⟩
  have hH : HolderWith (4 * L₂ / δ' ^ 2 * δ' ^ ((1 : ℝ≥0) - (α / 2 : ℝ≥0) : ℝ) +
      4 * L₁ / δ' * δ' ^ (-((α / 2 : ℝ≥0) : ℝ))) (α / 2) (deriv φ) := by
    refine holderOnWith_univ.1 (HolderOnWith.of_le_of_dist_le (fun t _ s _ _ ↦ ?_)
      (fun t _ s _ ↦ ?_) ?_ (NNReal.coe_pos.1 (hδ'.symm ▸ hδ)))
    · rw [NNReal.coe_one, Real.rpow_one, dist_eq_norm, hφ', hφ', ← sub_mul, norm_mul,
        Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2 / δ)]
      have h := hlip.dist_le_mul (2 * t / δ - 1) (2 * s / δ - 1)
      rw [dist_eq_norm, Real.dist_eq] at h
      have hts : |2 * t / δ - 1 - (2 * s / δ - 1)| = 2 / δ * |t - s| := by
        rw [show 2 * t / δ - 1 - (2 * s / δ - 1) = 2 / δ * (t - s) by ring, abs_mul,
          abs_of_pos (by positivity : (0 : ℝ) < 2 / δ)]
      rw [hts] at h
      push_cast
      rw [hδ', Real.dist_eq]
      calc _ ≤ ↑L₂ * (2 / δ * |t - s|) * (2 / δ) := mul_le_mul_of_nonneg_right h (by positivity)
        _ = _ := by field_simp; ring
    · rw [dist_eq_norm]
      push_cast
      rw [hδ']
      calc _ ≤ ‖deriv φ t‖ + ‖deriv φ s‖ := norm_sub_le _ _
        _ ≤ 2 * L₁ / δ + 2 * L₁ / δ := add_le_add (hbd t) (hbd s)
        _ = _ := by ring
    · exact (NNReal.half_le_self α).trans hα
  refine ⟨ofTime φ hφ hH, spatialFDerivL_ofTime _ _ _, fun p hp ↦ ?_, fun p hp ↦ ?_, ?_,
    fun p ↦ ?_, ?_⟩
  · have h : 2 * (p : ParabolicSpaceTime E).time / δ - 1 < 0 := by
      rw [sub_neg, div_lt_one hδ]
      linarith
    rw [ofTime_apply, timeDerivL_ofTime_apply, hφ']
    exact ⟨Real.smoothTransition.zero_of_nonpos h.le,
      by rw [Real.smoothTransition.deriv_of_neg h, zero_mul]⟩
  · rw [ofTime_apply]
    exact Real.smoothTransition.one_of_one_le (by rw [le_sub_iff_add_le, le_div_iff₀ hδ]; linarith)
  · have hv : ‖valueL (ofTime (E := E) (hab := hT) φ hφ hH)‖ ≤ 1 := by
      refine (BoundedContinuousFunction.norm_le zero_le_one).2 fun p ↦ ?_
      rw [valueL_apply, ofTime_apply, Real.norm_of_nonneg (Real.smoothTransition.nonneg _)]
      exact Real.smoothTransition.le_one _
    have ht : ‖(timeDerivL (ofTime (E := E) (hab := hT) φ hφ hH)).toBoundedContinuousFunction‖ ≤
        (2 * L₁ : ℝ≥0) / δ :=
      (BoundedContinuousFunction.norm_le (by positivity)).2 fun p ↦ by
        rw [HolderSpace.toBoundedContinuousFunction_apply, timeDerivL_ofTime_apply]
        exact (hbd _).trans (by push_cast; rfl)
    have h₃ := HolderSpace.norm_def (timeDerivL (ofTime (E := E) (hab := hT) φ hφ hH))
    rw [HolderSpace.coe_toBoundedContinuousFunction] at h₃
    have hz₁ : ‖spatialFDerivL (ofTime (E := E) (hab := hT) φ hφ hH)‖ = 0 := by
      rw [spatialFDerivL_ofTime]
      exact norm_zero (E := slab (E := E) 0 T →ᵇ (E →L[ℝ] ℝ))
    have hz₂ : ‖spatialSecondFDerivL (ofTime (E := E) (hab := hT) φ hφ hH)‖ = 0 := by
      rw [spatialSecondFDerivL_ofTime]
      exact norm_zero
    rw [norm_eq, hz₁, hz₂]
    linarith
  · rw [timeDerivL_ofTime_apply]
    exact (hbd _).trans (by push_cast; rfl)
  · have hfun : (timeDerivL (ofTime (E := E) (hab := hT) φ hφ hH) : slab (E := E) 0 T → ℝ) =
        fun p : slab (E := E) 0 T ↦ deriv φ (p : ParabolicSpaceTime E).time :=
      funext fun p ↦ timeDerivL_ofTime_apply φ hφ hH p
    rw [hfun]
    have hle := NNReal.coe_le_coe.2
      (holderWith_comp_time (E := E) (a := 0) (b := T) hH).nnholderNorm_le
    refine (mul_le_mul_of_nonneg_left hle (by positivity)).trans (le_of_eq ?_)
    push_cast
    rw [hδ', mul_add, ← mul_assoc, ← mul_assoc, mul_comm (δ ^ _) (4 * (L₂ : ℝ) / δ ^ 2),
      mul_comm (δ ^ _) (4 * (L₁ : ℝ) / δ), mul_assoc, mul_assoc, ← Real.rpow_add hδ,
      ← Real.rpow_add hδ]
    have e₁ : (1 + (α : ℝ) / 2) + (1 - (α : ℝ) / 2) = (2 : ℕ) := by push_cast; ring
    have e₂ : (1 + (α : ℝ) / 2) + -((α : ℝ) / 2) = 1 := by ring
    rw [e₁, e₂, Real.rpow_natCast, Real.rpow_one]
    field_simp

/-- **The term `χ' u` only sees `u` after time `s`.** If the time derivative of `χ` vanishes up to
time `s` and is bounded by `A`, then the `C_b^{α,α/2}` norm of `χ' u` on `E × [a, b]` is at most
`A ‖u‖_{α,par; [s, b]} + [χ']_{α,par} sup |u|`. -/
private theorem norm_mul_timeDerivL_valueHolderL_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a b s : ℝ} {hab : a < b} (has : a ≤ s) (hsb : s < b) (hα : α ≤ 1)
    (χ u : ParabolicC2HolderSpace α E ℝ hab) {A : ℝ≥0}
    (hχ₀ : ∀ p : slab (E := E) a b, (p : ParabolicSpaceTime E).time ≤ s → timeDerivL χ p = 0)
    (hχA : ∀ p, ‖timeDerivL χ p‖ ≤ A) :
    ‖(ContinuousLinearMap.mul ℝ ℝ).compHolder₂ (timeDerivL χ) (valueHolderL hα u)‖ ≤
      A * ‖valueHolderL hα (restrictL has le_rfl hsb u)‖ +
        nnHolderNorm α (timeDerivL χ : slab (E := E) a b → ℝ) * ‖valueL u‖ := by
  have hincl := LipschitzWith.inclusion (slab_subset_slab (E := E) has (le_refl b))
  refine (HolderSpace.norm_le_norm_compLipschitzL_inclusion_of_eq_zero has _
    fun p hp ↦ ?_).trans ?_
  · simp [hχ₀ p hp]
  -- On `[s, b]` the product is the product of the restrictions.
  have hR : HolderSpace.compLipschitzL _ hincl
      ((ContinuousLinearMap.mul ℝ ℝ).compHolder₂ (timeDerivL χ) (valueHolderL hα u)) =
      (ContinuousLinearMap.mul ℝ ℝ).compHolder₂ (HolderSpace.compLipschitzL _ hincl (timeDerivL χ))
        (valueHolderL hα (restrictL has le_rfl hsb u)) := by
    ext p
    simp
  rw [hR]
  refine ((ContinuousLinearMap.mul ℝ ℝ).norm_compHolder₂_apply_le_of_eq_zero _ _ (s := univ)
    (δ := A) (fun p _ ↦ ?_) fun p hp ↦ absurd (mem_univ p) hp).trans ?_
  · simpa using hχA _
  -- Restriction does not increase the Hölder seminorm of `χ'` or the supremum of `u`.
  have hsemi : (nnHolderNorm α (HolderSpace.compLipschitzL _ hincl (timeDerivL χ) :
      slab (E := E) s b → ℝ) : ℝ) ≤ nnHolderNorm α (timeDerivL χ : slab (E := E) a b → ℝ) := by
    have h := HolderSpace.nnHolderNorm_comp_le hincl (timeDerivL χ)
    rw [NNReal.one_rpow, mul_one] at h
    have hc : (HolderSpace.compLipschitzL _ hincl (timeDerivL χ) : slab (E := E) s b → ℝ) =
        (timeDerivL χ : slab (E := E) a b → ℝ) ∘ Set.inclusion _ :=
      funext fun p ↦ HolderSpace.compLipschitzL_apply hincl _ p
    rw [hc]
    exact_mod_cast h
  have hsup : ‖(valueHolderL hα (restrictL has le_rfl hsb u)).toBoundedContinuousFunction‖ ≤
      ‖valueL u‖ := by
    rw [toBoundedContinuousFunction_valueHolderL]
    exact norm_valueL_restrictL_le u
  have hmul : ‖ContinuousLinearMap.mul ℝ ℝ‖ ≤ 1 := ContinuousLinearMap.opNorm_mul_le ℝ ℝ
  have hin : 0 ≤ (A : ℝ) * ‖valueHolderL hα (restrictL has le_rfl hsb u)‖ +
      nnHolderNorm α (HolderSpace.compLipschitzL _ hincl (timeDerivL χ) :
        slab (E := E) s b → ℝ) *
        ‖(valueHolderL hα (restrictL has le_rfl hsb u)).toBoundedContinuousFunction‖ := by
    positivity
  refine (mul_le_of_le_one_left hin hmul).trans (add_le_add le_rfl ?_)
  exact mul_le_mul hsemi hsup (norm_nonneg _) (NNReal.coe_nonneg _)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The localized Schauder estimate at one time `δ`.** Let `χ` have vanishing spatial gradient,
vanish with its time derivative up to time `δ/4` and equal one from time `δ` on, with `|χ'| ≤ A`.
If the Schauder estimate `‖χ u‖ ≤ C (‖P (χ u)‖ + ‖(χ u)(·, 0)‖)` holds, then the order-two norm
of `u` on `[δ, T]` is at most
`C (‖χ‖_{α,par} ‖P u‖ + A ‖u‖_{α,par; [δ/4, T]} + [χ']_{α,par} sup |u|)`. -/
private theorem norm_restrictL_le_of_timeCutoff (hα : α ≤ 1) {T δ : ℝ} {hT : 0 < T}
    (hδ : 0 < δ) (hδT : δ < T) (h₄ : 0 ≤ δ / 4) (h₄T : δ / 4 < T)
    (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (χ u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT) (hχx : spatialFDerivL χ = 0)
    (hχ₀ : ∀ p : slab (E := EuclideanSpace ℝ ι) 0 T,
      (p : ParabolicSpaceTime (EuclideanSpace ℝ ι)).time ≤ δ / 4 →
        χ p = 0 ∧ timeDerivL χ p = 0)
    (hχ₁ : ∀ p : slab (E := EuclideanSpace ℝ ι) 0 T,
      δ ≤ (p : ParabolicSpaceTime (EuclideanSpace ℝ ι)).time → χ p = 1)
    {A : ℝ≥0} (hχA : ∀ p, ‖timeDerivL χ p‖ ≤ A) {C : ℝ} (hC₀ : 0 ≤ C)
    (hC : ‖(ContinuousLinearMap.mul ℝ ℝ).compParabolicC2Holder₂ hα χ u‖ ≤
      C * (‖euclideanParabolicOperatorL hα a b c
          ((ContinuousLinearMap.mul ℝ ℝ).compParabolicC2Holder₂ hα χ u)‖ +
        ‖((ContinuousLinearMap.mul ℝ ℝ).compParabolicC2Holder₂ hα χ u).spatialTrace
          ⟨0, left_mem_Icc.2 hT.le⟩‖)) :
    ‖restrictL hδ.le le_rfl hδT u‖ ≤
      C * (‖valueHolderL hα χ‖ * ‖euclideanParabolicOperatorL hα a b c u‖ +
        (A * ‖valueHolderL hα (restrictL h₄ le_rfl h₄T u)‖ +
          nnHolderNorm α (timeDerivL χ : slab (E := EuclideanSpace ℝ ι) 0 T → ℝ) *
            ‖valueL u‖)) := by
  set w := (ContinuousLinearMap.mul ℝ ℝ).compParabolicC2Holder₂ hα χ u
  -- `χ u` agrees with `u` from time `δ` on, and vanishes at the initial time.
  have hrw : restrictL hδ.le le_rfl hδT u = restrictL hδ.le le_rfl hδT w := by
    ext p
    rw [restrictL_apply, restrictL_apply, ContinuousLinearMap.compParabolicC2Holder₂_apply,
      hχ₁ _ (by simpa using (mem_slab.1 p.2).1), ContinuousLinearMap.mul_apply', one_mul]
  have htr : w.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩ = 0 := by
    refine CkHolderSpace.ext fun x ↦ ?_
    rw [spatialTrace_apply, ContinuousLinearMap.compParabolicC2Holder₂_apply,
      (hχ₀ _ (by rw [time_slabMk]; positivity)).1, ContinuousLinearMap.mul_apply', zero_mul]
    simp
  rw [htr, norm_zero, add_zero, euclideanParabolicOperatorL_def,
    parabolicOperatorL_mul_of_spatialFDerivL_eq_zero hα _ _ _ χ u hχx,
    ← euclideanParabolicOperatorL_def] at hC
  have hmul : ‖ContinuousLinearMap.mul ℝ ℝ‖ ≤ 1 := ContinuousLinearMap.opNorm_mul_le ℝ ℝ
  have h₁ : ‖(ContinuousLinearMap.mul ℝ ℝ).compHolder₂ (valueHolderL hα χ)
      (euclideanParabolicOperatorL hα a b c u)‖ ≤
      ‖valueHolderL hα χ‖ * ‖euclideanParabolicOperatorL hα a b c u‖ :=
    (ContinuousLinearMap.norm_compHolder₂_apply_le _ _ _).trans (by
      rw [mul_assoc]
      exact mul_le_of_le_one_left (by positivity) hmul)
  have h₂ := norm_mul_timeDerivL_valueHolderL_le h₄ h₄T hα χ u (fun p hp ↦ (hχ₀ p hp).2) hχA
  rw [hrw]
  refine (norm_restrictL_apply_le w).trans ?_
  exact hC.trans (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add h₁ h₂)) hC₀)

/-- Powers `d^(α/2)` with `0 < d ≤ T₀` and `α ≤ 1` are at most `max 1 T₀`. -/
private theorem rpow_half_le_max {d T₀ : ℝ} (hd : 0 < d) (hdT : d ≤ T₀) (hα : α ≤ 1) :
    d ^ ((α : ℝ) / 2) ≤ max 1 T₀ := by
  have hα₂ : (α : ℝ) / 2 ≤ 1 := by
    have : (α : ℝ) ≤ 1 := by exact_mod_cast hα
    linarith
  rcases le_or_gt d 1 with h | h
  · exact (Real.rpow_le_one hd.le h (by positivity)).trans (le_max_left _ _)
  · calc d ^ ((α : ℝ) / 2) ≤ d ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h.le hα₂
      _ = d := Real.rpow_one d
      _ ≤ max 1 T₀ := hdT.trans (le_max_right _ _)

/-- The arithmetic of one absorption step: the three contributions of the localized Schauder
estimate, multiplied by the weight `D = d^(1 + α/2) = d e`, are bounded using `D ≤ T₀ m`,
`e ≤ m`, `D ≤ 16 D₄`, `r e = q` and `D H ≤ B`, and the multiple `CS · 32 A τ ≤ 1/2` of the
weighted norm `D₄ N₄` at `d/4` is kept separate. -/
private theorem weighted_step_arith {N N₄ D D₄ e q r Pu V V₄ vχ I H A B CS τ d T₀ m : ℝ}
    (hloc : N ≤ CS * (vχ * Pu + (A / d * I + H * V)))
    (hI : I ≤ (1 + 40 * r) * V₄ + 2 * (τ * d) * N₄) (hV₄ : V₄ ≤ V)
    (hχn : vχ ≤ 24 * (1 + A / d + H)) (hD : D = d * e) (hqe : r * e = q) (h16 : D ≤ 16 * D₄)
    (he : e ≤ m) (hdT₀ : d ≤ T₀) (hχB : D * H ≤ B) (hτabs : CS * (32 * A * τ) ≤ 1 / 2)
    (hd : 0 < d) (he₀ : 0 ≤ e) (hCS : 0 ≤ CS) (hA : 0 ≤ A) (hτ : 0 < τ) (hr : 0 ≤ r)
    (hPu : 0 ≤ Pu) (hV₄₀ : 0 ≤ V₄) (hV : 0 ≤ V) (hN₄ : 0 ≤ N₄) (hD₄ : 0 ≤ D₄)
    (hH : 0 ≤ H) :
    D * N ≤ 1 / 2 * (D₄ * N₄) +
      CS * (24 * (T₀ * m + A * m + B) + (A * (m + 40 * q) + B)) * (Pu + V) := by
  have hD₀ : 0 ≤ D := by rw [hD]; positivity
  have hm₀ : 0 ≤ m := he₀.trans he
  have hAe : D * (A / d) = A * e := by rw [hD]; field_simp
  have hDT : D ≤ T₀ * m := by
    rw [hD]
    exact mul_le_mul hdT₀ he he₀ (hd.le.trans hdT₀)
  have hB : 0 ≤ B := (mul_nonneg hD₀ hH).trans hχB
  -- The contribution of `χ P u`.
  have t₁ : D * (vχ * Pu) ≤ 24 * (T₀ * m + A * m + B) * Pu := by
    have h : D * vχ ≤ 24 * (T₀ * m + A * m + B) := by
      calc D * vχ ≤ D * (24 * (1 + A / d + H)) := mul_le_mul_of_nonneg_left hχn hD₀
        _ = 24 * (D + D * (A / d) + D * H) := by ring
        _ ≤ 24 * (T₀ * m + A * m + B) := by
          rw [hAe]
          gcongr
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right h hPu
  -- The contribution of `χ' u`, after interpolation on `[d/4, T]`.
  have t₂ : D * (A / d * I) ≤ A * (m + 40 * q) * V + 32 * A * τ * (D₄ * N₄) := by
    calc D * (A / d * I) = A * e * I := by rw [← hAe]; ring
      _ ≤ A * e * ((1 + 40 * r) * V₄ + 2 * (τ * d) * N₄) := by gcongr
      _ = A * (e + 40 * (r * e)) * V₄ + 2 * A * τ * (D * N₄) := by rw [hD]; ring
      _ ≤ A * (m + 40 * q) * V + 2 * A * τ * (16 * D₄ * N₄) := by
          rw [hqe]
          have : 0 ≤ q := hqe ▸ mul_nonneg hr he₀
          gcongr
      _ = _ := by ring
  -- The contribution of the Hölder seminorm of `χ'`.
  have t₃ : D * (H * V) ≤ B * V := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hχB hV
  have hq₀ : 0 ≤ q := hqe ▸ mul_nonneg hr he₀
  have hT₀ : 0 ≤ T₀ := hd.le.trans hdT₀
  have hc₁ : 0 ≤ 24 * (T₀ * m + A * m + B) := by
    have := mul_nonneg hT₀ hm₀
    have := mul_nonneg hA hm₀
    linarith
  have hc₂ : 0 ≤ A * (m + 40 * q) + B := by
    have := mul_nonneg hA (by linarith : 0 ≤ m + 40 * q)
    linarith
  calc D * N ≤ D * (CS * (vχ * Pu + (A / d * I + H * V))) := mul_le_mul_of_nonneg_left hloc hD₀
    _ = CS * (D * (vχ * Pu) + D * (A / d * I) + D * (H * V)) := by ring
    _ ≤ CS * (24 * (T₀ * m + A * m + B) * Pu + (A * (m + 40 * q) * V +
          32 * A * τ * (D₄ * N₄)) + B * V) := by
        gcongr
    _ ≤ _ := by
        nlinarith [mul_le_mul_of_nonneg_right hτabs (mul_nonneg hD₄ hN₄),
          mul_nonneg (mul_nonneg hCS hc₁) hV, mul_nonneg (mul_nonneg hCS hc₂) hPu]

/-- **One absorption step.** With the time cutoff of `exists_timeCutoff` at scale `d`, the
Schauder estimate and the interpolation inequality at the time step `τ d` bound the weighted norm
`d^(1 + α/2) ‖u‖_{2+α,par; [d, T]}` by half the weighted norm at `d/4` plus a multiple of
`‖P u‖ + sup |u|`, provided `CS · 32 A τ ≤ 1/2`. -/
private theorem weighted_step (hα₁ : α < 1) {T d T₀ : ℝ} {hT : 0 < T} (hd : 0 < d)
    (hdT : d < T) (h₄ : 0 ≤ d / 4) (h₄T : d / 4 < T)
    (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT) {CS : ℝ} (hCS : 0 ≤ CS)
    (hS : ∀ w : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT,
      ‖w‖ ≤ CS * (‖euclideanParabolicOperatorL hα₁.le a b c w‖ +
        ‖w.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩‖))
    {A B : ℝ≥0} (hχ : ∀ {T : ℝ} (hT : 0 < T) {δ : ℝ}, 0 < δ →
      ∃ χ : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT,
        spatialFDerivL χ = 0 ∧
        (∀ p : slab (E := EuclideanSpace ℝ ι) 0 T,
          (p : ParabolicSpaceTime (EuclideanSpace ℝ ι)).time ≤ δ / 4 →
            χ p = 0 ∧ timeDerivL χ p = 0) ∧
        (∀ p : slab (E := EuclideanSpace ℝ ι) 0 T,
          δ ≤ (p : ParabolicSpaceTime (EuclideanSpace ℝ ι)).time → χ p = 1) ∧
        ‖χ‖ ≤ 1 + A / δ +
          nnHolderNorm α (timeDerivL χ : slab (E := EuclideanSpace ℝ ι) 0 T → ℝ) ∧
        (∀ p, ‖timeDerivL χ p‖ ≤ A / δ) ∧
        δ ^ (1 + (α : ℝ) / 2) *
          nnHolderNorm α (timeDerivL χ : slab (E := EuclideanSpace ℝ ι) 0 T → ℝ) ≤ B)
    {τ : ℝ} (hτ₀ : 0 < τ) (hτ₄ : τ ≤ 1 / 4) (hτabs : CS * (32 * A * τ) ≤ 1 / 2)
    (hdT₀ : d ≤ T₀) :
    d ^ (1 + (α : ℝ) / 2) * ‖restrictL hd.le le_rfl hdT u‖ ≤
      1 / 2 * ((d / 4) ^ (1 + (α : ℝ) / 2) * ‖restrictL h₄ le_rfl h₄T u‖) +
        CS * (24 * (T₀ * max 1 T₀ + A * max 1 T₀ + B) +
            (A * (max 1 T₀ + 40 * τ ^ (-(α : ℝ) / 2)) + B)) *
          (‖euclideanParabolicOperatorL hα₁.le a b c u‖ + ‖valueL u‖) := by
  obtain ⟨χ, hχx, hχ₀, hχ₁, hχv, hχA, hχB⟩ := hχ hT hd
  have hα1 : (α : ℝ) ≤ 1 := by exact_mod_cast hα₁.le
  -- The localized Schauder estimate and the interpolation inequality on `[d/4, T]`.
  have hloc := norm_restrictL_le_of_timeCutoff hα₁.le hd hdT h₄ h₄T a b c χ u hχx hχ₀ hχ₁
    (A := ⟨A / d, by positivity⟩) hχA hCS (hS _)
  have hI := norm_valueHolderL_le_add_mul hα₁.le (restrictL h₄ le_rfl h₄T u)
    (r := τ * d) (by positivity) (by nlinarith)
  have hV₄ : ‖valueL (restrictL h₄ le_rfl h₄T u)‖ ≤ ‖valueL u‖ := norm_valueL_restrictL_le u
  -- The norm of the cutoff: `‖χ‖_{α,par} ≤ 24 (1 + A/d + [χ']_{α,par})`.
  have hχn : ‖valueHolderL hα₁.le χ‖ ≤ 24 * (1 + A / d +
      nnHolderNorm α (timeDerivL χ : slab (E := EuclideanSpace ℝ ι) 0 T → ℝ)) :=
    (norm_valueHolderL_le_mul hα₁.le χ).trans (mul_le_mul_of_nonneg_left hχv (by norm_num))
  -- Powers of `d`.
  have hD : d ^ (1 + (α : ℝ) / 2) = d * d ^ ((α : ℝ) / 2) := by
    rw [Real.rpow_add hd, Real.rpow_one]
  have hqe : (τ * d) ^ (-(α : ℝ) / 2) * d ^ ((α : ℝ) / 2) = τ ^ (-(α : ℝ) / 2) := by
    rw [Real.mul_rpow hτ₀.le hd.le, mul_assoc, ← Real.rpow_add hd, neg_div, neg_add_cancel,
      Real.rpow_zero, mul_one]
  have h16 : d ^ (1 + (α : ℝ) / 2) ≤ 16 * (d / 4) ^ (1 + (α : ℝ) / 2) := by
    have h4 : (4 : ℝ) ^ (1 + (α : ℝ) / 2) ≤ 16 := by
      calc (4 : ℝ) ^ (1 + (α : ℝ) / 2) ≤ 4 ^ ((2 : ℕ) : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith)
        _ = 16 := by norm_num
    rw [Real.div_rpow hd.le (by norm_num), mul_div_assoc', le_div_iff₀ (by positivity),
      mul_comm 16]
    exact mul_le_mul_of_nonneg_left h4 (by positivity)
  have he := rpow_half_le_max hd hdT₀ hα₁.le
  have key := weighted_step_arith hloc hI hV₄ hχn hD hqe h16 he hdT₀ hχB hτabs hd
    (by positivity) hCS A.coe_nonneg hτ₀ (by positivity) (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) (norm_nonneg _) (by positivity) (NNReal.coe_nonneg _)
  -- The restrictions in `key` and in the goal differ only in proof terms.
  convert key using 3

/-- **The supremum bound from the comparison principle.** For degenerate elliptic `a` and
`‖c‖_{α,par} ≤ K`, every `u ∈ C_b^{2+α,1+α/2}` on `ℝⁿ × [0, T]`, `T ≤ T₀`, with
`|u(·, 0)| ≤ M` satisfies `sup |u| ≤ exp(K T₀) (1 + T₀) (M + ‖P u‖_{α,par})`. -/
private theorem norm_valueL_le_exp_mul (hα : α ≤ 1) {T T₀ K : ℝ≥0} {hT : (0 : ℝ) < T}
    (hTT₀ : T ≤ T₀) (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (ha : ∀ p (ξ : EuclideanSpace ℝ ι), 0 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
    (hck : ‖c‖ ≤ K) (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT) {M : ℝ}
    (hM : ∀ x, |u (slabMk x ⟨0, left_mem_Icc.2 hT.le⟩)| ≤ M) :
    ‖valueL u‖ ≤
      Real.exp (K * T₀) * (1 + T₀) * (M + ‖euclideanParabolicOperatorL hα a b c u‖) := by
  set Pu := ‖euclideanParabolicOperatorL hα a b c u‖
  have hM₀ : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hPu : 0 ≤ Pu := norm_nonneg _
  have hT₀ : (T : ℝ) ≤ T₀ := by exact_mod_cast hTT₀
  refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun p ↦ ?_
  have hmax := abs_le_exp_mul_mul_add_mul_of_abs_euclideanParabolicOperatorL_le hα (b := b) ha
    (fun q ↦ (le_abs_self _).trans ((HolderSpace.norm_apply_le c q).trans hck))
    K.coe_nonneg u (fun q ↦ by
      simpa only [Real.norm_eq_abs] using HolderSpace.norm_apply_le
        (euclideanParabolicOperatorL hα a b c u) q) hM p
  obtain ⟨ht₀, htT⟩ := (slabTime p).2
  have htT₀ : (slabTime p : ℝ) ≤ T₀ := htT.trans hT₀
  rw [valueL_apply, Real.norm_eq_abs]
  refine hmax.trans ?_
  rw [sub_zero]
  have hexp : Real.exp (K * (slabTime p : ℝ)) ≤ Real.exp (K * T₀) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left htT₀ K.coe_nonneg)
  have hlin : M + (slabTime p : ℝ) * Pu ≤ (1 + T₀) * (M + Pu) := by
    nlinarith [mul_le_mul_of_nonneg_right htT₀ hPu, T₀.coe_nonneg]
  calc _ ≤ Real.exp (K * T₀) * (M + (slabTime p : ℝ) * Pu) :=
        mul_le_mul_of_nonneg_right hexp (by positivity)
    _ ≤ Real.exp (K * T₀) * ((1 + T₀) * (M + Pu)) :=
        mul_le_mul_of_nonneg_left hlin (Real.exp_pos _).le
    _ = _ := by ring

variable {lam Lam : ℝ}

/-- **The weighted interior estimate.** For `0 < α < 1`, ellipticity constants `λ > 0` and `Λ`, a
bound `K` on the Hölder norms of the coefficients and a bound `T₀` on the horizon, there is a
constant `C` such that on `ℝⁿ × [0, T]`, `T ≤ T₀`, every `u ∈ C_b^{2+α,1+α/2}` with
`|u(·, 0)| ≤ M` satisfies, for every `0 < δ < T`,

`δ^(1 + α/2) ‖u‖_{2+α,par; [δ, T]} ≤ C (M + ‖P u‖_{α,par})`,

where `P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u` and `‖u‖_{2+α,par; [δ, T]}` is the order-two norm of
the restriction of `u` to `ℝⁿ × [δ, T]`. Unlike the global Schauder estimate, only the supremum of
the initial slice enters, not its `C_b^{2,α}` norm. -/
theorem exists_rpow_mul_norm_restrictL_le (hα₀ : 0 < α) (hα₁ : α < 1) (hlam : 0 < lam)
    (K T₀ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T), T ≤ T₀ →
      ∀ (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ),
        (∀ p (ξ : EuclideanSpace ℝ ι),
          lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) →
        (∀ p (ξ : EuclideanSpace ℝ ι),
          (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) →
        (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
        ∀ (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT) {M : ℝ},
        (∀ x, |u (slabMk x ⟨0, left_mem_Icc.2 hT.le⟩)| ≤ M) →
        ∀ {δ : ℝ} (hδ : 0 < δ) (hδT : δ < T),
          δ ^ (1 + (α : ℝ) / 2) * ‖restrictL hδ.le le_rfl hδT u‖ ≤
            C * (M + ‖euclideanParabolicOperatorL hα₁.le a b c u‖) := by
  obtain ⟨CS, hCS, hS⟩ :=
    exists_norm_le_euclideanParabolicOperatorL (ι := ι) hα₀ hα₁ (Lam := Lam) hlam K T₀
  obtain ⟨A, B, hχ⟩ := exists_timeCutoff (α := α) (E := EuclideanSpace ℝ ι) hα₁.le
  -- The time step `τ d` of the interpolation, with `τ` small enough to absorb the weighted norm.
  set τ : ℝ := (64 * CS * A + 4)⁻¹ with hτ
  have hτ₀ : 0 < τ := by positivity
  have hτ₄ : τ ≤ 1 / 4 := by
    rw [hτ, one_div]
    exact inv_anti₀ (by norm_num) (by nlinarith [mul_nonneg hCS A.coe_nonneg])
  have hτabs : CS * (32 * A * τ) ≤ 1 / 2 := by
    rw [hτ, ← div_eq_mul_inv, mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hCS A.coe_nonneg]
  set m : ℝ := max 1 T₀
  set C₁ : ℝ := CS * (24 * (T₀ * m + A * m + B) + (A * (m + 40 * τ ^ (-(α : ℝ) / 2)) + B))
  set E₀ : ℝ := Real.exp (K * T₀) * (1 + T₀)
  have hm : 1 ≤ m := le_max_left _ _
  have hC₁ : 0 ≤ C₁ := by positivity
  refine ⟨2 * C₁ * (1 + E₀), by positivity,
    fun T hT hTT₀ a b c ha ha' hak hbk hck u M hM δ hδ hδT ↦ ?_⟩
  set Pu := ‖euclideanParabolicOperatorL hα₁.le a b c u‖
  set V := ‖valueL u‖
  have hM₀ : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hPu : 0 ≤ Pu := norm_nonneg _
  have hT₀ : (T : ℝ) ≤ T₀ := by exact_mod_cast hTT₀
  -- The comparison principle bounds the supremum of `u` by its initial values and `P u`.
  have hV : V ≤ E₀ * (M + Pu) := norm_valueL_le_exp_mul hα₁.le hTT₀ a b c
    (fun q ξ ↦ (mul_nonneg hlam.le (sq_nonneg ‖ξ‖)).trans (ha q ξ)) hck u hM
  -- The weighted norms `W d = d^(1 + α/2) ‖u‖_{2+α,par; [d, T]}` for `0 < d < T`.
  let W : ℝ → ℝ := fun d ↦ if h : 0 < d ∧ d < T then
    d ^ (1 + (α : ℝ) / 2) * ‖restrictL h.1.le le_rfl h.2 u‖ else 0
  have hWeq (d : ℝ) (h : 0 < d ∧ d < T) :
      W d = d ^ (1 + (α : ℝ) / 2) * ‖restrictL h.1.le le_rfl h.2 u‖ :=
    dite_eq_left h
  have hW₀ (d : ℝ) : 0 ≤ W d := by
    by_cases h : 0 < d ∧ d < T
    · rw [hWeq d h]
      exact mul_nonneg (Real.rpow_nonneg h.1.le _) (norm_nonneg _)
    · rw [show W d = 0 from dite_eq_right h]
  have hW (d : ℝ) : W d ≤ 1 / 2 * W (d / 4) + C₁ * (Pu + V) := by
    by_cases h : 0 < d ∧ d < T
    · have h' : 0 < d / 4 ∧ d / 4 < T := ⟨by linarith [h.1], by linarith [h.1, h.2]⟩
      rw [hWeq d h, hWeq (d / 4) h']
      have key := weighted_step hα₁ h.1 h.2 h'.1.le h'.2 a b c u hCS
        (hS T hT hTT₀ a b c ha ha' hak hbk hck) hχ hτ₀ hτ₄ hτabs (h.2.le.trans hT₀)
      -- The restrictions in `key` and in the goal differ only in proof terms.
      convert key using 3
    · rw [show W d = 0 from dite_eq_right h]
      have := hW₀ (d / 4)
      have := mul_nonneg hC₁ (add_nonneg hPu (norm_nonneg (valueL u)))
      linarith
  have hbdd : BddAbove (range W) := by
    refine ⟨T₀ * m * ‖u‖, ?_⟩
    rintro _ ⟨d, rfl⟩
    by_cases h : 0 < d ∧ d < T
    · rw [hWeq d h]
      have hpow : d ^ (1 + (α : ℝ) / 2) ≤ T₀ * m := by
        rw [Real.rpow_add h.1, Real.rpow_one]
        exact mul_le_mul (h.2.le.trans hT₀) (rpow_half_le_max h.1 (h.2.le.trans hT₀) hα₁.le)
          (Real.rpow_nonneg h.1.le _) T₀.coe_nonneg
      exact mul_le_mul hpow (norm_restrictL_apply_le u) (norm_nonneg _)
        (mul_nonneg T₀.coe_nonneg (zero_le_one.trans hm))
    · rw [show W d = 0 from dite_eq_right h]
      exact mul_nonneg (mul_nonneg T₀.coe_nonneg (zero_le_one.trans hm)) (norm_nonneg _)
  -- Absorb half of the supremum of the weighted norms.
  have hsup : iSup W ≤ 2 * C₁ * (Pu + V) := by
    have h : iSup W ≤ 1 / 2 * iSup W + C₁ * (Pu + V) :=
      ciSup_le fun d ↦ by
        have := le_ciSup hbdd (d / 4)
        have := hW d
        linarith
    linarith
  have hδW := le_ciSup hbdd δ
  rw [hWeq δ ⟨hδ, hδT⟩] at hδW
  calc δ ^ (1 + (α : ℝ) / 2) * ‖restrictL hδ.le le_rfl hδT u‖ ≤ iSup W := by
        convert hδW using 3
    _ ≤ 2 * C₁ * (Pu + V) := hsup
    _ ≤ 2 * C₁ * ((1 + E₀) * (M + Pu)) := by
      gcongr
      nlinarith [hV, Real.exp_pos (K * T₀)]
    _ = _ := by ring

end Weighted

end ParabolicC2HolderSpace

end TauCeti
