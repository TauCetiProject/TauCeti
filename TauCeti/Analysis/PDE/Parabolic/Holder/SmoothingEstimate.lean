/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Restriction
public import TauCeti.Analysis.PDE.Parabolic.Holder.Schauder
import TauCeti.Analysis.Matrix.QuadraticBounds
import TauCeti.Analysis.SpecialFunctions.Pow.Real
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
`[δ/4, T]` (`TauCeti.HolderSpace.norm_compLipschitzL_inclusion_eq_of_eq_zero`), where the
interpolation inequality at the time step `τ δ`
(`TauCeti.ParabolicC2HolderSpace.norm_valueHolderL_le_add_mul`) bounds the parabolic Hölder norm
of `u` by `(1 + 40 (τ δ)^(-α/2)) sup |u|` plus `2 τ δ ‖u‖_{2+α,par; [δ/4, T]}`. After
multiplication by `δ^(1 + α/2)`, the last term is a multiple of `τ` times the weighted norm at
`δ/4`; for `τ` small it is absorbed into the supremum over `δ` of the weighted norms, which is
finite because `u` lies in the closed-slab space. Finally the comparison principle
(`TauCeti.ParabolicC2HolderSpace.norm_valueL_le_exp_mul`) bounds `sup |u|` by `sup |u(·, 0)|`
and `‖P u‖`.

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

/-- **The rescaled transition profile.** If `ψ'` is bounded by `L₁` and `L₂`-Lipschitz, then for
`δ > 0` the function `t ↦ ψ'(2 t / δ - 1) (2 / δ)` is bounded by `2 L₁ / δ` and, for `α ≤ 1`,
`(α/2)`-Hölder with constant `(4 L₂ + 4 L₁) δ^(-(1 + α/2))`. -/
private theorem norm_le_and_holderWith_rescale {ψ' : ℝ → ℝ} {L₁ L₂ : ℝ≥0}
    (hL₁ : ∀ x, ‖ψ' x‖ ≤ L₁) (hL₂ : LipschitzWith L₂ ψ') (hα : α ≤ 1) {δ : ℝ≥0} (hδ : 0 < δ) :
    (∀ t : ℝ, ‖ψ' (2 * t / δ - 1) * (2 / δ)‖ ≤ 2 * L₁ / δ) ∧
      HolderWith ((4 * L₂ + 4 * L₁) * δ ^ (-(1 + (α : ℝ) / 2))) (α / 2)
        fun t : ℝ ↦ ψ' (2 * t / δ - 1) * (2 / δ) := by
  have hδr : (0 : ℝ) < δ := hδ
  have hbd (t : ℝ) : ‖ψ' (2 * t / δ - 1) * (2 / δ)‖ ≤ 2 * L₁ / δ := by
    rw [norm_mul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2 / δ)]
    calc _ ≤ (L₁ : ℝ) * (2 / δ) := by gcongr; exact hL₁ _
      _ = _ := by ring
  refine ⟨hbd, ?_⟩
  -- Interpolate between the Lipschitz constant `4 L₂ / δ²` and the oscillation bound `4 L₁ / δ`.
  have hK : 4 * L₂ / δ ^ 2 * δ ^ ((1 : ℝ≥0) - (α / 2 : ℝ≥0) : ℝ) +
      4 * L₁ / δ * δ ^ (-((α / 2 : ℝ≥0) : ℝ)) = (4 * L₂ + 4 * L₁) * δ ^ (-(1 + (α : ℝ) / 2)) := by
    rw [← NNReal.coe_inj]
    push_cast
    have e₁ : (δ : ℝ) ^ (1 - (α : ℝ) / 2) = δ ^ (2 : ℝ) * δ ^ (-(1 + (α : ℝ) / 2)) := by
      rw [← Real.rpow_add hδr]
      congr 1
      ring
    have e₂ : (δ : ℝ) ^ (-((α : ℝ) / 2)) = δ ^ (1 : ℝ) * δ ^ (-(1 + (α : ℝ) / 2)) := by
      rw [← Real.rpow_add hδr]
      congr 1
      ring
    rw [e₁, e₂, Real.rpow_two, Real.rpow_one]
    field_simp
  rw [← hK]
  refine holderOnWith_univ.1 (HolderOnWith.of_le_of_dist_le (fun t _ s _ _ ↦ ?_)
    (fun t _ s _ ↦ ?_) ((NNReal.half_le_self α).trans hα) hδ)
  · rw [NNReal.coe_one, Real.rpow_one, dist_eq_norm, ← sub_mul, norm_mul,
      Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2 / δ)]
    have h := hL₂.dist_le_mul (2 * t / δ - 1) (2 * s / δ - 1)
    rw [dist_eq_norm, Real.dist_eq] at h
    have hts : |2 * t / δ - 1 - (2 * s / δ - 1)| = 2 / δ * |t - s| := by
      rw [show 2 * t / (δ : ℝ) - 1 - (2 * s / δ - 1) = 2 / δ * (t - s) by ring, abs_mul,
        abs_of_pos (by positivity : (0 : ℝ) < 2 / δ)]
    rw [hts] at h
    push_cast
    rw [Real.dist_eq]
    calc _ ≤ ↑L₂ * (2 / δ * |t - s|) * (2 / δ) := mul_le_mul_of_nonneg_right h (by positivity)
      _ = _ := by field_simp; ring
  · rw [dist_eq_norm]
    push_cast
    calc _ ≤ ‖ψ' (2 * t / δ - 1) * (2 / δ)‖ + ‖ψ' (2 * s / δ - 1) * (2 / δ)‖ := norm_sub_le _ _
      _ ≤ 2 * L₁ / δ + 2 * L₁ / δ := add_le_add (hbd t) (hbd s)
      _ = _ := by ring

/-- **The time cutoff.** For `δ > 0` there is a map `χ` of time alone, vanishing together with its
time derivative up to time `δ/4` and equal to one from time `δ` on, with
`‖χ‖ ≤ 1 + A / δ + [χ']_{α,par}`, `|χ'| ≤ A / δ` and `δ^(1 + α/2) [χ']_{α,par} ≤ B` for constants
`A`, `B` independent of `δ`. -/
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
  have hlip : LipschitzWith L₂ (deriv Real.smoothTransition) :=
    lipschitzWith_of_nnNorm_deriv_le
      (Real.smoothTransition.contDiff (n := 2)).differentiable_deriv_two fun x ↦ by
        rw [← NNReal.coe_le_coe, coe_nnNorm]
        exact hL₂ x
  refine ⟨2 * L₁, 4 * L₂ + 4 * L₁, fun {T} hT {δ} hδ ↦ ?_⟩
  lift δ to ℝ≥0 using hδ.le
  -- The cutoff is `φ(t) = ψ(2 t / δ - 1)`, with derivative `φ'`.
  set φ : ℝ → ℝ := fun t ↦ Real.smoothTransition (2 * t / δ - 1)
  set φ' : ℝ → ℝ := fun t ↦ deriv Real.smoothTransition (2 * t / δ - 1) * (2 / δ)
  have hφ (t : ℝ) : HasDerivAt φ (φ' t) t := by
    have h := HasDerivAt.smoothTransition
      ((((hasDerivAt_id t).const_mul 2).div_const (δ : ℝ)).sub_const 1)
    rwa [mul_one] at h
  obtain ⟨hbd, hH⟩ := norm_le_and_holderWith_rescale hL₁ hlip hα (NNReal.coe_pos.1 hδ)
  have hφ'c : Continuous φ' := (hlip.continuous.comp (by fun_prop)).mul continuous_const
  refine ⟨ofTime φ φ' (fun t _ ↦ (hφ t).hasDerivWithinAt) hφ'c.continuousOn
      ⟨_, hH.holderOnWith _⟩, spatialFDerivL_ofTime .., fun p hp ↦ ?_, fun p hp ↦ ?_, ?_,
    fun p ↦ ?_, ?_⟩
  · have h : 2 * (p : ParabolicSpaceTime E).time / δ - 1 < 0 := by
      rw [sub_neg, div_lt_one hδ]
      linarith
    rw [ofTime_apply, timeDerivL_ofTime_apply]
    exact ⟨Real.smoothTransition.zero_of_nonpos h.le,
      by simp only [φ']; rw [Real.smoothTransition.deriv_of_neg h, zero_mul]⟩
  · rw [ofTime_apply]
    exact Real.smoothTransition.one_of_one_le (by rw [le_sub_iff_add_le, le_div_iff₀ hδ]; linarith)
  · -- The supremum of `χ` is at most one and that of `χ'` at most `A / δ`.
    rw [norm_ofTime, HolderSpace.norm_def, HolderSpace.coe_toBoundedContinuousFunction]
    have hv : ‖valueL (ofTime (E := E) (hab := hT) φ φ' (fun t _ ↦ (hφ t).hasDerivWithinAt)
        hφ'c.continuousOn ⟨_, hH.holderOnWith _⟩)‖ ≤ 1 := by
      refine (BoundedContinuousFunction.norm_le zero_le_one).2 fun p ↦ ?_
      rw [valueL_apply, ofTime_apply, Real.norm_of_nonneg (Real.smoothTransition.nonneg _)]
      exact Real.smoothTransition.le_one _
    have ht : ‖(timeDerivL (ofTime (E := E) (hab := hT) φ φ' (fun t _ ↦ (hφ t).hasDerivWithinAt)
        hφ'c.continuousOn ⟨_, hH.holderOnWith _⟩)).toBoundedContinuousFunction‖ ≤
        (2 * L₁ : ℝ≥0) / δ :=
      (BoundedContinuousFunction.norm_le (by positivity)).2 fun p ↦ by
        rw [HolderSpace.toBoundedContinuousFunction_apply, timeDerivL_ofTime_apply]
        exact (hbd _).trans (by push_cast; rfl)
    linarith
  · rw [timeDerivL_ofTime_apply]
    exact (hbd _).trans (by push_cast; rfl)
  · -- The weight cancels the factor `δ^(-(1 + α/2))` of the Hölder constant of `φ'`.
    refine (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.2
      (nnHolderNorm_timeDerivL_ofTime_le _ _ _ _ _ (hH.holderOnWith _))) (by positivity)).trans_eq
      ?_
    push_cast
    rw [Real.rpow_neg hδ.le]
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
  refine (HolderSpace.norm_compLipschitzL_inclusion_eq_of_eq_zero has _
    fun p hp ↦ ?_).ge.trans ?_
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
        CS * (24 * (T₀ * (1 + T₀) + A * (1 + T₀) + B) +
            (A * ((1 + T₀) + 40 * τ ^ (-(α : ℝ) / 2)) + B)) *
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
  have he : d ^ ((α : ℝ) / 2) ≤ 1 + T₀ :=
    (Real.rpow_le_one_add hd.le (by positivity) (by linarith)).trans (by linarith)
  have key := weighted_step_arith hloc hI hV₄ hχn hD hqe h16 he hdT₀ hχB hτabs hd
    (by positivity) hCS A.coe_nonneg hτ₀ (by positivity) (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) (norm_nonneg _) (by positivity) (NNReal.coe_nonneg _)
  -- The restrictions in `key` and in the goal differ only in proof terms.
  convert key using 3

/-- **Absorption of the weighted supremum.** Let `w d ≥ 0` be defined for `0 < d < T` and bounded
above. If `w d ≤ w (d / 4) / 2 + C` for every `d`, with `0 ≤ C`, then `w d ≤ 2 C` for every
`d`. -/
private theorem le_two_mul_of_le_half_mul_add {T B C : ℝ} (w : ∀ d : ℝ, 0 < d → d < T → ℝ)
    (hw₀ : ∀ d hd hdT, 0 ≤ w d hd hdT) (hB : ∀ d hd hdT, w d hd hdT ≤ B) (hC : 0 ≤ C)
    (hw : ∀ d (hd : 0 < d) (hdT : d < T),
      w d hd hdT ≤ 1 / 2 * w (d / 4) (by linarith) (by linarith) + C)
    {d : ℝ} (hd : 0 < d) (hdT : d < T) : w d hd hdT ≤ 2 * C := by
  -- Extend `w` by zero outside `(0, T)`.
  let W : ℝ → ℝ := fun d ↦ if h : 0 < d ∧ d < T then w d h.1 h.2 else 0
  have hWeq (d : ℝ) (h : 0 < d ∧ d < T) : W d = w d h.1 h.2 := dite_eq_left h
  have hWne (d : ℝ) (h : ¬(0 < d ∧ d < T)) : W d = 0 := dite_eq_right h
  have hW₀ (d : ℝ) : 0 ≤ W d := by
    by_cases h : 0 < d ∧ d < T
    · rw [hWeq d h]
      exact hw₀ _ _ _
    · rw [hWne d h]
  have hbdd : BddAbove (range W) := by
    refine ⟨max B 0, ?_⟩
    rintro _ ⟨d, rfl⟩
    by_cases h : 0 < d ∧ d < T
    · rw [hWeq d h]
      exact (hB _ _ _).trans (le_max_left _ _)
    · rw [hWne d h]
      exact le_max_right _ _
  have hW (d : ℝ) : W d ≤ 1 / 2 * W (d / 4) + C := by
    by_cases h : 0 < d ∧ d < T
    · rw [hWeq d h, hWeq (d / 4) ⟨by linarith [h.1], by linarith [h.1, h.2]⟩]
      exact hw d h.1 h.2
    · rw [hWne d h]
      linarith [hW₀ (d / 4)]
  -- Half of the supremum of `W` absorbs into the left-hand side.
  have hsup : iSup W ≤ 1 / 2 * iSup W + C :=
    ciSup_le fun d ↦ by linarith [le_ciSup hbdd (d / 4), hW d]
  have hd' := le_ciSup hbdd d
  rw [hWeq d ⟨hd, hdT⟩] at hd'
  linarith

variable {lam : ℝ}

/-- **The weighted interior estimate.** For `0 < α < 1`, an ellipticity constant `λ > 0`, a bound
`K` on the Hölder norms of the coefficients and a bound `T₀` on the horizon, there is a constant
`C` such that on `ℝⁿ × [0, T]`, `T ≤ T₀`, every `u ∈ C_b^{2+α,1+α/2}` with `|u(·, 0)| ≤ M`
satisfies, for every `0 < δ < T`,

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
        (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
        ∀ (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT) {M : ℝ},
        (∀ x, |u (slabMk x ⟨0, left_mem_Icc.2 hT.le⟩)| ≤ M) →
        ∀ {δ : ℝ} (hδ : 0 < δ) (hδT : δ < T),
          δ ^ (1 + (α : ℝ) / 2) * ‖restrictL hδ.le le_rfl hδT u‖ ≤
            C * (M + ‖euclideanParabolicOperatorL hα₁.le a b c u‖) := by
  -- An entry bound `K` gives the upper ellipticity bound `∑ᵢⱼ K`.
  obtain ⟨CS, hCS, hS⟩ := exists_norm_le_euclideanParabolicOperatorL (ι := ι) hα₀ hα₁
    (Lam := ∑ _i : ι, ∑ _j : ι, (K : ℝ)) hlam K T₀
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
  set m : ℝ := 1 + T₀
  set C₁ : ℝ := CS * (24 * (T₀ * m + A * m + B) + (A * (m + 40 * τ ^ (-(α : ℝ) / 2)) + B))
  set E₀ : ℝ := Real.exp (K * T₀) * (1 + T₀)
  have hC₁ : 0 ≤ C₁ := by positivity
  refine ⟨2 * C₁ * (1 + E₀), by positivity,
    fun T hT hTT₀ a b c ha hak hbk hck u M hM δ hδ hδT ↦ ?_⟩
  set Pu := ‖euclideanParabolicOperatorL hα₁.le a b c u‖
  set V := ‖valueL u‖
  have hM₀ : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hPu : 0 ≤ Pu := norm_nonneg _
  have hT₀ : (T : ℝ) ≤ T₀ := by exact_mod_cast hTT₀
  have hα₂ : (α : ℝ) / 2 ≤ 1 := by
    have : (α : ℝ) ≤ 1 := by exact_mod_cast hα₁.le
    linarith
  have ha' : ∀ p (ξ : EuclideanSpace ℝ ι), (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ ≤
      (∑ _i : ι, ∑ _j : ι, (K : ℝ)) * ‖ξ‖ ^ 2 := fun p ξ ↦
    (Matrix.toQuadraticForm'_le_sum_abs_mul_sq _ ξ).trans (mul_le_mul_of_nonneg_right
      (Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦
        (HolderSpace.norm_apply_le (a i j) p).trans (hak i j)) (sq_nonneg _))
  -- The comparison principle bounds the supremum of `u` by its initial values and `P u`.
  have hV : V ≤ E₀ * (M + Pu) := norm_valueL_le_exp_mul hα₁.le (b := b)
    (fun q ξ ↦ (mul_nonneg hlam.le (sq_nonneg ‖ξ‖)).trans (ha q ξ))
    (fun q ↦ (le_abs_self _).trans ((HolderSpace.norm_apply_le c q).trans hck)) K.coe_nonneg
    (by rw [sub_zero]; exact hT₀) u hM
  -- Absorb the weighted norms `d^(1 + α/2) ‖u‖_{2+α,par; [d, T]}`, `0 < d < T`.
  have hsup := le_two_mul_of_le_half_mul_add
    (fun d hd hdT ↦ d ^ (1 + (α : ℝ) / 2) * ‖restrictL hd.le le_rfl hdT u‖)
    (fun d hd _ ↦ mul_nonneg (Real.rpow_nonneg hd.le _) (norm_nonneg _)) (B := T₀ * m * ‖u‖)
    (fun d hd hdT ↦ by
      have hpow : d ^ (1 + (α : ℝ) / 2) ≤ T₀ * m := by
        rw [Real.rpow_add hd, Real.rpow_one]
        exact mul_le_mul (hdT.le.trans hT₀) ((Real.rpow_le_one_add hd.le (by positivity) hα₂).trans
          (by linarith)) (Real.rpow_nonneg hd.le _) T₀.coe_nonneg
      exact mul_le_mul hpow (norm_restrictL_apply_le u) (norm_nonneg _) (by positivity))
    (mul_nonneg hC₁ (add_nonneg hPu (norm_nonneg _)))
    (fun d hd hdT ↦ by
      have key := weighted_step hα₁ hd hdT (by positivity) (by linarith) a b c u hCS
        (hS T hT hTT₀ a b c ha ha' hak hbk hck) hχ hτ₀ hτ₄ hτabs (hdT.le.trans hT₀)
      -- The restrictions in `key` and in the goal differ only in proof terms.
      convert key using 3) hδ hδT
  calc δ ^ (1 + (α : ℝ) / 2) * ‖restrictL hδ.le le_rfl hδT u‖ ≤ 2 * (C₁ * (Pu + V)) := hsup
    _ ≤ 2 * C₁ * ((1 + E₀) * (M + Pu)) := by
      rw [← mul_assoc]
      gcongr
      nlinarith [hV, Real.exp_pos (K * T₀)]
    _ = _ := by ring

end Weighted

end ParabolicC2HolderSpace

end TauCeti
