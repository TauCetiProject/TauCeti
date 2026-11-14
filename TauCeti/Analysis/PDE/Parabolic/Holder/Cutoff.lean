/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Smooth
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Topology.MetricSpace.Holder

/-!
# Smooth cutoffs on parabolic cylinders

These cutoffs localize a closed time slab to a spatial ball of radius `ρ` and a
time interval of radius `ρ²`. They are one on the smaller cylinder of spatial radius
`ρ / 2` and temporal radius `ρ² / 4`. One order-two parabolic Hölder norm bound works
for every spatial and temporal center and every slab. Centering the time interval at
the initial endpoint preserves the initial trace on the smaller spatial ball.
Choosing such a cutoff for every point of a slab gives cutoffs centred at every point,
one on the parabolic ball of radius `ρ / 2` about their centre and vanishing at parabolic
distance at least `2 ρ`, as used to patch local estimates into global ones.

The construction uses Mathlib's `ContDiffBump` on ordinary product space, with the
time coordinate rescaled by `ρ`.

A time cutoff at scale `δ` (`TauCeti.ParabolicC2HolderSpace.IsTimeCutoff`) is a map of time
alone on `E × [0, T]`, vanishing up to time `δ / 4` and equal to one from time `δ` on, whose
time derivative is bounded by `A / δ` and has parabolic Hölder seminorm at most `B δ^(-1 - α/2)`.
Such cutoffs exist with `A` and `B` independent of `δ` and `T`
(`TauCeti.ParabolicC2HolderSpace.exists_timeCutoff`); they localize estimates away from the
initial time.
-/

public section
noncomputable section

open Set Metric TauCeti ParabolicSpaceTime
open scoped NNReal ContDiff

namespace TauCeti.ParabolicC2HolderSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {α : ℝ≥0}

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- Smooth cutoffs on parabolic cylinders, with a common norm bound independent of
both centers and of the closed time slab. The cutoff is the restriction of a smooth
function on ordinary space-time. -/
theorem exists_cutoff (hα : α ≤ 1) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : E) (s a b : ℝ) (hab : a < b),
      ∃ χ : ParabolicC2HolderSpace α E ℝ hab,
        ‖χ‖ ≤ C ∧
        (∀ p, χ p ∈ Icc 0 1) ∧
        (∀ p : slab (E := E) a b, dist (p : ParabolicSpaceTime E).space z ≤ ρ / 2 →
          |(p : ParabolicSpaceTime E).time - s| ≤ ρ ^ 2 / 4 → χ p = 1) ∧
        (∀ p : slab (E := E) a b, ρ ≤ dist (p : ParabolicSpaceTime E).space z ∨
          ρ ^ 2 ≤ |(p : ParabolicSpaceTime E).time - s| → χ p = 0) ∧
        ∃ ψ : E × ℝ → ℝ, ContDiff ℝ ∞ ψ ∧
          ∀ p, χ p = ψ ((p : ParabolicSpaceTime E).space,
            (p : ParabolicSpaceTime E).time) := by
  -- The product norm gives a spatial ball and an independently rescaled time interval.
  let β : ContDiffBump (0 : E × ℝ) := ⟨ρ / 2, ρ, by positivity, by linarith⟩
  let e : E × ℝ ≃ₜ E × ℝ := (Homeomorph.refl E).prodCongr
    (Homeomorph.smulOfNeZero ρ⁻¹ (inv_ne_zero hρ.ne'))
  let f : E × ℝ → ℝ := fun p ↦ β (p.1, p.2 / ρ)
  have hf : ContDiff ℝ ∞ f := β.contDiff.comp (contDiff_fst.prodMk (contDiff_snd.div_const ρ))
  have hs : HasCompactSupport f := by
    simpa [f, e, Function.comp_def, div_eq_inv_mul, Prod.map_def] using
      β.hasCompactSupport.comp_homeomorph e
  obtain ⟨C, hC, hχ⟩ := exists_norm_le_comp_coords hα (hf.of_le (by simp)) hs
  refine ⟨C, hC, fun z s a b hab ↦ ?_⟩
  obtain ⟨χ, hχ, hnχ⟩ := hχ (z, s) a b hab
  refine ⟨χ, hnχ, ?_, ?_, ?_, ?_⟩
  · intro p
    rw [hχ]
    exact ⟨β.nonneg, β.le_one⟩
  · intro p hx ht
    rw [hχ]
    apply β.one_of_mem_closedBall
    rw [mem_closedBall_zero_iff, Prod.norm_def, max_le_iff]
    simp only [β]
    constructor
    · simpa [dist_eq_norm] using hx
    · simp only [Real.norm_eq_abs, abs_div, abs_of_pos hρ]
      exact (div_le_iff₀ hρ).2 (by nlinarith)
  · intro p hp
    rw [hχ]
    apply β.zero_of_le_dist
    rw [dist_zero_right, Prod.norm_def]
    simp only [β]
    rcases hp with hx | ht
    · have hx' : ρ ≤ ‖(p : ParabolicSpaceTime E).space - z‖ := by
        simpa [dist_eq_norm] using hx
      exact hx'.trans (le_max_left _ _)
    · apply le_trans _ (le_max_right _ _)
      simp only [Real.norm_eq_abs, abs_div, abs_of_pos hρ]
      exact (le_div_iff₀ hρ).2 (by nlinarith)
  · refine ⟨fun p ↦ f (p.1 - z, p.2 - s), ?_, fun p ↦ hχ p⟩
    exact hf.comp ((contDiff_fst.sub contDiff_const).prodMk
      (contDiff_snd.sub contDiff_const))

/-- **Cutoffs centred at every point of a slab.** For `α ≤ 1` and `ρ > 0` there is a constant
`C` such that on every slab there are scalar maps `χ p`, one for each point `p`, with
`‖χ p‖ ≤ C`, values in `[0, 1]`, equal to one on the parabolic ball of radius `ρ / 2` about `p`
and vanishing at parabolic distance at least `2 ρ` from `p`. -/
theorem exists_cutoff_family (hα : α ≤ 1) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a b : ℝ) (hab : a < b),
      ∃ χ : slab (E := E) a b → ParabolicC2HolderSpace α E ℝ hab,
        (∀ p, ‖χ p‖ ≤ C) ∧ (∀ p q, χ p q ∈ Icc 0 1) ∧
        (∀ p, ∀ q ∈ ball p (ρ / 2), χ p q = 1) ∧
        ∀ p q, 2 * ρ ≤ dist q p → χ p q = 0 := by
  obtain ⟨C, hC, hχ⟩ := exists_cutoff (E := E) hα hρ
  refine ⟨C, hC, fun a b hab ↦ ?_⟩
  choose χ hnorm hmem hone hzero _ using fun p : slab (E := E) a b ↦
    hχ (p : ParabolicSpaceTime E).space (p : ParabolicSpaceTime E).time a b hab
  refine ⟨χ, hnorm, hmem, fun p q hq ↦ hone p q ?_ ?_, fun p q hq ↦ hzero p q ?_⟩
  · -- Inside the parabolic ball of radius `ρ / 2`, the spatial distance is at most `ρ / 2` ...
    exact (dist_space_le _ _).trans (mem_ball.1 hq).le
  · -- ... and the time distance at most `ρ² / 4`.
    have hs := (sqrt_abs_time_sub_le_dist (q : ParabolicSpaceTime E) p).trans (mem_ball.1 hq).le
    have hτ := Real.sq_sqrt (abs_nonneg ((q : ParabolicSpaceTime E).time -
      (p : ParabolicSpaceTime E).time))
    nlinarith [Real.sqrt_nonneg |(q : ParabolicSpaceTime E).time -
      (p : ParabolicSpaceTime E).time|]
  · -- At parabolic distance at least `2 ρ`, either the spatial distance is at least `ρ` or the
    -- time distance is at least `ρ²`.
    rw [Subtype.dist_eq, dist_eq] at hq
    by_contra! hlt
    obtain ⟨hx, ht⟩ := hlt
    have hs : √|(q : ParabolicSpaceTime E).time - (p : ParabolicSpaceTime E).time| < ρ :=
      (Real.sqrt_lt' hρ).2 ht
    linarith

end FiniteDimensional

/-! ### Time cutoffs -/

/-- A **time cutoff at scale `δ`** on `E × [0, T]`: a map `χ` of time alone, vanishing together
with its time derivative up to time `δ/4` and equal to one from time `δ` on, with
`‖χ‖ ≤ 1 + A / δ + [χ']_{α,par}`, `|χ'| ≤ A / δ` and `δ^(1 + α/2) [χ']_{α,par} ≤ B`. -/
structure IsTimeCutoff {T : ℝ} {hT : 0 < T} (A B : ℝ≥0) (δ : ℝ)
    (χ : ParabolicC2HolderSpace α E ℝ hT) : Prop where
  spatialFDerivL_eq_zero : spatialFDerivL χ = 0
  eq_zero_of_time_le :
    ∀ p : slab (E := E) 0 T, (p : ParabolicSpaceTime E).time ≤ δ / 4 → χ p = 0
  timeDerivL_eq_zero_of_time_le :
    ∀ p : slab (E := E) 0 T, (p : ParabolicSpaceTime E).time ≤ δ / 4 → timeDerivL χ p = 0
  eq_one_of_le_time : ∀ p : slab (E := E) 0 T, δ ≤ (p : ParabolicSpaceTime E).time → χ p = 1
  norm_le : ‖χ‖ ≤ 1 + A / δ + nnHolderNorm α (timeDerivL χ : slab (E := E) 0 T → ℝ)
  norm_timeDerivL_apply_le : ∀ p, ‖timeDerivL χ p‖ ≤ A / δ
  rpow_mul_nnHolderNorm_timeDerivL_le :
    δ ^ (1 + (α : ℝ) / 2) * nnHolderNorm α (timeDerivL χ : slab (E := E) 0 T → ℝ) ≤ B

/-- **The rescaled transition profile.** If `ψ'` is bounded by `L₁` and `L₂`-Lipschitz, then for
`δ ≥ 0` the function `t ↦ ψ'(2 t / δ - 1) (2 / δ)` is bounded by `2 L₁ / δ` and, for `α ≤ 2`,
`(α/2)`-Hölder with constant `(4 L₂ + 4 L₁) δ^(-(1 + α/2))`. -/
private theorem norm_le_and_holderWith_rescale {ψ' : ℝ → ℝ} {L₁ L₂ : ℝ≥0}
    (hL₁ : ∀ x, ‖ψ' x‖ ≤ L₁) (hL₂ : LipschitzWith L₂ ψ') (hα : α ≤ 2) (δ : ℝ≥0) :
    (∀ t : ℝ, ‖ψ' (2 * t / δ - 1) * (2 / δ)‖ ≤ 2 * L₁ / δ) ∧
      HolderWith ((4 * L₂ + 4 * L₁) * δ ^ (-(1 + (α : ℝ) / 2))) (α / 2)
        fun t : ℝ ↦ ψ' (2 * t / δ - 1) * (2 / δ) := by
  -- At `δ = 0` the function is identically zero.
  rcases eq_zero_or_pos δ with rfl | hδ
  · refine ⟨fun t ↦ by simp, ?_⟩
    simp only [NNReal.coe_zero, div_zero, mul_zero]
    exact HolderWith.const
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
    (fun t _ s _ ↦ ?_) ((div_le_one₀ two_pos).2 hα) hδ)
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

/-- **Time cutoffs.** For `α ≤ 2` there are constants `A`, `B` such that on every slab
`E × [0, T]` and at every scale `δ > 0` there is a time cutoff at scale `δ` with these constants.
The cutoff is `t ↦ ψ(2 t / δ - 1)`, with `ψ` Mathlib's smooth transition. -/
theorem exists_timeCutoff (hα : α ≤ 2) :
    ∃ A B : ℝ≥0, ∀ {T : ℝ} (hT : 0 < T) {δ : ℝ}, 0 < δ →
      ∃ χ : ParabolicC2HolderSpace α E ℝ hT, IsTimeCutoff A B δ χ := by
  obtain ⟨L₁, hL₁⟩ := Real.smoothTransition.exists_forall_norm_deriv_le
  lift L₁ to ℝ≥0 using (norm_nonneg _).trans (hL₁ 0)
  obtain ⟨L₂, hlip⟩ := Real.smoothTransition.exists_lipschitzWith_deriv
  refine ⟨2 * L₁, 4 * L₂ + 4 * L₁, fun {T} hT {δ} hδ ↦ ?_⟩
  lift δ to ℝ≥0 using hδ.le
  -- The cutoff is `φ(t) = ψ(2 t / δ - 1)`, with derivative `φ'`.
  set φ : ℝ → ℝ := fun t ↦ Real.smoothTransition (2 * t / δ - 1)
  set φ' : ℝ → ℝ := fun t ↦ deriv Real.smoothTransition (2 * t / δ - 1) * (2 / δ)
  have hφ (t : ℝ) : HasDerivAt φ (φ' t) t := by
    have h := HasDerivAt.smoothTransition
      ((((hasDerivAt_id t).const_mul 2).div_const (δ : ℝ)).sub_const 1)
    rwa [mul_one] at h
  obtain ⟨hbd, hH⟩ := norm_le_and_holderWith_rescale hL₁ hlip hα δ
  have hφ'c : Continuous φ' := (hlip.continuous.comp (by fun_prop)).mul continuous_const
  -- Before time `δ / 4` the argument `2 t / δ - 1` of the transition is negative.
  have hneg {t : ℝ} (ht : t ≤ δ / 4) : 2 * t / δ - 1 < 0 := by
    rw [sub_neg, div_lt_one hδ]
    linarith
  refine ⟨ofTime φ φ' (fun t _ ↦ (hφ t).hasDerivWithinAt) hφ'c.continuousOn
      ⟨_, hH.holderOnWith _⟩, spatialFDerivL_ofTime .., fun p hp ↦ ?_, fun p hp ↦ ?_,
    fun p hp ↦ ?_, ?_, fun p ↦ ?_, ?_⟩
  · rw [ofTime_apply]
    exact Real.smoothTransition.zero_of_nonpos (hneg hp).le
  · rw [timeDerivL_ofTime_apply]
    simp only [φ', Real.smoothTransition.deriv_of_neg (hneg hp), zero_mul]
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

end TauCeti.ParabolicC2HolderSpace
