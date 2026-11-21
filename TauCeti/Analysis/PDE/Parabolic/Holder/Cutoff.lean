/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Smooth
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.PDE.Parabolic.SpaceTime.Interpolation
import TauCeti.Analysis.SpecialFunctions.SmoothTransition

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

Time cutoffs (`exists_timeCutoff`) localize in time alone: `t ↦ ψ (t / s - 1)` for the smooth step
`ψ = Real.smoothTransition` vanishes up to time `s` and equals one from time `2 s` on. Its
parabolic Hölder norms are explicit in `s`: `[χ]_{α,par} ≲ s^(-α/2)`, `|∂ₜχ| ≲ s⁻¹` and
`[∂ₜχ]_{α,par} ≲ s^(-(1 + α/2))`. These scalings are what estimates weighted by powers of the
time need.
-/

public section
noncomputable section

open Set Metric TauCeti ParabolicSpaceTime
open scoped NNReal ContDiff

namespace TauCeti.ParabolicC2HolderSpace

section Cylinder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {α : ℝ≥0}

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

end Cylinder

section TimeCutoff

open scoped BoundedContinuousFunction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {α : ℝ≥0}

omit [NormedSpace ℝ E] in
/-- `ParabolicSpaceTime.holderWith_comp_time` at the time scale `s`, for a real function of time
with `|g| ≤ A` and `|g'| ≤ B / s`: its parabolic `α`-seminorm is at most `(B + 2 A) s^(-α/2)`. -/
private theorem memHolder_comp_time_of_le {a b s A B : ℝ} {g g' : ℝ → ℝ} (hs : 0 < s)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hα : α ≤ 2) (hg : ∀ t, HasDerivAt g (g' t) t)
    (hgA : ∀ t, |g t| ≤ A) (hgB : ∀ t, |g' t| ≤ B / s) :
    MemHolder α (fun p : slab (E := E) a b ↦ g (p : ParabolicSpaceTime E).time) ∧
      (nnHolderNorm α (fun p : slab (E := E) a b ↦ g (p : ParabolicSpaceTime E).time) : ℝ) ≤
        (B + 2 * A) * s ^ (-((α : ℝ) / 2)) := by
  lift A to ℝ≥0 using hA
  lift B to ℝ≥0 using hB
  lift s to ℝ≥0 using hs.le
  have h := holderWith_comp_time (E := E) (a := a) (b := b) (A := A) (A' := B / s) hg
    (fun t ↦ hgA t) (fun t ↦ by simpa using hgB t) hα (by exact_mod_cast hs)
  refine ⟨h.memHolder, (NNReal.coe_le_coe.2 h.nnholderNorm_le).trans_eq ?_⟩
  have hs' : (0 : ℝ) < s := hs
  push_cast
  rw [Real.rpow_sub hs', Real.rpow_one, Real.rpow_neg hs'.le]
  field_simp

/-- A map of the time alone, `(x, t) ↦ g t`, with `g` differentiable and bounded and `g'` bounded
and parabolically `α`-Hölder, belongs to the order-two parabolic Hölder space, with vanishing
spatial derivatives and time derivative `(x, t) ↦ g' t`. -/
private theorem exists_eq_comp_time {a b : ℝ} (hab : a < b) {g g' : ℝ → ℝ} {A A' : ℝ}
    (hg : ∀ t, HasDerivAt g (g' t) t) (hgA : ∀ t, |g t| ≤ A) (hg'c : Continuous g')
    (hg'A : ∀ t, |g' t| ≤ A')
    (hg' : MemHolder α fun p : slab (E := E) a b ↦ g' (p : ParabolicSpaceTime E).time) :
    ∃ χ : ParabolicC2HolderSpace α E ℝ hab,
      (∀ p : slab (E := E) a b, χ p = g (p : ParabolicSpaceTime E).time) ∧
      spatialFDerivL χ = 0 ∧
      ∀ p : slab (E := E) a b, timeDerivL χ p = g' (p : ParabolicSpaceTime E).time := by
  have hcont (g : ℝ → ℝ) (hg : Continuous g) :
      Continuous fun p : slab (E := E) a b ↦ g (p : ParabolicSpaceTime E).time :=
    hg.comp (continuous_time.comp continuous_subtypeVal)
  let u : slab (E := E) a b →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup _
    (hcont g (continuous_iff_continuousAt.2 fun t ↦ (hg t).continuousAt)) A fun p ↦ hgA _
  let ut : HolderSpace α (slab (E := E) a b) ℝ := HolderSpace.ofBoundedContinuousFunction
    (BoundedContinuousFunction.ofNormedAddCommGroup _ (hcont g' hg'c) A'
      fun p ↦ hg'A _) hg'
  have hut (p : slab (E := E) a b) : ut p = g' (p : ParabolicSpaceTime E).time :=
    HolderSpace.ofBoundedContinuousFunction_apply _ hg' p
  refine ⟨mk u 0 0 ut (fun t x ↦ by simpa [u] using hasFDerivAt_const (𝕜 := ℝ) (g t) x)
    (fun t x ↦ by simpa using hasFDerivAt_const (𝕜 := ℝ) (0 : E →L[ℝ] ℝ) x)
    (fun x t ↦ ((hg t).hasDerivWithinAt.congr_of_mem (f₁ := timeExtension hab.le u x)
      (fun τ hτ ↦ by simp [u, timeExtension_def, projIcc_of_mem hab.le hτ]) t.property).congr_deriv
      (by rw [hut, time_slabMk])), fun p ↦ by simp [u], spatialFDerivL_mk ..,
    fun p ↦ by rw [timeDerivL_mk, hut]⟩

open Real in
/-- The first two derivatives of the smooth transition function `ψ`, rescaled to a length scale
`s > 0`, are bounded by the matching powers of `s⁻¹`: `|s⁻¹ ψ'(x)| ≤ L / s` and
`|s⁻¹ ψ''(x) s⁻¹| ≤ L / s²`, for a constant `L` independent of `s`. These are the derivatives of
`ψ (x / s)` and `s⁻¹ ψ' (x / s)`. -/
private theorem exists_forall_abs_inv_mul_deriv_smoothTransition_le :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ {s : ℝ}, 0 < s → ∀ x,
      |s⁻¹ * deriv smoothTransition x| ≤ L / s ∧
        |s⁻¹ * (deriv (deriv smoothTransition) x * s⁻¹)| ≤ L / s / s := by
  obtain ⟨L₁, hL₁⟩ := smoothTransition.exists_forall_norm_deriv_le
  obtain ⟨L₂, hL₂⟩ := smoothTransition.exists_forall_norm_deriv_deriv_le
  refine ⟨max L₁ L₂, (norm_nonneg _).trans ((hL₁ 0).trans (le_max_left _ _)),
    fun {s} hs x ↦ ⟨?_, ?_⟩⟩
  · have h := (hL₁ x).trans (le_max_left L₁ L₂)
    rw [Real.norm_eq_abs] at h
    rw [abs_mul, abs_inv, abs_of_pos hs, inv_mul_eq_div]
    gcongr
  · have h := (hL₂ x).trans (le_max_right L₁ L₂)
    rw [Real.norm_eq_abs] at h
    rw [abs_mul, abs_mul, abs_inv, abs_of_pos hs,
      show ∀ y : ℝ, s⁻¹ * (y * s⁻¹) = y / s / s from fun y ↦ by field_simp]
    gcongr

/-- **Time cutoffs.** For `α ≤ 2` there is a constant `C` such that on every slab `E × [a, b]` and
for every `s > 0` there is a map `χ` of the time alone, in the order-two parabolic Hölder space,
vanishing up to time `s`, equal to one from time `2 s` on, with values in `[0, 1]`, with
`[χ]_{α,par} ≤ C s^(-α/2)`, and with time derivative vanishing before time `s`, bounded by
`C / s` and with `[∂ₜχ]_{α,par} ≤ C s^(-(1 + α/2))`. These are the rescalings `t ↦ ψ (t / s - 1)`
for a fixed smooth step `ψ`. -/
theorem exists_timeCutoff (hα : α ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {a b : ℝ} (hab : a < b) {s : ℝ}, 0 < s →
      ∃ χ : ParabolicC2HolderSpace α E ℝ hab,
        (∀ p : slab (E := E) a b, (p : ParabolicSpaceTime E).time ≤ s → χ p = 0) ∧
        (∀ p : slab (E := E) a b, 2 * s ≤ (p : ParabolicSpaceTime E).time → χ p = 1) ∧
        (∀ p, χ p ∈ Icc 0 1) ∧ spatialFDerivL χ = 0 ∧
        (nnHolderNorm α (valueL χ : slab (E := E) a b → ℝ) : ℝ) ≤ C * s ^ (-((α : ℝ) / 2)) ∧
        (∀ p : slab (E := E) a b, (p : ParabolicSpaceTime E).time < s → timeDerivL χ p = 0) ∧
        (∀ p, |timeDerivL χ p| ≤ C / s) ∧
        (nnHolderNorm α (timeDerivL χ : slab (E := E) a b → ℝ) : ℝ) ≤
          C * s ^ (-(1 + (α : ℝ) / 2)) := by
  open Real in
  obtain ⟨L, hL₀, hL⟩ := exists_forall_abs_inv_mul_deriv_smoothTransition_le
  refine ⟨3 * L + 2, by positivity, fun {a b} hab {s} hs ↦ ?_⟩
  -- The cutoff is `t ↦ ψ (t / s - 1)`, with derivative `t ↦ s⁻¹ ψ' (t / s - 1)`.
  set g₀ : ℝ → ℝ := fun t ↦ smoothTransition (t / s - 1)
  set g₁ : ℝ → ℝ := fun t ↦ s⁻¹ * deriv smoothTransition (t / s - 1)
  have hlin (t : ℝ) : HasDerivAt (fun t ↦ t / s - 1) s⁻¹ t := by
    simpa [div_eq_mul_inv, mul_comm] using ((hasDerivAt_id t).div_const s).sub_const 1
  have hg₀ (t : ℝ) := (hlin t).smoothTransition.congr_deriv (mul_comm _ s⁻¹)
  have hg₁ (t : ℝ) := (hlin t).deriv_smoothTransition.const_mul s⁻¹
  have hb₁ (t : ℝ) := (hL hs (t / s - 1)).1
  have hb₂ (t : ℝ) := (hL hs (t / s - 1)).2
  have hb₀ (t : ℝ) : |g₀ t| ≤ 1 := smoothTransition.abs_le_one _
  -- The Hölder bounds of the value and of the time derivative at the time scale `s`.
  obtain ⟨-, hH₀⟩ := memHolder_comp_time_of_le (E := E) (a := a) (b := b) hs zero_le_one
    hL₀ hα hg₀ hb₀ hb₁
  obtain ⟨hm₁, hH₁⟩ := memHolder_comp_time_of_le (E := E) (a := a) (b := b) hs
    (by positivity : 0 ≤ L / s) (by positivity : 0 ≤ L / s) hα hg₁ hb₁ hb₂
  obtain ⟨χ, hχ, hD, hχt⟩ := exists_eq_comp_time (E := E) hab hg₀ hb₀
    (continuous_iff_continuousAt.2 fun t ↦ (hg₁ t).continuousAt) hb₁ hm₁
  refine ⟨χ, fun p hp ↦ ?_, fun p hp ↦ ?_, fun p ↦ ?_, hD, ?_, fun p hp ↦ ?_, fun p ↦ ?_, ?_⟩
  · exact (hχ p).trans
      (smoothTransition.zero_of_nonpos (by rw [sub_nonpos, div_le_one hs]; exact hp))
  · exact (hχ p).trans
      (smoothTransition.one_of_one_le (by rw [le_sub_iff_add_le, le_div_iff₀ hs]; linarith))
  · exact hχ p ▸ ⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩
  · have h : (valueL χ : slab (E := E) a b → ℝ) =
        fun p : slab (E := E) a b ↦ g₀ (p : ParabolicSpaceTime E).time :=
      funext fun p ↦ (valueL_apply χ p).trans (hχ p)
    rw [h]
    exact hH₀.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  · refine (hχt p).trans ?_
    rw [smoothTransition.deriv_of_nonpos (by rw [sub_nonpos, div_le_one hs]; exact hp.le), mul_zero]
  · exact (congrArg abs (hχt p)).trans_le ((hb₁ _).trans (by gcongr; linarith))
  · have h : (timeDerivL χ : slab (E := E) a b → ℝ) =
        fun p : slab (E := E) a b ↦ g₁ (p : ParabolicSpaceTime E).time := funext hχt
    rw [h]
    refine hH₁.trans ?_
    rw [show -(1 + (α : ℝ) / 2) = -1 + -((α : ℝ) / 2) by ring, Real.rpow_add hs, Real.rpow_neg_one,
      ← mul_assoc, show L / s + 2 * (L / s) = 3 * L * s⁻¹ by ring]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
      (by positivity)

end TimeCutoff

end TauCeti.ParabolicC2HolderSpace
