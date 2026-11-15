/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Hadamard
public import Mathlib.Analysis.Complex.HasPrimitives
import TauCeti.Analysis.Complex.HasPrimitives

/-!
# Vertical strips

Mathlib's three-lines theorem is stated on the open strip `verticalStrip a b` and the closed
strip `verticalClosedStrip a b`, the preimages of `Ioo a b` and `Icc a b` under `Complex.re`.
This file records their membership criteria, behavior under reflection and vertical translation,
convexity, closure, the exponential gauge multiplier `scaleFactor` normalizing strip boundary
bounds, and holomorphic primitives `Complex.wedgeIntegral` for functions satisfying `DiffContOnCl`
on a vertical strip (specializing `TauCeti.Analysis.Complex.HasPrimitives` to
`verticalClosedStrip a b = Icc a b ×ℂ univ`).
-/

public section

open Complex Complex.HadamardThreeLines Set
open scoped Interval Topology

namespace TauCeti.Complex.HadamardThreeLines

variable {a b : ℝ} {z : ℂ}

@[simp]
theorem mem_verticalStrip_iff : z ∈ verticalStrip a b ↔ z.re ∈ Ioo a b :=
  Iff.rfl

@[simp]
theorem mem_verticalClosedStrip_iff : z ∈ verticalClosedStrip a b ↔ z.re ∈ Icc a b :=
  Iff.rfl

/-- Vertical translation preserves open-strip membership. -/
theorem add_mul_I_mem_verticalStrip_iff (z : ℂ) (t : ℝ) :
    z + t * I ∈ verticalStrip a b ↔ z ∈ verticalStrip a b := by simp

/-- Vertical translation preserves closed-strip membership. -/
theorem add_mul_I_mem_verticalClosedStrip_iff (z : ℂ) (t : ℝ) :
    z + t * I ∈ verticalClosedStrip a b ↔ z ∈ verticalClosedStrip a b := by simp

/-- Reflection by `z ↦ w - z` reverses the real endpoints of an open vertical strip. -/
theorem sub_mem_verticalStrip_iff (w z : ℂ) :
    w - z ∈ verticalStrip a b ↔ z ∈ verticalStrip (w.re - b) (w.re - a) := by
  simp only [mem_verticalStrip_iff, mem_Ioo, sub_re]
  constructor <;> rintro ⟨_, _⟩ <;> constructor <;> linarith

/-- Reflection by `z ↦ w - z` reverses the real endpoints of a closed vertical strip. -/
theorem sub_mem_verticalClosedStrip_iff (w z : ℂ) :
    w - z ∈ verticalClosedStrip a b ↔ z ∈ verticalClosedStrip (w.re - b) (w.re - a) := by
  simp only [mem_verticalClosedStrip_iff, mem_Icc, sub_re]
  constructor <;> rintro ⟨_, _⟩ <;> constructor <;> linarith

/-- Reflection in the middle of the unit strip preserves open-strip membership. -/
theorem one_sub_mem_verticalStrip_iff :
    1 - z ∈ verticalStrip 0 1 ↔ z ∈ verticalStrip 0 1 := by
  simpa only [one_re, sub_self, sub_zero] using
    sub_mem_verticalStrip_iff (a := 0) (b := 1) (1 : ℂ) z

/-- Reflection in the middle of the unit strip preserves closed-strip membership. -/
theorem one_sub_mem_verticalClosedStrip_iff :
    1 - z ∈ verticalClosedStrip 0 1 ↔ z ∈ verticalClosedStrip 0 1 := by
  simpa only [one_re, sub_self, sub_zero] using
    sub_mem_verticalClosedStrip_iff (a := 0) (b := 1) (1 : ℂ) z

theorem isOpen_verticalStrip (a b : ℝ) : IsOpen (verticalStrip a b) :=
  isOpen_Ioo.preimage continuous_re

theorem convex_verticalStrip (a b : ℝ) : Convex ℝ (verticalStrip a b) :=
  (convex_Ioo a b).linear_preimage reLm

theorem convex_verticalClosedStrip (a b : ℝ) : Convex ℝ (verticalClosedStrip a b) :=
  (convex_Icc a b).linear_preimage reLm

theorem verticalStrip_subset_verticalClosedStrip (a b : ℝ) :
    verticalStrip a b ⊆ verticalClosedStrip a b :=
  preimage_mono Ioo_subset_Icc_self

theorem closure_verticalStrip_subset (a b : ℝ) :
    closure (verticalStrip a b) ⊆ verticalClosedStrip a b := by
  rw [verticalStrip, closure_preimage_re]
  exact preimage_mono (closure_minimal Ioo_subset_Icc_self isClosed_Icc)

/-- When `a < b`, the closure of the open vertical strip `verticalStrip a b` is the closed strip
`verticalClosedStrip a b`. -/
theorem closure_verticalStrip (hab : a < b) :
    closure (verticalStrip a b) = verticalClosedStrip a b := by
  rw [verticalStrip, closure_preimage_re, closure_Ioo hab.ne, verticalClosedStrip]

section ScaleFactor

/-- The exponential gauge multiplier `exp ((z - 1) * log M₀ - z * log M₁)` on the unit vertical
strip, equal to `M₀ ^ (z - 1) * M₁ ^ (-z)` for `0 < M₀` and `0 < M₁`, with modulus `M₀⁻¹` on
`re z = 0` and `M₁⁻¹` on `re z = 1`. -/
noncomputable def scaleFactor (M₀ M₁ : ℝ) (z : ℂ) : ℂ :=
  exp ((z - 1) * Real.log M₀ - z * Real.log M₁)

variable {M₀ M₁ : ℝ}

theorem differentiable_scaleFactor (M₀ M₁ : ℝ) : Differentiable ℂ (scaleFactor M₀ M₁) := by
  unfold scaleFactor
  fun_prop

theorem norm_scaleFactor (z : ℂ) :
    ‖scaleFactor M₀ M₁ z‖ = Real.exp ((z.re - 1) * Real.log M₀ - z.re * Real.log M₁) := by
  simp [scaleFactor, norm_exp]

theorem norm_scaleFactor_le {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) :
    ‖scaleFactor M₀ M₁ z‖ ≤ Real.exp (|Real.log M₀| + |Real.log M₁|) := by
  rw [norm_scaleFactor]
  refine Real.exp_le_exp.2 ?_
  have hz' := mem_verticalClosedStrip_iff.1 hz
  nlinarith [hz'.1, hz'.2, neg_abs_le (Real.log M₀), le_abs_self (Real.log M₀),
    neg_abs_le (Real.log M₁), le_abs_self (Real.log M₁), abs_nonneg (Real.log M₀),
    abs_nonneg (Real.log M₁)]

theorem norm_scaleFactor_mul_I (hM₀ : 0 < M₀) (t : ℝ) :
    ‖scaleFactor M₀ M₁ (t * I)‖ = M₀⁻¹ := by
  simp [norm_scaleFactor, Real.exp_neg, Real.exp_log hM₀]

theorem norm_scaleFactor_one_add_mul_I (hM₁ : 0 < M₁) (t : ℝ) :
    ‖scaleFactor M₀ M₁ (1 + t * I)‖ = M₁⁻¹ := by
  simp [norm_scaleFactor, Real.exp_neg, Real.exp_log hM₁]

theorem norm_scaleFactor_mul_rpow (hM₀ : 0 < M₀) (hM₁ : 0 < M₁) (θ : ℝ) :
    ‖scaleFactor M₀ M₁ θ‖ * (M₀ ^ (1 - θ) * M₁ ^ θ) = 1 := by
  rw [norm_scaleFactor, Real.rpow_def_of_pos hM₀, Real.rpow_def_of_pos hM₁, ← Real.exp_add,
    ← Real.exp_add, ← Real.exp_zero]
  congr 1
  simp only [ofReal_re]
  ring

theorem hasDerivAt_scaleFactor (M₀ M₁ : ℝ) (z : ℂ) :
    HasDerivAt (scaleFactor M₀ M₁)
      ((Real.log M₀ - Real.log M₁ : ℂ) * scaleFactor M₀ M₁ z) z := by
  set a : ℝ := Real.log M₀ - Real.log M₁
  have heq : scaleFactor M₀ M₁ = fun w : ℂ => exp ((a : ℂ) * w - Real.log M₀) := by
    funext w; simp only [scaleFactor, a]; congr 1; push_cast; ring
  have hlin : HasDerivAt (fun w : ℂ => (a : ℂ) * w - Real.log M₀) (a : ℂ) z := by
    simpa using ((hasDerivAt_id z).const_mul (a : ℂ)).sub_const (Real.log M₀ : ℂ)
  rw [heq]
  convert hlin.cexp using 1
  simp only [a]; push_cast; ring

theorem integral_deriv_scaleFactor_add_mul_I (M₀ M₁ c t₀ t : ℝ) :
    (∫ u in t₀..t,
      ((Real.log M₀ - Real.log M₁ : ℂ) * I) * scaleFactor M₀ M₁ (c + u * I)) =
      scaleFactor M₀ M₁ (c + t * I) - scaleFactor M₀ M₁ (c + t₀ * I) := by
  have hd (u : ℝ) : HasDerivAt (fun x : ℝ => scaleFactor M₀ M₁ (c + x * I))
      (((Real.log M₀ - Real.log M₁ : ℂ) * I) * scaleFactor M₀ M₁ (c + u * I)) u := by
    have hφ : HasDerivAt (fun x : ℝ => (c : ℂ) + (x : ℂ) * I) I u := by
      simpa using (Complex.ofRealCLM.hasDerivAt.mul_const I).const_add (c : ℂ)
    exact ((hasDerivAt_scaleFactor M₀ M₁ (c + u * I)).comp u hφ).congr_deriv (mul_right_comm _ _ _)
  have hcont : Continuous fun u : ℝ =>
      ((Real.log M₀ - Real.log M₁ : ℂ) * I) * scaleFactor M₀ M₁ (c + u * I) :=
    continuous_const.mul ((differentiable_scaleFactor M₀ M₁).continuous.comp (by fun_prop))
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    (hcont.intervalIntegrable _ _)

end ScaleFactor

end TauCeti.Complex.HadamardThreeLines

section Primitive

open TauCeti.Complex.HadamardThreeLines

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℂ → E} {a b : ℝ}

private theorem reProdIm_Icc_univ (a b : ℝ) :
    Icc a b ×ℂ (univ : Set ℝ) = verticalClosedStrip a b := by
  ext; simp [verticalClosedStrip, mem_reProdIm]

/-- For `a < b`, a function satisfying `DiffContOnCl ℂ f (verticalStrip a b)` is continuous on
`verticalClosedStrip a b`. -/
theorem DiffContOnCl.continuousOn_verticalClosedStrip (hab : a < b)
    (hf : DiffContOnCl ℂ f (verticalStrip a b)) :
    ContinuousOn f (verticalClosedStrip a b) :=
  closure_verticalStrip hab ▸ hf.continuousOn

/-- Cauchy–Goursat on the closed vertical strip: a function holomorphic on `verticalStrip a b` and
continuous up to its boundary has zero integral around every closed rectangle in
`verticalClosedStrip a b`, even when the rectangle meets the boundary lines. -/
theorem DiffContOnCl.isConservativeOn_verticalClosedStrip (hab : a < b)
    (hf : DiffContOnCl ℂ f (verticalStrip a b)) :
    IsConservativeOn f (verticalClosedStrip a b) := by
  rintro z w hzw
  rw [← add_eq_zero_iff_eq_neg, wedgeIntegral_add_wedgeIntegral_eq]
  refine integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn f z w
    ((hf.continuousOn_verticalClosedStrip hab).mono hzw) (hf.differentiableOn.mono fun u hu => ?_)
  have hz : z ∈ verticalClosedStrip a b := hzw ⟨left_mem_uIcc, left_mem_uIcc⟩
  have hw : w ∈ verticalClosedStrip a b := hzw ⟨right_mem_uIcc, right_mem_uIcc⟩
  exact ⟨(le_min hz.1 hw.1).trans_lt hu.1.1, hu.1.2.trans_le (max_le hz.2 hw.2)⟩

/-- Wedge integrals of a function satisfying `DiffContOnCl` on a vertical strip are additive across
arbitrary points of the closed strip, including boundary points. -/
theorem DiffContOnCl.wedgeIntegral_sub_wedgeIntegral_eq_of_mem_verticalClosedStrip (hab : a < b)
    (hf : DiffContOnCl ℂ f (verticalStrip a b)) {z₀ z w : ℂ}
    (hz₀ : z₀ ∈ verticalClosedStrip a b) (hz : z ∈ verticalClosedStrip a b)
    (hw : w ∈ verticalClosedStrip a b) :
    wedgeIntegral z₀ w f - wedgeIntegral z₀ z f = wedgeIntegral z w f := by
  have hcons : IsConservativeOn f (Icc a b ×ℂ (univ : Set ℝ)) :=
    reProdIm_Icc_univ a b ▸ hf.isConservativeOn_verticalClosedStrip hab
  exact hcons.wedgeIntegral_sub_wedgeIntegral_eq_of_mem_reProdIm ordConnected_Icc ordConnected_univ
    (reProdIm_Icc_univ a b ▸ hf.continuousOn_verticalClosedStrip hab)
    (reProdIm_Icc_univ a b ▸ hz₀) (reProdIm_Icc_univ a b ▸ hz) (reProdIm_Icc_univ a b ▸ hw)

/-- The wedge integral on a closed vertical strip is continuous up to the boundary. -/
theorem DiffContOnCl.continuousOn_wedgeIntegral_verticalClosedStrip (hab : a < b)
    (hf : DiffContOnCl ℂ f (verticalStrip a b)) {z₀ : ℂ} (hz₀ : z₀ ∈ verticalClosedStrip a b) :
    ContinuousOn (fun z => wedgeIntegral z₀ z f) (verticalClosedStrip a b) := by
  intro z hz
  let K : Set ℂ := Icc a b ×ℂ Icc (z.im - 1) (z.im + 1)
  have hK_sub : K ⊆ verticalClosedStrip a b := fun _ hu => hu.1
  obtain ⟨M, hM⟩ := (isCompact_Icc.reProdIm isCompact_Icc).exists_bound_of_continuousOn
    ((hf.continuousOn_verticalClosedStrip hab).mono hK_sub)
  have hzero : Filter.Tendsto (fun w => wedgeIntegral z w f)
      (𝓝[verticalClosedStrip a b] z) (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun w => 2 * M * ‖w - z‖) ?_ ?_
    · filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds z zero_lt_one),
        self_mem_nhdsWithin] with w hwball hw
      have him : |w.im - z.im| ≤ 1 :=
        (abs_im_le_norm (w - z)).trans ((dist_eq_norm w z).symm.trans_lt hwball).le
      refine TauCeti.norm_wedgeIntegral_le_of_norm_le_const fun u hu =>
        hM u ⟨ordConnected_Icc.uIcc_subset hz hw hu.1, ?_⟩
      have hu_im := abs_le.1 ((abs_sub_left_of_mem_uIcc hu.2).trans him)
      exact ⟨by linarith, by linarith⟩
    · have : Filter.Tendsto (fun w => 2 * M * ‖w - z‖) (𝓝 z) (𝓝 0) := by
        simpa using ((continuous_id.sub (continuous_const (y := z))).norm.const_mul
          (2 * M)).tendsto z
      exact this.mono_left nhdsWithin_le_nhds
  refine Metric.tendsto_nhdsWithin_nhds.2 fun ε hε => ?_
  obtain ⟨δ, hδ, hδε⟩ := Metric.tendsto_nhdsWithin_nhds.1 hzero ε hε
  refine ⟨δ, hδ, fun {w} hw hdist => ?_⟩
  rw [dist_eq_norm,
    hf.wedgeIntegral_sub_wedgeIntegral_eq_of_mem_verticalClosedStrip hab hz₀ hz hw]
  simpa [dist_eq_norm] using hδε hw hdist

/-- On the open vertical strip, the wedge integral from any base point in the closed strip has
complex derivative equal to its integrand. -/
theorem DiffContOnCl.hasDerivAt_wedgeIntegral_verticalStrip [CompleteSpace E] (hab : a < b)
    (hf : DiffContOnCl ℂ f (verticalStrip a b)) {z₀ z : ℂ}
    (hz₀ : z₀ ∈ verticalClosedStrip a b) (hz : z ∈ verticalStrip a b) :
    HasDerivAt (fun w => wedgeIntegral z₀ w f) (f z) z :=
  (reProdIm_Icc_univ a b ▸
      hf.isConservativeOn_verticalClosedStrip hab).hasDerivAt_wedgeIntegral_of_mem_reProdIm
    ordConnected_Icc ordConnected_univ
    (reProdIm_Icc_univ a b ▸ hf.continuousOn_verticalClosedStrip hab)
    (reProdIm_Icc_univ a b ▸ hz₀)
    (Filter.mem_of_superset ((isOpen_verticalStrip a b).mem_nhds hz)
      ((verticalStrip_subset_verticalClosedStrip a b).trans (reProdIm_Icc_univ a b).symm.subset))

/-- The wedge integral of a function satisfying `DiffContOnCl` on a vertical strip again satisfies
`DiffContOnCl` on that strip. -/
theorem DiffContOnCl.diffContOnCl_wedgeIntegral_verticalStrip [CompleteSpace E] (hab : a < b)
    (hf : DiffContOnCl ℂ f (verticalStrip a b)) {z₀ : ℂ}
    (hz₀ : z₀ ∈ verticalClosedStrip a b) :
    DiffContOnCl ℂ (fun w => wedgeIntegral z₀ w f) (verticalStrip a b) :=
  ⟨fun _ hz => (hf.hasDerivAt_wedgeIntegral_verticalStrip hab hz₀
      hz).differentiableAt.differentiableWithinAt,
    closure_verticalStrip hab ▸ hf.continuousOn_wedgeIntegral_verticalClosedStrip hab hz₀⟩

end Primitive
