/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.TwistMap.OpenStrip
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import TauCeti.Analysis.Calculus.FDeriv.Prod

/-!
# Examples of monotone twist maps of an open strip

Checks for `TauCeti.IsMonotoneTwistMap` (Katok–Hasselblatt, *Introduction to the Modern Theory of
Dynamical Systems*, Section 9.3).

* The standard map `(x, y) ↦ (x + y + ε sin 2πx, y + ε sin 2πx)` of the plane, the open strip
  `ℝ × ℝ`, is a monotone twist map with period `1` for every `ε`, with `∂F₁/∂y = 1`
  (`TauCeti.isMonotoneTwistMap_standardMap`).
* On the strip `ℝ × (0, ∞)`, the map `(x, y) ↦ (x + log y, y)` preserves both ends, which here
  are `0` and `∞`, and has `∂F₁/∂y = 1/y > 0` (`TauCeti.isMonotoneTwistMap_logShear`). Conjugating
  it by the decreasing involution `y ↦ 1/y` of `(0, ∞)` gives `(x, y) ↦ (x - log y, y)`, whose
  first coordinate decreases in `y`, with derivative `-1/y`
  (`TauCeti.logShear_conj_inv`, `TauCeti.strictAntiOn_conj_logShear_fst`,
  `TauCeti.hasDerivAt_conj_logShear_fst`). This illustrates, for this map, that conjugation by a
  decreasing map of the heights reverses the sign of the twist.
-/

public section

noncomputable section

open Set Real

namespace TauCeti

/-- The **standard map** `(x, y) ↦ (x + y + ε sin 2πx, y + ε sin 2πx)` of the plane, a
homeomorphism with inverse `(x, y) ↦ (x - y, y - ε sin 2π(x - y))`. -/
def standardMap (ε : ℝ) : ℝ × ℝ ≃ₜ ℝ × ℝ where
  toFun p := (p.1 + p.2 + ε * sin (2 * π * p.1), p.2 + ε * sin (2 * π * p.1))
  invFun p := (p.1 - p.2, p.2 - ε * sin (2 * π * (p.1 - p.2)))
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp]
theorem standardMap_apply (ε : ℝ) (p : ℝ × ℝ) :
    standardMap ε p = (p.1 + p.2 + ε * sin (2 * π * p.1), p.2 + ε * sin (2 * π * p.1)) :=
  (rfl)

@[simp]
theorem standardMap_symm_apply (ε : ℝ) (p : ℝ × ℝ) :
    (standardMap ε).symm p = (p.1 - p.2, p.2 - ε * sin (2 * π * (p.1 - p.2))) :=
  (rfl)

/-- The standard map is a monotone twist map of the plane with period `1`, for every `ε`. -/
theorem isMonotoneTwistMap_standardMap (ε : ℝ) :
    IsMonotoneTwistMap 1 univ (standardMap ε).toOpenPartialHomeomorph := by
  have hs : ContDiff ℝ 1 (standardMap ε) := by
    rw [show ⇑(standardMap ε) = _ from funext (standardMap_apply ε)]
    fun_prop
  have hsymm : ContDiff ℝ 1 (standardMap ε).symm := by
    rw [show ⇑(standardMap ε).symm = _ from funext (standardMap_symm_apply ε)]
    fun_prop
  have hbound (x : ℝ) : |ε * sin (2 * π * x)| ≤ |ε| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg ε) (abs_sin_le_one _)
  refine
    { period_pos := one_pos
      nonempty := univ_nonempty
      isOpen := isOpen_univ
      ordConnected := ordConnected_univ
      source_eq := univ_prod_univ.symm
      target_eq := univ_prod_univ.symm
      apply_add_period := fun x y _ => ?_
      strictMonoOn_fst := fun x y₁ _ y₂ _ h => ?_
      lower_end := fun c _ => ⟨c - |ε|, mem_univ _, fun x y _ hy => ?_⟩
      upper_end := fun c _ => ⟨c + |ε|, mem_univ _, fun x y _ hy => ?_⟩
      contDiffOn := hs.contDiffOn
      contDiffOn_symm := hsymm.contDiffOn
      fderiv_fst_pos := fun p _ => ?_ }
  · have : sin (2 * π * (x + 1)) = sin (2 * π * x) := by
      rw [mul_add, mul_one, sin_add_two_pi]
    simp only [Homeomorph.toOpenPartialHomeomorph_apply, standardMap_apply, this,
      Prod.mk_add_mk, add_zero]
    ext <;> ring
  · simp only [Homeomorph.toOpenPartialHomeomorph_apply, standardMap_apply]
    linarith
  · simp only [Homeomorph.toOpenPartialHomeomorph_apply, standardMap_apply]
    linarith [(abs_le.1 (hbound x)).2]
  · simp only [Homeomorph.toOpenPartialHomeomorph_apply, standardMap_apply]
    linarith [(abs_le.1 (hbound x)).1]
  · have h1 : HasDerivAt (fun x : ℝ => x + ε * sin (2 * π * x))
        (1 + ε * (cos (2 * π * p.1) * (2 * π))) p.1 := by
      convert (hasDerivAt_id' p.1).add
        (((hasDerivAt_id' p.1).const_mul (2 * π)).sin.const_mul ε) using 1
      ring
    have hL : HasFDerivAt (fun q => (standardMap ε q).1) (ContinuousLinearMap.snd ℝ ℝ ℝ +
        (1 + ε * (cos (2 * π * p.1) * (2 * π))) • ContinuousLinearMap.fst ℝ ℝ ℝ) p := by
      convert hasFDerivAt_snd.add (h1.comp_hasFDerivAt p (hasFDerivAt_fst (𝕜 := ℝ))) using 1
      ext q
      simp only [standardMap_apply, Pi.add_apply, Function.comp_apply]
      ring
    rw [Homeomorph.toOpenPartialHomeomorph_apply,
      fderiv_apply_fst (hs.differentiable one_ne_zero p) hL]
    simp

/-- The map `(x, y) ↦ (x + log y, y)` as a homeomorphism of the strip `ℝ × (0, ∞)`, with inverse
`(x, y) ↦ (x - log y, y)`. -/
def logShear : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) where
  toFun p := (p.1 + log p.2, p.2)
  invFun p := (p.1 - log p.2, p.2)
  source := univ ×ˢ Ioi 0
  target := univ ×ˢ Ioi 0
  map_source' _ hp := hp
  map_target' _ hp := hp
  left_inv' p _ := by simp
  right_inv' p _ := by simp
  open_source := isOpen_univ.prod isOpen_Ioi
  open_target := isOpen_univ.prod isOpen_Ioi
  continuousOn_toFun := by
    refine ContinuousOn.prodMk ?_ continuousOn_snd
    exact continuousOn_fst.add (continuousOn_snd.log fun p hp => (ne_of_gt hp.2))
  continuousOn_invFun := by
    refine ContinuousOn.prodMk ?_ continuousOn_snd
    exact continuousOn_fst.sub (continuousOn_snd.log fun p hp => (ne_of_gt hp.2))

@[simp]
theorem logShear_apply (p : ℝ × ℝ) : logShear p = (p.1 + log p.2, p.2) :=
  (rfl)

@[simp]
theorem logShear_symm_apply (p : ℝ × ℝ) : logShear.symm p = (p.1 - log p.2, p.2) :=
  (rfl)

@[simp]
theorem logShear_source : logShear.source = univ ×ˢ Ioi 0 :=
  (rfl)

@[simp]
theorem logShear_target : logShear.target = univ ×ˢ Ioi 0 :=
  (rfl)

/-- The map `(x, y) ↦ (x + log y, y)` is a monotone twist map of the strip `ℝ × (0, ∞)`, for every
positive period: it preserves both ends `0` and `∞`, and `∂F₁/∂y = 1/y > 0`. -/
theorem isMonotoneTwistMap_logShear {ℓ : ℝ} (hℓ : 0 < ℓ) :
    IsMonotoneTwistMap ℓ (Ioi 0) logShear := by
  have hU : IsOpen (univ ×ˢ Ioi (0 : ℝ)) := (isOpen_univ (X := ℝ)).prod isOpen_Ioi
  have hlog : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => log p.2) (univ ×ˢ Ioi 0) :=
    ContDiffOn.log (contDiffOn_snd (𝕜 := ℝ)) fun p hp => ne_of_gt hp.2
  have hC : ContDiffOn ℝ 1 logShear (univ ×ˢ Ioi 0) :=
    (contDiffOn_fst.add hlog).prodMk contDiffOn_snd
  refine
    { period_pos := hℓ
      nonempty := nonempty_Ioi
      isOpen := isOpen_Ioi
      ordConnected := ordConnected_Ioi
      source_eq := rfl
      target_eq := rfl
      apply_add_period := fun x y _ => ?_
      strictMonoOn_fst := fun x y₁ hy₁ y₂ _ h => ?_
      lower_end := fun c hc => ⟨c, hc, fun _ _ _ hy => by simpa [logShear_apply] using hy⟩
      upper_end := fun c hc => ⟨c, hc, fun _ _ _ hy => by simpa [logShear_apply] using hy⟩
      contDiffOn := hC
      contDiffOn_symm := (contDiffOn_fst.sub hlog).prodMk contDiffOn_snd
      fderiv_fst_pos := fun p hp => ?_ }
  · ext
    · simp only [logShear_apply, Prod.fst_add]
      ring
    · simp [logShear_apply]
  · simpa [logShear_apply] using log_lt_log hy₁ h
  · have hp2 : p.2 ≠ 0 := ne_of_gt hp.2
    have hL : HasFDerivAt (fun q : ℝ × ℝ => (logShear q).1)
        (ContinuousLinearMap.fst ℝ ℝ ℝ + p.2⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
      hasFDerivAt_fst.add ((hasDerivAt_log hp2).comp_hasFDerivAt p hasFDerivAt_snd)
    have hF : DifferentiableAt ℝ logShear p :=
      (hC.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hp)
    rw [fderiv_apply_fst hF hL]
    simpa using hp.2

/-- The height inversion `(x, y) ↦ (x, y⁻¹)`, an involution of the strip `ℝ × (0, ∞)` decreasing
in `y`, used to conjugate `logShear`. -/
def invHeight (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1, p.2⁻¹)

@[simp]
theorem invHeight_apply (p : ℝ × ℝ) : invHeight p = (p.1, p.2⁻¹) :=
  (rfl)

/-- Conjugating `(x, y) ↦ (x + log y, y)` by `y ↦ 1/y` gives `(x, y) ↦ (x - log y, y)`. -/
theorem logShear_conj_inv (p : ℝ × ℝ) : invHeight (logShear (invHeight p)) = logShear.symm p := by
  simp [log_inv, sub_eq_add_neg]

/-- The conjugate `(x, y) ↦ (x - log y, y)` twists negatively on `ℝ × (0, ∞)`: its first
coordinate is strictly decreasing on every vertical. -/
theorem strictAntiOn_conj_logShear_fst (x : ℝ) :
    StrictAntiOn (fun y => (invHeight (logShear (invHeight (x, y)))).1) (Ioi 0) := by
  simp only [logShear_conj_inv, logShear_symm_apply]
  exact fun y₁ hy₁ y₂ _ h => by simpa using log_lt_log hy₁ h

/-- The first coordinate of the conjugate `(x, y) ↦ (x - log y, y)` has derivative `-1/y` in `y`
at every `y > 0`. -/
theorem hasDerivAt_conj_logShear_fst (x : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun y => (invHeight (logShear (invHeight (x, y)))).1) (-y⁻¹) y := by
  simp only [logShear_conj_inv, logShear_symm_apply]
  simpa using (hasDerivAt_log (ne_of_gt hy)).const_sub x

end TauCeti
