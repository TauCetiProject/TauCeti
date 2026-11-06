/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pompeiu.Holder.Gain
public import TauCeti.Analysis.Holder.Normed
import TauCeti.Topology.MetricSpace.Holder
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Bounded value and derivative operators for the actual Cauchy transform

The source is the native bounded Hölder subspace supported in a fixed input disc.
`cauchyValueCLM` takes values on the output disc with the supremum norm, and
`cauchyDerivativeCLM` takes actual real derivatives with the supremum-plus-Hölder norm.
Their product `cauchyTransformCLM` carries the local `C^{1,α}` norm
`max ‖T f‖_∞ (‖D T f‖_∞ + [D T f]_α)`. All three operators are bounded and real linear, so
continuous source families remain continuous in the respective complete target norms.
-/

public noncomputable section

open Complex Metric MeasureTheory Set
open scoped NNReal ContDiff BoundedContinuousFunction

namespace TauCeti

private def normalizedCauchy {α : ℝ≥0} {c : ℂ} {r : ℝ}
    (f : supportedHolderSubmodule (Y := ℂ) α (closedBall c r)) : ℂ → ℂ :=
  fun w ↦ (Real.pi : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • (f : HolderSpace α ℂ ℂ) z

private theorem source_bound {α : ℝ≥0} (f : HolderSpace α ℂ ℂ) (z : ℂ) :
    ‖f z‖ ≤ ‖f.toBoundedContinuousFunction‖₊ := by
  simpa only [HolderSpace.toBoundedContinuousFunction_apply, coe_nnnorm] using
    f.toBoundedContinuousFunction.norm_coe_le_norm z

private theorem source_gain {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {c : ℂ} {r R : ℝ}
    (hr : 0 ≤ r) (hR : 0 ≤ R) (f : supportedHolderSubmodule (Y := ℂ) α (closedBall c r)) :
    ContDiffOn ℝ 1 (normalizedCauchy f) (ball c (R + 1)) ∧
      ∃ B : ℝ≥0, HolderOnWith B α (fderiv ℝ (normalizedCauchy f)) (closedBall c R) := by
  obtain ⟨C, hC⟩ :=
    exists_contDiffOn_holderOnWith_fderiv_pi_inv_smul_integral_sub_inv_smul hα hα1 c hr hR
  obtain ⟨hcd, hH, -, -⟩ := hC (support_subset_of_mem_supportedHolderSubmodule f.property)
    f.1.holderWith (source_bound f.1)
  exact ⟨hcd, _, hH⟩

private def cauchyDerivativeHolder {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {c : ℂ} {r R : ℝ}
    (hr : 0 ≤ r) (hR : 0 ≤ R) (f : supportedHolderSubmodule (Y := ℂ) α (closedBall c r)) :
    HolderSpace α (closedBall c R) (ℂ →L[ℝ] ℂ) := by
  let B := Classical.choose (source_gain hα hα1 hr hR f).2
  have hB := Classical.choose_spec (source_gain hα hα1 hr hR f).2
  let F : closedBall c R →ᵇ (ℂ →L[ℝ] ℂ) := BoundedContinuousFunction.mkOfCompact
    ⟨(closedBall c R).domRestrict (fderiv ℝ (normalizedCauchy f)),
      (hB.continuousOn hα).domRestrict⟩
  have hFH : HolderWith B α (F : closedBall c R → (ℂ →L[ℝ] ℂ)) :=
    fun x y ↦ hB x x.property y y.property
  exact HolderSpace.ofBoundedContinuousFunction F hFH.memHolder

private theorem cauchyDerivativeHolder_apply {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    {c : ℂ} {r R : ℝ} (hr : 0 ≤ r) (hR : 0 ≤ R)
    (f : supportedHolderSubmodule (Y := ℂ) α (closedBall c r)) (x : closedBall c R) :
    cauchyDerivativeHolder hα hα1 hr hR f x = fderiv ℝ (normalizedCauchy f) x := by
  unfold cauchyDerivativeHolder
  dsimp only
  rw [← HolderSpace.toBoundedContinuousFunction_apply,
    HolderSpace.toBoundedContinuousFunction_ofBoundedContinuousFunction,
    BoundedContinuousFunction.mkOfCompact_apply]
  exact domRestrict_apply _ _ _

private theorem integrable_cauchy_source {α : ℝ≥0} {c : ℂ} {r : ℝ}
    (f : supportedHolderSubmodule (Y := ℂ) α (closedBall c r)) (w : ℂ) :
    Integrable (fun z ↦ (w - z)⁻¹ • (f : HolderSpace α ℂ ℂ) z) :=
  (Complex.locallyIntegrable_sub_inv w).integrable_smul_right_of_hasCompactSupport
    (HolderSpace.continuous f.1)
    (HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall c r)
      (support_subset_of_mem_supportedHolderSubmodule f.property))

private theorem normalizedCauchy_add {α : ℝ≥0} {c : ℂ} {r : ℝ}
    (f g : supportedHolderSubmodule (Y := ℂ) α (closedBall c r)) :
    normalizedCauchy (f + g : supportedHolderSubmodule (Y := ℂ) α (closedBall c r)) =
      fun w ↦ normalizedCauchy f w + normalizedCauchy g w := by
  funext w
  simp only [normalizedCauchy, Submodule.coe_add, HolderSpace.add_apply, smul_add]
  rw [integral_add (integrable_cauchy_source f w) (integrable_cauchy_source g w), smul_add]

private theorem normalizedCauchy_smul {α : ℝ≥0} {c : ℂ} {r : ℝ}
    (a : ℝ) (f : supportedHolderSubmodule (Y := ℂ) α (closedBall c r)) :
    normalizedCauchy (a • f : supportedHolderSubmodule (Y := ℂ) α (closedBall c r)) =
      fun w ↦ a • normalizedCauchy f w := by
  funext w
  simp only [normalizedCauchy, Submodule.coe_smul, HolderSpace.smul_apply]
  simp_rw [smul_comm (w - _)⁻¹ a]
  rw [integral_smul, smul_comm]

private theorem source_differentiableAt {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    {c : ℂ} {r R : ℝ} (hr : 0 ≤ r) (hR : 0 ≤ R)
    (f : supportedHolderSubmodule (Y := ℂ) α (closedBall c r)) (x : closedBall c R) :
    DifferentiableAt ℝ (normalizedCauchy f) (x : ℂ) := by
  have h := (source_gain hα hα1 hr hR f).1.contDiffAt
    (isOpen_ball.mem_nhds (closedBall_subset_ball (by linarith) x.property))
  exact h.differentiableAt one_ne_zero

private def cauchyDerivativeLinearMap {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    {c : ℂ} {r R : ℝ} (hr : 0 ≤ r) (hR : 0 ≤ R) :
    supportedHolderSubmodule (Y := ℂ) α (closedBall c r) →ₗ[ℝ]
      HolderSpace α (closedBall c R) (ℂ →L[ℝ] ℂ) where
  toFun := cauchyDerivativeHolder hα hα1 hr hR
  map_add' f g := by
    apply HolderSpace.ext
    intro x
    simp only [cauchyDerivativeHolder_apply, HolderSpace.add_apply]
    rw [normalizedCauchy_add]
    exact fderiv_add (source_differentiableAt hα hα1 hr hR f x)
      (source_differentiableAt hα hα1 hr hR g x)
  map_smul' a f := by
    apply HolderSpace.ext
    intro x
    simp only [cauchyDerivativeHolder_apply, HolderSpace.smul_apply, RingHom.id_apply]
    rw [normalizedCauchy_smul]
    exact ((source_differentiableAt hα hα1 hr hR f x).hasFDerivAt.const_smul a).fderiv

private theorem exists_norm_cauchyDerivativeLinearMap_le {α : ℝ≥0}
    (hα : 0 < α) (hα1 : α < 1) {c : ℂ} {r R : ℝ} (hr : 0 ≤ r) (hR : 0 ≤ R) :
    ∃ B : ℝ, ∀ f : supportedHolderSubmodule (Y := ℂ) α (closedBall c r),
      ‖cauchyDerivativeLinearMap hα hα1 hr hR f‖ ≤ B * ‖f‖ := by
  obtain ⟨C, hC⟩ :=
    exists_contDiffOn_holderOnWith_fderiv_pi_inv_smul_integral_sub_inv_smul hα hα1 c hr hR
  refine ⟨2 * C, fun f ↦ ?_⟩
  let u := cauchyDerivativeHolder hα hα1 hr hR f
  let H := nnHolderNorm α (f : HolderSpace α ℂ ℂ)
  let M := ‖(f : HolderSpace α ℂ ℂ).toBoundedContinuousFunction‖₊
  obtain ⟨-, hH, hN, -⟩ := hC (support_subset_of_mem_supportedHolderSubmodule f.property)
    f.1.holderWith (source_bound f.1)
  -- Match the integral representative and the local source seminorm abbreviations.
  change HolderOnWith (C * (H + M)) α (fderiv ℝ (normalizedCauchy f)) (closedBall c R) at hH
  -- The norm bound uses the same representative and source abbreviations.
  change ∀ x ∈ closedBall c R, ‖fderiv ℝ (normalizedCauchy f) x‖ ≤
    (C * (H + M) : ℝ≥0) at hN
  have hU : HolderWith (C * (H + M)) α (u.toBoundedContinuousFunction : closedBall c R →
      (ℂ →L[ℝ] ℂ)) := by
    intro x y
    rw [HolderSpace.toBoundedContinuousFunction_apply,
      HolderSpace.toBoundedContinuousFunction_apply]
    -- Expose the let-bound derivative field after its native HolderSpace coercion.
    change edist (cauchyDerivativeHolder hα hα1 hr hR f x)
      (cauchyDerivativeHolder hα hα1 hr hR f y) ≤ _
    rw [cauchyDerivativeHolder_apply, cauchyDerivativeHolder_apply]
    exact hH x x.property y y.property
  have hUN : ‖u.toBoundedContinuousFunction‖ ≤ (C * (H + M) : ℝ≥0) := by
    apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro x
    rw [HolderSpace.toBoundedContinuousFunction_apply]
    -- Expose the same let-bound derivative field in the pointwise norm bound.
    change ‖cauchyDerivativeHolder hα hα1 hr hR f x‖ ≤ _
    rw [cauchyDerivativeHolder_apply]
    exact hN x x.property
  have hHN : nnHolderNorm α (u.toBoundedContinuousFunction : closedBall c R →
      (ℂ →L[ℝ] ℂ)) ≤ C * (H + M) :=
    ENNReal.coe_le_coe.mp (coe_nnHolderNorm_le_eHolderNorm.trans hU.eHolderNorm_le)
  have hsum : (H + M : ℝ≥0) = ‖f‖ := by
    rw [← Submodule.norm_coe]
    rw [HolderSpace.norm_def]
    simp only [H, M, NNReal.coe_add, coe_nnnorm, HolderSpace.coe_toBoundedContinuousFunction]
    ring
  -- The linear-map structure evaluates to the chosen derivative HolderSpace representative.
  change ‖u‖ ≤ (2 * C) * ‖f‖
  calc
    _ = ‖u.toBoundedContinuousFunction‖ +
        nnHolderNorm α (u.toBoundedContinuousFunction : closedBall c R → (ℂ →L[ℝ] ℂ)) :=
      HolderSpace.norm_def u
    _ ≤ (C * (H + M) : ℝ≥0) + (C * (H + M) : ℝ≥0) :=
      add_le_add hUN (by exact_mod_cast hHN)
    _ = _ := by rw [← hsum]; push_cast; ring

/-- The derivative of the actual normalized Cauchy integral, restricted to a fixed output
disc, is a bounded real-linear operator on the fixed-support Hölder source space. -/
def cauchyDerivativeCLM {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {c : ℂ} {r R : ℝ}
    (hr : 0 ≤ r) (hR : 0 ≤ R) :
    supportedHolderSubmodule (Y := ℂ) α (closedBall c r) →L[ℝ]
      HolderSpace α (closedBall c R) (ℂ →L[ℝ] ℂ) :=
  (cauchyDerivativeLinearMap hα hα1 hr hR).mkContinuous
    (Classical.choose (exists_norm_cauchyDerivativeLinearMap_le hα hα1 hr hR))
    (Classical.choose_spec (exists_norm_cauchyDerivativeLinearMap_le hα hα1 hr hR))

/-- The bounded operator is the real derivative of the actual `π⁻¹` Cauchy kernel integral. -/
@[simp]
theorem cauchyDerivativeCLM_apply {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    {c : ℂ} {r R : ℝ} (hr : 0 ≤ r) (hR : 0 ≤ R)
    (f : supportedHolderSubmodule (Y := ℂ) α (closedBall c r)) (x : closedBall c R) :
    cauchyDerivativeCLM hα hα1 hr hR f x =
      fderiv ℝ (fun w : ℂ ↦ (Real.pi : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ •
        (f : HolderSpace α ℂ ℂ) z) (x : ℂ) := by
  exact cauchyDerivativeHolder_apply hα hα1 hr hR f x

private def cauchyValue {α : ℝ≥0} (hα : 0 < α) {c : ℂ} {r R : ℝ}
    (hr : 0 ≤ r) (hR : 0 ≤ R) (f : supportedHolderSubmodule (Y := ℂ) α (closedBall c r)) :
    closedBall c R →ᵇ ℂ := by
  have h := holderOnWith_pi_inv_smul_integral_sub_inv_smul hα f.1.holderWith
    hr hR (support_subset_of_mem_supportedHolderSubmodule f.property)
  exact BoundedContinuousFunction.mkOfCompact
    ⟨(closedBall c R).domRestrict (normalizedCauchy f), (h.continuousOn hα).domRestrict⟩

private theorem cauchyValue_apply {α : ℝ≥0} (hα : 0 < α) {c : ℂ} {r R : ℝ}
    (hr : 0 ≤ r) (hR : 0 ≤ R) (f : supportedHolderSubmodule (Y := ℂ) α (closedBall c r))
    (x : closedBall c R) :
    cauchyValue hα hr hR f x = normalizedCauchy f x := by
  unfold cauchyValue
  dsimp only
  rw [BoundedContinuousFunction.mkOfCompact_apply]
  -- mkOfCompact retains a continuous-map wrapper; expose its underlying restriction so
  -- the public domRestrict application law matches the goal.
  change (closedBall c R).domRestrict (normalizedCauchy f) x = _
  exact domRestrict_apply _ _ _

private def cauchyValueLinearMap {α : ℝ≥0} (hα : 0 < α) {c : ℂ} {r R : ℝ}
    (hr : 0 ≤ r) (hR : 0 ≤ R) :
    supportedHolderSubmodule (Y := ℂ) α (closedBall c r) →ₗ[ℝ] (closedBall c R →ᵇ ℂ) where
  toFun := cauchyValue hα hr hR
  map_add' f g := by
    apply BoundedContinuousFunction.ext
    intro x
    simp only [cauchyValue_apply, add_apply]
    rw [normalizedCauchy_add]
  map_smul' a f := by
    apply BoundedContinuousFunction.ext
    intro x
    simp only [cauchyValue_apply, smul_apply, RingHom.id_apply]
    rw [normalizedCauchy_smul]

/-- The values of the actual normalized Cauchy transform on the output disc, as a bounded
linear operator in the source Hölder norm. -/
def cauchyValueCLM {α : ℝ≥0} (hα : 0 < α) {c : ℂ} {r R : ℝ}
    (hr : 0 ≤ r) (hR : 0 ≤ R) :
    supportedHolderSubmodule (Y := ℂ) α (closedBall c r) →L[ℝ] (closedBall c R →ᵇ ℂ) :=
  (cauchyValueLinearMap hα hr hR).mkContinuous (2 * (r + R)) fun f ↦ by
    apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro x
    -- Evaluate the linear-map wrapper before applying the representative identity.
    change ‖cauchyValue hα hr hR f x‖ ≤ _
    rw [cauchyValue_apply]
    exact norm_pi_inv_smul_integral_sub_inv_smul_le hr hR
      (support_subset_of_mem_supportedHolderSubmodule f.property)
      (fun z ↦ (f : HolderSpace α ℂ ℂ).norm_apply_le z) x.property

/-- Evaluation of the bounded value operator is the actual normalized Cauchy integral. -/
@[simp]
theorem cauchyValueCLM_apply {α : ℝ≥0} (hα : 0 < α) {c : ℂ} {r R : ℝ}
    (hr : 0 ≤ r) (hR : 0 ≤ R)
    (f : supportedHolderSubmodule (Y := ℂ) α (closedBall c r))
    (x : closedBall c R) :
    cauchyValueCLM hα hr hR f x =
      (Real.pi : ℂ)⁻¹ • ∫ z, ((x : ℂ) - z)⁻¹ • (f : HolderSpace α ℂ ℂ) z :=
  cauchyValue_apply hα hr hR f x

/-- The Cauchy transform together with its real derivative, bounded in the local `C^{1,α}`
norm `max ‖T f‖_∞ (‖D T f‖_∞ + [D T f]_α)` on the output disc. Continuity of parameter families
in the source Hölder norm therefore gives continuity in this complete target norm. -/
def cauchyTransformCLM {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {c : ℂ} {r R : ℝ}
    (hr : 0 ≤ r) (hR : 0 ≤ R) : supportedHolderSubmodule (Y := ℂ) α (closedBall c r) →L[ℝ]
      (closedBall c R →ᵇ ℂ) × HolderSpace α (closedBall c R) (ℂ →L[ℝ] ℂ) :=
  (cauchyValueCLM hα hr hR).prod (cauchyDerivativeCLM hα hα1 hr hR)

/-- The value component of the bounded `C^{1,α}` operator is the actual Cauchy integral. -/
@[simp]
theorem cauchyTransformCLM_apply_fst {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    {c : ℂ} {r R : ℝ} (hr : 0 ≤ r) (hR : 0 ≤ R)
    (f : supportedHolderSubmodule (Y := ℂ) α (closedBall c r)) (x : closedBall c R) :
    (cauchyTransformCLM hα hα1 hr hR f).1 x =
      (Real.pi : ℂ)⁻¹ • ∫ z, ((x : ℂ) - z)⁻¹ • (f : HolderSpace α ℂ ℂ) z :=
  cauchyValueCLM_apply hα hr hR f x

/-- The derivative component of the bounded `C^{1,α}` operator is the actual real derivative. -/
@[simp]
theorem cauchyTransformCLM_apply_snd {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    {c : ℂ} {r R : ℝ} (hr : 0 ≤ r) (hR : 0 ≤ R)
    (f : supportedHolderSubmodule (Y := ℂ) α (closedBall c r)) (x : closedBall c R) :
    (cauchyTransformCLM hα hα1 hr hR f).2 x =
      fderiv ℝ (fun w : ℂ ↦ (Real.pi : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ •
        (f : HolderSpace α ℂ ℂ) z) (x : ℂ) :=
  cauchyDerivativeCLM_apply hα hα1 hr hR f x

end TauCeti
