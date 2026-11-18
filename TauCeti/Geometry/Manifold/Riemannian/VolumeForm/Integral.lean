/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
public import TauCeti.Analysis.InnerProductSpace.AlternatingForm
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Positivity
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
import TauCeti.Geometry.Manifold.Riemannian.FormMetric

/-!
# Integrating functions against the Riemannian volume form

On an oriented Riemannian manifold `M`, a function `f : M → ℝ` is integrated as the top form
`f vol`, where `vol = TauCeti.riemannianVolumeForm o` is the Riemannian volume form of the
orientation `o`: `∫_M f vol = integralTopForm o (fun x ↦ f x • vol x)`. This file records the
basic properties of this integral that pointwise estimates need: it is nonnegative on nonnegative
functions, it commutes with constant factors, and on a compact manifold it is additive and
monotone on continuous functions. Thus a pointwise inequality `f ≤ g` between continuous functions
integrates to `∫_M f vol ≤ ∫_M g vol`.

## Main results

* `TauCeti.integralTopForm_smul_riemannianVolumeForm_nonneg`: `0 ≤ f` gives `0 ≤ ∫_M f vol`.
* `TauCeti.integralTopForm_mul_smul_riemannianVolumeForm`: `∫_M c f vol = c ∫_M f vol`.
* `TauCeti.isSmoothForm_smul_riemannianVolumeForm`: `f vol` is a continuous top form when `f`
  is continuous.
* `TauCeti.integralTopForm_add_smul_riemannianVolumeForm`: on a compact manifold,
  `∫_M (f + g) vol = ∫_M f vol + ∫_M g vol` for continuous `f` and `g`.
* `TauCeti.integralTopForm_smul_riemannianVolumeForm_mono`: on a compact manifold, `f ≤ g`
  gives `∫_M f vol ≤ ∫_M g vol` for continuous `f` and `g`.
* `TauCeti.abs_integralTopForm_inner_smul_riemannianVolumeForm_le`: on a compact manifold, the
  `L²` pairing of continuous forms satisfies `|∫_M ⟨α, β⟩ vol| ≤ K ∫_M |β| vol` when `|α| ≤ K`
  pointwise.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Proposition 16.6 and Proposition 15.29.
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {m : ℕ} (o : Manifold.Orientation I M (Fin m))

/-- The integral `∫_M f vol` of a nonnegative function against the Riemannian volume form is
nonnegative, on an oriented Riemannian manifold of positive dimension. -/
theorem integralTopForm_smul_riemannianVolumeForm_nonneg [NeZero m] {f : M → ℝ}
    (hf : ∀ x, 0 ≤ f x) :
    0 ≤ integralTopForm o (fun x ↦ f x • riemannianVolumeForm o x) :=
  integralTopForm_nonneg o fun x c hc ↦ by
    let := o.fact_finrank_tangentSpace x
    rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, riemannianVolumeForm_apply]
    exact mul_nonneg (hf x) (Orientation.volumeForm_apply_pos_iff.2 hc).le

/-- Constant factors come out of the integral against the Riemannian volume form:
`∫_M c f vol = c ∫_M f vol`. -/
theorem integralTopForm_mul_smul_riemannianVolumeForm (c : ℝ) (f : M → ℝ) :
    integralTopForm o (fun x ↦ (c * f x) • riemannianVolumeForm o x) =
      c * integralTopForm o (fun x ↦ f x • riemannianVolumeForm o x) := by
  rw [← integralTopForm_smul]
  congr 1
  funext x
  rw [Pi.smul_apply, mul_smul]

section Continuous

variable [IsContMDiffRiemannianBundle I 0 E (fun x : M ↦ TangentSpace I x)]

/-- For a continuous function `f`, the top form `f vol` is continuous. -/
theorem isSmoothForm_smul_riemannianVolumeForm {f : M → ℝ} (hf : Continuous f) :
    IsSmoothForm I 0 (fun x ↦ f x • riemannianVolumeForm o x) := by
  have : IsManifold I (0 + 1) M := by simpa using (inferInstance : IsManifold I 1 M)
  exact (isSmoothForm_riemannianVolumeForm o).fun_smul (contMDiff_zero_iff.2 hf)

variable [CompactSpace M]

/-- On a compact oriented Riemannian manifold, the integral against the Riemannian volume form is
additive on continuous functions: `∫_M (f + g) vol = ∫_M f vol + ∫_M g vol`. -/
theorem integralTopForm_add_smul_riemannianVolumeForm {f g : M → ℝ} (hf : Continuous f)
    (hg : Continuous g) :
    integralTopForm o (fun x ↦ (f x + g x) • riemannianVolumeForm o x) =
      integralTopForm o (fun x ↦ f x • riemannianVolumeForm o x) +
        integralTopForm o (fun x ↦ g x • riemannianVolumeForm o x) := by
  rw [← integralTopForm_add_of_compactSpace o (isSmoothForm_smul_riemannianVolumeForm o hf)
    (isSmoothForm_smul_riemannianVolumeForm o hg)]
  congr 1
  funext x
  rw [Pi.add_apply, add_smul]

/-- **Monotonicity of the integral against the Riemannian volume form**: on a compact oriented
Riemannian manifold of positive dimension, continuous functions with `f ≤ g` satisfy
`∫_M f vol ≤ ∫_M g vol`. -/
theorem integralTopForm_smul_riemannianVolumeForm_mono [NeZero m] {f g : M → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hfg : ∀ x, f x ≤ g x) :
    integralTopForm o (fun x ↦ f x • riemannianVolumeForm o x) ≤
      integralTopForm o (fun x ↦ g x • riemannianVolumeForm o x) := by
  have h :=
    integralTopForm_add_smul_riemannianVolumeForm o (g := fun x ↦ g x - f x) hf (hg.sub hf)
  simp only [add_sub_cancel] at h
  rw [h, le_add_iff_nonneg_right]
  exact integralTopForm_smul_riemannianVolumeForm_nonneg o fun x ↦ sub_nonneg.2 (hfg x)

/-- **The `L²` pairing against a bounded form.** On a compact oriented Riemannian manifold of
positive dimension, if a continuous `k`-form `α` has pointwise norm `|α| = √⟨α, α⟩ ≤ K`, then its
`L²` pairing with a continuous `k`-form `β` satisfies `|∫_M ⟨α, β⟩ vol| ≤ K ∫_M |β| vol`. This is
the fibrewise Cauchy–Schwarz inequality `|⟨α, β⟩| ≤ |α| |β|`, integrated. -/
theorem abs_integralTopForm_inner_smul_riemannianVolumeForm_le [NeZero m] {k : ℕ}
    {α β : RoughForm I M ℝ k} (hα : IsSmoothForm I 0 α) (hβ : IsSmoothForm I 0 β) {K : ℝ}
    (hαK : ∀ x, √(alternatingFormInner (TangentSpace I x) k (α x) (α x)) ≤ K) :
    |integralTopForm o (fun x ↦
        alternatingFormInner (TangentSpace I x) k (α x) (β x) • riemannianVolumeForm o x)| ≤
      K * integralTopForm o (fun x ↦
        √(alternatingFormInner (TangentSpace I x) k (β x) (β x)) • riemannianVolumeForm o x) := by
  have : IsManifold I (0 + 1) M := by simpa using (inferInstance : IsManifold I 1 M)
  have hαβ := (hα.contMDiff_alternatingFormInner hβ).continuous
  have hg : Continuous fun x ↦ K * √(alternatingFormInner (TangentSpace I x) k (β x) (β x)) :=
    continuous_const.mul (hβ.contMDiff_alternatingFormInner hβ).continuous.sqrt
  -- Fibrewise Cauchy–Schwarz: `|⟨α, β⟩| ≤ |α| |β| ≤ K |β|`.
  have hpt (x : M) : |alternatingFormInner (TangentSpace I x) k (α x) (β x)| ≤
      K * √(alternatingFormInner (TangentSpace I x) k (β x) (β x)) := by
    have h := abs_real_inner_le_norm ((alternatingFormEquiv (TangentSpace I x) k).symm (α x))
      ((alternatingFormEquiv (TangentSpace I x) k).symm (β x))
    rw [← alternatingFormInner_apply, ← ContinuousAlternatingMap.sqrt_alternatingFormInner_self,
      ← ContinuousAlternatingMap.sqrt_alternatingFormInner_self] at h
    exact h.trans (mul_le_mul_of_nonneg_right (hαK x) (Real.sqrt_nonneg _))
  rw [← integralTopForm_mul_smul_riemannianVolumeForm, abs_le, neg_le, ← neg_one_mul,
    ← integralTopForm_mul_smul_riemannianVolumeForm]
  simp_rw [neg_one_mul]
  exact ⟨integralTopForm_smul_riemannianVolumeForm_mono o hαβ.neg hg fun x ↦
      (neg_le_abs _).trans (hpt x),
    integralTopForm_smul_riemannianVolumeForm_mono o hαβ hg fun x ↦ le_of_abs_le (hpt x)⟩

end Continuous

end TauCeti
