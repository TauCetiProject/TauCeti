/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-!
# Conformal rescaling of Riemannian metrics

Multiplying a `C^n` Riemannian metric `g` on a vector bundle by a positive `C^n` function `f` on
the base gives another `C^n` Riemannian metric `f • g`, conformal to `g`. Many model metrics are
written this way: the upper half-space model of hyperbolic space is the Euclidean metric divided by
the square of the height, and the Poincaré ball model is the Euclidean metric multiplied by
`4 / (1 - ‖x‖²)²`.

## Main definitions

* `Bundle.ContMDiffRiemannianMetric.rescale`: the rescaled metric `f • g`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
  (conformal metrics) and Chapter 3 (the models of hyperbolic space).
-/

public section

open Bundle Bornology
open scoped Manifold ContDiff

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousConstSMul ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]

/-- The Riemannian metric `f • g` obtained by multiplying a `C^n` Riemannian metric `g` by a
positive `C^n` function `f` on the base. -/
def rescale (g : ContMDiffRiemannianMetric IB n F E) (f : B → ℝ)
    (hf : ContMDiff IB 𝓘(ℝ) n f) (hf_pos : ∀ b, 0 < f b) :
    ContMDiffRiemannianMetric IB n F E where
  inner b := f b • g.inner b
  symm b v w := by
    simp only [smul_apply, g.symm b v w]
  pos b v hv := by
    simpa only [smul_apply, smul_eq_mul] using
      mul_pos (hf_pos b) (g.pos b v hv)
  isVonNBounded b := by
    -- The unit ball of `f b • g` is the unit ball of `g` scaled by `(√(f b))⁻¹`.
    set c := Real.sqrt (f b)
    have hc : 0 < c := Real.sqrt_pos.mpr (hf_pos b)
    refine ((g.isVonNBounded b).image (c⁻¹ • ContinuousLinearMap.id ℝ (E b))).subset ?_
    intro v hv
    refine ⟨c • v, ?_, by simp [smul_smul, mul_inv_cancel₀ hc.ne']⟩
    simp only [Set.mem_ofPred_eq, smul_apply, smul_eq_mul, map_smul] at hv ⊢
    calc c * (c * g.inner b v v) = f b * g.inner b v v := by
          rw [← mul_assoc, Real.mul_self_sqrt (hf_pos b).le]
      _ < 1 := hv
  contMDiff := hf.smul_section g.contMDiff

omit [∀ b, IsTopologicalAddGroup (E b)] in
/-- The rescaled metric `f • g` is `f b` times `g` on the fibre over `b`. -/
@[simp]
theorem rescale_inner (g : ContMDiffRiemannianMetric IB n F E) (f : B → ℝ)
    (hf : ContMDiff IB 𝓘(ℝ) n f) (hf_pos : ∀ b, 0 < f b) (b : B) (v w : E b) :
    (g.rescale f hf hf_pos).inner b v w = f b * g.inner b v w :=
  (rfl)

end Bundle.ContMDiffRiemannianMetric
