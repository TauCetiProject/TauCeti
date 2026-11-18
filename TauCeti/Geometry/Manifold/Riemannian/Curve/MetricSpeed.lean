/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.MetricSegment

/-!
# Native speed from actual local metric arclength

A genuine local unit-distance identity determines the actual native Riemannian velocity norm
at every center parameter. Translation to the native normal-coordinate rigidity theorem and
the actual curve chain rule identify that norm without assuming differentiability in advance.
-/

public noncomputable section

open Bundle Filter Function Manifold Metric Set TopologicalSpace
open scoped ContDiff ENNReal Manifold Topology
namespace TauCeti.Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]
/-- A genuine local unit-distance curve has actual native Riemannian speed one at
its center, at any real center parameter. -/
theorem norm_curveVelocity_eq_one_of_dist_eq_abs_at
    {γ : ℝ → M} {ε t₀ : ℝ} (hε : 0 < ε)
    (hdist : ∀ s ∈ Icc (t₀ - ε) (t₀ + ε), ∀ t ∈ Icc (t₀ - ε) (t₀ + ε),
      dist (γ s) (γ t) = |s - t|) : ‖curveVelocity I γ t₀‖ = 1 := by
  let η : ℝ → M := fun s ↦ γ (t₀ + s)
  have hmaps : ∀ s ∈ Icc (-ε) ε, t₀ + s ∈ Icc (t₀ - ε) (t₀ + ε) :=
    fun s hs ↦ ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hηdist : ∀ s ∈ Icc (-ε) ε, ∀ t ∈ Icc (-ε) ε,
      dist (η s) (η t) = |s - t| := by
    intro s hs t ht
    dsimp only [η]
    rw [hdist _ (hmaps s hs) _ (hmaps t ht),
      show t₀ + s - (t₀ + t) = s - t by ring]
  have hnorm := norm_curveVelocity_eq_one_of_dist_eq_abs (I := I) (γ := η) hε hηdist
  have hsmooth := contMDiffAt_of_dist_eq_mul_abs (I := I) (γ := γ) hε zero_le_one
    (fun s hs t ht ↦ by simpa only [mul_one] using hdist s hs t ht)
  have hmd : MDifferentiableAt 𝓘(ℝ) I γ (t₀ + 0) := by
    simpa only [add_zero] using hsmooth.mdifferentiableAt (by simp)
  have hderiv : HasDerivAt (fun s : ℝ ↦ t₀ + s) 1 0 := (hasDerivAt_id (0 : ℝ)).const_add t₀
  change ‖curveVelocity I (γ ∘ fun s : ℝ ↦ t₀ + s) 0‖ = 1 at hnorm
  rw [curveVelocity_comp hderiv hmd, one_smul] at hnorm
  have heq := congrArg (fun t : ℝ ↦ ‖curveVelocity I γ t‖) (add_zero t₀)
  rwa [heq] at hnorm
end TauCeti.Manifold
