/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.Chart.EndpointVariation
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Exponential.Variation

/-!
# Realizing a prescribed variation field with moving endpoint

The fibre exponential realizes every smooth tangent field along a curve as the transverse
field of an actual variation. A local chart correction makes the left endpoint follow a
prescribed curve with the same initial velocity, while keeping the right endpoint fixed.
The ambient manifold need not be complete, and no single normal neighborhood containing
the central curve is required.

See J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 6.
-/

public section

open Bundle Filter Set
open scoped ContDiff Manifold Topology
noncomputable section
namespace TauCeti.Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  (γ σ : ℝ → M) (V : ∀ t, TangentSpace I (γ t))
  {n : ℕ∞}

/-- Two prescribed fields agreeing at their common endpoint are realized by actual smooth
variation branches with matching moving vertices, a prescribed moving left endpoint, and
a fixed right endpoint. The central curves and both variation fields remain exact. -/
theorem exists_contMDiffAt_variationField_pair_eq (W : ∀ t, TangentSpace I (γ t))
    (hn : 1 ≤ n) {a c b : ℝ} (hac : a < c)
    (hV : ∀ t ∈ uIcc a c, ContMDiffAt 𝓘(ℝ) I.tangent n
      (fun t ↦ (⟨γ t, V t⟩ : TangentBundle I M)) t)
    (hW : ∀ t ∈ uIcc c b, ContMDiffAt 𝓘(ℝ) I.tangent n
      (fun t ↦ (⟨γ t, W t⟩ : TangentBundle I M)) t)
    (hσ : ContMDiffAt 𝓘(ℝ) I n σ 0) (hbase : γ a = σ 0)
    (hvel : curveVelocity I σ 0 = V a) (hjoin : V c = W c) (hWb : W b = 0) :
    ∃ G₁ G₂ : ℝ → ℝ → M, G₁ 0 = γ ∧ G₂ 0 = γ ∧
      (∀ t ∈ uIcc a c,
        ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I n (fun z : ℝ × ℝ ↦ G₁ z.1 z.2) (0, t)) ∧
      (∀ t ∈ uIcc c b,
        ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I n (fun z : ℝ × ℝ ↦ G₂ z.1 z.2) (0, t)) ∧
      (∀ᶠ s in 𝓝 0, G₁ s a = σ s) ∧ (∀ s, G₁ s c = G₂ s c) ∧
      (∀ s, G₂ s b = γ b) ∧
      (∀ t ∈ uIcc a c, variationField I G₁ t = V t) ∧
      (∀ t ∈ uIcc c b, variationField I G₂ t = W t) := by
  let H := exponentialVariation (I := I) γ V
  have hH₀ : H 0 = γ := exponentialVariation_zero γ V
  have hH : ∀ t ∈ uIcc a c, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I n
      (fun z : ℝ × ℝ ↦ H z.1 z.2) (0, t) := by
    intro t ht
    exact contMDiffAt_exponentialVariation γ V (hV t ht)
      (by simpa only [zero_smul] using zero_mem_expDomain (I := I) (γ t))
  have hHV (t : ℝ) : variationField I H t = V t := variationField_exponentialVariation γ V t
  obtain ⟨G₁, hG₁₀, hG₁, hG₁a, hG₁c, hG₁V⟩ := exists_contMDiffAt_endpointCorrection
    (F := H) (σ := σ) hn hac hH hσ (hH₀ ▸ hbase) (hvel.trans (hHV a).symm)
  let G₂ := exponentialVariation (I := I) γ W
  refine ⟨G₁, G₂, hG₁₀.trans hH₀, exponentialVariation_zero γ W, hG₁, ?_,
    hG₁a, ?_, ?_, fun t ht ↦ (hG₁V t ht).trans (hHV t), ?_⟩
  · intro t ht
    exact contMDiffAt_exponentialVariation γ W (hW t ht)
      (by simpa only [zero_smul] using zero_mem_expDomain (I := I) (γ t))
  · intro s
    rw [hG₁c]
    simp only [H, G₂, exponentialVariation_apply, hjoin]
  · intro s
    simp only [G₂, exponentialVariation_apply, hWb, smul_zero, riemannianExp_zero]
  · intro t _
    exact variationField_exponentialVariation γ W t

end TauCeti.Manifold
