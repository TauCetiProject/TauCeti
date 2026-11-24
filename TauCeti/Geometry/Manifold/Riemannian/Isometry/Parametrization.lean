/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.ContMDiff.Parametrization
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Pullback
import TauCeti.Geometry.Manifold.ContMDiffMap.Extension
import TauCeti.Geometry.Manifold.Riemannian.Isometry.Restriction

/-!
# Local Riemannian parametrizations by the model space

An interior point of a smooth finite-dimensional Riemannian manifold has an open
neighbourhood diffeomorphic to the model space. Pulling the metric back along this
parametrization makes it a local Riemannian isometry. The model space carries the pulled-back
metric, which need not be its constant Euclidean metric. On a Hausdorff manifold, this
parametrization also transports vector-valued `C^n` germs to global `C^n` maps.
-/

public section

open Bundle Filter Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- An interior point has a parametrization by the model space which is a local Riemannian
isometry for a smooth pulled-back metric. No separation assumption on the manifold is needed. -/
theorem exists_localRiemannianIsometry_parametrization {x : M} (hx : I.IsInteriorPoint x) :
    ∃ (O : TopologicalSpace.Opens M) (_ : x ∈ O) (Φ : O ≃ₘ^∞⟮I, 𝓘(ℝ, E)⟯ E)
      (gE : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (fun z : E ↦ TangentSpace 𝓘(ℝ, E) z)),
      letI : RiemannianBundle (fun z : E ↦ TangentSpace 𝓘(ℝ, E) z) := ⟨gE.toRiemannianMetric⟩
      IsLocalRiemannianIsometry 𝓘(ℝ, E) I ((Subtype.val : O → M) ∘ Φ.symm) := by
  obtain ⟨O, hxO, ⟨Φ₀⟩⟩ := exists_opens_diffeomorph_euclideanSpace (n := (⊤ : ℕ∞)) hx
  let Φ : O ≃ₘ^∞⟮I, 𝓘(ℝ, E)⟯ E := Φ₀.trans (toEuclidean (E := E)).symm.toDiffeomorph
  let f : E → M := (Subtype.val : O → M) ∘ Φ.symm
  have hfs : ContMDiff 𝓘(ℝ, E) I (∞ + 1) f :=
    (contMDiff_subtypeVal.comp Φ.symm.contMDiff).of_le (by simp)
  have hinv (z : E) : (mfderiv 𝓘(ℝ, E) I f z).IsInvertible := by
    rw [mfderiv_comp z ((contMDiff_subtypeVal (n := ∞)).mdifferentiableAt (by simp))
      (Φ.symm.contMDiff.mdifferentiableAt (by simp))]
    exact ((IsLocalRiemannianIsometry.subtype_val O).isInvertible_mfderiv
      (Φ.symm z)).comp (Φ.symm.isInvertible_mfderiv (by simp))
  let gM := ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle
    (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)
  let gE := gM.pullback f hfs (fun z ↦ (hinv z).injective)
  refine ⟨O, hxO, Φ, gE, ?_⟩
  have hgM : (⟨gM.toRiemannianMetric⟩ : RiemannianBundle (fun x : M ↦ TangentSpace I x)) =
      ‹RiemannianBundle (fun x : M ↦ TangentSpace I x)› := by
    have hinner : gM.toRiemannianMetric.inner = RiemannianBundle.g.inner := by
      ext x v w
      exact ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle_inner
        (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x) x v w
    refine congrArg RiemannianBundle.mk ?_
    cases h₁ : gM.toRiemannianMetric
    cases h₂ : RiemannianBundle.g (E := fun x : M ↦ TangentSpace I x)
    rw [h₁, h₂] at hinner
    cases hinner
    rfl
  exact hgM ▸ gM.isLocalRiemannianIsometry_pullback_of_isInvertible hfs hinv

/-- An interior point has an open model-space parametrization which is a local Riemannian
isometry for a smooth pulled-back metric and transports each vector-valued `C^n` germ to
a global `C^n` map on the manifold. -/
theorem exists_pullback_parametrization_of_isInteriorPoint [T2Space M]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] {x₀ : M}
    (hx₀ : I.IsInteriorPoint x₀) :
    ∃ (f : E → M) (z₀ : E)
      (gE : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (fun z : E ↦ TangentSpace 𝓘(ℝ, E) z)),
      f z₀ = x₀ ∧ Topology.IsOpenEmbedding f ∧
      (∀ {n : ℕ∞} {ψ : E → F},
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) n ψ →
        ∃ φ : M → F, ContMDiff I 𝓘(ℝ, F) n φ ∧ (φ ∘ f) =ᶠ[𝓝 z₀] ψ) ∧
      letI : RiemannianBundle (fun z : E ↦ TangentSpace 𝓘(ℝ, E) z) := ⟨gE.toRiemannianMetric⟩
      IsLocalRiemannianIsometry 𝓘(ℝ, E) I f := by
  obtain ⟨U, hx₀U, Φ, gE, hf_iso⟩ := exists_localRiemannianIsometry_parametrization hx₀
  let f : E → M := (Subtype.val : U → M) ∘ Φ.symm
  have hemb : Topology.IsOpenEmbedding f :=
    U.isOpen.isOpenEmbedding_subtypeVal.comp Φ.symm.toHomeomorph.isOpenEmbedding
  refine ⟨f, Φ ⟨x₀, hx₀U⟩, gE, by simp [f], hemb, fun {n} {ψ} hψ ↦ ?_, hf_iso⟩
  have hψΦ : ContMDiff I 𝓘(ℝ, F) n (ψ ∘ Φ) :=
    hψ.comp (Φ.contMDiff.of_le (by exact_mod_cast le_top))
  obtain ⟨G, hG_eq⟩ := hψΦ.exists_contMDiffMap_eventuallyEq_comp_subtype_val (x := ⟨x₀, hx₀U⟩)
  refine ⟨G, G.contMDiff, ?_⟩
  have hΦ_tendsto : Tendsto Φ.symm (𝓝 (Φ ⟨x₀, hx₀U⟩)) (𝓝 ⟨x₀, hx₀U⟩) := by
    simpa using Φ.symm.continuous.tendsto (Φ ⟨x₀, hx₀U⟩)
  exact (hΦ_tendsto.eventually hG_eq).mono fun z hz ↦ by
    simpa [f] using hz

end TauCeti
