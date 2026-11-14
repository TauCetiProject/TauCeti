/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Riemannian
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Representative
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import TauCeti.Geometry.Manifold.Riemannian.Immersion.Projection
import TauCeti.Geometry.Manifold.VectorBundle.Pullback

/-!
# Smooth orthogonal representatives in intrinsic normal bundles

Orthogonal representatives of intrinsic normal classes vary smoothly with both the base point
and the normal vector. The metric is the ambient Riemannian metric; no normal framing or
compactness assumption is needed. This supplies the map from the normal bundle to the ambient
tangent bundle used by the normal exponential.

The construction applies the smooth normal-projection endomorphism field along an immersion
to the ambient vector. For embeddings, this projection is the orthogonal representative of its
intrinsic normal class, and it descends through the smooth normal quotient.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 6.24.
* M. W. Hirsch, *Differential Topology*, Chapter 4, Theorem 6.3.
-/

public noncomputable section

open Bundle Manifold Function
open scoped ContDiff Manifold

namespace TauCeti.SmoothEmbedding

variable {E V P H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V G}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω}
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]

variable {m : ℕ∞ω} [IsManifold J 1 N]
  [IsContMDiffRiemannianBundle J m V (fun y : N ↦ TangentSpace J y)]

omit [FiniteDimensional ℝ E] in
/-- Orthogonal normal projection is `C^m` on the pulled-back ambient tangent bundle for a
`C^n` embedding with `m + 1 ≤ n` and a `C^m` ambient metric. Both the base point and the
ambient tangent vector may vary. -/
theorem contMDiff_normalRepresentative_normalClass
    [IsManifold I 1 M]
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (hm : m + 1 ≤ n) :
    ContMDiff (I.prod 𝓘(ℝ, V)) (J.prod 𝓘(ℝ, V)) m
      (fun p : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)) =>
        (⟨f p.proj, f.normalRepresentative p.proj hn (f.normalClass p.proj hn p.2)⟩ :
          TangentBundle J N)) := by
  rcases isEmpty_or_nonempty M with hM | ⟨⟨x₀⟩⟩
  · exact fun p ↦ isEmptyElim p.proj
  -- the differential of an immersion embeds `E` in the finite-dimensional space `V`
  have : FiniteDimensional ℝ E :=
    Module.Finite.of_injective (mfderiv I J f x₀ : E →L[ℝ] V).toLinearMap
      (f.isImmersion.mfderiv_injective hn x₀)
  have hbase : ContMDiff (I.prod 𝓘(ℝ, V)) I m
      (π V ((f : M → N) *ᵖ (TangentSpace J))) := contMDiff_proj _
  have hlift : ContMDiff (I.prod 𝓘(ℝ, V)) (J.prod 𝓘(ℝ, V)) m
      (Pullback.lift (f : M → N)) :=
    Pullback.contMDiff_lift (E := TangentSpace J) f
      (f.contMDiff.of_le (le_self_add.trans hm))
  have hprojection := f.contMDiff.starProjection_orthogonal_range_mfderiv hm
    (f.isImmersion.mfderiv_injective hn)
  refine ((hprojection.comp hbase).clm_bundle_apply hlift).congr fun p ↦ ?_
  exact congrArg (TotalSpace.mk (f p.proj))
    (f.normalRepresentative_normalClass p.proj hn p.2)

/-- The map taking an intrinsic normal vector to its orthogonal representative in the ambient
tangent bundle is `C^m` for a `C^n` embedding with `m + 1 ≤ n` and a `C^m` ambient metric. -/
theorem contMDiff_normalRepresentative
    [IsManifold I (m + 1) M] [IsManifold J (m + 1) N]
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (hm : m + 1 ≤ n)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    letI := f.normalSpaceFiberBundle hn hdim
    ContMDiff (I.prod 𝓘(ℝ, P)) (J.prod 𝓘(ℝ, V)) m
      (fun p : TotalSpace P (fun x => f.NormalSpace x hn) =>
        (⟨f p.proj, f.normalRepresentative p.proj hn p.2⟩ : TangentBundle J N)) := by
  have : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  exact f.contMDiff_normalBundle_of_contMDiff_normalClass hn hm hdim
    (fun x v ↦ f.normalRepresentative x hn v)
    (f.contMDiff_normalRepresentative_normalClass hn hm)

end TauCeti.SmoothEmbedding
