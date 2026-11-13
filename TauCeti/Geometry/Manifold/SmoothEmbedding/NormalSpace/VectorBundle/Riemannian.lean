/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Riemannian
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Representative
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import TauCeti.Geometry.Manifold.Riemannian.Pullback.Basic
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# Smooth orthogonal representatives in intrinsic normal bundles

Orthogonal representatives of intrinsic normal classes vary smoothly with both the base point
and the normal vector. The metric is the ambient Riemannian metric; no normal framing or
compactness assumption is needed. This supplies the map from the normal bundle to the ambient
tangent bundle used by the normal exponential.

The construction uses the pullback metric on the embedded manifold. Inverting its flat map
recovers the tangential component of an ambient vector from its pairings with tangent vectors.
Subtracting this component gives the orthogonal representative
(`TauCeti.SmoothEmbedding.contMDiff_of_eq_sub_mfderiv_inverse`), which descends through the
smooth normal quotient (`TauCeti.SmoothEmbedding.contMDiff_normalBundle_of_contMDiff_normalClass`).

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

omit [IsContMDiffRiemannianBundle J m V (fun y : N ↦ TangentSpace J y)] in
/-- Pointwise formula for the orthogonal representative of an intrinsic normal class, written
with any `C^m` Riemannian metric `g` that has the ambient metric as its fiberwise inner product:
the tangential component is recovered by inverting the pullback of `g` along `f`. -/
private theorem normalRepresentative_normalClass_eq_sub_inverse_pullback
    [IsManifold I 1 M]
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (hm : m + 1 ≤ n)
    (g : ContMDiffRiemannianMetric J m V (fun y : N ↦ TangentSpace J y))
    (hg : ∀ y, g.inner y = RiemannianBundle.g.inner y) (x : M) (v : TangentSpace J (f x)) :
    f.normalRepresentative x hn (f.normalClass x hn v) = v -
      mfderiv I J f x
        (((g.pullback f (f.contMDiff.of_le (by simpa using hm))
          (f.isImmersion.mfderiv_injective hn)).inner x).inverse
            ((g.inner (f x) v).comp (mfderiv I J f x))) := by
  have hflat : (g.pullback f (f.contMDiff.of_le (by simpa using hm))
      (f.isImmersion.mfderiv_injective hn)).inner x =
      (ContinuousLinearMap.precomp ℝ (mfderiv I J f x)).comp
        ((g.inner (f x)).comp (mfderiv I J f x)) := by
    ext w z
    exact ContMDiffRiemannianMetric.pullback_inner _ _ _ _ _ _ _
  simpa only [hflat, hg] using f.normalRepresentative_normalClass_eq_sub_mfderiv_inverse x hn v

omit [FiniteDimensional ℝ E] in
/-- Orthogonal normal projection is `C^m` on the pulled-back ambient tangent bundle for a
`C^n` embedding with `m + 1 ≤ n` and a `C^m` ambient metric. Both the base point and the
ambient tangent vector may vary. -/
theorem contMDiff_normalRepresentative_normalClass
    [IsManifold I (m + 1) M] [IsManifold J (m + 1) N]
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
  have : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  let : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  -- The induced metric identifies tangent vectors with covectors on the source.
  let g := ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle
    (IB := J) (n := m) (F := V) (V := fun y : N => TangentSpace J y)
  let a := g.pullback f (f.contMDiff.of_le (by simpa using hm)) (f.isImmersion.mfderiv_injective hn)
  exact f.contMDiff_of_eq_sub_mfderiv_inverse hm a.contMDiff
    (fun x ↦ ContinuousLinearMap.isInvertible_of_pos (E := E) (a.pos x)) g.contMDiff _
    (normalRepresentative_normalClass_eq_sub_inverse_pullback f hn hm g fun y ↦ by
      ext w z
      exact ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle_inner _ _ _)

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
