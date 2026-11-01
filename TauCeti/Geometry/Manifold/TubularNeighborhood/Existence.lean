/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.TubularNeighborhood.Riemannian.Coordinates

/-!
# Tubular neighbourhoods without a prescribed metric

The intrinsic normal bundle of a smooth embedding between finite-dimensional, boundaryless
real manifolds is diffeomorphic to an open neighbourhood of its image. The neighbourhood
can be chosen inside any prescribed open neighbourhood, and the zero section is sent to
the original embedding. The ambient manifold is Hausdorff and second countable; neither
compactness nor closedness of the image is required.

An auxiliary smooth Riemannian metric is chosen on the ambient tangent bundle using
`TauCeti.nonempty_contMDiffRiemannianMetric`. The Riemannian tubular theorem
`SmoothEmbedding.exists_diffeomorph_normalBundle_riemannian_subset` then supplies the
coordinates. The conclusion uses the intrinsic quotient normal bundle and its existing
complementary-coordinate atlas, both independent of that metric.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 6.24.
* M. Hirsch, *Differential Topology*, Chapter 4, Theorem 6.3.
-/

public noncomputable section

open Bundle Manifold Set
open scoped ContDiff Manifold

namespace TauCeti.SmoothEmbedding

variable {E V P H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V G}
  [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [T2Space N] [SecondCountableTopology N]

/-- **Smooth tubular neighbourhood theorem.** The entire intrinsic normal bundle of a
smooth embedding is diffeomorphic to an arbitrarily small open neighbourhood of its image,
with the zero section sent to the embedding. No Riemannian metric is part of the input or
output, and the image need not be closed or compact. -/
theorem exists_diffeomorph_normalBundle_subset
    (f : SmoothEmbedding I J ∞ M N)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E)
    {O : Set N} (hO : IsOpen O) (hfO : range f ⊆ O) :
    let hn : (∞ : ℕ∞ω) ≠ 0 := by simp
    letI := f.normalSpaceFiberBundle hn hdim
    ∃ W : TopologicalSpace.Opens N, (W : Set N) ⊆ O ∧
      ∃ Φ : TotalSpace P (fun x ↦ f.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W,
        ∀ x, (Φ (zeroSection P (fun x ↦ f.NormalSpace x hn) x) : N) = f x := by
  have : LocallyCompactSpace G := J.locallyCompactSpace
  have : LocallyCompactSpace N := ChartedSpace.locallyCompactSpace G N
  obtain ⟨g⟩ := nonempty_contMDiffRiemannianMetric (IB := J) (n := ⊤) (F := V)
    (E := fun y : N ↦ TangentSpace J y)
  let : RiemannianBundle (fun y : N ↦ TangentSpace J y) := ⟨g.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle J ∞ V (fun y : N ↦ TangentSpace J y) :=
    Bundle.instIsContMDiffRiemannianBundle g
  exact f.exists_diffeomorph_normalBundle_riemannian_subset hdim hO hfO

end TauCeti.SmoothEmbedding
