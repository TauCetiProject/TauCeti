/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.TubularNeighborhood.Riemannian.Basic
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Riemannian

/-!
# Smoothness of the normal exponential

The natural domain of the normal exponential is open in the intrinsic normal bundle, and the
normal exponential is smooth there. Both statements concern the total space, so the base point
and normal vector vary together. The domain contains the zero section by
`SmoothEmbedding.zeroSection_mem_normalExpDomain`.

These are the regularity inputs to the inverse function theorem in the construction of tubular
neighbourhoods. They do not assert injectivity or the existence of a tubular diffeomorphism.

## References

* M. W. Hirsch, *Differential Topology*, Chapter 4, Theorem 6.3.
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
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [J.Boundaryless] [T2Space N] {n : ℕ∞ω}
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ V (fun y : N ↦ TangentSpace J y)]

/-- The natural normal-exponential domain is open in the total intrinsic normal bundle. -/
theorem isOpen_normalExpDomain [IsManifold I 1 M]
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E) :
    letI := f.normalSpaceFiberBundle hn hdim
    IsOpen (f.normalExpDomain (P := P) hn) := by
  have : IsManifold I (0 + 1) M := by simpa using (inferInstance : IsManifold I 1 M)
  have : IsManifold J (0 + 1) N := by simpa using (inferInstance : IsManifold J 1 N)
  let := f.normalSpaceFiberBundle hn hdim
  convert (Manifold.isOpen_setOfPred_mem_expDomain (I := J) (M := N)).preimage
    (f.contMDiff_normalRepresentative (m := 0) hn
      (by simpa using ENat.one_le_iff_ne_zero_withTop.mpr hn) hdim).continuous using 1
  ext p
  exact f.mem_normalExpDomain hn p

variable [IsManifold I ∞ M]

/-- The normal exponential is smooth on its natural open domain in the total normal bundle. -/
theorem contMDiffOn_normalExp
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (hm : ∞ ≤ n)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E) :
    letI := f.normalSpaceFiberBundle hn hdim
    ContMDiffOn (I.prod 𝓘(ℝ, P)) J ∞ (f.normalExp (P := P) hn)
      (f.normalExpDomain (P := P) hn) := by
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have : IsManifold J (∞ + 1) N := by simpa using (inferInstance : IsManifold J ∞ N)
  let := f.normalSpaceFiberBundle hn hdim
  convert (Manifold.contMDiffOn_riemannianExp_tangentBundle (I := J) (M := N)).comp
    (f.contMDiff_normalRepresentative (m := ∞) hn (by simpa using hm) hdim).contMDiffOn
    (fun p hp => (f.mem_normalExpDomain hn p).mp hp) using 1
  funext p
  exact f.normalExp_apply hn p

end TauCeti.SmoothEmbedding
