/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Immersion.NormalSpace.Quotient
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Basic

/-!
# Smooth quotient maps to intrinsic normal bundles of embeddings

For an embedding in an arbitrary finite-dimensional manifold, taking the normal class of an
ambient tangent vector is smooth, with one derivative lost from the embedding, and a map out of the
normal bundle is smooth exactly when its expression on ambient tangent representatives is smooth.
These are the results `Manifold.IsImmersion.contMDiff_normalQuotientMap` and
`Manifold.IsImmersion.contMDiff_normalBundle_iff` for the underlying immersion, stated for the
bundled embedding's normal bundle `TauCeti.SmoothEmbedding.normalSpaceFiberBundle`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, the normal-bundle construction
  preceding Theorem 6.24.
-/

public noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {𝕜 E V P H G M N : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  [NormedAddCommGroup P] [NormedSpace 𝕜 P] [FiniteDimensional 𝕜 P]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 V G}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]
  {n m : ℕ∞ω} [IsManifold I (m + 1) M] [IsManifold J (m + 1) N]

/-- Taking the intrinsic normal class of an ambient tangent vector is `C^m` for a `C^n`
embedding when `m + 1 ≤ n`. Both bundles carry their usual bundle charts. -/
theorem contMDiff_normalQuotientMap (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hm : m + 1 ≤ n)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    haveI : IsManifold J 1 N := .of_le (n := m + 1) le_add_self
    letI := f.normalSpaceFiberBundle hn hdim
    ContMDiff (I.prod 𝓘(𝕜, V)) (I.prod 𝓘(𝕜, P)) m
      (f.normalQuotientMap (K := P) hn) :=
  f.isImmersion.contMDiff_normalQuotientMap (f := f) hn hm hdim

/-- A map out of an intrinsic normal bundle is `C^m` exactly when it is `C^m` on
ambient tangent representatives. This is the smooth descent property of the normal quotient. -/
theorem contMDiff_normalBundle_iff
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (hm : m + 1 ≤ n)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
    {E' H' X : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    [TopologicalSpace X] [ChartedSpace H' X]
    (q : TotalSpace P (fun x => f.NormalSpace x hn) → X) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    haveI : IsManifold J 1 N := .of_le (n := m + 1) le_add_self
    letI := f.normalSpaceFiberBundle hn hdim
    ContMDiff (I.prod 𝓘(𝕜, P)) I' m q ↔
      ContMDiff (I.prod 𝓘(𝕜, V)) I' m (q ∘ f.normalQuotientMap hn) :=
  f.isImmersion.contMDiff_normalBundle_iff (f := f) hn hm hdim q

end TauCeti.SmoothEmbedding
