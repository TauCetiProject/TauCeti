/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution

/-!
# Foliations

A foliation of rank `k` of a manifold `M` decomposes `M` into `k`-dimensional immersed
submanifolds, its leaves. It is recorded here by its tangent distribution, the field of tangent
spaces of the leaves: a `C^n` foliation of rank `k` is a `C^n` involutive distribution of rank
`k`. For `1 ≤ n`, the Frobenius theorem, which is not proved here, makes such a distribution the
tangent field of a unique foliation in the chart sense, the leaves being its maximal connected
integral manifolds; the distribution is therefore the data of the foliation. For `n = 0` the
structure is not the notion of a `C⁰` foliation, whose leaves need not have a continuous tangent
field.

A foliation is data rather than a property of `M`, so it is a structure, bundling the
distribution with its regularity and involutivity. The foliation of a normed space by the
translates of a finite-dimensional subspace is the basic example.

## Main definitions

* `TauCeti.Foliation I n M k`: the `C^n` foliations of `M` of rank `k`.
* `TauCeti.Foliation.ofSubmodule S`: the foliation of a normed space `E` by the translates of a
  finite-dimensional subspace `S`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 19.
* A. Candel, L. Conlon, *Foliations I*, AMS GSM 23 (2000), Chapter 1.
* D. Calegari, *Foliations and the Geometry of 3-Manifolds*, Oxford (2007), Chapter 4.
-/

public section

noncomputable section

open Module
open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] {k : ℕ}

variable (I n M k) in
/-- A `C^n` foliation of `M` of rank `k`, recorded by the tangent spaces of its leaves: a `C^n`
involutive distribution of rank `k`. -/
@[ext]
structure Foliation where
  /-- The tangent distribution of the foliation: at each point, the tangent space of the leaf
  through it. -/
  distribution : Π x : M, Submodule 𝕜 (TangentSpace I x)
  /-- The tangent distribution is a `C^n` distribution of rank `k`. -/
  isContMDiffDistribution : IsContMDiffDistribution I n k distribution
  /-- The tangent distribution is involutive. -/
  isInvolutiveDistribution : IsInvolutiveDistribution I distribution

namespace Foliation

/-- The leaves of a foliation of rank `k` have `k`-dimensional tangent spaces. -/
theorem finrank_distribution (F : Foliation I n M k) (x : M) :
    finrank 𝕜 (F.distribution x) = k :=
  F.isContMDiffDistribution.finrank_eq x

variable [CompleteSpace 𝕜]

variable (n) in
/-- The foliation of a normed space `E` whose leaves are the translates `x + S` of a
finite-dimensional subspace `S`: its tangent space at every point is `S`. -/
def ofSubmodule (S : Submodule 𝕜 E) [FiniteDimensional 𝕜 S] :
    Foliation 𝓘(𝕜, E) n E (finrank 𝕜 S) where
  distribution _ := S
  isContMDiffDistribution := isContMDiffDistribution_const S
  isInvolutiveDistribution := isInvolutiveDistribution_const S.closed_of_finiteDimensional

@[simp]
theorem ofSubmodule_distribution (S : Submodule 𝕜 E) [FiniteDimensional 𝕜 S] (x : E) :
    (ofSubmodule n S).distribution x = S :=
  (rfl)

end Foliation

end TauCeti
