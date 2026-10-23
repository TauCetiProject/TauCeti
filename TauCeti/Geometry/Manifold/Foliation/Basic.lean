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
submanifolds, its leaves. This library defines a foliation by its tangent distribution, the field
of tangent spaces of the leaves: here a `C^n` foliation of rank `k`, for `1 ≤ n`, is by definition
a `C^n` involutive distribution of rank `k`, over any nontrivially normed field and model space.
In the classical setting of a real manifold modelled on a finite-dimensional space, the Frobenius
theorem, which is not proved here, makes such a distribution the tangent field of a unique
foliation in the chart sense, the leaves being its maximal connected integral manifolds, so that
there the distribution is the data of the foliation.
The regularity `1 ≤ n` is required: a `C⁰` foliation need not have a continuous tangent field,
and for a merely continuous distribution the involutivity condition, which tests only
differentiable tangent vector fields, need not constrain it. The manifold `M` is required to be
`C^(n+1)`, so that its tangent bundle is a `C^n` vector bundle and a `C^n` distribution is a
`C^n` subbundle of it; on a less regular manifold the regularity of the distribution would not be
meaningful (the rank-zero distribution, for instance, would be `C^n` for every `n`).

A foliation is data rather than a property of `M`, so it is a structure, bundling the
distribution with its regularity and involutivity. The foliation of a normed space by the
translates of a finite-dimensional subspace is the basic example.

## Main definitions

* `TauCeti.Foliation I n M k`: the `C^n` foliations of rank `k` of a `C^(n+1)` manifold `M`.
* `TauCeti.Foliation.ofSubmodule S hn`: the foliation of a normed space `E` by the translates of a
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
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {k : ℕ}

variable (I n M k) in
/-- A `C^n` foliation of the `C^(n+1)` manifold `M` of rank `k`, for `1 ≤ n`, recorded by the
tangent spaces of its leaves: a `C^n` involutive distribution of rank `k`. -/
@[ext]
structure Foliation [IsManifold I (n + 1) M] where
  /-- The foliation is at least `C¹`, so that its tangent distribution is locally spanned by
  differentiable vector fields and involutivity is a condition on it. -/
  one_le : 1 ≤ n
  /-- The tangent distribution of the foliation: at each point, the tangent space of the leaf
  through it. -/
  distribution : Π x : M, Submodule 𝕜 (TangentSpace I x)
  /-- The tangent distribution is a `C^n` distribution of rank `k`. -/
  isContMDiffDistribution :
    let _ : IsManifold I 1 M := IsManifold.of_le (n := n + 1) le_add_self
    IsContMDiffDistribution I n k distribution
  /-- The tangent distribution is involutive. -/
  isInvolutiveDistribution :
    let _ : IsManifold I 1 M := IsManifold.of_le (n := n + 1) le_add_self
    IsInvolutiveDistribution I distribution

namespace Foliation

variable [IsManifold I (n + 1) M]

/-- The leaves of a foliation of rank `k` have `k`-dimensional tangent spaces. -/
theorem finrank_distribution (F : Foliation I n M k) (x : M) :
    finrank 𝕜 (F.distribution x) = k := by
  let _ : IsManifold I 1 M := IsManifold.of_le (n := n + 1) le_add_self
  exact F.isContMDiffDistribution.finrank_eq x

variable [CompleteSpace 𝕜]

/-- The `C^n` foliation, for `1 ≤ n`, of a normed space `E` whose leaves are the translates
`x + S` of a finite-dimensional subspace `S`: its tangent space at every point is `S`. -/
def ofSubmodule (S : Submodule 𝕜 E) [FiniteDimensional 𝕜 S] (hn : 1 ≤ n) :
    Foliation 𝓘(𝕜, E) n E (finrank 𝕜 S) where
  one_le := hn
  distribution _ := S
  isContMDiffDistribution := isContMDiffDistribution_const S
  isInvolutiveDistribution := isInvolutiveDistribution_const S.closed_of_finiteDimensional

@[simp]
theorem ofSubmodule_distribution (S : Submodule 𝕜 E) [FiniteDimensional 𝕜 S] (hn : 1 ≤ n)
    (x : E) : (ofSubmodule S hn).distribution x = S :=
  (rfl)

end Foliation

end TauCeti
