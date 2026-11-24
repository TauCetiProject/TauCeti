/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Euclidean
public import TauCeti.Geometry.Manifold.SmoothSingular.Integral

/-!
# Integrals over oriented simplices and integrals of top forms

Let `N` be a manifold of dimension `p` with an orientation `o`, and let `σ` be a smooth singular
`p`-simplex of `N`. Suppose that `σ` is the restriction to the full-dimensional simplex
`Δᵖ ⊆ ℝᵖ` of a map `g : ℝᵖ → N` which, on an open neighbourhood `U` of `Δᵖ`, is an open embedding
preserving orientation from the standard orientation of `ℝᵖ`
(`TauCeti.Manifold.Orientation.euclideanSpace p`) to `o`. Then for every integrable top form `φ`
supported in `σ(Δᵖ)`, for instance a continuous one, the integral of `φ` over the simplex is the
integral of `φ` over the oriented manifold:

`∫_σ φ = ∫_N φ`

(`TauCeti.SmoothSimplex.integral_eq_integralTopForm`). Both sides are integrals over `Δᵖ` of the
pullback `g^*φ` evaluated on the standard basis: the left side by definition, and the right side
by `TauCeti.integralTopForm_eq_setIntegral_mpullback`, the change of variables along the open
embedding `U → N`. For an orientation-reversing `g` the two sides differ by a sign
(`TauCeti.SmoothSimplex.integral_eq_neg_integralTopForm`).

This is the local identity in the comparison of integration of top forms with the pairing of
de Rham classes against fundamental classes: a top form supported in the interior of a positively
oriented simplex of an oriented chart integrates over that simplex to its integral over the
manifold.

## Main results

* `TauCeti.SmoothSimplex.integral_eq_integralTopForm`: `∫_σ φ = ∫_N φ` for an orientation-preserving
  simplex.
* `TauCeti.SmoothSimplex.integral_eq_neg_integralTopForm`: `∫_σ φ = -∫_N φ` for an
  orientation-reversing simplex.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 16 (integration of top forms)
  and Chapter 18 (integration over smooth chains).
-/

public section

noncomputable section

open MeasureTheory Set Topology TopologicalSpace
open scoped Manifold

namespace TauCeti

namespace SmoothSimplex

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {N : Type*} [TopologicalSpace N]
  [ChartedSpace H N] [IsManifold I 1 N] {p : ℕ}

/-- **The integral over an oriented simplex is the integral over the manifold.** Let `σ` be a
smooth `p`-simplex of a `p`-dimensional manifold `N` oriented by `o`, which is the restriction to
`Δᵖ` of a map `g : ℝᵖ → N` that is an open embedding on an open neighbourhood `U` of `Δᵖ` and
preserves orientation there from the standard orientation of `ℝᵖ`. Then every integrable top form
supported in `g(Δᵖ)`, for instance a continuous one, has the same integral over `σ` as over `N`:
`∫_σ φ = ∫_N φ`. -/
theorem integral_eq_integralTopForm (o : Manifold.Orientation I N (Fin p))
    (σ : SmoothSimplex I N p) {U : Opens (EuclideanSpace ℝ (Fin p))} (hU : fullSimplex p ⊆ U)
    {g : EuclideanSpace ℝ (Fin p) → N} (hgσ : ∀ x : fullSimplex p, g x = σ.toContinuousMap x)
    (hg : IsOpenEmbedding (g ∘ ((↑) : U → EuclideanSpace ℝ (Fin p))))
    (ho : ∀ x ∈ U, Manifold.Orientation.IsOrientationPreservingAt
      (Manifold.Orientation.euclideanSpace p) o g x)
    {φ : RoughForm I N ℝ p} (hφ : IntegrableTopForm φ)
    (hsupp : _root_.tsupport (α := E [⋀^Fin p]→L[ℝ] ℝ) φ ⊆ g '' fullSimplex p) :
    σ.integral φ = integralTopForm o φ := by
  rw [integralTopForm_eq_setIntegral_mpullback o (isClosed_fullSimplex p) hU hg ho hφ hsupp,
    σ.integral_eq_setIntegral_mpullback φ hgσ fun x hx ↦
      mdifferentiableAt_of_isInvertible_mfderiv (ho x (hU hx)).isInvertible_mfderiv]

/-- For a simplex given on a neighbourhood of `Δᵖ` by an orientation-reversing open embedding, the
integral over the simplex of an integrable top form supported in its image is minus the integral
over the manifold: `∫_σ φ = -∫_N φ`. -/
theorem integral_eq_neg_integralTopForm (o : Manifold.Orientation I N (Fin p))
    (σ : SmoothSimplex I N p) {U : Opens (EuclideanSpace ℝ (Fin p))} (hU : fullSimplex p ⊆ U)
    {g : EuclideanSpace ℝ (Fin p) → N} (hgσ : ∀ x : fullSimplex p, g x = σ.toContinuousMap x)
    (hg : IsOpenEmbedding (g ∘ ((↑) : U → EuclideanSpace ℝ (Fin p))))
    (ho : ∀ x ∈ U, Manifold.Orientation.IsOrientationReversingAt
      (Manifold.Orientation.euclideanSpace p) o g x)
    {φ : RoughForm I N ℝ p} (hφ : IntegrableTopForm φ)
    (hsupp : _root_.tsupport (α := E [⋀^Fin p]→L[ℝ] ℝ) φ ⊆ g '' fullSimplex p) :
    σ.integral φ = -integralTopForm o φ := by
  rw [← integralTopForm_neg]
  exact σ.integral_eq_integralTopForm (-o) hU hgσ hg
    (fun x hx ↦ (Manifold.Orientation.isOrientationPreservingAt_neg_right _ o g x).2 (ho x hx))
    hφ hsupp

end SmoothSimplex

end TauCeti
