/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Contractible
public import TauCeti.Geometry.Manifold.SmoothEmbedding.HomologyConcordance
public import TauCeti.KnotTheory.SmoothCircle

/-!
# Knots in homology spheres and Levine's theorem

Knots in integral homology `3`-spheres are compared by *homology concordance*: two knots
`K₀ ⊆ Y₀` and `K₁ ⊆ Y₁` are homology concordant when they cobound a smoothly and properly embedded
annulus in some smooth integral homology cobordism between `Y₀` and `Y₁`
(`TauCeti.HomologyConcordant`, with the circle as source). Every knot in `S³` is homology concordant
to a knot in `S³`, namely itself (`TauCeti.not_forall_not_homologyConcordant_sphere`).

Matsumoto asked (Kirby's problem 1.31) whether the knots in homology spheres bounding acyclic
`4`-manifolds are, up to homology concordance, just the knots in `S³`. Levine answered this
negatively: there is a smooth compact contractible `4`-manifold `X` and a knot `K` in its boundary
`Y = ∂X` which is not homology concordant to any knot in `S³`. Since `X` is contractible, `Y` is an
integral homology sphere, by Lefschetz duality. Levine states the result as: `K` bounds no
piecewise-linear disc in any homology ball with boundary `Y`. This implies the statement here. A
homology concordance `W` from `K` to a knot `K'` in `S³`, capped off by the four-ball along `S³`,
would be a homology ball with boundary `Y` in which the annulus, together with the cone on `K'`,
is a piecewise-linear disc bounded by `K`.

`TauCeti.LevineHomologyConcordanceTheorem` records the statement in the smooth category, with
`ℤ` coefficients. It is stated, not proved. The four-manifolds `X` and `W` are modelled on the
half-space `ℝ³ × [0, ∞)`, the model `(𝓡 3).prod (𝓡∂ 1)` of the cylinders over `3`-manifolds; this
is the half-space of Lee's *Introduction to Smooth Manifolds*. No orientations are imposed; by the
discussion in `TauCeti/Geometry/Manifold/SmoothEmbedding/HomologyConcordance.lean` this only allows
`K'` to be replaced by its mirror or reverse, which are again knots in `S³`.

## Main definitions

* `TauCeti.LevineHomologyConcordanceTheorem`: some knot in the boundary of a smooth compact
  contractible `4`-manifold is not homology concordant to any knot in `S³`.

## Main results

* `TauCeti.not_forall_not_homologyConcordant_sphere`: every knot in `S³` is homology concordant to
  some knot in `S³`, so the boundary in Levine's theorem is not `S³`.

## References

* A. S. Levine, *Nonsurjective satellite operators and piecewise-linear concordance*, Forum Math.
  Sigma 4 (2016), e34, Theorem 1.1 and Remark 1.5.
* R. Kirby (ed.), *Problems in Low-Dimensional Topology*, Problem 1.31, in *Geometric Topology*,
  AMS/IP Stud. Adv. Math. 2.2 (1997).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer (2013), Chapter 1, for the half-space model.
-/

public section

open Manifold Metric Set
open scoped Manifold ContDiff

namespace TauCeti

/-- **Levine's theorem** (an answer to Kirby's problem 1.31): there are a smooth compact
contractible `4`-manifold `X`, whose boundary is a closed `3`-manifold `Y`, and a knot `K` in `Y`
that is not integrally homology concordant to any knot in `S³`.

The boundary of `X` is presented by a smooth embedding `κ : Y → X` onto it. The four-manifolds are
modelled on the half-space `ℝ³ × [0, ∞)`. It is recorded as a proposition and not proved. -/
def LevineHomologyConcordanceTheorem : Prop :=
  ∃ (Y : Type) (_ : TopologicalSpace Y) (_ : T2Space Y) (_ : CompactSpace Y)
    (_ : ChartedSpace (EuclideanSpace ℝ (Fin 3)) Y) (_ : IsManifold (𝓡 3) ∞ Y)
    (X : Type) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CompactSpace X)
    (_ : ContractibleSpace X)
    (_ : ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 3)) (EuclideanHalfSpace 1)) X)
    (_ : IsManifold ((𝓡 3).prod (𝓡∂ 1)) ∞ X)
    (κ : SmoothEmbedding (𝓡 3) ((𝓡 3).prod (𝓡∂ 1)) ∞ Y X) (K : SmoothCircleEmbedding (𝓡 3) Y),
    range κ = ((𝓡 3).prod (𝓡∂ 1)).boundary X ∧
      ∀ K' : SmoothCircleEmbedding (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1),
        ¬ HomologyConcordant ℤ ((𝓡 3).prod (𝓡∂ 1)) ∞ K K'

/-- Levine's theorem spelled out. -/
theorem levineHomologyConcordanceTheorem_iff :
    LevineHomologyConcordanceTheorem ↔
      ∃ (Y : Type) (_ : TopologicalSpace Y) (_ : T2Space Y) (_ : CompactSpace Y)
        (_ : ChartedSpace (EuclideanSpace ℝ (Fin 3)) Y) (_ : IsManifold (𝓡 3) ∞ Y)
        (X : Type) (_ : TopologicalSpace X) (_ : T2Space X) (_ : CompactSpace X)
        (_ : ContractibleSpace X)
        (_ : ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 3)) (EuclideanHalfSpace 1)) X)
        (_ : IsManifold ((𝓡 3).prod (𝓡∂ 1)) ∞ X)
        (κ : SmoothEmbedding (𝓡 3) ((𝓡 3).prod (𝓡∂ 1)) ∞ Y X)
        (K : SmoothCircleEmbedding (𝓡 3) Y),
        range κ = ((𝓡 3).prod (𝓡∂ 1)).boundary X ∧
          ∀ K' : SmoothCircleEmbedding (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1),
            ¬ HomologyConcordant ℤ ((𝓡 3).prod (𝓡∂ 1)) ∞ K K' :=
  Iff.rfl

/-- Every knot in `S³` is homology concordant to a knot in `S³`, namely itself, through the
cylinder `S³ × [0, 1]`. So the conclusion of Levine's theorem fails for knots in `S³`: the boundary
`Y` there is not `S³`. -/
theorem not_forall_not_homologyConcordant_sphere
    (K : SmoothCircleEmbedding (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)) :
    ¬ ∀ K' : SmoothCircleEmbedding (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1),
      ¬ HomologyConcordant ℤ ((𝓡 3).prod (𝓡∂ 1)) ∞ K K' :=
  fun h ↦ h K (.refl ℤ K)

end TauCeti
