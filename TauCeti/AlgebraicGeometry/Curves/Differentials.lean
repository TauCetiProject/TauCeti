/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.HighDegree
public import TauCeti.AlgebraicGeometry.Curves.Smooth
public import TauCeti.AlgebraicGeometry.Modules.Differentials.Canonical
public import TauCeti.AlgebraicGeometry.Modules.Differentials.Rank
public import TauCeti.AlgebraicGeometry.Morphisms.Separated
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.RiemannRoch.GeometricallyIntegral

/-!
# The sheaf of differentials of a smooth proper curve

Let `X` be smooth, proper and geometrically connected of relative dimension one over a field `k`,
with genus `g = dim_k H¹(X, 𝒪_X)`. No rational point and no perfectness of `k` is assumed. This
file shows that the invertible sheaf of differentials `Ω_{X/k}` has the numerical invariants of
a canonical bundle:

* `dim_k H⁰(X, Ω_{X/k}) = g` and `dim_k H¹(X, Ω_{X/k}) = 1`;
* its Euler-characteristic degree is `2g - 2`;
* for every line bundle `L`, `dim H¹(X, L) = dim H⁰(X, Ω_{X/k} ⊗ L⁻¹)`, and Riemann–Roch holds
  in the form `dim H⁰(X, L) - dim H⁰(X, Ω_{X/k} ⊗ L⁻¹) = deg L + 1 - g`.

These are the results of `TauCeti.AlgebraicGeometry.Modules.Differentials.Canonical` for integral
curves over an exact constant field, and the point is that the standing hypotheses imply all of
theirs. The curve is geometrically integral
(`TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral`), hence integral, and `k` is integrally
closed in its function field
(`TauCeti.AlgebraicGeometry.isIntegrallyClosedIn_functionField_of_geometricallyIntegral`). It is a
curve in the sense of `AlgebraicGeometry.Scheme.IsCurveOver`, so it is Noetherian with points of
coheight at most one, its function field is an algebraic function field of one variable, and its
structure morphism satisfies the existence part of the valuative criterion. It is separated, its
codimension-one local rings are discrete valuation rings, and its differentials are invertible.

Geometric connectedness cannot be weakened to connectedness. For a separable quadratic extension
`l/k`, the projective line over `l` regarded over `k` is smooth, proper and connected of genus
zero, but `H⁰(𝒪) = l`, `dim_k H¹(Ω) = 2` and its differentials have degree `-4`, not `2g - 2`.

## Main results

* `finrank_cohomology_zero_relativeDifferentials_of_smooth`: `dim_k H⁰(X, Ω_{X/k}) = g`;
* `finrank_cohomology_one_relativeDifferentials_of_smooth`: `dim_k H¹(X, Ω_{X/k}) = 1`;
* `eulerDegree_relativeDifferentials_of_smooth`: `deg Ω_{X/k} = 2g - 2`;
* `finrank_cohomology_one_eq_finrank_cohomology_zero_differentials_tensor_dual_of_smooth`:
  `dim H¹(X, L) = dim H⁰(X, Ω_{X/k} ⊗ L⁻¹)`;
* `finrank_cohomology_zero_sub_finrank_cohomology_zero_differentials_tensor_dual_of_smooth`:
  Riemann–Roch with the sheaf of differentials.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter IV, Section 1.
* The Stacks Project, Tag 0BUG and Tag 0C1A.
-/

public section

open CategoryTheory AlgebraicGeometry Order
open Module (finrank)

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
  [GeometricallyConnected (X ↘ Spec (.of k))]

/-- A statement which holds on every integral Noetherian separated curve over an exact constant
field, with invertible differentials, discrete valuation rings at its codimension-one points and
the existence part of the valuative criterion, holds on a smooth proper geometrically connected
curve. -/
private lemma of_canonicalCurve {P : Prop}
    (h : ∀ [IsIntegral X] [IsNoetherian X] [X.IsSeparated]
      [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]
      [SheafOfModules.isInvertible X (X.relativeDifferentials k)],
      IsFunctionField k X.functionField → IsIntegrallyClosedIn k X.functionField →
        (∀ y : X, coheight y ≤ 1) → ValuativeCriterion.Existence (X ↘ Spec (.of k)) → P) :
    P := by
  obtain ⟨hI, hDVR, hcoheight, hF, hk⟩ :=
    InvertibleSheaf.high_degree_hypotheses_of_smooth (k := k) (X := X)
  have := hI
  have := hDVR
  have := SmoothOfRelativeDimension.smooth 1 (X ↘ Spec (.of k))
  have := Scheme.IsCurveOver.of_smooth k X
  have := Scheme.IsCurveOver.isNoetherian k X
  have := Scheme.IsSeparated.of_isSeparated (X ↘ Spec (.of k))
  have := isInvertible_relativeDifferentials k (X := X)
  exact h hF hk hcoheight (Scheme.IsCurveOver.valuativeCriterion_existence k X)

/-- **The global differentials have dimension the genus.** On a smooth proper geometrically
connected curve over `k`, `dim_k H⁰(X, Ω_{X/k}) = g`. -/
theorem finrank_cohomology_zero_relativeDifferentials_of_smooth :
    finrank k (Scheme.Modules.Cohomology (X.relativeDifferentials k) 0) = X.genus k :=
  of_canonicalCurve fun hF hk hdim hex ↦
    finrank_cohomology_zero_relativeDifferentials hF hk hdim hex

/-- On a smooth proper geometrically connected curve over `k`, `H¹(X, Ω_{X/k})` is
one-dimensional over `k`, the same dimension as the constants `H⁰(X, 𝒪_X) = k`. -/
@[simp]
theorem finrank_cohomology_one_relativeDifferentials_of_smooth :
    finrank k (Scheme.Modules.Cohomology (X.relativeDifferentials k) 1) = 1 :=
  of_canonicalCurve fun hF hk hdim hex ↦
    finrank_cohomology_one_relativeDifferentials hF hk hdim hex

/-- **The differentials have degree `2g - 2`.** On a smooth proper geometrically connected curve
over `k`, the Euler-characteristic degree of `Ω_{X/k}` is `2g - 2`. -/
@[simp]
theorem eulerDegree_relativeDifferentials_of_smooth :
    (InvertibleSheaf.relativeDifferentials k X).eulerDegree k = 2 * X.genus k - 2 :=
  of_canonicalCurve fun hF hk hdim hex ↦
    (InvertibleSheaf.eulerDegree_congr k (M := ⟨X.relativeDifferentials k, inferInstance⟩)
      (eqToIso (InvertibleSheaf.relativeDifferentials_obj k X))).trans
      (eulerDegree_relativeDifferentials hF hk hdim hex)

/-- **The dimensions in Serre duality agree.** On a smooth proper geometrically connected curve
over `k`, every line bundle `L` satisfies `dim H¹(X, L) = dim H⁰(X, Ω_{X/k} ⊗ L⁻¹)`. -/
theorem finrank_cohomology_one_eq_finrank_cohomology_zero_differentials_tensor_dual_of_smooth
    (L : InvertibleSheaf X) :
    finrank k (Scheme.Modules.Cohomology L.obj 1) =
      finrank k (Scheme.Modules.Cohomology (InvertibleSheaf.tensorProduct
        (InvertibleSheaf.relativeDifferentials k X) (InvertibleSheaf.dual L)).obj 0) :=
  of_canonicalCurve fun hF hk hdim hex ↦ by
    obtain ⟨e⟩ := nonempty_iso_relativeDifferentials_canonicalBundle (k := k) (X := X)
      hF hk hdim hex
    exact InvertibleSheaf.finrank_cohomology_one_eq_finrank_cohomology_zero_tensor_dual
      hex hdim hF hk L _
      (LineBundleClass.mk_eq_mk_iff.mpr
        ⟨eqToIso (InvertibleSheaf.relativeDifferentials_obj k X) ≪≫ e⟩)

/-- **The Riemann–Roch theorem with the sheaf of differentials.** On a smooth proper
geometrically connected curve over `k`, every line bundle `L` satisfies
`dim H⁰(X, L) - dim H⁰(X, Ω_{X/k} ⊗ L⁻¹) = deg L + 1 - g`. -/
theorem finrank_cohomology_zero_sub_finrank_cohomology_zero_differentials_tensor_dual_of_smooth
    (L : InvertibleSheaf X) :
    (finrank k (Scheme.Modules.Cohomology L.obj 0) : ℤ) -
        finrank k (Scheme.Modules.Cohomology (InvertibleSheaf.tensorProduct
          (InvertibleSheaf.relativeDifferentials k X) (InvertibleSheaf.dual L)).obj 0) =
      L.eulerDegree k + 1 - X.genus k := by
  have := SmoothOfRelativeDimension.smooth 1 (X ↘ Spec (.of k))
  rw [← finrank_cohomology_one_eq_finrank_cohomology_zero_differentials_tensor_dual_of_smooth
    (k := k) L, ← Scheme.Modules.eulerCharBelow_two]
  exact InvertibleSheaf.eulerCharBelow_eq_eulerDegree_add_one_sub_genus_of_geometricallyIntegral
    k L

end

end TauCeti.AlgebraicGeometry
