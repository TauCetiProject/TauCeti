/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Genus
public import TauCeti.AlgebraicGeometry.Geometrically.GlobalSections

/-!
# The structure sheaf of a geometrically integral scheme

On a scheme `X` universally closed and geometrically integral over a field `k`, every global
function is constant (`Scheme.baseRingToGlobalSections_bijective_of_geometricallyIntegral`), even
when `X` has no `k`-rational point. The results of `TauCeti.AlgebraicGeometry.Cohomology.Genus`
for schemes whose global functions are constants therefore give `dim_k H⁰(X, 𝒪_X) = 1` and
`χ(𝒪_X) = 1 - g`, where `χ` is the truncation `dim H⁰ - dim H¹` and `g` is the genus.

These statements are kept apart from `TauCeti.AlgebraicGeometry.Cohomology.Genus` so that its
importers do not also import the geometric-integrality theory of global sections.

## Main results

* `TauCeti.AlgebraicGeometry.finrank_cohomology_zero_trivial_eq_one_of_geometricallyIntegral`:
  `dim_k H⁰(X, 𝒪_X) = 1`;
* `TauCeti.AlgebraicGeometry.eulerCharBelow_trivial_eq_one_sub_genus_of_geometricallyIntegral`:
  `χ(𝒪_X) = 1 - g`.

## References

* R. Hartshorne, *Algebraic Geometry*, Exercise III.5.3 (the arithmetic genus).
* The Stacks Project, Section 33.9, *Geometrically integral schemes*.
-/

public section

open AlgebraicGeometry CategoryTheory
open Module (finrank)

namespace TauCeti.AlgebraicGeometry

universe u

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [UniversallyClosed (X ↘ Spec (.of k))] [GeometricallyIntegral (X ↘ Spec (.of k))]

/-- **The constants are exact.** On a universally closed geometrically integral scheme over a
field `k`, `H⁰(X, 𝒪_X)` is one-dimensional over `k`. No rational point is needed. -/
theorem finrank_cohomology_zero_trivial_eq_one_of_geometricallyIntegral :
    finrank k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 0) = 1 := by
  have := GeometricallyIntegral.isIntegral_of_subsingleton (X ↘ Spec (.of k))
  exact finrank_cohomology_zero_trivial_eq_one_of_surjective k
    (X.baseRingToGlobalSections_bijective_of_geometricallyIntegral k).surjective

/-- On a universally closed geometrically integral scheme over a field `k` with
finite-dimensional `H¹(X, 𝒪_X)`, `χ(𝒪_X) = 1 - g`, where `χ` is the truncation
`dim H⁰ - dim H¹` and `g` is the genus. No rational point is needed. -/
theorem eulerCharBelow_trivial_eq_one_sub_genus_of_geometricallyIntegral
    [FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1)] :
    Scheme.Modules.eulerCharBelow k X (InvertibleSheaf.trivial X).obj 2 = 1 - X.genus k := by
  have := GeometricallyIntegral.isIntegral_of_subsingleton (X ↘ Spec (.of k))
  exact eulerCharBelow_trivial_eq_one_sub_genus_of_surjective k
    (X.baseRingToGlobalSections_bijective_of_geometricallyIntegral k).surjective

end TauCeti.AlgebraicGeometry
