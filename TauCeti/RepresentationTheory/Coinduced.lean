/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Exactness of subgroup coinduction

Coinduction along a subgroup preserves short exact sequences of representations. Unlike
coinduction along an arbitrary homomorphism, subgroup coinduction preserves epimorphisms;
together with its right adjoint structure this gives exactness, without a finite-index
assumption. This allows connecting maps to be compared through Shapiro's isomorphism.

## References

* K. S. Brown, *Cohomology of Groups*, Chapter III, §6 and §9.
-/

public section

open CategoryTheory

namespace Rep

universe u

variable {R G : Type u} [CommRing R] [Group G]

/-- Coinduction acts additively on coefficient maps. -/
instance {H : Type u} [Group H] (φ : H →* G) :
    (coindFunctor.{u} R φ).Additive where
  map_add := by intro X Y f g; ext x; rfl

/-- Subgroup coinduction preserves homology of short complexes of representations. -/
noncomputable instance (H : Subgroup G) :
    (coindFunctor.{u} R H.subtype).PreservesHomology :=
  (coindFunctor.{u} R H.subtype).preservesHomology_of_preservesEpis_and_kernels

/-- Subgroup coinduction is exact, so also preserves finite colimits. -/
instance (H : Subgroup G) :
    Limits.PreservesFiniteColimits (coindFunctor.{u} R H.subtype) :=
  (coindFunctor.{u} R H.subtype).preservesFiniteColimits_of_preservesHomology

end Rep
