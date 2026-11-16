/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.RingTheory.Finiteness.Small
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import TauCeti.Algebra.Category.HopfModuleCat.Basic
public import TauCeti.Algebra.Category.ModuleCat.Frobenius
import TauCeti.Algebra.HopfAlgebra.LarsonSweedler

/-!
# Modules over a finite-dimensional Hopf algebra form a Frobenius category

By the Larson–Sweedler theorem (`TauCeti.exists_isFrobeniusFunctional`), every finite-dimensional
Hopf algebra `H` over a field `k` admits a Frobenius functional. Consequently, the canonical exact
structure on the abelian category of **all** left `H`-modules — not only the finitely generated
ones — is a Frobenius exact structure: projective and injective objects coincide, and there are
enough of both.

We state this both for `ModuleCat.{w} H` in an arbitrary universe `w` with `[Small.{w} H]`, and
for `TauCeti.HopfModuleCat k H` (whose carrier universe is that of `k`, so `Small.{u} H` holds
automatically from finite-dimensionality). In particular, the stable category of all left
`H`-modules is triangulated by `TauCeti.ExactStructure.IsFrobenius.stableIsTriangulated`.

## Main results

* `ModuleCat.projective_iff_injective_of_hopfAlgebra`: over a finite-dimensional Hopf algebra, an
  object of `ModuleCat H` is projective if and only if it is injective.
* `ModuleCat.abelian_isFrobenius_of_hopfAlgebra`: the canonical exact structure on `ModuleCat H`
  is Frobenius.
* `TauCeti.HopfModuleCat.projective_iff_injective`: over a finite-dimensional Hopf algebra, an
  object of `HopfModuleCat k H` is projective if and only if it is injective.
* `TauCeti.HopfModuleCat.abelian_isFrobenius`: the canonical exact structure on
  `HopfModuleCat k H` is Frobenius.

## References

* M. Khovanov, *Hopfological algebra and categorification at a root of unity: the first steps*,
  J. Knot Theory Ramifications 25 (2016), Proposition 1.
* R. G. Larson and M. E. Sweedler, *An associative orthogonal bilinear form for Hopf algebras*,
  Amer. J. Math. 91 (1969), 75–94.
-/

public section

namespace ModuleCat

open CategoryTheory TauCeti

universe u v w

variable (k : Type u) [Field k] {H : Type v} [Ring H] [HopfAlgebra k H]
  [FiniteDimensional k H] [Small.{w} H]

include k in
/-- **Projective and injective modules over a finite-dimensional Hopf algebra coincide.** Over a
finite-dimensional Hopf algebra `H`, an object of `ModuleCat H` (not necessarily finitely
generated) is projective if and only if it is injective. -/
theorem projective_iff_injective_of_hopfAlgebra (X : ModuleCat.{w} H) :
    Projective X ↔ Injective X := by
  obtain ⟨_, hφ⟩ := exists_isFrobeniusFunctional k H
  exact projective_iff_injective_of_isFrobeniusFunctional hφ X

include k in
/-- **All modules over a finite-dimensional Hopf algebra form a Frobenius category.** For a
finite-dimensional Hopf algebra `H` over a field `k`, the canonical exact structure on the abelian
category `ModuleCat H` of all left `H`-modules is Frobenius. -/
theorem abelian_isFrobenius_of_hopfAlgebra :
    (ExactStructure.abelian (ModuleCat.{w} H)).IsFrobenius := by
  obtain ⟨_, hφ⟩ := exists_isFrobeniusFunctional k H
  exact abelian_isFrobenius hφ

end ModuleCat

namespace TauCeti.HopfModuleCat

open CategoryTheory

universe u v

variable {k : Type u} [Field k] {H : Type v} [Ring H] [HopfAlgebra k H]
  [FiniteDimensional k H]

/-- **Projective and injective objects of `HopfModuleCat k H` coincide.** Over a
finite-dimensional Hopf algebra `H`, a left `H`-module in `HopfModuleCat k H` (not necessarily
finitely generated) is projective if and only if it is injective. -/
theorem projective_iff_injective (X : HopfModuleCat k H) :
    Projective X ↔ Injective X := by
  have : Small.{u} H := Module.Finite.small k H
  exact ModuleCat.projective_iff_injective_of_hopfAlgebra k X

variable (k H) in
/-- **All modules over a finite-dimensional Hopf algebra form a Frobenius category.** For a
finite-dimensional Hopf algebra `H` over a field `k`, the canonical exact structure on
`HopfModuleCat k H` is Frobenius. -/
theorem abelian_isFrobenius :
    (ExactStructure.abelian (HopfModuleCat k H)).IsFrobenius := by
  have : Small.{u} H := Module.Finite.small k H
  exact ModuleCat.abelian_isFrobenius_of_hopfAlgebra k (H := H)

end TauCeti.HopfModuleCat
