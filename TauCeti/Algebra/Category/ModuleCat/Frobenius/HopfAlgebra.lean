/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Frobenius.Basic
public import TauCeti.Algebra.HopfAlgebra.Frobenius

/-!
# All modules over a finite-dimensional Hopf algebra form a Frobenius category (`ModuleCat`)

Let `H` be a finite-dimensional Hopf algebra over a field `k`. By the Larson–Sweedler theorem
(`TauCeti.exists_isFrobeniusFunctional_of_hopfAlgebra`), `H` admits a Frobenius functional.
Specializing `ModuleCat.projective_iff_injective_of_isFrobeniusFunctional` and
`ModuleCat.abelian_isFrobenius` therefore shows that in `ModuleCat.{w} H` (for any universe `w` in
which `H` is small), an arbitrary left `H`-module is projective if and only if it is injective, and
the canonical abelian exact structure on `ModuleCat.{w} H` is Frobenius.

## Main declarations

* `ModuleCat.projective_iff_injective_of_hopfAlgebra`: over a finite-dimensional Hopf algebra, an
  object of `ModuleCat.{w} H` (not necessarily finitely generated) is projective if and only if it
  is injective.
* `ModuleCat.abelian_isFrobenius_of_hopfAlgebra`: the canonical exact structure on `ModuleCat.{w} H`
  is Frobenius.

## References

* M. Khovanov, *Hopfological algebra and categorification at a root of unity: the first steps*,
  J. Knot Theory Ramifications 25 (2016), Proposition 1.
* R. G. Larson and M. E. Sweedler, *An associative orthogonal bilinear form for Hopf algebras*,
  Amer. J. Math. 91 (1969), 75–94.
* D. Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional Algebras*,
  Chapter I, Section 2.
-/

public section

open CategoryTheory

namespace ModuleCat

open TauCeti

universe w

variable (k : Type*) [Field k] {H : Type*} [Ring H] [HopfAlgebra k H] [FiniteDimensional k H]
  [Small.{w} H]

include k in
/-- Over a finite-dimensional Hopf algebra, an object of `ModuleCat.{w} H` (not necessarily
finitely generated) is projective if and only if it is injective. -/
theorem projective_iff_injective_of_hopfAlgebra (X : ModuleCat.{w} H) :
    Projective X ↔ Injective X := by
  obtain ⟨_, hφ⟩ := exists_isFrobeniusFunctional_of_hopfAlgebra k H
  exact projective_iff_injective_of_isFrobeniusFunctional hφ X

include k in
/-- Over a finite-dimensional Hopf algebra, the canonical exact structure on `ModuleCat.{w} H` is
Frobenius. -/
theorem abelian_isFrobenius_of_hopfAlgebra :
    (ExactStructure.abelian (ModuleCat.{w} H)).IsFrobenius := by
  obtain ⟨_, hφ⟩ := exists_isFrobeniusFunctional_of_hopfAlgebra k H
  exact abelian_isFrobenius hφ

end ModuleCat
