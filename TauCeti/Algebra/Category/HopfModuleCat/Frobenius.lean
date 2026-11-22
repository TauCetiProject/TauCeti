/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.HopfModuleCat.Basic
public import TauCeti.Algebra.Category.ModuleCat.Frobenius.Basic
public import TauCeti.Algebra.HopfAlgebra.Frobenius
import Mathlib.RingTheory.Finiteness.Small

/-!
# Frobenius exact structure on `HopfModuleCat`

Let `H` be a finite-dimensional algebra over a field `k`. When `H` carries a Frobenius functional
`φ`, smallness of `H` in the universe of `k` holds automatically by finite-dimensionality over `k`,
so `ModuleCat.projective_iff_injective_of_isFrobeniusFunctional` and `ModuleCat.abelian_isFrobenius`
transport directly to `TauCeti.HopfModuleCat k H`:

* an object of `HopfModuleCat k H` (not necessarily finite-dimensional) is projective if and only if
  it is injective (`TauCeti.HopfModuleCat.projective_iff_injective_of_isFrobeniusFunctional`);
* the canonical abelian exact structure on `HopfModuleCat k H` is Frobenius
  (`TauCeti.HopfModuleCat.abelian_isFrobenius_of_isFrobeniusFunctional`).

When `H` is a finite-dimensional Hopf algebra over `k`, the Larson–Sweedler theorem
(`TauCeti.exists_isFrobeniusFunctional_of_hopfAlgebra`) supplies such a Frobenius functional
unconditionally, giving `TauCeti.HopfModuleCat.projective_iff_injective` and
`TauCeti.HopfModuleCat.abelian_isFrobenius`. Together with
`TauCeti.ExactStructure.IsFrobenius.stableIsTriangulated`, the `ProjectiveStableCategory` of
`HopfModuleCat k H` is Khovanov's stable module category of all `H`-modules as a triangulated
category.

## Main declarations

* `TauCeti.HopfModuleCat.projective_iff_injective_of_isFrobeniusFunctional` and
  `TauCeti.HopfModuleCat.abelian_isFrobenius_of_isFrobeniusFunctional`: Frobenius exact structure on
  `HopfModuleCat k H` from a Frobenius functional on a finite-dimensional `k`-algebra `H`.
* `TauCeti.HopfModuleCat.projective_iff_injective` and `TauCeti.HopfModuleCat.abelian_isFrobenius`:
  unconditional specialization to any finite-dimensional Hopf algebra `H` over `k`.

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

namespace TauCeti.HopfModuleCat

universe u v

section Frobenius

variable {k : Type u} [Field k] {H : Type v} [Ring H] [Algebra k H] [FiniteDimensional k H]
  {φ : H →ₗ[k] k}

/-- Over a finite-dimensional `k`-algebra `H` equipped with a Frobenius functional, an object of
`HopfModuleCat k H` (not necessarily finite-dimensional) is projective if and only if it is
injective. -/
theorem projective_iff_injective_of_isFrobeniusFunctional (hφ : φ.IsFrobeniusFunctional)
    (X : HopfModuleCat k H) : Projective X ↔ Injective X := by
  have := Module.Finite.small k H
  exact ModuleCat.projective_iff_injective_of_isFrobeniusFunctional hφ (X : ModuleCat.{u} H)

/-- Over a finite-dimensional `k`-algebra `H` equipped with a Frobenius functional, the canonical
abelian exact structure on `HopfModuleCat k H` is Frobenius, with no universe-smallness hypothesis
needed beyond finite-dimensionality of `H` over `k`. -/
theorem abelian_isFrobenius_of_isFrobeniusFunctional (hφ : φ.IsFrobeniusFunctional) :
    (ExactStructure.abelian (HopfModuleCat k H)).IsFrobenius := by
  have := Module.Finite.small k H
  exact ModuleCat.abelian_isFrobenius hφ

end Frobenius

section HopfAlgebra

variable {k : Type u} [Field k] {H : Type v} [Ring H] [HopfAlgebra k H] [FiniteDimensional k H]

/-- Over a finite-dimensional Hopf algebra `H` over `k`, an object of `HopfModuleCat k H` (not
necessarily finite-dimensional) is projective if and only if it is injective. -/
theorem projective_iff_injective (X : HopfModuleCat k H) :
    Projective X ↔ Injective X := by
  obtain ⟨_, hφ⟩ := exists_isFrobeniusFunctional_of_hopfAlgebra k H
  exact projective_iff_injective_of_isFrobeniusFunctional hφ X

variable (k H) in
/-- **All modules over a finite-dimensional Hopf algebra form a Frobenius category**: the canonical
abelian exact structure on `HopfModuleCat k H` is Frobenius, with no universe-smallness hypothesis
needed beyond finite-dimensionality of `H` over `k`. -/
theorem abelian_isFrobenius :
    (ExactStructure.abelian (HopfModuleCat k H)).IsFrobenius := by
  obtain ⟨_, hφ⟩ := exists_isFrobeniusFunctional_of_hopfAlgebra k H
  exact abelian_isFrobenius_of_isFrobeniusFunctional hφ

end HopfAlgebra

end TauCeti.HopfModuleCat
