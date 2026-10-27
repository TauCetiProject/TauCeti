/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Mod
public import TauCeti.AlgebraicTopology.Spectra.SmashPow

/-!
# The sphere symmetric sequence and symmetric spectra

The sphere sequence `n ↦ S^n = (S¹)^∧n`, with the coordinate-permutation actions of `Σ_n` and the
block-concatenation maps `S^p ∧ S^q → S^(p+q)`, is a braided monoidal functor out of the
finite-bijection groupoid (`PointedSSet.sphereSequence`). Regarded as a symmetric sequence, it is
the monoid `SymmetricSequence.smashPow PointedSSet.circle` of smash powers of the circle, and so
a commutative monoid for the Day convolution product: its multiplication `S ⊗ S ⟶ S` is induced
by block concatenation of sphere coordinates (`SymmetricSequence.smashPow_mul_app_smashMk`) and
its unit by `S⁰ ≅ S^0`. Following Hovey, Shipley and Smith, a symmetric spectrum is a module over
this commutative monoid.

Unwinding the universal property of the Day convolution, a symmetric spectrum `X` amounts to a
symmetric sequence of pointed simplicial sets `X_n` with based `Σ_p × Σ_q`-equivariant structure
maps `S^p ∧ X_q → X_(p+q)`, compatible with the unit `S⁰ ≅ S^0` and with block concatenation of
spheres; this description in terms of structure maps is not formalized in this file.

## Main definitions

* `SymmetricSequence.sphere`: the sphere symmetric sequence. Its commutative monoid structure is
  the instance `DayFunctor.monObj`, with commutativity `DayFunctor.isCommMonObj`.
* `SymmetricSpectrum`: symmetric spectra of pointed simplicial sets, the modules over
  `SymmetricSequence.sphere`.

## References

* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc. 13 (2000),
  Sections 1 and 2.
* S. Schwede, *Symmetric spectra*, book project, Chapter I.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti

open scoped DayFunctor

/-- The sphere symmetric sequence `n ↦ S^n = (S¹)^∧n`, with the coordinate-permutation actions.
Block concatenation `S^p ∧ S^q → S^(p+q)` and `S⁰ ≅ S^0` make it a commutative monoid for the Day
convolution product, through the instances `DayFunctor.monObj` and `DayFunctor.isCommMonObj`. -/
-- An abbreviation, so that the instances for lax braided functors apply to it.
noncomputable abbrev SymmetricSequence.sphere : SymmetricSequence.{0} :=
  smashPow PointedSSet.circle

/- The sphere symmetric sequence is a commutative monoid for the Day convolution product. -/
noncomputable example : IsCommMonObj SymmetricSequence.sphere := inferInstance

/-- Symmetric spectra of pointed simplicial sets: the modules over the commutative monoid
`SymmetricSequence.sphere` of symmetric sequences. A symmetric spectrum is a symmetric sequence
`X` with an action `S ⊗ X ⟶ X` for the Day convolution product, satisfying the unit and
associativity laws. -/
abbrev SymmetricSpectrum := Mod SymmetricSequence.{0} SymmetricSequence.sphere

end TauCeti
