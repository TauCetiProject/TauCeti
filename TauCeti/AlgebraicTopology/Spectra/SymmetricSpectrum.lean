/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Spectra.SmashPow
public import TauCeti.CategoryTheory.Monoidal.DayConvolution.Module
public import TauCeti.CategoryTheory.Monoidal.Mod.InternalHom
public import TauCeti.CategoryTheory.Monoidal.Mod.Bimodule

/-!
# The sphere symmetric sequence and symmetric spectra

The sphere sequence `n ↦ S^n = (S¹)^∧n`, with the coordinate-permutation actions of `Σ_n` and the
block-concatenation maps `S^p ∧ S^q → S^(p+q)`, is a braided monoidal functor out of the
finite-bijection groupoid (`PointedSSet.smashPowFunctor PointedSSet.circle`). Regarded as a
symmetric sequence, it is the monoid `SymmetricSequence.smashPow PointedSSet.circle` of smash
powers of the circle, and so a commutative monoid for the Day convolution product: its
multiplication `S ⊗ S ⟶ S` is induced by block concatenation of sphere coordinates
(`SymmetricSequence.smashPow_mul_app_smashMk`) and its unit by `S⁰ ≅ S^0`. Following Hovey,
Shipley and Smith, a symmetric spectrum is a module over this commutative monoid.

Unwinding the universal property of the Day convolution, a symmetric spectrum `X` amounts to a
symmetric sequence of pointed simplicial sets `X_n` with based `Σ_p × Σ_q`-equivariant structure
maps `S^p ∧ X_q → X_(p+q)`, compatible with the unit `S⁰ ≅ S^0` and with block concatenation of
spheres. These iterated structure maps and their laws are developed in
`TauCeti.CategoryTheory.Monoidal.DayConvolution.Module`, through the generic
`CategoryTheory.Mod.dayStructureMap` API.

As the sphere monoid is commutative and Day convolution is closed, symmetric spectra have internal
function spectra `Hom_S(X, Y) = (Mod.internalHom X).obj Y`: the equalizer of the two maps
`Hom(X, Y) ⇉ Hom(S ⊗ X, Y)` of internal homs of symmetric sequences given by the actions on `X`
and on `Y`, with the sphere acting through `X`. Spectrum maps `X ⊗ K ⟶ Y` out of the Day
convolution of `X` with a symmetric sequence `K` are the maps of symmetric sequences
`K ⟶ Hom_S(X, Y)` (`Mod.ihomAdjunction`).

The commutative sphere action also gives a native sphere bimodule via
`CategoryTheory.Mod.toBimod`: the right action is obtained by swapping the sphere and
spectrum factors before applying the left action. This adapter is fully faithful.

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

/- The function spectrum `Hom_S(X, Y)` of symmetric spectra, through `Mod.internalHom`. -/
noncomputable example (X Y : SymmetricSpectrum) : SymmetricSpectrum := (Mod.internalHom X).obj Y

/- Spectrum maps `X ⊗ K ⟶ Y` are the maps of symmetric sequences `K ⟶ Hom_S(X, Y)`. -/
noncomputable example (X : SymmetricSpectrum) : Mod.tensorLeft X ⊣ Mod.ihom X :=
  Mod.ihomAdjunction X

/- The native bimodule adapter applies to the actual sphere-module carrier. -/
noncomputable example :
    (Mod.toBimod (C := SymmetricSequence.{0}) (A := SymmetricSequence.sphere)).FullyFaithful :=
  Mod.fullyFaithfulToBimod

end TauCeti
