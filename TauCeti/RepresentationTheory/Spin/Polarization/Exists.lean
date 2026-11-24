/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Spin.Polarization.Basic
public import Mathlib.FieldTheory.IsSepClosed
import TauCeti.LinearAlgebra.QuadraticForm.SepClosed
import TauCeti.RepresentationTheory.Spin.Polarization.Map
import TauCeti.RepresentationTheory.Spin.Polarization.Split.Even
import TauCeti.RepresentationTheory.Spin.Polarization.Split.Odd

/-!
# Existence of polarization data

This file constructs `TauCeti.SpinPolarizationData` for finite-dimensional nondegenerate
quadratic spaces over separably closed fields of characteristic different from two.

Over such a field a nondegenerate quadratic form is determined up to isometry by its dimension
(`QuadraticForm.equivalent_of_finrank_eq_of_isSepClosed`), so it is isometric to the standard
split form of the same dimension, `TauCeti.splitEvenForm` or `TauCeti.splitOddForm`. The
polarization is the canonical polarization of that split form, transported back along such an
isometry by `TauCeti.SpinPolarizationData.map`.

## Main definition

* `TauCeti.SpinPolarizationData.ofNondegenerate` constructs the data for a finite-dimensional
  nondegenerate quadratic space over a separably closed field of characteristic different from
  two.
-/

public section

open Module

namespace TauCeti

universe u v

namespace SpinPolarizationData

noncomputable section

variable {F : Type u} [Field F] [NeZero (2 : F)] [IsSepClosed F]
  {V : Type v} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- Polarization data on a nondegenerate quadratic space, pulled back from a polarized quadratic
space of the same dimension. -/
private def ofFinrankEq {Q : QuadraticForm F V} (hQ : Q.Nondegenerate) {V' : Type*}
    [AddCommGroup V'] [Module F V'] [FiniteDimensional F V'] {Q' : QuadraticForm F V'}
    (P : SpinPolarizationData Q') (h : finrank F V = finrank F V') : SpinPolarizationData Q :=
  letI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  P.map (Classical.choice <| Q.equivalent_of_finrank_eq_of_isSepClosed Q' hQ
    (P.nondegenerate (.of_ne_zero two_ne_zero)) h).symm

/-- Every finite-dimensional nondegenerate quadratic space over a separably closed field of
characteristic different from two admits polarization data. -/
def ofNondegenerate (Q : QuadraticForm F V) (hQ : Q.Nondegenerate) : SpinPolarizationData Q :=
  if hV : Even (finrank F V) then
    ofFinrankEq hQ (splitEvenPolarization F (finrank F V / 2)) (by simp; grind)
  else
    ofFinrankEq hQ (splitOddPolarization F (finrank F V / 2)) (by simp; grind)

end

end SpinPolarizationData

end TauCeti
