/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Spin.Polarization.Basic
public import Mathlib.FieldTheory.IsSepClosed
import TauCeti.LinearAlgebra.QuadraticForm.Isometry
import TauCeti.LinearAlgebra.QuadraticForm.SepClosed
import TauCeti.RepresentationTheory.Spin.Polarization.Split.Even
import TauCeti.RepresentationTheory.Spin.Polarization.Split.Odd

/-!
# Existence of polarization data

This file constructs `TauCeti.SpinPolarizationData` for finite-dimensional nondegenerate
quadratic spaces over separably closed fields of characteristic different from two.

Over such a field a nondegenerate quadratic form is determined up to isometry by its dimension
(`QuadraticForm.equivalent_of_finrank_eq_of_isSepClosed`), so it is isometric to the standard
split form of the same dimension, `TauCeti.splitEvenForm` or `TauCeti.splitOddForm`. The
polarization is the pullback of the canonical polarization of that split form along such an
isometry.

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

/-- Polarization data pulled back along an isometric equivalence. -/
private def pullback {K : Type*} [CommRing K] {V V' : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module K V'] {Q : QuadraticForm K V} {Q' : QuadraticForm K V'}
    (e : Q.IsometryEquiv Q') (P : SpinPolarizationData Q') : SpinPolarizationData Q :=
  let eS (S : Submodule K V') : S.comap e.toLinearEquiv.toLinearMap ≃ₗ[K] S :=
    Submodule.comap_equiv_self_of_inj_of_le e.toLinearEquiv.injective (by simp)
  have he (S : Submodule K V') (x) : (eS S x : V') = e x := by simp [eS]
  { W := P.W.comap e.toLinearEquiv.toLinearMap
    W' := P.W'.comap e.toLinearEquiv.toLinearMap
    line := P.line.comap e.toLinearEquiv.toLinearMap
    decompositionEquiv := (((eS P.W).prodCongr (eS P.W')).prodCongr (eS P.line)).trans <|
      P.decompositionEquiv.trans e.toLinearEquiv.symm
    decompositionEquiv_apply x := e.toLinearEquiv.injective <| by simp [he]
    isotropic_W x := by rw [← e.map_app, ← he P.W, P.isotropic_W]
    isotropic_W' y := by rw [← e.map_app, ← he P.W', P.isotropic_W']
    pairingEquiv := (eS P.W').trans <| P.pairingEquiv.trans (eS P.W).dualMap
    pairingEquiv_apply y x := by
      simp only [LinearEquiv.trans_apply, LinearEquiv.dualMap_apply, P.pairingEquiv_apply, he,
        e.polar_apply]
    pairing_separatingLeft x hx := (eS P.W).map_eq_zero_iff.mp <| P.pairing_separatingLeft _ <|
      (eS P.W').surjective.forall.mpr fun y ↦ by rw [he, he, e.polar_apply, hx]
    lineCoordinate := P.lineCoordinate.comp (eS P.line).toLinearMap
    lineCoordinate_injective := P.lineCoordinate_injective.comp (eS P.line).injective
    lineCoordinate_sq z := by
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, P.lineCoordinate_sq, he, e.map_app]
    line_orthogonal_W z x := by rw [← e.polar_apply, ← he P.line, ← he P.W, P.line_orthogonal_W]
    line_orthogonal_W' z y := by
      rw [← e.polar_apply, ← he P.line, ← he P.W', P.line_orthogonal_W'] }

variable {F : Type u} [Field F] [NeZero (2 : F)] [IsSepClosed F]
  {V : Type v} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- Polarization data on a nondegenerate quadratic space, pulled back from a polarized quadratic
space of the same dimension. -/
private def ofFinrankEq {Q : QuadraticForm F V} (hQ : Q.Nondegenerate) {V' : Type*}
    [AddCommGroup V'] [Module F V'] [FiniteDimensional F V'] {Q' : QuadraticForm F V'}
    (P : SpinPolarizationData Q') (h : finrank F V = finrank F V') : SpinPolarizationData Q :=
  letI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  pullback (Classical.choice <| Q.equivalent_of_finrank_eq_of_isSepClosed Q' hQ
    (P.nondegenerate (.of_ne_zero two_ne_zero)) h) P

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
