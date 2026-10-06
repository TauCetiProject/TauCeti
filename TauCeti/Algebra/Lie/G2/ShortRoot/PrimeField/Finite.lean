/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.SpecialIsogeny
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.BaseChange
public import TauCeti.RingTheory.RingHom.Power

/-!
# Finiteness of the exceptional G2 endomorphism

The exceptional endomorphism of the short-root carrier over `𝔽₃` is finite, has a finite
scheme-theoretic kernel, and induces an involution on the prime spectrum of its coordinate
ring. In particular its map on the underlying scheme points is bijective. These facts follow
from the existing cubic Frobenius-square identity and do not assert faithful flatness.

The coordinate map and its square identity are constructed in
`TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.SpecialIsogeny`.
-/

public section

open CategoryTheory

namespace TauCeti.G2ShortRoot.PrimeField

private theorem specialIsogenyCoordinateMap_apply_apply (x : carrierAlgebra) :
    specialIsogenyCoordinateMap.hom (specialIsogenyCoordinateMap.hom x) = x ^ 3 := by
  have h := congrArg (fun f => f.hom x) specialIsogenyCoordinateMap_comp_self
  exact h.trans (frobeniusCoordinateMap_apply x)

/-- The exceptional G2 coordinate endomorphism is finite. -/
theorem finite_specialIsogenyCoordinateMap : specialIsogenyCoordinateMap.hom.toAlgHom.Finite :=
  specialIsogenyCoordinateMap.hom.toAlgHom.finite_of_comp_self_eq_pow (by decide)
    specialIsogenyCoordinateMap_apply_apply

/-- The scheme-theoretic kernel of the exceptional G2 endomorphism is finite over `𝔽₃`. -/
instance moduleFinite_quotient_kernel_specialIsogenyCoordinateMap :
    Module.Finite (ZMod 3)
      (carrierAlgebra ⧸ (CommHopfAlgCat.kernelHopfIdeal specialIsogenyCoordinateMap).toIdeal) :=
  CommHopfAlgCat.moduleFinite_quotient_kernelHopfIdeal finite_specialIsogenyCoordinateMap

/-- The exceptional G2 endomorphism induces an involution on the underlying prime spectrum.
It is therefore bijective there, even though the coordinate endomorphism need not be invertible. -/
theorem comap_specialIsogenyCoordinateMap_involutive :
    Function.Involutive (PrimeSpectrum.comap specialIsogenyCoordinateMap.hom.toAlgHom.toRingHom) :=
  specialIsogenyCoordinateMap.hom.toAlgHom.toRingHom.comap_involutive_of_comp_self_eq_pow
    (by decide) specialIsogenyCoordinateMap_apply_apply

end TauCeti.G2ShortRoot.PrimeField
