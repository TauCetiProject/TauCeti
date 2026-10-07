/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.QuotientSpecialIsogeny
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.BaseChange
public import TauCeti.RingTheory.RingHom.Power

/-!
# Finiteness of the exceptional F4 endomorphism

The represented-quotient endomorphism of the short-root carrier over `𝔽₂` is finite, has a
finite scheme-theoretic kernel, and induces an involution on the prime spectrum of its
coordinate ring. In particular its map on the underlying scheme points is bijective. These
facts follow from the existing quadratic Frobenius-square identity; faithful flatness is
a separate question.

The coordinate map and its square identity are constructed in
`TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.QuotientSpecialIsogeny`.
-/

public section

open CategoryTheory

namespace TauCeti.F4ShortRoot.PrimeField

private theorem quotientIsogeny_apply_apply
    (x : CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra (ZMod 2) 26)
      (CommHopfAlgCat.commonKernelHopfIdeal generator)) :
    quotientIsogeny.hom (quotientIsogeny.hom x) = x ^ 2 := by
  have h := congrArg (fun f => f.hom x) quotientIsogeny_comp_self
  simpa only [CommHopfAlgCat.hom_comp, BialgHom.comp_apply, CommHopfAlgCat.hom_ofHom,
    frobeniusBialgHom_apply, ZMod.card] using h

/-- The exceptional F4 coordinate endomorphism is finite. -/
theorem finite_quotientIsogeny : quotientIsogeny.hom.toAlgHom.Finite :=
  quotientIsogeny.hom.toAlgHom.finite_of_comp_self_eq_pow (by decide)
    quotientIsogeny_apply_apply

/-- The scheme-theoretic kernel of the exceptional F4 endomorphism is finite over `𝔽₂`. -/
instance moduleFinite_quotient_kernel_quotientIsogeny :
    Module.Finite (ZMod 2)
      (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra (ZMod 2) 26)
        (CommHopfAlgCat.commonKernelHopfIdeal generator) ⧸
          (CommHopfAlgCat.kernelHopfIdeal quotientIsogeny).toIdeal) :=
  CommHopfAlgCat.moduleFinite_quotient_kernelHopfIdeal finite_quotientIsogeny

/-- The exceptional F4 endomorphism induces an involution on the underlying prime spectrum.
It is therefore bijective there, even though the coordinate endomorphism need not be invertible. -/
theorem comap_quotientIsogeny_involutive :
    Function.Involutive (PrimeSpectrum.comap quotientIsogeny.hom.toAlgHom.toRingHom) :=
  quotientIsogeny.hom.toAlgHom.toRingHom.comap_involutive_of_comp_self_eq_pow
    (by decide) quotientIsogeny_apply_apply

end TauCeti.F4ShortRoot.PrimeField
