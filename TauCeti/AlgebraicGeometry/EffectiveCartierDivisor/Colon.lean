/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Subtraction
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.TensorProduct

/-!
# Picard-group classes of differences of effective Cartier divisors

This file supplements `TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Subtraction` with the
Picard-group identity `[(I : J)] = [I] * [J]⁻¹`
(`TauCeti.AlgebraicGeometry.LineBundleClass.mk_toInvertibleSheaf_colon`) for nested effective
Cartier divisors `I ≤ J`.

## Main results

* `TauCeti.AlgebraicGeometry.LineBundleClass.mk_toInvertibleSheaf_colon`:
  `[(I : J)] = [I] * [J]⁻¹` in the Picard group.

## References

* [The Stacks Project, Tag 01WQ](https://stacks.math.columbia.edu/tag/01WQ): effective Cartier
  divisors and their ideal sheaves.
-/

public section

open CategoryTheory

universe u

namespace TauCeti.AlgebraicGeometry.LineBundleClass

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} {I J : X.IdealSheafData}

/-- The line-bundle class of the quotient `(I : J)` of two effective Cartier divisors with `I ≤ J`
is `[I] * [J]⁻¹` in the Picard group. -/
theorem mk_toInvertibleSheaf_colon (hI : I.IsEffectiveCartier) (hJ : J.IsEffectiveCartier)
    (hIJ : I ≤ J) :
    mk (hI.colon hJ.locallyPrincipal hIJ).toInvertibleSheaf =
      mk hI.toInvertibleSheaf * (mk hJ.toInvertibleSheaf)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq, mul_comm,
    ← mk_toInvertibleSheaf_mul hJ (hI.colon hJ.locallyPrincipal hIJ)]
  exact mk_toInvertibleSheaf_congr _ hI
    ((mul_comm _ _).trans (I.eq_colon_mul J hJ.locallyPrincipal hIJ).symm)

end TauCeti.AlgebraicGeometry.LineBundleClass
