/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.LaurentExpansion.Basic
public import TauCeti.RingTheory.LaurentSeries.Substitution.Basic

/-!
# Laurent substitution of Weierstrass generic coordinate expansions

Substituting a nonzero power series `q : K⟦X⟧` with zero constant coefficient into the Laurent
expansions at infinity of the generic coordinates `genericX` and `genericY` evaluates them as
`q / w(q)` and `-1 / w(q)`.

## Main results

* `WeierstrassCurve.substAlgHom_functionFieldLaurentExpansion_genericY`: substituting `q` into
  the Laurent expansion of `genericY` yields `-1 / w(q)`.
* `WeierstrassCurve.substAlgHom_functionFieldLaurentExpansion_genericX`: substituting `q` into
  the Laurent expansion of `genericX` yields `q / w(q)`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1.
-/

public section

open HahnSeries
open scoped LaurentSeries PowerSeries

namespace WeierstrassCurve

variable {K : Type*} [Field K] (W : WeierstrassCurve K)

-- Not `@[simp]`: `W.functionFieldLaurentExpansion_genericY` already rewrites the inner argument.
/-- Evaluating the Laurent expansion of `genericY` along substitution by a nonzero power series `q`
with zero constant coefficient gives `-1 / w(q)`. -/
theorem substAlgHom_functionFieldLaurentExpansion_genericY {q : K⟦X⟧}
    (hq₀ : PowerSeries.constantCoeff q = 0) (hq : q ≠ 0) :
    TauCeti.LaurentSeries.substAlgHom hq₀ hq
        (W.functionFieldLaurentExpansion W.toAffine.genericY) =
      -1 / ofPowerSeries ℤ K (PowerSeries.subst q (formalW W)) := by
  rw [W.functionFieldLaurentExpansion_genericY_eq_div_formalW, map_div₀, map_neg, map_one,
    TauCeti.LaurentSeries.substAlgHom_coe]

-- Not `@[simp]`: `W.functionFieldLaurentExpansion_genericX` already rewrites the inner argument.
/-- Evaluating the Laurent expansion of `genericX` along substitution by a nonzero power series `q`
with zero constant coefficient gives `q / w(q)`. -/
theorem substAlgHom_functionFieldLaurentExpansion_genericX {q : K⟦X⟧}
    (hq₀ : PowerSeries.constantCoeff q = 0) (hq : q ≠ 0) :
    TauCeti.LaurentSeries.substAlgHom hq₀ hq
        (W.functionFieldLaurentExpansion W.toAffine.genericX) =
      ofPowerSeries ℤ K q / ofPowerSeries ℤ K (PowerSeries.subst q (formalW W)) := by
  rw [W.functionFieldLaurentExpansion_genericX_eq_div_formalW, map_div₀,
    TauCeti.LaurentSeries.substAlgHom_coe, TauCeti.LaurentSeries.substAlgHom_coe,
    PowerSeries.subst_X (.of_constantCoeff_zero' hq₀)]

end WeierstrassCurve
