/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.FormalSeries.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Neg

/-!
# The formal power series of the negation isogeny

For a Weierstrass curve `W` over a field `K`, the formal power series induced by the negation
isogeny is the formal group's inverse series (`TauCeti.Isogeny.formalSeries_negIsogeny`). The
statement needs no nonsingularity hypothesis: it compares the Laurent expansions of the pulled-back
parameter `-x / y` directly. For elliptic curves, the formal series of every multiplication-by-`n`
isogeny is identified with the formal group's multiplication series in
`TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.FormalSeries.Hom`.

## Main results

* `TauCeti.Isogeny.formalSeries_negIsogeny`: the formal series of `negIsogeny` is the formal group's
  inverse series.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1 and IV.4.
-/

public section

open WeierstrassCurve HahnSeries
open scoped LaurentSeries PowerSeries

namespace TauCeti.Isogeny

variable {K : Type*} [Field K] (W : WeierstrassCurve K)

/-- **The formal series of the negation isogeny is the formal-group inverse series.** This holds
for every Weierstrass curve over a field, without a nonsingularity hypothesis. -/
@[simp]
theorem formalSeries_negIsogeny :
    (negIsogeny W.toAffine).formalSeries = (formalGroup W).addInvX := by
  rw [W.formalGroup_addInvX, formalSeries_eq_iff]
  set φ := W.functionFieldLaurentExpansion
  set x : K⸨X⸩ := φ W.toAffine.genericX
  set y : K⸨X⸩ := φ W.toAffine.genericY
  have hy : y ≠ 0 := (map_ne_zero_iff φ φ.injective).mpr W.toAffine.genericY_ne_zero
  have hX : ((PowerSeries.X : K⟦X⟧) : K⸨X⸩) = -x / y := by
    rw [← W.functionFieldLaurentExpansion_neg_genericX_div_genericY, map_div₀, map_neg]
  have hW : ((W.formalW : K⟦X⟧) : K⸨X⸩) = -y⁻¹ := by
    rw [← W.functionFieldLaurentExpansion_neg_inv_genericY, map_neg, map_inv₀]
  have hd_mul :
      ((W.formalInverseDenom : K⟦X⟧) : K⸨X⸩) *
        ((PowerSeries.invOfUnit W.formalInverseDenom 1 : K⟦X⟧) : K⸨X⸩) = 1 := by
    rw [← map_mul, W.mul_invOfUnit_formalInverseDenom, map_one]
  have hd_ne : ((W.formalInverseDenom : K⟦X⟧) : K⸨X⸩) ≠ 0 := left_ne_zero_of_mul_eq_one hd_mul
  have hinv_mul : ((W.formalInverse : K⟦X⟧) : K⸨X⸩) * ((W.formalInverseDenom : K⟦X⟧) : K⸨X⸩) =
      -((PowerSeries.X : K⟦X⟧) : K⸨X⸩) := by
    rw [W.formalInverse_def, map_neg, map_mul, neg_mul, mul_assoc,
      mul_comm (((PowerSeries.invOfUnit W.formalInverseDenom 1 : K⟦X⟧) : K⸨X⸩)), hd_mul, mul_one]
  have hnegY : φ ((negIsogeny W.toAffine).fieldPullback W.toAffine.genericY) =
      -y * ((W.formalInverseDenom : K⟦X⟧) : K⸨X⸩) := by
    rw [fieldPullback_negIsogeny_genericY, Affine.negY, map_sub, map_sub, map_neg, map_mul]
    have ha₁ : φ (W.toAffine⁄W.toAffine.FunctionField).a₁ = algebraMap K K⸨X⸩ W.a₁ := by
      rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, φ.commutes]
    have ha₃ : φ (W.toAffine⁄W.toAffine.FunctionField).a₃ = algebraMap K K⸨X⸩ W.a₃ := by
      rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₃, φ.commutes]
    simp only [W.formalInverseDenom_def, ha₁, ha₃, map_sub, map_one, map_mul, hX, hW,
      ← LaurentSeries.coe_algebraMap, ← PowerSeries.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply K K⟦X⟧ K⸨X⸩]
    dsimp only [x, y] at hy ⊢
    field_simp
    ring
  rw [map_div₀, map_neg, fieldPullback_negIsogeny_genericX, map_div₀, map_neg, hnegY]
  have hden : -y * ((W.formalInverseDenom : K⟦X⟧) : K⸨X⸩) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr hy) hd_ne
  rw [eq_div_iff hden]
  calc
    ((W.formalInverse : K⟦X⟧) : K⸨X⸩) * (-y * ((W.formalInverseDenom : K⟦X⟧) : K⸨X⸩)) =
        (((W.formalInverse : K⟦X⟧) : K⸨X⸩) * ((W.formalInverseDenom : K⟦X⟧) : K⸨X⸩)) * -y := by
      ring
    _ = -(-x / y) * -y := by rw [hinv_mul, hX]
    _ = -x := by field_simp

end TauCeti.Isogeny
