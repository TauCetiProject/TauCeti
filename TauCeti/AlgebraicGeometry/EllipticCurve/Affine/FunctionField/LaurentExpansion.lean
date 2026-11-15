/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.CoordinateRing.LaurentExpansion
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.InfinityPlace.Unique
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.GenericPoint.Basic
import TauCeti.RingTheory.LaurentSeries.Basic
import TauCeti.RingTheory.Valuation.IsTrivialOn
import TauCeti.RingTheory.Valuation.Discrete.Order

/-!
# Laurent expansions of Weierstrass rational functions

The coordinate-ring expansion at infinity extends to the function field. Its parameter
`z = -x/y` expands to `X`, and its valuation equals the place at infinity.
Consequently a rational function is regular at infinity exactly when its expansion is a
power series. This lets local expansions of morphisms be constructed from their actual
function-field pullbacks.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, IV.1.
-/

public section

open Polynomial HahnSeries
open scoped LaurentSeries PowerSeries WithZero

namespace WeierstrassCurve

variable {K : Type*} [Field K] (W : WeierstrassCurve K)

/-- The Laurent expansion at infinity of a rational function, in the parameter `z = -x/y`. -/
noncomputable def functionFieldLaurentExpansion : W.toAffine.FunctionField →ₐ[K] K⸨X⸩ :=
  IsFractionRing.liftAlgHom W.laurentExpansion_injective

/-- The rational-function expansion extends the coordinate-ring expansion. -/
@[simp]
theorem functionFieldLaurentExpansion_algebraMap (f : W.toAffine.CoordinateRing) :
    W.functionFieldLaurentExpansion (algebraMap _ W.toAffine.FunctionField f) =
      W.laurentExpansion f :=
  IsFractionRing.lift_algebraMap W.laurentExpansion_injective _

/-- The Laurent expansion of the generic abscissa is `z⁻² u(z)⁻¹`. -/
@[simp]
theorem functionFieldLaurentExpansion_genericX :
    W.functionFieldLaurentExpansion W.toAffine.genericX =
      single (-2) 1 * ofPowerSeries ℤ K ((formalU W).invOfUnit 1) := by
  rw [Affine.genericX_def, Affine.CoordinateRing.mk_C_eq_algebraMap,
    functionFieldLaurentExpansion_algebraMap]
  exact W.laurentExpansion_of_X

/-- The Laurent expansion of the generic ordinate is `-z⁻³ u(z)⁻¹`. -/
@[simp]
theorem functionFieldLaurentExpansion_genericY :
    W.functionFieldLaurentExpansion W.toAffine.genericY =
      single (-3) (-1) * ofPowerSeries ℤ K ((formalU W).invOfUnit 1) := by
  rw [Affine.genericY_def, AdjoinRoot.mk_X, functionFieldLaurentExpansion_algebraMap,
    laurentExpansion_root]

private theorem functionFieldLaurentExpansion_genericY_ne_zero :
    W.functionFieldLaurentExpansion W.toAffine.genericY ≠ 0 :=
  (map_ne_zero_iff W.functionFieldLaurentExpansion
    W.functionFieldLaurentExpansion.injective).mpr W.toAffine.genericY_ne_zero

/-- The function `-1/y` expands to the formal power series `w(z)`. -/
@[simp]
theorem functionFieldLaurentExpansion_neg_inv_genericY :
    W.functionFieldLaurentExpansion (-W.toAffine.genericY⁻¹) = (formalW W : K⸨X⸩) := by
  have hy := W.functionFieldLaurentExpansion_genericY_ne_zero
  apply (mul_right_inj' hy).mp
  rw [map_neg, map_inv₀, mul_neg, mul_inv_cancel₀ hy]
  rw [Affine.genericY_def, AdjoinRoot.mk_X, functionFieldLaurentExpansion_algebraMap,
    laurentExpansion_root_mul_formalW]

/-- The local parameter `-x/y` expands to the power-series variable. -/
-- Rewrite the parameter before simplification distributes the algebra map over division.
@[simp↓]
theorem functionFieldLaurentExpansion_neg_genericX_div_genericY :
    W.functionFieldLaurentExpansion (-W.toAffine.genericX / W.toAffine.genericY) =
      (PowerSeries.X : K⟦X⟧) := by
  have hy := W.functionFieldLaurentExpansion_genericY_ne_zero
  have hx : W.functionFieldLaurentExpansion W.toAffine.genericX =
      -((PowerSeries.X : K⟦X⟧) * W.functionFieldLaurentExpansion W.toAffine.genericY) := by
    rw [Affine.genericX_def, Affine.genericY_def,
      Affine.CoordinateRing.mk_C_eq_algebraMap, AdjoinRoot.mk_X,
      functionFieldLaurentExpansion_algebraMap, functionFieldLaurentExpansion_algebraMap]
    exact W.laurentExpansion_of_X_eq_neg_X_mul_laurentExpansion_root
  rw [map_div₀, map_neg, hx, neg_neg, mul_div_cancel_right₀ _ hy]

/-- Laurent expansion in `z = -x/y` preserves the normalized valuation at infinity. -/
@[simp]
theorem valuation_functionFieldLaurentExpansion (f : W.toAffine.FunctionField) :
    Valued.v (W.functionFieldLaurentExpansion f) = W.toAffine.infinityPlace f := by
  let v := (Valued.v : Valuation K⸨X⸩ ℤᵐ⁰).comap
    W.functionFieldLaurentExpansion.toRingHom
  have : v.IsTrivialOn K := ⟨fun c hc ↦ by
    simp only [v, Valuation.comap_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.commutes]
    rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq]
    exact TauCeti.LaurentSeries.valuation_coe_of_isUnit
      (PowerSeries.isUnit_iff_constantCoeff.mpr (by simpa using hc))⟩
  have hu : Valued.v (ofPowerSeries ℤ K ((formalU W).invOfUnit 1)) = (1 : ℤᵐ⁰) := by
    apply TauCeti.LaurentSeries.valuation_coe_of_isUnit
    rw [PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_invOfUnit]
    simp
  have hequiv : v.IsEquiv W.toAffine.infinityPlace := by
    apply Affine.isEquiv_infinityPlace_of_one_lt
    rw [← Affine.genericX_eq_algebraMap, Valuation.comap_apply]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [functionFieldLaurentExpansion_genericX, map_mul, hu,
      mul_one, LaurentSeries.valuation_single_zpow, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by norm_num)
  have hv : v (-W.toAffine.genericX / W.toAffine.genericY) = WithZero.exp (-1) := by
    simp only [v, Valuation.comap_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [functionFieldLaurentExpansion_neg_genericX_div_genericY, ofPowerSeries_X,
      LaurentSeries.valuation_single_zpow]
  exact DFunLike.congr_fun (Valuation.eq_of_isEquiv_of_surjective
    (Valuation.surjective_of_map_eq_exp_neg_one v hv)
    (Valuation.surjective_of_map_eq_exp_neg_one W.toAffine.infinityPlace
      W.toAffine.infinityPlace_neg_genericX_div_genericY) hequiv) f

/-- A rational function is regular at infinity exactly when its expansion has no negative powers. -/
theorem exists_powerSeries_functionFieldLaurentExpansion_iff (f : W.toAffine.FunctionField) :
    (∃ g : K⟦X⟧, (g : K⸨X⸩) = W.functionFieldLaurentExpansion f) ↔
      W.toAffine.infinityPlace f ≤ 1 := by
  rw [← LaurentSeries.val_le_one_iff_eq_coe]
  rw [valuation_functionFieldLaurentExpansion]

/-- A rational function vanishes at infinity exactly when its expansion is a power series
with zero constant coefficient. -/
theorem exists_powerSeries_constantCoeff_zero_functionFieldLaurentExpansion_iff
    (f : W.toAffine.FunctionField) :
    (∃ g : K⟦X⟧, PowerSeries.constantCoeff g = 0 ∧
      (g : K⸨X⸩) = W.functionFieldLaurentExpansion f) ↔ W.toAffine.infinityPlace f < 1 := by
  refine ⟨?_, fun hf ↦ ?_⟩
  · rintro ⟨g, hg₀, hg⟩
    rw [← valuation_functionFieldLaurentExpansion, ← hg]
    exact TauCeti.LaurentSeries.valuation_coe_lt_one_iff.mpr hg₀
  · obtain ⟨g, hg⟩ := (W.exists_powerSeries_functionFieldLaurentExpansion_iff f).mpr hf.le
    refine ⟨g, TauCeti.LaurentSeries.valuation_coe_lt_one_iff.mp ?_, hg⟩
    rwa [hg, valuation_functionFieldLaurentExpansion]

end WeierstrassCurve
