/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Unramified
public import TauCeti.RingTheory.Norm.Units
import TauCeti.NumberTheory.LocalField.FiniteExtension.Basic
import Mathlib.RingTheory.Norm.Transitivity

/-!
# Norms in unramified local-field extensions

This file computes the normalized valuation of a field norm in a finite Galois extension of
nonarchimedean local fields.  The general calculation says that, after mapping the norm back to the
extension field, its valuation is the degree-th power of the valuation of the original element.
For an unramified extension this gives the intrinsic formula
`v_K(N_{L/K}(x)) = f(L/K) v_L(x)`.

The formula is the valuation input to the norm-group criterion for unramified extensions.  The
subsequent surjectivity-on-units argument identifies the entire norm group; this file deliberately
records only the valuation computation that that argument uses.

## Main results

* `TauCeti.normalizedValuation_algebraMap_norm`: the valuation calculation after applying the
  algebra map to a norm from a finite Galois extension.
* `TauCeti.normalizedValuation_norm`: for an unramified extension, the normalized valuation of a
  norm is multiplied by the inertia degree.
* `TauCeti.toAdd_normalizedValuation_norm`: the preceding result in additive notation.
* `TauCeti.normalizedValuationWithZero_norm`: the same formula for arbitrary field elements,
  including zero.

## References

* J.-P. Serre, *Local Fields*, Chapter V, §2.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §7.
-/

public section

open ValuativeRel IsNonarchimedeanLocalField

namespace TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [FiniteDimensional K L]

/-- A `K`-automorphism of a finite local-field extension preserves its normalized valuation. -/
private theorem normalizedValuation_algEquiv (σ : L ≃ₐ[K] L) (x : Lˣ) :
    normalizedValuation L (Units.map σ.toRingEquiv.toRingHom x) = normalizedValuation L x := by
  apply Multiplicative.toAdd.injective
  simp only [toAdd_normalizedValuation_eq_neg_log, Units.coe_map]
  change -((valueGroupWithZeroIsoInt L) (valuation L (σ (x : L)))).log =
    -((valueGroupWithZeroIsoInt L) (valuation L (x : L))).log
  rw [σ.valuation_eq]

/-- **Valuation of a Galois norm after scalar extension.** The norm is the product of the Galois
conjugates, and each conjugate has the same normalized valuation. -/
theorem normalizedValuation_algebraMap_norm [IsGalois K L] (x : Lˣ) :
    normalizedValuation L (Units.map (algebraMap K L : K →* L) (Algebra.normUnits K x)) =
      normalizedValuation L x ^ Module.finrank K L := by
  have hnorm : Units.map (algebraMap K L : K →* L) (Algebra.normUnits K x) =
      ∏ σ : L ≃ₐ[K] L, Units.map σ.toRingEquiv.toRingHom x := by
    apply Units.ext
    simp only [Units.coe_map, Algebra.coe_normUnits]
    change algebraMap K L (Algebra.norm K (x : L)) =
      (Units.coeHom L) (∏ σ : L ≃ₐ[K] L, Units.map σ.toRingEquiv.toRingHom x)
    rw [map_prod]
    change algebraMap K L (Algebra.norm K (x : L)) = ∏ σ : L ≃ₐ[K] L, σ (x : L)
    exact Algebra.norm_eq_prod_automorphisms K (x : L)
  rw [hnorm, map_prod]
  simp_rw [normalizedValuation_algEquiv]
  rw [Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    IsGalois.card_aut_eq_finrank]

/-- **Valuation of a norm in an unramified extension.** For `L/K` unramified, the normalized
valuation of `N_{L/K}(x)` is `f(L/K)` times the normalized valuation of `x`. -/
theorem normalizedValuation_norm [IsUnramified K L] [IsGalois K L] (x : Lˣ) :
    normalizedValuation K (Algebra.normUnits K x) =
      normalizedValuation L x ^ inertiaDegree K L := by
  rw [← IsUnramified.normalizedValuation_algebraMap (K := K) (L := L),
    normalizedValuation_algebraMap_norm]
  congr 1
  exact IsUnramified.inertiaDegree_eq_finrank.symm

/-- **Additive valuation of a norm in an unramified extension.** This is
`v_K(N_{L/K}(x)) = f(L/K) v_L(x)`. -/
theorem toAdd_normalizedValuation_norm [IsUnramified K L] [IsGalois K L] (x : Lˣ) :
    (normalizedValuation K (Algebra.normUnits K x)).toAdd =
      inertiaDegree K L * (normalizedValuation L x).toAdd := by
  rw [normalizedValuation_norm, toAdd_pow, nsmul_eq_mul]

/-- **Valuation of the field norm in an unramified extension**, including the zero element. -/
theorem normalizedValuationWithZero_norm [IsUnramified K L] [IsGalois K L] (x : L) :
    normalizedValuationWithZero K (Algebra.norm K x) =
      normalizedValuationWithZero L x ^ inertiaDegree K L := by
  by_cases hx : x = 0
  · subst x
    have hzero : (0 : WithZero (Multiplicative ℤ)) ^ inertiaDegree K L = 0 :=
      zero_pow (show inertiaDegree K L ≠ 0 by
        rw [IsUnramified.inertiaDegree_eq_finrank]
        exact Module.finrank_pos.ne')
    have hnorm : Algebra.norm K (0 : L) = 0 :=
      Algebra.norm_eq_zero_iff.mpr rfl
    rw [hnorm]
    simpa only [map_zero] using hzero.symm
  · let x' : Lˣ := Units.mk0 x hx
    have hnorm : normalizedValuationWithZero K (Algebra.norm K (x' : L)) =
        normalizedValuationWithZero L (x' : L) ^ inertiaDegree K L := by
      rw [← Algebra.coe_normUnits K x', normalizedValuationWithZero_coe,
        normalizedValuationWithZero_coe, normalizedValuation_norm]
      exact WithZero.coe_pow _ _
    simpa only [x', Units.val_mk0] using hnorm

end TauCeti
