/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.InertiaDegree
public import TauCeti.NumberTheory.LocalField.FiniteExtension.Basic
public import TauCeti.RingTheory.Norm.Units
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Valuation.Integral

/-!
# Norm valuations in finite local-field extensions

This file computes the normalized valuation of a field norm in finite extensions of
nonarchimedean local fields. Mapping the norm back to the extension field raises the original
valuation to the extension degree. The intrinsic formula is
`v_K(N_{L/K}(x)) = f(L/K) v_L(x)`.

The formula is the valuation input to the norm-group criterion for unramified extensions.  The
subsequent surjectivity-on-units argument identifies the entire norm group; this file deliberately
records only the valuation computation that that argument uses.

## Main results

* `TauCeti.normalizedValuation_algebraMap_norm`: the valuation calculation after applying the
  algebra map to a norm.
* `TauCeti.normalizedValuation_norm`: the normalized valuation of a norm is multiplied by the
  inertia degree.
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

/-- The norm of a valuation-zero unit has valuation zero in every finite local-field extension. -/
theorem normalizedValuation_norm_eq_one_of_eq_one (x : Lˣ)
    (hx : normalizedValuation L x = 1) :
    normalizedValuation K (Algebra.normUnits K x) = 1 := by
  have hint (y : Lˣ) (hy : normalizedValuation L y = 1) : IsIntegral 𝒪[K] (y : L) := by
    apply (Valuation.Integers.isIntegral_iff_valuation_le_one
      (Valuation.integer.integers (valuation K)) (y : L)).2
    rw [(normalizedValuation_eq_one_iff y).1 hy]
  have hnorm (y : Lˣ) (hy : normalizedValuation L y = 1) :
      0 ≤ (normalizedValuation K (Algebra.normUnits K y)).toAdd := by
    apply (mem_integer_iff_toAdd_normalizedValuation_nonneg _).1
    rw [Valuation.mem_integer_iff, Algebra.coe_normUnits]
    exact (Valuation.Integers.isIntegral_iff_v_le_one
      (Valuation.integer.integers (valuation K))).1
        (Algebra.isIntegral_norm K (hint y hy))
  have hxinv : normalizedValuation L x⁻¹ = 1 := by simp [hx]
  have h₁ := hnorm x hx
  have h₂ := hnorm x⁻¹ hxinv
  simp only [map_inv, toAdd_inv] at h₂
  apply Multiplicative.toAdd.injective
  simp only [toAdd_one]
  omega

/-- **Valuation of a norm in a finite local-field extension.** The normalized valuation of
`N_{L/K}(x)` is `f(L/K)` times the normalized valuation of `x`. -/
@[simp]
theorem normalizedValuation_norm (x : Lˣ) :
    normalizedValuation K (Algebra.normUnits K x) =
      normalizedValuation L x ^ inertiaDegree K L := by
  obtain ⟨t, ht⟩ := normalizedValuation_surjective (K := K) (normalizedValuation L x)
  let u : Lˣ := Units.map (algebraMap K L : K →* L) t
  have hu : normalizedValuation L u =
      normalizedValuation L x ^ ramificationIndex K L := by
    rw [normalizedValuation_algebraMap, ht]
  let y := x ^ ramificationIndex K L * u⁻¹
  have hy : normalizedValuation L y = 1 := by
    simp only [y, map_mul, map_pow, map_inv]
    rw [hu]
    simp
  have hnorm : Algebra.normUnits K u = t ^ Module.finrank K L := by
    apply Units.ext
    simp [u, Algebra.norm_algebraMap]
  have hmap : (normalizedValuation K (Algebra.normUnits K u)).toAdd =
      Module.finrank K L * (normalizedValuation L x).toAdd := by
    rw [hnorm, map_pow, ht, toAdd_pow, nsmul_eq_mul]
  have heq : (normalizedValuation K (Algebra.normUnits K y)).toAdd =
      ramificationIndex K L * (normalizedValuation K (Algebra.normUnits K x)).toAdd -
        (normalizedValuation K (Algebra.normUnits K u)).toAdd := by
    simp [y, toAdd_mul, toAdd_pow, toAdd_inv, sub_eq_add_neg]
  have h := congrArg Multiplicative.toAdd
    (normalizedValuation_norm_eq_one_of_eq_one (K := K) y hy)
  rw [heq, hmap, toAdd_one, ← ramificationIndex_mul_inertiaDegree (K := K) (L := L)] at h
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, nsmul_eq_mul]
  have he : (ramificationIndex K L : ℤ) ≠ 0 := by
    exact_mod_cast (ramificationIndex_pos (K := K) (L := L)).ne'
  simp only [Nat.cast_mul] at h
  exact mul_left_cancel₀ he (by simpa only [mul_assoc] using (sub_eq_zero.mp h))

/-- **Valuation of a norm after scalar extension.** This is the intrinsic norm formula
multiplied by the ramification index, using `e(L/K) f(L/K) = [L : K]`. -/
theorem normalizedValuation_algebraMap_norm (x : Lˣ) :
    normalizedValuation L (Units.map (algebraMap K L : K →* L) (Algebra.normUnits K x)) =
      normalizedValuation L x ^ Module.finrank K L := by
  rw [normalizedValuation_algebraMap, normalizedValuation_norm, ← pow_mul,
    mul_comm (inertiaDegree K L) (ramificationIndex K L),
    ramificationIndex_mul_inertiaDegree]

/-- **Additive valuation of a norm in a finite local-field extension.** This is
`v_K(N_{L/K}(x)) = f(L/K) v_L(x)`. -/
theorem toAdd_normalizedValuation_norm (x : Lˣ) :
    (normalizedValuation K (Algebra.normUnits K x)).toAdd =
      inertiaDegree K L * (normalizedValuation L x).toAdd := by
  rw [normalizedValuation_norm, toAdd_pow, nsmul_eq_mul]

/-- **Valuation of the field norm in a finite local-field extension**, including zero. -/
@[simp]
theorem normalizedValuationWithZero_norm (x : L) :
    normalizedValuationWithZero K (Algebra.norm K x) =
      normalizedValuationWithZero L x ^ inertiaDegree K L := by
  by_cases hx : x = 0
  · subst x
    have hzero : (0 : WithZero (Multiplicative ℤ)) ^ inertiaDegree K L = 0 :=
      zero_pow ((inertiaDegree_pos (K := K) (L := L)).ne')
    rw [Algebra.norm_zero]
    simpa only [map_zero] using hzero.symm
  · let x' : Lˣ := Units.mk0 x hx
    have hnorm : normalizedValuationWithZero K (Algebra.norm K (x' : L)) =
        normalizedValuationWithZero L (x' : L) ^ inertiaDegree K L := by
      rw [← Algebra.coe_normUnits K x', normalizedValuationWithZero_coe,
        normalizedValuationWithZero_coe, normalizedValuation_norm]
      exact WithZero.coe_pow _ _
    simpa only [x', Units.val_mk0] using hnorm

end TauCeti
