/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.NumberTheory.LocalField.AbsoluteRamificationIndex
public import TauCeti.NumberTheory.LocalField.AlgebraicExtension.Basic
public import TauCeti.NumberTheory.LocalField.RealAddValuation

/-!
# The `p`-adic norm of a finite extension of `ℚ_[p]`

Let `K` be a finite extension of `ℚ_[p]`, presented as a nonarchimedean local field with a
`FinitePadicExtension K p` structure, with absolute ramification index `e` and normalized additive
valuation `v_K`, so that `v_K(p) = e`. The analytic estimates of the `p`-adic method of linear
forms in logarithms are proved for a normed field extension of `ℚ_[p]`, in which the norm of `p`
is `p⁻¹`, while their arithmetic consumers measure the same quantities by `v_K`. This file
supplies the norm that connects the two: the spectral norm of `K/ℚ_[p]`
(`TauCeti.algebraicExtensionNormedField`), which extends the norm of `ℚ_[p]` and satisfies

`‖x‖ = p ^ (-v_K(x) / e)`.

Its topology is the given topology of `K` only propositionally
(`TauCeti.algebraicExtensionNormedFieldTopology_eq`). The normed field `padicNormedField K p`
replaces it by the given topology, so that the two agree definitionally: the exponential and
logarithm series of `K`, which depend only on the topology, are then the same for the norm as for
the valuation, and normed estimates for them apply verbatim in the valuation setting.

Consequently a norm bound `‖x‖ ≤ p ^ (-r / e)` is the valuation bound `r ≤ v_K(x)`, read in the
real-valued valuation `realAddValuation K`, with `v_K(0) = ⊤`.

The structures are named definitions rather than global instances, so that installing them is
always local; they are meant to be used as `letI := padicNormedField K p`.

## Main definitions

* `TauCeti.padicNormedField`: the spectral norm of `K/ℚ_[p]`, with the given topology of `K`.
* `TauCeti.padicNormedAlgebra`: the resulting normed `ℚ_[p]`-algebra structure.

## Main results

* `TauCeti.padicNormedField_norm_le_norm_iff`: the norm induces the order of the valuation.
* `TauCeti.padicNormedField_norm_algebraMap`: the norm extends the norm of `ℚ_[p]`.
* `TauCeti.padicNormedField_norm_eq_rpow`: `‖x‖ = p ^ (-v_K(x) / e)` for `x ≠ 0`.
* `TauCeti.padicNormedField_norm_le_rpow_iff`, `TauCeti.padicNormedField_norm_lt_rpow_iff`:
  `‖x‖ ≤ p ^ (-r / e) ↔ r ≤ v_K(x)`, and the strict form.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, §§4–6.
* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter II, §2.
-/

public section
noncomputable section

open ValuativeRel

namespace TauCeti

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] (p : ℕ) [Fact p.Prime] [FinitePadicExtension K p]

/-- The normed-field structure on a finite extension `K` of `ℚ_[p]` given by the spectral norm of
`K/ℚ_[p]`, `algebraicExtensionNormedField ℚ_[p] K`, with its topology replaced by the given
topology of `K`, which it equals, so that the two agree definitionally. -/
@[expose, implicit_reducible]
def padicNormedField : NormedField K :=
  letI N := algebraicExtensionNormedField ℚ_[p] K
  { N with
    toMetricSpace :=
      N.toMetricSpace.replaceTopology (algebraicExtensionNormedFieldTopology_eq ℚ_[p] K).symm }

/-- The norm of `padicNormedField K p` is the spectral norm of `K/ℚ_[p]`. -/
theorem padicNormedField_norm_def (x : K) :
    @norm K (padicNormedField K p).toNorm x =
      @norm K (algebraicExtensionNormedField ℚ_[p] K).toNorm x := (rfl)

variable {K} in
/-- The `p`-adic norm of a finite extension `K` of `ℚ_[p]` induces the order of the valuation. -/
theorem padicNormedField_norm_le_norm_iff (x y : K) :
    letI := padicNormedField K p
    ‖x‖ ≤ ‖y‖ ↔ valuation K x ≤ valuation K y := by
  rw [padicNormedField_norm_def, padicNormedField_norm_def,
    ← vle_iff_algebraicExtensionNormedField_norm_le ℚ_[p] x y, (valuation K).vle_iff_le]

variable {K} in
/-- The `p`-adic norm of a finite extension `K` of `ℚ_[p]` extends the norm of `ℚ_[p]`. -/
-- Not `@[simp]`: `simp` already rewrites the left-hand side through
-- `algebraicExtensionNormedField_norm_algebraMap`, so `simpNF` rejects the attribute.
theorem padicNormedField_norm_algebraMap (a : ℚ_[p]) :
    letI := padicNormedField K p
    ‖algebraMap ℚ_[p] K a‖ = ‖a‖ := by
  rw [padicNormedField_norm_def, algebraicExtensionNormedField_norm_algebraMap, ← coe_nnNorm,
    ← Padic.normalizedAbsoluteValue_eq_nnnorm p a]
  norm_cast

variable {K} in
/-- **The `p`-adic norm in terms of the valuation.** For nonzero `x` in a finite extension `K` of
`ℚ_[p]` with absolute ramification index `e`, `‖x‖ = p ^ (-v_K(x) / e)`. -/
theorem padicNormedField_norm_eq_rpow {x : K} (hx : x ≠ 0) :
    letI := padicNormedField K p
    ‖x‖ = (p : ℝ) ^ (-((WithZero.log (normalizedValuationWithZero K x) : ℤ) : ℝ) /
      absoluteRamificationIndex K p) := by
  let _ := padicNormedField K p
  have := FinitePadicExtension.charZero K p
  have hP : (0 : ℝ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have hp : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have he : absoluteRamificationIndex K p ≠ 0 := (absoluteRamificationIndex_pos K p).ne'
  have hm : (normalizedValuation K (Units.mk0 x hx)).toAdd =
      WithZero.log (normalizedValuationWithZero K x) := by
    have h := normalizedValuationWithZero_coe (Units.mk0 x hx)
    rw [Units.val_mk0] at h
    rw [h, ← WithZero.toAdd_unzero_eq_log WithZero.coe_ne_zero, WithZero.unzero_coe]
  -- `x ^ e` and `p ^ v_K(x)` have the same valuation `e v_K(x)`, hence the same norm.
  have hval : valuation K (x ^ absoluteRamificationIndex K p) =
      valuation K ((p : K) ^ WithZero.log (normalizedValuationWithZero K x)) := by
    have h := (toAdd_normalizedValuation_eq_iff_valuation_eq
      (Units.mk0 x hx ^ absoluteRamificationIndex K p)
      (Units.mk0 (p : K) hp ^ WithZero.log (normalizedValuationWithZero K x))).mp (by
        rw [map_pow, map_zpow, toAdd_pow, toAdd_zpow, hm, toAdd_normalizedValuation_natCast,
          ← absoluteRamificationIndex_eq_natCastValuation, smul_eq_mul, nsmul_eq_mul, mul_comm])
    simpa using h
  have hnorm : ‖x‖ ^ absoluteRamificationIndex K p =
      (p : ℝ)⁻¹ ^ WithZero.log (normalizedValuationWithZero K x) := by
    have h : ‖x ^ absoluteRamificationIndex K p‖ =
        ‖(p : K) ^ WithZero.log (normalizedValuationWithZero K x)‖ :=
      le_antisymm ((padicNormedField_norm_le_norm_iff p _ _).2 hval.le)
        ((padicNormedField_norm_le_norm_iff p _ _).2 hval.ge)
    rwa [norm_pow, norm_zpow, ← map_natCast (algebraMap ℚ_[p] K),
      padicNormedField_norm_algebraMap, Padic.norm_p] at h
  rw [← Real.pow_rpow_inv_natCast (norm_nonneg x) he, hnorm, ← Real.rpow_neg_one,
    ← Real.rpow_intCast, ← Real.rpow_mul hP.le, ← Real.rpow_mul hP.le]
  congr 1
  ring

variable {K} in
/-- **Norm bounds are valuation bounds.** In a finite extension `K` of `ℚ_[p]` with absolute
ramification index `e`, `‖x‖ ≤ p ^ (-r / e)` exactly when `r ≤ v_K(x)`, for every real `r`.
For `x = 0` both sides hold, with `v_K(0) = ⊤`. -/
theorem padicNormedField_norm_le_rpow_iff (x : K) (r : ℝ) :
    letI := padicNormedField K p
    ‖x‖ ≤ (p : ℝ) ^ (-r / absoluteRamificationIndex K p) ↔
      (r : WithTop ℝ) ≤ realAddValuation K x := by
  let _ := padicNormedField K p
  rcases eq_or_ne x 0 with rfl | hx
  · rw [norm_zero, AddValuation.map_zero]
    simp only [le_top, iff_true]
    positivity
  have he : (0 : ℝ) < absoluteRamificationIndex K p :=
    Nat.cast_pos.mpr (absoluteRamificationIndex_pos K p)
  rw [padicNormedField_norm_eq_rpow p hx, realAddValuation_of_ne_zero hx, WithTop.coe_le_coe,
    Real.rpow_le_rpow_left_iff (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt),
    div_le_div_iff_of_pos_right he, neg_le_neg_iff]

variable {K} in
/-- **Strict norm bounds are strict valuation bounds.** In a finite extension `K` of `ℚ_[p]`
with absolute ramification index `e`, `‖x‖ < p ^ (-r / e)` exactly when `r < v_K(x)`, for every
real `r`. For `x = 0` both sides hold, with `v_K(0) = ⊤`. -/
theorem padicNormedField_norm_lt_rpow_iff (x : K) (r : ℝ) :
    letI := padicNormedField K p
    ‖x‖ < (p : ℝ) ^ (-r / absoluteRamificationIndex K p) ↔
      (r : WithTop ℝ) < realAddValuation K x := by
  let _ := padicNormedField K p
  rcases eq_or_ne x 0 with rfl | hx
  · rw [norm_zero, AddValuation.map_zero]
    simp only [WithTop.coe_lt_top, iff_true]
    exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Fact.out : p.Prime).pos) _
  have he : (0 : ℝ) < absoluteRamificationIndex K p :=
    Nat.cast_pos.mpr (absoluteRamificationIndex_pos K p)
  rw [padicNormedField_norm_eq_rpow p hx, realAddValuation_of_ne_zero hx, WithTop.coe_lt_coe,
    Real.rpow_lt_rpow_left_iff (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt),
    div_lt_div_iff_of_pos_right he, neg_lt_neg_iff]

/-- The normed `ℚ_[p]`-algebra structure on a finite extension `K` of `ℚ_[p]` given by the
`p`-adic norm `padicNormedField K p` and the algebra structure of `FinitePadicExtension K p`. Its
underlying algebra is definitionally that of `FinitePadicExtension K p`. -/
@[expose, implicit_reducible]
def padicNormedAlgebra :
    letI := padicNormedField K p
    NormedAlgebra ℚ_[p] K :=
  letI := padicNormedField K p
  { FinitePadicExtension.toAlgebra K p with
    norm_smul_le a x := by
      rw [Algebra.smul_def, norm_mul, padicNormedField_norm_algebraMap] }

end TauCeti
