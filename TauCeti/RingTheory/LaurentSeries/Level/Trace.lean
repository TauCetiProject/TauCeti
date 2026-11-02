/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Trace.Basic
public import TauCeti.RingTheory.LaurentSeries.Level.Basis

/-!
# The trace of a ramified Laurent-series level

Let `L = K⸨u⸩` be the ramified level of degree `d` over `F = K⸨t⸩`, where `t = u ^ d`. In the
power basis `1, u, ..., u ^ (d - 1)`, multiplication by `f` has `r`-th diagonal coefficient the
residue-zero exponent-congruence component of `f`, for every `r`. Hence, in every characteristic,

`Tr_{L/F} (f) = d • contract d f 0`,

so the trace keeps exactly the exponents of `f` divisible by `d`, multiplies them by `d` and
reads them as exponents of `t`. On monomials, `Tr (u ^ k)` is `d t ^ (k / d)` when `d ∣ k` and
`0` otherwise.

This is the trace on the coefficient of `dt`: the residue of `g dt` in the variable `u`, for
`g ∈ L`, is that of `g · d(u ^ d) = d g u ^ (d - 1) du`. Comparing coefficients gives, in every
characteristic, the residue formula for the trace

`Res_t (Tr_{L/F} (g) dt) = Res_u (g dt)`.

When `d` is nonzero in `K`, every differential on `L` has the form `g dt`, so this is the formula
`Res_F ∘ Tr_{L/F} = Res_L` for all differentials. When the characteristic of `K` divides `d`,
the form `dt = d u ^ (d - 1) du` vanishes on `L`, so every `g dt` is zero there and the identity
says nothing about other differentials such as `u⁻¹ du`.

On the actual level `K⸨t ^ (1 / d)⸩` of the Puiseux field, the coefficient of `t ^ j` in the trace
of `x` is `d` times the rational-exponent coefficient of `t ^ j` in `x`. For `j = -1` this says
that the residue of the trace of `x dt` is `d` times the rational-exponent residue of `x dt`, and
it shows that the traces of `x` from levels `n ∣ m` differ by the factor `m / n`.

## Main results

* `TauCeti.LaurentSeries.Level.trace_eq_nsmul_contract`: `Tr_{L/F} (f) = d • contract d f 0`.
* `TauCeti.LaurentSeries.Level.coeff_trace`: the coefficient of `t ^ j` in `Tr_{L/F} (f)` is
  `d` times the coefficient of `u ^ (d * j)` in `f`.
* `TauCeti.LaurentSeries.Level.trace_parameter_zpow`: the trace of the monomial `u ^ k`.
* `TauCeti.LaurentSeries.Level.coeff_neg_one_trace`: `Res_t (Tr_{L/F} (g) dt) = Res_u (g dt)`.
* `TauCeti.puiseuxField.coeff_trace_level`: on the actual level `d` of the Puiseux field, the
  trace multiplies the integer-exponent coefficients by `d`.
* `TauCeti.puiseuxField.trace_inclusion_level`: for `n ∣ m`, the trace from level `m` of an
  element of level `n` is `m / n` times its trace from level `n`.
-/

public section

open HahnSeries LaurentSeries
open scoped LaurentSeries

namespace TauCeti.LaurentSeries.Level

variable {K : Type*} [Field K] (d : ℕ+)

/-- **The trace of a ramified level.** The trace of `f` from level `d` down to `K⸨X⸩` is `d`
times the residue-zero exponent-congruence component of `f`, in every characteristic. -/
theorem trace_eq_nsmul_contract (f : Level K d) :
    Algebra.trace K⸨X⸩ (Level K d) f = (d : ℕ) • contract d (ringEquivLaurentSeries K d f) 0 := by
  classical
  rw [Algebra.trace_eq_matrix_trace (basis K d), Matrix.trace]
  simp [Algebra.leftMulMatrix_eq_repr_mul, single_pow, mul_comm _ (single _ _)]

/-- The coefficient of `t ^ j` in the trace of `f` is `d` times the coefficient of `u ^ (d * j)`
in `f`. -/
@[simp]
theorem coeff_trace (f : Level K d) (j : ℤ) :
    (Algebra.trace K⸨X⸩ (Level K d) f).coeff j =
      (d : ℕ) • (ringEquivLaurentSeries K d f).coeff ((d : ℤ) * j) := by
  rw [trace_eq_nsmul_contract, coeff_nsmul, Pi.smul_apply, coeff_contract, Fin.val_zero,
    Nat.cast_zero, add_zero]

/-- The trace of the monomial `u ^ k` is `d t ^ (k / d)` when `d ∣ k`, and zero otherwise. -/
theorem trace_parameter_zpow (k : ℤ) :
    Algebra.trace K⸨X⸩ (Level K d) (parameter K d ^ k) =
      if (d : ℤ) ∣ k then (d : ℕ) • single (k / d) 1 else 0 := by
  rw [trace_eq_nsmul_contract, map_zpow₀, ringEquiv_parameter, ← RatFunc.single_zpow,
    contract_single]
  simp

/-- **Residue of the trace.** For `g` in level `d`, the residue of `Tr_{L/F} (g) dt` is the
residue in the level variable `u` of the form `g dt`, where `dt = d(u ^ d)`. -/
theorem coeff_neg_one_trace (g : Level K d) :
    (Algebra.trace K⸨X⸩ (Level K d) g).coeff (-1) =
      (ringEquivLaurentSeries K d g * derivative K (single (d : ℤ) 1)).coeff (-1) := by
  have h : (-1 - ((d : ℤ) - (1 : ℕ))) = (d : ℤ) * -1 := by ring
  rw [coeff_trace, derivative_apply, hasseDeriv_single, Ring.choose_one_right, coeff_mul_single, h]
  simp [mul_comm]

end TauCeti.LaurentSeries.Level

namespace TauCeti.puiseuxField

variable {K : Type*} [Field K]

/-- **The trace of an actual level.** For `x` in level `d` of the Puiseux field, the coefficient
of `t ^ j` in its trace down to `K⸨X⸩` is `d` times the coefficient of `t ^ j` in `x`. For
`j = -1` this is `Res_t (Tr (x) dt) = d • Res_t (x dt)`, with the residue on the right taken
among rational exponents. -/
@[simp]
theorem coeff_trace_level (d : ℕ+) (x : level K d) (j : ℤ) :
    (Algebra.trace K⸨X⸩ (level K d) x).coeff j =
      (d : ℕ) • ((x : puiseuxField K) : HahnSeries ℚ K).coeff (j : ℚ) := by
  obtain ⟨f, rfl⟩ := (levelEquiv K d).surjective x
  have hj : ((j : ℤ) : ℚ) = (((d : ℤ) * j : ℤ) : ℚ) / (d : ℕ+) := by
    push_cast
    field_simp
  rw [Algebra.trace_eq_of_algEquiv, LaurentSeries.Level.coeff_trace, coe_levelEquiv_apply,
    LaurentSeries.Level.coe_toPuiseux, hj, coeff_ramifiedEmbedding_intCast_div]

/-- For `n ∣ m`, the trace from level `m` of an element of level `n` is `m / n` times its trace
from level `n`. -/
theorem trace_inclusion_level {n m : ℕ+} (h : n ∣ m) (x : level K n) :
    Algebra.trace K⸨X⸩ (level K m) (IntermediateField.inclusion (level_le_level_of_dvd K h) x) =
      ((m : ℕ) / n) • Algebra.trace K⸨X⸩ (level K n) x := by
  ext j
  rw [coeff_trace_level, coeff_nsmul, Pi.smul_apply, coeff_trace_level, smul_smul,
    Nat.div_mul_cancel (PNat.dvd_iff.1 h), IntermediateField.coe_inclusion]

end TauCeti.puiseuxField
