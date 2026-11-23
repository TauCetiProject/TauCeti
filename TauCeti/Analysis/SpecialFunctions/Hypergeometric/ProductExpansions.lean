/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import TauCeti.Analysis.Analytic.TaylorSeries
public import TauCeti.Analysis.SpecialFunctions.Hypergeometric.Orr
public import TauCeti.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.Algebra.Order.Antidiag.Prod
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.Convex
import TauCeti.Analysis.Analytic.OfScalars
import TauCeti.Analysis.Polynomial.Pochhammer
import TauCeti.Analysis.SpecialFunctions.Gamma.Basic
import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric.Basic
import TauCeti.Analysis.SpecificLimits.Normed
import TauCeti.Data.Nat.Choose.Cast
import TauCeti.Data.Nat.Factorial.Basic
import TauCeti.RingTheory.Binomial
import TauCeti.RingTheory.Polynomial.Pochhammer

/-!
# Product expansions of the Gauss hypergeometric function

This file supplements `TauCeti.Analysis.SpecialFunctions.Hypergeometric.Orr` with basic identities
and power-series/Taylor characterizations for `TauCeti.orrCoefficient` (DLMF 15.16.1–15.16.2), and
proves the Burchnall–Chaundy two-variable product expansion (DLMF 15.16.3) of the Gauss
hypergeometric function on its open convergence region.

For `‖z‖ < 1`, `‖ζ‖ < 1`, and `‖z + ζ - z * ζ‖ < 1`, combining
`Complex.regularizedGaussHGFun_eq_sum_choose_mul_regularizedGaussHGFun` and
`Complex.hasSum_regularizedGaussHGFun_add` via absolute double summation near `0` and analytic
continuation across `{z | ‖z‖ < 1 ∧ ‖z + ζ - z * ζ‖ < 1}` yields DLMF 15.16.3 for **all**
`a, b, c : ℂ` (including `c ∈ -ℕ`), and multiplying by `Γ(c)²` gives the `₂F₁` form when `c ∉ -ℕ`:
$$\mathbf{F}(a, b; c; z) \, \mathbf{F}(a, b; c; \zeta)
  = \sum_{s=0}^\infty \frac{(a)_s (b)_s (c - a)_s (c - b)_s}{s! \, \Gamma(c + s)} (z \zeta)^s \,
    \mathbf{F}(a + s, b + s; c + 2s; z + \zeta - z\zeta).$$

## Main results

* `TauCeti.map_orrCoefficient`, `TauCeti.orrCoefficient_one`, `TauCeti.orrCoefficient_comm`,
  `TauCeti.orrCoefficient_zero_left`, `TauCeti.orrCoefficient_zero_right`,
  `TauCeti.orrCoefficient_add_self`: basic algebraic identities for `TauCeti.orrCoefficient`.
* `TauCeti.hasFPowerSeriesOnBall_ordinaryHypergeometric_mul_ordinaryHypergeometric_sub`: DLMF
  15.16.1 Cayley–Orr product expansion in `HasFPowerSeriesOnBall` form over `RCLike` scalars.
* `Complex.hasFPowerSeriesOnBall_one_sub_cpow_mul_ordinaryHypergeometric`,
  `Complex.coeff_taylorSeries_one_sub_cpow_mul_ordinaryHypergeometric`,
  `Complex.eq_orrCoefficient_of_eventually_hasSum`: DLMF 15.16.2 generating-function power-series
  and Taylor-coefficient characterizations.
* `Complex.hasSum_regularizedGaussHGFun_mul_regularizedGaussHGFun`,
  `Complex.hasSum_ordinaryHypergeometric_mul_ordinaryHypergeometric`: DLMF 15.16.3
  Burchnall–Chaundy two-variable product expansion in regularized and ordinary forms.

## References

* NIST Digital Library of Mathematical Functions, §15.16, equations 15.16.1–15.16.3.
* A. Cayley, *On a theorem relating to hypergeometric series*, Philos. Mag. (4) **16** (1858),
  356–357.
* W. McF. Orr, *Theorems relating to the product of two hypergeometric series*, Trans. Cambridge
  Philos. Soc. **17** (1899), 1–15.
* W. N. Bailey, *Generalized Hypergeometric Series*, Cambridge Univ. Press, 1935, §10.1.
* J. L. Burchnall and T. W. Chaundy, *Expansions of Appell's double hypergeometric functions*,
  Quart. J. Math. Oxford Ser. **11** (1940), 249–270.
-/

public section

open Filter Finset Polynomial
open scoped Nat Topology BigOperators

namespace TauCeti

/-! ### Additional identities and power-series forms (DLMF 15.16.1–15.16.2) -/

private theorem orrCoefficient_eq_sum_range {𝕂 : Type*} [Field 𝕂] [CharZero 𝕂]
    (a b c : 𝕂) (s : ℕ) :
    orrCoefficient a b c s =
      ∑ k ∈ range (s + 1),
        ordinaryHypergeometricCoefficient (2 * a) (2 * b) (2 * c - 1) k *
          Ring.multichoose (c - a - b) (s - k) := by
  rw [orrCoefficient_def]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun k l ↦ ordinaryHypergeometricCoefficient (2 * a) (2 * b) (2 * c - 1) k *
      Ring.multichoose (c - a - b) l) s

/-- Ring homomorphisms between characteristic-zero fields commute with `orrCoefficient`. -/
@[simp]
theorem map_orrCoefficient {𝕂 L F : Type*} [Field 𝕂] [CharZero 𝕂] [Field L] [CharZero L]
    [FunLike F 𝕂 L] [RingHomClass F 𝕂 L] (f : F) (a b c : 𝕂) (s : ℕ) :
    f (orrCoefficient a b c s) = orrCoefficient (f a) (f b) (f c) s := by
  have hp (m : ℕ) (x : 𝕂) :
      f ((ascPochhammer 𝕂 m).eval x) = (ascPochhammer L m).eval (f x) := by
    simpa using (Polynomial.eval_map_apply (f := (f : 𝕂 →+* L)) (p := ascPochhammer 𝕂 m) x).symm
  simp [orrCoefficient_def, ordinaryHypergeometricCoefficient,
    TauCeti.Ring.multichoose_eq_inv_factorial_mul_eval_ascPochhammer, hp, map_ofNat]

/-- The first Orr coefficient is `(c - a - b) + 4ab / (2c - 1)` (with `/ 0 = 0` when
`2c = 1`). -/
@[simp]
theorem orrCoefficient_one {𝕂 : Type*} [Field 𝕂] [CharZero 𝕂] (a b c : 𝕂) :
    orrCoefficient a b c 1 = c - a - b + 4 * a * b / (2 * c - 1) := by
  rw [orrCoefficient_eq_sum_range, sum_range_succ, sum_range_one]
  simp only [Nat.sub_zero, Nat.sub_self,
    TauCeti.Ring.multichoose_eq_inv_factorial_mul_eval_ascPochhammer,
    ordinaryHypergeometricCoefficient, ascPochhammer_zero, Polynomial.eval_one,
    ascPochhammer_one, Polynomial.eval_X, Nat.factorial_zero, Nat.factorial_one,
    Nat.cast_one, inv_one, div_eq_mul_inv]
  ring

/-- The Orr coefficients are symmetric in `a` and `b`. -/
theorem orrCoefficient_comm {𝕂 : Type*} [Field 𝕂] [CharZero 𝕂] (a b c : 𝕂) (s : ℕ) :
    orrCoefficient a b c s = orrCoefficient b a c s := by
  rw [orrCoefficient_def, orrCoefficient_def]
  refine sum_congr rfl fun p _ ↦ ?_
  have hsub : c - b - a = c - a - b := by ring
  simp only [ordinaryHypergeometricCoefficient, hsub]
  ring

/-- When `a = 0`, only the `k = 0` term of `orrCoefficient` survives, leaving
`Ring.multichoose (c - b) s`. -/
@[simp]
theorem orrCoefficient_zero_left {𝕂 : Type*} [Field 𝕂] [CharZero 𝕂] (b c : 𝕂) (s : ℕ) :
    orrCoefficient 0 b c s = Ring.multichoose (c - b) s := by
  rw [orrCoefficient_eq_sum_range, sum_eq_single 0]
  · simp [ordinaryHypergeometricCoefficient]
  · intro k _ hk
    simp [ordinaryHypergeometricCoefficient, ascPochhammer_ne_zero_eval_zero 𝕂 hk]
  · simp

/-- When `b = 0`, only the `k = 0` term of `orrCoefficient` survives, leaving
`Ring.multichoose (c - a) s`. -/
@[simp]
theorem orrCoefficient_zero_right {𝕂 : Type*} [Field 𝕂] [CharZero 𝕂] (a c : 𝕂) (s : ℕ) :
    orrCoefficient a 0 c s = Ring.multichoose (c - a) s := by
  rw [orrCoefficient_comm, orrCoefficient_zero_left]

/-- When `c = a + b`, the binomial factor reduces to `1` and `orrCoefficient a b (a + b) s` reduces
to the single hypergeometric coefficient
`ordinaryHypergeometricCoefficient (2a) (2b) (2(a + b) - 1) s`. -/
@[simp]
theorem orrCoefficient_add_self {𝕂 : Type*} [Field 𝕂] [CharZero 𝕂] (a b : 𝕂) (s : ℕ) :
    orrCoefficient a b (a + b) s =
      ordinaryHypergeometricCoefficient (2 * a) (2 * b) (2 * (a + b) - 1) s := by
  rw [orrCoefficient_eq_sum_range, sum_eq_single s]
  · simp
  · intro k hk hne
    have hpos : s - k ≠ 0 := Nat.sub_ne_zero_of_lt (lt_of_le_of_ne (mem_range_succ_iff.mp hk) hne)
    have hsub : a + b - a - b = 0 := by ring
    rw [hsub, TauCeti.Ring.multichoose_eq_inv_factorial_mul_eval_ascPochhammer,
      ascPochhammer_ne_zero_eval_zero 𝕂 hpos, mul_zero, mul_zero]
  · simp

/-- **Cayley–Orr product expansion on the unit ball (DLMF 15.16.1, `HasFPowerSeriesOnBall` form).**
In any Banach division algebra `𝔸` over an `RCLike` scalar field `𝕂`, when `2 * c - 1` avoids the
nonpositive integers, `₂F₁(a, b; c - 1/2; z) * ₂F₁(c - a, c - b; c + 1/2; z)` is represented on the
open unit ball around `0` by the scalar power series with coefficients
`((c)_s / (c + 1/2)_s) * orrCoefficient a b c s`. -/
theorem hasFPowerSeriesOnBall_ordinaryHypergeometric_mul_ordinaryHypergeometric_sub
    {𝕂 : Type*} (𝔸 : Type*) [RCLike 𝕂] [NormedDivisionRing 𝔸] [NormedAlgebra 𝕂 𝔸]
    [CompleteSpace 𝔸] (a b : 𝕂) {c : 𝕂} (hc : ∀ n : ℕ, 2 * c - 1 ≠ -n) :
    HasFPowerSeriesOnBall
      (fun z : 𝔸 ↦ ₂F₁ a b (c - 1 / 2) z * ₂F₁ (c - a) (c - b) (c + 1 / 2) z)
      (FormalMultilinearSeries.ofScalars 𝔸 fun s : ℕ ↦
        (ascPochhammer 𝕂 s).eval c / (ascPochhammer 𝕂 s).eval (c + 1 / 2) *
          orrCoefficient a b c s) 0 1 := by
  have hcoeff (s : ℕ) :
      ∑ k ∈ range (s + 1),
        ordinaryHypergeometricCoefficient a b (c - 1 / 2) k *
          ordinaryHypergeometricCoefficient (c - a) (c - b) (c + 1 / 2) (s - k) =
        (ascPochhammer 𝕂 s).eval c / (ascPochhammer 𝕂 s).eval (c + 1 / 2) *
          orrCoefficient a b c s := by
    rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun k l ↦ ordinaryHypergeometricCoefficient a b (c - 1 / 2) k *
        ordinaryHypergeometricCoefficient (c - a) (c - b) (c + 1 / 2) l)]
    exact sum_antidiagonal_ordinaryHypergeometricCoefficient_mul_eq_mul_orrCoefficient hc s
  simpa only [hcoeff] using
    (hasFPowerSeriesOnBall_ordinaryHypergeometric 𝔸 a b (c - 1 / 2)).mul_ofScalars
      (hasFPowerSeriesOnBall_ordinaryHypergeometric 𝔸 (c - a) (c - b) (c + 1 / 2))

end TauCeti

namespace Complex

/-! ### Generating function power series and Taylor coefficients (DLMF 15.16.2) -/

/-- **Generating function of the Orr coefficients (DLMF 15.16.2, `HasFPowerSeriesOnBall` form).**
On the open unit disk, `(1 - z) ^ (a + b - c) * ₂F₁(2a, 2b; 2c - 1; z)` is represented by the
scalar power series with coefficients `TauCeti.orrCoefficient a b c`. Classical DLMF 15.16.2
requires `2 * c - 1 ∉ -ℕ` (outside terminating cases); at `2 * c - 1 ∈ -ℕ` both
`₂F₁(2a, 2b; 2c - 1; z)` and `TauCeti.orrCoefficient` zero out summands with `(2 * c - 1)_k = 0`
via `0⁻¹ = 0`. -/
theorem hasFPowerSeriesOnBall_one_sub_cpow_mul_ordinaryHypergeometric (a b c : ℂ) :
    HasFPowerSeriesOnBall
      (fun z : ℂ ↦ (1 - z) ^ (a + b - c) * ₂F₁ (2 * a) (2 * b) (2 * c - 1) z)
      (FormalMultilinearSeries.ofScalars ℂ (TauCeti.orrCoefficient a b c)) 0 1 := by
  have h1 := one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero (c - a - b)
  have h2 := TauCeti.hasFPowerSeriesOnBall_ordinaryHypergeometric ℂ (2 * a) (2 * b) (2 * c - 1)
  have hmul := h2.mul_ofScalars h1
  have hchoose (j : ℕ) : Ring.choose (c - a - b + j - 1) j = Ring.multichoose (c - a - b) j := by
    have hsub : c - a - b + j - 1 - j + 1 = c - a - b := by ring
    rw [Ring.choose_eq_smul, Polynomial.descPochhammer_smeval_eq_ascPochhammer, hsub,
      Polynomial.ascPochhammer_smeval_eq_eval, smul_eq_mul,
      TauCeti.Ring.multichoose_eq_inv_factorial_mul_eval_ascPochhammer]
  have hser :
      (FormalMultilinearSeries.ofScalars ℂ fun s ↦
        ∑ k ∈ range (s + 1),
          ordinaryHypergeometricCoefficient (2 * a) (2 * b) (2 * c - 1) k *
            Ring.choose (c - a - b + ((s - k : ℕ) : ℂ) - 1) (s - k)) =
      FormalMultilinearSeries.ofScalars ℂ (TauCeti.orrCoefficient a b c) := by
    congr 1; ext s
    rw [TauCeti.orrCoefficient_eq_sum_range]
    exact sum_congr rfl fun k _ ↦ by rw [hchoose]
  rw [hser] at hmul
  refine hmul.congr fun z _ ↦ ?_
  dsimp only
  have hneg : -(c - a - b) = a + b - c := by ring
  rw [one_div, ← cpow_neg, hneg, mul_comm]

/-- The Taylor coefficients at `0` of `(1 - z) ^ (a + b - c) * ₂F₁(2a, 2b; 2c - 1; z)` are
`TauCeti.orrCoefficient a b c` (DLMF 15.16.2; classical when `2 * c - 1 ∉ -ℕ`, and reflecting
`0⁻¹ = 0` truncation of summands with `(2 * c - 1)_k = 0` when `2 * c - 1 ∈ -ℕ`). -/
theorem coeff_taylorSeries_one_sub_cpow_mul_ordinaryHypergeometric (a b c : ℂ) (s : ℕ) :
    PowerSeries.coeff s
      (TauCeti.taylorSeries
        (fun z : ℂ ↦ (1 - z) ^ (a + b - c) * ₂F₁ (2 * a) (2 * b) (2 * c - 1) z) 0) =
      TauCeti.orrCoefficient a b c s := by
  rw [(hasFPowerSeriesOnBall_one_sub_cpow_mul_ordinaryHypergeometric
    a b c).hasFPowerSeriesAt.coeff_taylorSeries, FormalMultilinearSeries.coeff_ofScalars]

/-- Uniqueness of the generating-function coefficients in DLMF 15.16.2: any sequence `A : ℕ → ℂ`
whose power series represents `(1 - z) ^ (a + b - c) * ₂F₁(2a, 2b; 2c - 1; z)` in a neighborhood of
`0` equals `TauCeti.orrCoefficient a b c` (classical when `2 * c - 1 ∉ -ℕ`, and matching the
`0⁻¹ = 0` truncation of `(2 * c - 1)_k = 0` summands when `2 * c - 1 ∈ -ℕ`). -/
theorem eq_orrCoefficient_of_eventually_hasSum (a b c : ℂ) {A : ℕ → ℂ}
    (hA : ∀ᶠ z in 𝓝 (0 : ℂ), HasSum (fun s : ℕ ↦ A s * z ^ s)
      ((1 - z) ^ (a + b - c) * ₂F₁ (2 * a) (2 * b) (2 * c - 1) z)) :
    A = TauCeti.orrCoefficient a b c := by
  have hpA : HasFPowerSeriesAt
      (fun z : ℂ ↦ (1 - z) ^ (a + b - c) * ₂F₁ (2 * a) (2 * b) (2 * c - 1) z)
      (FormalMultilinearSeries.ofScalars ℂ A) 0 :=
    hasFPowerSeriesAt_iff.mpr <| hA.mono fun z hz ↦ by
      simpa only [zero_add, FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul,
        mul_comm] using hz
  exact FormalMultilinearSeries.ofScalars_series_injective ℂ ℂ
    (hpA.eq_formalMultilinearSeries
      (hasFPowerSeriesOnBall_one_sub_cpow_mul_ordinaryHypergeometric a b c).hasFPowerSeriesAt)


/-! ### Burchnall–Chaundy two-variable product expansion (DLMF 15.16.3) -/

section BurchnallChaundyBounds

private noncomputable def bcPref (a b c : ℂ) (s : ℕ) (u : ℂ) : ℂ :=
  (ascPochhammer ℂ s).eval a * (ascPochhammer ℂ s).eval b *
    (ascPochhammer ℂ s).eval (c - a) * (ascPochhammer ℂ s).eval (c - b) /
      (s ! * Gamma (c + s)) * u ^ s

private noncomputable def bcTerm (a b c : ℂ) (s : ℕ) (z ζ : ℂ) : ℂ :=
  bcPref a b c s (z * ζ) *
    regularizedGaussHGFun (a + s) (b + s) (c + 2 * s) (z + ζ - z * ζ)

private noncomputable def bcGenCoeff (a b c : ℂ) (s j k : ℕ) : ℂ :=
  (ascPochhammer ℂ (s + j + k)).eval a * (ascPochhammer ℂ (s + j + k)).eval b *
    (ascPochhammer ℂ s).eval (c - a) * (ascPochhammer ℂ s).eval (c - b) /
    (s ! * Gamma (c + s) * j ! * k ! * Gamma (c + (2 * s + j + k : ℕ)))

private noncomputable def bcGenPref (a b c u v : ℂ) (s j : ℕ) : ℂ :=
  bcPref a b c s u *
    ((ascPochhammer ℂ j).eval (a + s) * (ascPochhammer ℂ j).eval (b + s) / j ! * v ^ j)

private theorem bcGenPref_zero (a b c u v : ℂ) (s : ℕ) :
    bcGenPref a b c u v s 0 = bcPref a b c s u := by
  simp [bcGenPref]

private noncomputable def bcDoubleTerm (a b c z ζ : ℂ) (p : ℕ × ℕ) : ℂ :=
  bcGenPref a b c (z * ζ) (ζ * (1 - z)) p.1 p.2 *
    regularizedGaussHGFun (a + p.1 + p.2) (b + p.1 + p.2) (c + 2 * p.1 + p.2) z

private theorem bc_factorial_ratio_le (s j k : ℕ) :
    (((s + (j + k))! : ℝ) * (s + (j + k))! * s ! * s !) /
      ((s ! : ℝ) * s ! * j ! * k ! * (2 * s + (j + k))!) ≤ ((j + k).choose j : ℝ) := by
  set m := j + k
  rw [div_le_iff₀ (by positivity)]
  have hsq : ((s + m)! : ℝ) * (s + m)! ≤ m ! * (2 * s + m)! := by
    rw [← sq, add_comm s m, add_comm (2 * s) m]
    exact_mod_cast Nat.factorial_add_sq_le_factorial_mul_factorial_add_two_mul m s
  have hch : (m ! : ℝ) = (m.choose j : ℝ) * j ! * k ! := by
    exact_mod_cast (by simpa [m, add_tsub_cancel_left] using
      (Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right j k)).symm)
  calc ((s + m)! : ℝ) * (s + m)! * s ! * s !
      ≤ (m ! * (2 * s + m)!) * s ! * s ! := by gcongr
    _ = (m.choose j : ℝ) * ((s ! : ℝ) * s ! * j ! * k ! * (2 * s + m)!) := by rw [hch]; ring

private theorem natCast_add_natCast_le_mul (s N : ℕ) :
    ((s + N : ℕ) : ℝ) ≤ ((N : ℝ) + 1) * ((s : ℝ) + 1) := by
  push_cast
  nlinarith [N.cast_nonneg (α := ℝ), s.cast_nonneg (α := ℝ)]

private theorem natCast_add_add_le_mul (s m N : ℕ) :
    ((s + m + N : ℕ) : ℝ) ≤ ((N : ℝ) + 1) * ((s : ℝ) + 1) * ((m : ℝ) + 1) := by
  have h1 : (s : ℝ) + m + 1 ≤ ((s : ℝ) + 1) * ((m : ℝ) + 1) := by
    nlinarith [s.cast_nonneg (α := ℝ), m.cast_nonneg (α := ℝ)]
  have h2 := natCast_add_natCast_le_mul (s + m) N
  push_cast at h2 ⊢
  nlinarith [N.cast_nonneg (α := ℝ)]

private theorem two_mul_add_natCast_add_one_le (s m : ℕ) :
    ((2 * s + m : ℕ) : ℝ) + 1 ≤ 2 * ((s : ℝ) + 1) * ((m : ℝ) + 1) := by
  push_cast
  nlinarith [s.cast_nonneg (α := ℝ), m.cast_nonneg (α := ℝ)]

private theorem norm_bcGenCoeff_le_pochhammer_gamma {a b c : ℂ} {N M : ℕ} {CΓ : ℝ}
    (haN : ‖a‖ ≤ N) (hbN : ‖b‖ ≤ N) (hcaN : ‖c - a‖ ≤ N) (hcbN : ‖c - b‖ ≤ N)
    (hCΓ : 0 ≤ CΓ)
    (hΓ : ∀ n : ℕ, ‖(Gamma (c + n))⁻¹‖ ≤ CΓ * ((n : ℝ) + 1) ^ M / n !)
    (s j k : ℕ) :
    ‖bcGenCoeff a b c s j k‖ ≤
      CΓ ^ 2 * ((s + (j + k) + N : ℕ) : ℝ) ^ (2 * N) * ((s + N : ℕ) : ℝ) ^ (2 * N) *
        ((s : ℝ) + 1) ^ M * (((2 * s + (j + k) : ℕ) : ℝ) + 1) ^ M * ((j + k).choose j : ℝ) := by
  set m := j + k
  have h1 := TauCeti.norm_ascPochhammer_eval_le_pow_mul_factorial haN (s + m)
  have h2 := TauCeti.norm_ascPochhammer_eval_le_pow_mul_factorial hbN (s + m)
  have h3 := TauCeti.norm_ascPochhammer_eval_le_pow_mul_factorial hcaN s
  have h4 := TauCeti.norm_ascPochhammer_eval_le_pow_mul_factorial hcbN s
  have h5 := hΓ s
  have h6 := hΓ (2 * s + m)
  have hfac := bc_factorial_ratio_le s j k
  have hsjk : s + j + k = s + m := add_assoc s j k
  have h2sjk : 2 * s + j + k = 2 * s + m := add_assoc (2 * s) j k
  have hfac_inv (n : ℕ) : ‖((n ! : ℂ))⁻¹‖ = (n ! : ℝ)⁻¹ := by rw [norm_inv, norm_natCast]
  rw [bcGenCoeff, hsjk, h2sjk, div_eq_mul_inv]
  simp only [mul_inv, norm_mul, hfac_inv]
  calc ‖(ascPochhammer ℂ (s + m)).eval a‖ * ‖(ascPochhammer ℂ (s + m)).eval b‖ *
        ‖(ascPochhammer ℂ s).eval (c - a)‖ * ‖(ascPochhammer ℂ s).eval (c - b)‖ *
        ((s ! : ℝ)⁻¹ * ‖(Gamma (c + s))⁻¹‖ * (j ! : ℝ)⁻¹ * (k ! : ℝ)⁻¹ *
          ‖(Gamma (c + (2 * s + m : ℕ)))⁻¹‖)
      ≤ ((((s + m : ℕ) + (N : ℝ)) ^ N * (s + m)!) * (((s + m : ℕ) + (N : ℝ)) ^ N * (s + m)!) *
          ((s + N : ℝ) ^ N * s !) * ((s + N : ℝ) ^ N * s !)) *
        ((s ! : ℝ)⁻¹ * (CΓ * ((s : ℝ) + 1) ^ M / s !) * (j ! : ℝ)⁻¹ * (k ! : ℝ)⁻¹ *
          (CΓ * (((2 * s + m : ℕ) : ℝ) + 1) ^ M / (2 * s + m)!)) := by gcongr
    _ = CΓ ^ 2 * ((s + m + N : ℕ) : ℝ) ^ (2 * N) * ((s + N : ℕ) : ℝ) ^ (2 * N) *
          ((s : ℝ) + 1) ^ M * (((2 * s + m : ℕ) : ℝ) + 1) ^ M *
          ((((s + m)! : ℝ) * (s + m)! * s ! * s !) /
            ((s ! : ℝ) * s ! * j ! * k ! * (2 * s + m)!)) := by push_cast; ring
    _ ≤ CΓ ^ 2 * ((s + m + N : ℕ) : ℝ) ^ (2 * N) * ((s + N : ℕ) : ℝ) ^ (2 * N) *
          ((s : ℝ) + 1) ^ M * (((2 * s + m : ℕ) : ℝ) + 1) ^ M * (m.choose j : ℝ) := by gcongr

private theorem norm_bcGenCoeff_le {a b c : ℂ} {N M : ℕ} {CΓ : ℝ}
    (haN : ‖a‖ ≤ N) (hbN : ‖b‖ ≤ N) (hcaN : ‖c - a‖ ≤ N) (hcbN : ‖c - b‖ ≤ N)
    (hCΓ : 0 ≤ CΓ)
    (hΓ : ∀ n : ℕ, ‖(Gamma (c + n))⁻¹‖ ≤ CΓ * ((n : ℝ) + 1) ^ M / n !)
    (s j k : ℕ) :
    ‖bcGenCoeff a b c s j k‖ ≤
      CΓ ^ 2 * ((N : ℝ) + 1) ^ (4 * N) * 2 ^ M * ((s : ℝ) + 1) ^ (4 * N + 2 * M) *
        ((j + k : ℝ) + 1) ^ (2 * N + M) * ((j + k).choose j : ℝ) := by
  set m := j + k
  have hp1 := natCast_add_add_le_mul s m N
  have hp2 := natCast_add_natCast_le_mul s N
  have hp3 := two_mul_add_natCast_add_one_le s m
  have h4N : 4 * N = 2 * N + 2 * N := by ring
  have h2M : 2 * M = M + M := by ring
  calc ‖bcGenCoeff a b c s j k‖
      ≤ CΓ ^ 2 * ((s + m + N : ℕ) : ℝ) ^ (2 * N) * ((s + N : ℕ) : ℝ) ^ (2 * N) *
          ((s : ℝ) + 1) ^ M * (((2 * s + m : ℕ) : ℝ) + 1) ^ M * (m.choose j : ℝ) :=
        norm_bcGenCoeff_le_pochhammer_gamma haN hbN hcaN hcbN hCΓ hΓ s j k
    _ ≤ CΓ ^ 2 * (((N : ℝ) + 1) * ((s : ℝ) + 1) * ((m : ℝ) + 1)) ^ (2 * N) *
          (((N : ℝ) + 1) * ((s : ℝ) + 1)) ^ (2 * N) * ((s : ℝ) + 1) ^ M *
          (2 * ((s : ℝ) + 1) * ((m : ℝ) + 1)) ^ M * (m.choose j : ℝ) := by gcongr
    _ = CΓ ^ 2 * ((N : ℝ) + 1) ^ (4 * N) * 2 ^ M * ((s : ℝ) + 1) ^ (4 * N + 2 * M) *
          ((j + k : ℝ) + 1) ^ (2 * N + M) * ((j + k).choose j : ℝ) := by
        simp only [m, Nat.cast_add, mul_pow, h4N, h2M, pow_add]
        ring

private theorem exists_bc_coeff_bound (a b c : ℂ) :
    ∃ K : ℝ, ∃ P Q : ℕ, 0 ≤ K ∧ ∀ s j k : ℕ,
      ‖bcGenCoeff a b c s j k‖ ≤
        K * ((s : ℝ) + 1) ^ P * ((j + k : ℝ) + 1) ^ Q * ((j + k).choose j : ℝ) := by
  let N : ℕ := max (max ⌈‖a‖⌉₊ ⌈‖b‖⌉₊) (max ⌈‖c - a‖⌉₊ ⌈‖c - b‖⌉₊) + 1
  have hN (w : ℂ) (hw : ⌈‖w‖⌉₊ ≤ N - 1) : ‖w‖ ≤ N :=
    (Nat.le_ceil ‖w‖).trans (by exact_mod_cast hw.trans (Nat.sub_le N 1))
  obtain ⟨CΓ, M, hCΓ, hΓ⟩ := exists_norm_inv_Gamma_add_natCast_le c
  exact ⟨CΓ ^ 2 * ((N : ℝ) + 1) ^ (4 * N) * 2 ^ M, 4 * N + 2 * M, 2 * N + M, by positivity,
    norm_bcGenCoeff_le (hN a ((le_max_left _ _).trans (le_max_left _ _)))
      (hN b ((le_max_right _ _).trans (le_max_left _ _)))
      (hN (c - a) ((le_max_left _ _).trans (le_max_right _ _)))
      (hN (c - b) ((le_max_right _ _).trans (le_max_right _ _))) hCΓ hΓ⟩

private theorem ascPochhammer_add_add_eval (x : ℂ) (s j k : ℕ) :
    (ascPochhammer ℂ s).eval x * (ascPochhammer ℂ j).eval (x + s) *
        (ascPochhammer ℂ k).eval (x + s + j) =
      (ascPochhammer ℂ (s + j + k)).eval x := by
  rw [TauCeti.ascPochhammer_add_eval x (s + j) k, TauCeti.ascPochhammer_add_eval x s j]
  push_cast
  rw [add_assoc x (s : ℂ) j]

private theorem norm_bcGenTerm_coeff_eq (a b c u v y : ℂ) (s j k : ℕ) :
    ‖bcGenPref a b c u v s j *
        ((regularizedGaussHGFunSeries (a + s + j) (b + s + j) (c + 2 * s + j)).coeff k *
          y ^ k)‖ =
      ‖bcGenCoeff a b c s j k‖ * ‖u‖ ^ s * ‖v‖ ^ j * ‖y‖ ^ k := by
  have hc_eq : c + 2 * (s : ℂ) + j + k = c + (2 * s + j + k : ℕ) := by push_cast; ring
  simp only [bcGenPref, bcPref, bcGenCoeff, coeff_regularizedGaussHGFunSeries, hc_eq]
  rw [← norm_pow u s, ← norm_pow v j, ← norm_pow y k, ← norm_mul, ← norm_mul, ← norm_mul]
  refine congrArg norm ?_
  simp only [div_eq_mul_inv, mul_inv]
  rw [← ascPochhammer_add_add_eval a, ← ascPochhammer_add_add_eval b]
  ring

private theorem norm_bcGenTerm_le {a b c u v y : ℂ} {K : ℝ} {P Q : ℕ} (hy : ‖y‖ < 1)
    (hbound : ∀ s j k : ℕ,
      ‖bcGenCoeff a b c s j k‖ ≤
        K * ((s : ℝ) + 1) ^ P * ((j + k : ℝ) + 1) ^ Q * ((j + k).choose j : ℝ))
    (s j : ℕ)
    (hrow : Summable fun k : ℕ ↦
      ((j + k : ℝ) + 1) ^ Q * ((j + k).choose j : ℝ) * ‖v‖ ^ j * ‖y‖ ^ k) :
    ‖bcGenPref a b c u v s j *
        regularizedGaussHGFun (a + s + j) (b + s + j) (c + 2 * s + j) y‖ ≤
      K * ((s : ℝ) + 1) ^ P * ‖u‖ ^ s *
        (∑' k : ℕ, ((j + k : ℝ) + 1) ^ Q * ((j + k).choose j : ℝ) * ‖v‖ ^ j * ‖y‖ ^ k) := by
  have hsy := (hasSum_regularizedGaussHGFun (a + s + j) (b + s + j)
    (c + 2 * s + j) hy).mul_left (bcGenPref a b c u v s j)
  have hterm_le (k : ℕ) :
      ‖bcGenPref a b c u v s j *
          ((regularizedGaussHGFunSeries (a + s + j) (b + s + j) (c + 2 * s + j)).coeff k *
            y ^ k)‖ ≤
        K * ((s : ℝ) + 1) ^ P * ‖u‖ ^ s *
          (((j + k : ℝ) + 1) ^ Q * ((j + k).choose j : ℝ) * ‖v‖ ^ j * ‖y‖ ^ k) := by
    rw [norm_bcGenTerm_coeff_eq a b c u v y s j k]
    calc _ ≤ (K * ((s : ℝ) + 1) ^ P * ((j + k : ℝ) + 1) ^ Q * ((j + k).choose j : ℝ)) *
            ‖u‖ ^ s * ‖v‖ ^ j * ‖y‖ ^ k := by gcongr; exact hbound s j k
      _ = K * ((s : ℝ) + 1) ^ P * ‖u‖ ^ s *
            (((j + k : ℝ) + 1) ^ Q * ((j + k).choose j : ℝ) * ‖v‖ ^ j * ‖y‖ ^ k) := by ring
  have hmaj := hrow.mul_left (K * ((s : ℝ) + 1) ^ P * ‖u‖ ^ s)
  have hsum_norm := Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hterm_le hmaj
  rw [← hsy.tsum_eq]
  exact (norm_tsum_le_tsum_norm hsum_norm).trans
    ((Summable.tsum_le_tsum hterm_le hsum_norm hmaj).trans_eq (hrow.tsum_mul_left _))

private theorem exists_summable_norm_bcTerm_le (a b c : ℂ) {ζ : ℂ} {r : ℝ}
    (hζ : ‖ζ‖ < 1) (hr1 : r < 1) :
    ∃ g : ℕ → ℝ, Summable g ∧ ∀ s : ℕ, ∀ z : ℂ, ‖z‖ ≤ r → ‖z + ζ - z * ζ‖ ≤ r →
      ‖bcTerm a b c s z ζ‖ ≤ g s := by
  by_cases hr0 : 0 ≤ r
  · obtain ⟨K, P, Q, hK0, hbound⟩ := exists_bc_coeff_bound a b c
    have hrow_r : Summable fun k : ℕ ↦ ((k : ℝ) + 1) ^ Q * r ^ k :=
      TauCeti.summable_add_pow_mul_geometric_of_norm_lt_one 1 Q (by rwa [Real.norm_of_nonneg hr0])
    refine ⟨fun s ↦ K * (∑' k : ℕ, ((k : ℝ) + 1) ^ Q * r ^ k) * (((s : ℝ) + 1) ^ P * (r * ‖ζ‖) ^ s),
      (TauCeti.summable_add_pow_mul_geometric_of_norm_lt_one 1 P (r := r * ‖ζ‖)
        (by rw [Real.norm_of_nonneg (by positivity)]; nlinarith [norm_nonneg ζ])).mul_left _,
      fun s z hz hw ↦ ?_⟩
    set w := z + ζ - z * ζ
    have hw1 : ‖w‖ < 1 := hw.trans_lt hr1
    have hrow_w0 := TauCeti.summable_add_pow_mul_geometric_of_norm_lt_one 1 Q
      (r := ‖w‖) (by simpa using hw1)
    have hbc : ‖bcTerm a b c s z ζ‖ ≤
        K * ((s : ℝ) + 1) ^ P * ‖z * ζ‖ ^ s * (∑' k : ℕ, ((k : ℝ) + 1) ^ Q * ‖w‖ ^ k) := by
      have h0 := norm_bcGenTerm_le (u := z * ζ) (v := 1) hw1 hbound s 0
        (hrow_w0.congr fun k ↦ by simp)
      rw [bcGenPref_zero] at h0
      simp only [Nat.cast_zero, add_zero, zero_add, Nat.choose_zero_right, Nat.cast_one,
        norm_one, one_pow, mul_one] at h0
      exact h0
    have htsum : (∑' k : ℕ, ((k : ℝ) + 1) ^ Q * ‖w‖ ^ k) ≤ ∑' k : ℕ, ((k : ℝ) + 1) ^ Q * r ^ k :=
      Summable.tsum_le_tsum (fun k ↦ by gcongr) hrow_w0 hrow_r
    have huz : ‖z * ζ‖ ^ s ≤ (r * ‖ζ‖) ^ s := by
      rw [norm_mul]; exact pow_le_pow_left₀ (by positivity) (by gcongr) s
    calc ‖bcTerm a b c s z ζ‖
        ≤ K * ((s : ℝ) + 1) ^ P * ‖z * ζ‖ ^ s * (∑' k : ℕ, ((k : ℝ) + 1) ^ Q * ‖w‖ ^ k) := hbc
      _ ≤ K * ((s : ℝ) + 1) ^ P * (r * ‖ζ‖) ^ s * (∑' k : ℕ, ((k : ℝ) + 1) ^ Q * r ^ k) := by
          gcongr
      _ = K * (∑' k : ℕ, ((k : ℝ) + 1) ^ Q * r ^ k) * (((s : ℝ) + 1) ^ P * (r * ‖ζ‖) ^ s) := by
          ring
  · exact ⟨0, summable_zero, fun _ z hz _ ↦ absurd ((norm_nonneg z).trans hz) hr0⟩

private theorem isOpen_bcBall (ζ : ℂ) (r : ℝ) :
    IsOpen {z : ℂ | ‖z‖ < r ∧ ‖z + ζ - z * ζ‖ < r} :=
  (isOpen_lt continuous_norm continuous_const).inter
    (isOpen_lt (by fun_prop : Continuous fun z : ℂ ↦ ‖z + ζ - z * ζ‖) continuous_const)

private theorem differentiableOn_tsum_bcTerm (a b c : ℂ) {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    DifferentiableOn ℂ (fun z : ℂ ↦ ∑' s : ℕ, bcTerm a b c s z ζ)
      {z : ℂ | ‖z‖ < 1 ∧ ‖z + ζ - z * ζ‖ < 1} := by
  intro z₀ hz₀
  set r : ℝ := (max ‖z₀‖ ‖z₀ + ζ - z₀ * ζ‖ + 1) / 2
  have hr_lt : r < 1 := by simp only [r]; linarith [max_lt hz₀.1 hz₀.2]
  let V : Set ℂ := {z : ℂ | ‖z‖ < r ∧ ‖z + ζ - z * ζ‖ < r}
  have hV_open : IsOpen V := isOpen_bcBall ζ r
  have hz₀V : z₀ ∈ V :=
    ⟨by simp only [r]; linarith [le_max_left ‖z₀‖ ‖z₀ + ζ - z₀ * ζ‖, hz₀.1, hz₀.2],
      by simp only [r]; linarith [le_max_right ‖z₀‖ ‖z₀ + ζ - z₀ * ζ‖, hz₀.1, hz₀.2]⟩
  obtain ⟨g, hg, hbound⟩ := exists_summable_norm_bcTerm_le a b c hζ hr_lt
  have hdiffV : DifferentiableOn ℂ (fun z : ℂ ↦ ∑' s : ℕ, bcTerm a b c s z ζ) V := by
    refine differentiableOn_tsum_of_summable_norm hg (fun s z hzV ↦ ?_) hV_open fun s z hzV ↦
      hbound s z hzV.1.le hzV.2.le
    have hcomp : DifferentiableAt ℂ
        (fun z : ℂ ↦ regularizedGaussHGFun (a + s) (b + s) (c + 2 * s) (z + ζ - z * ζ)) z :=
      (analyticAt_regularizedGaussHGFun _ _ _ (hzV.2.trans hr_lt)).differentiableAt.comp z
        (by fun_prop)
    simp only [bcTerm, bcPref]
    exact ((by fun_prop : DifferentiableAt ℂ _ z).mul hcomp).differentiableWithinAt
  exact ((hdiffV z₀ hz₀V).differentiableAt (hV_open.mem_nhds hz₀V)).differentiableWithinAt

private theorem norm_snd_lt_one_of_add_norm_mul_sub_lt_one {z ζ : ℂ}
    (hzv : ‖z‖ + ‖ζ * (1 - z)‖ < 1) : ‖ζ‖ < 1 := by
  have hz1 : ‖z‖ < 1 := by linarith [norm_nonneg (ζ * (1 - z))]
  have h1z : 1 - ‖z‖ ≤ ‖1 - z‖ := by simpa using norm_sub_norm_le 1 z
  have hmul : ‖ζ‖ * (1 - ‖z‖) ≤ ‖ζ * (1 - z)‖ := by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left h1z (norm_nonneg ζ)
  by_contra! hζ
  nlinarith

private theorem summable_norm_bcDoubleTerm (a b c : ℂ) {z ζ : ℂ}
    (hzv : ‖z‖ + ‖ζ * (1 - z)‖ < 1) :
    Summable fun p : ℕ × ℕ ↦ ‖bcDoubleTerm a b c z ζ p‖ := by
  obtain ⟨K, P, Q, _, hbound⟩ := exists_bc_coeff_bound a b c
  have hz1 : ‖z‖ < 1 := by linarith [norm_nonneg (ζ * (1 - z))]
  have hζ : ‖ζ‖ < 1 := norm_snd_lt_one_of_add_norm_mul_sub_lt_one hzv
  have hzζ1 : ‖z * ζ‖ < 1 := by rw [norm_mul]; nlinarith [norm_nonneg z, norm_nonneg ζ]
  set r₁ := ‖z‖
  set r₂ := ‖ζ * (1 - z)‖
  have hjk_sum : Summable fun q : ℕ × ℕ ↦
      ((q.1 + q.2 : ℝ) + 1) ^ Q * ((q.1 + q.2).choose q.1 : ℝ) * r₂ ^ q.1 * r₁ ^ q.2 := by
    have hdiag : Summable fun m : ℕ ↦ ((m : ℝ) + 1) ^ Q * (r₂ + r₁) ^ m :=
      TauCeti.summable_add_pow_mul_geometric_of_norm_lt_one 1 Q (r := r₂ + r₁)
        (by rw [Real.norm_of_nonneg (by positivity)]; linarith)
    have hsigma : Summable fun x : Σ m : ℕ, antidiagonal m ↦
        ((x.2.val.1 + x.2.val.2 : ℝ) + 1) ^ Q * ((x.2.val.1 + x.2.val.2).choose x.2.val.1 : ℝ) *
          r₂ ^ x.2.val.1 * r₁ ^ x.2.val.2 := by
      rw [summable_sigma_of_nonneg (fun _ ↦ by positivity)]
      refine ⟨fun _ ↦ Summable.of_finite, hdiag.congr fun m ↦ ?_⟩
      rw [tsum_fintype]
      dsimp only
      rw [sum_coe_sort (antidiagonal m) (fun q : ℕ × ℕ ↦
        ((q.1 + q.2 : ℝ) + 1) ^ Q * ((q.1 + q.2).choose q.1 : ℝ) * r₂ ^ q.1 * r₁ ^ q.2),
        (Commute.all r₂ r₁).add_pow', mul_sum]
      refine sum_congr rfl fun q hq ↦ ?_
      rw [← Nat.cast_add, mem_antidiagonal.mp hq, nsmul_eq_mul]; ring
    exact HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff.mp hsigma
  obtain ⟨hk_row, hj_col⟩ := (summable_prod_of_nonneg (fun _ ↦ by positivity)).mp hjk_sum
  have hs_sum : Summable fun s : ℕ ↦ K * ((s : ℝ) + 1) ^ P * ‖z * ζ‖ ^ s :=
    ((TauCeti.summable_add_pow_mul_geometric_of_norm_lt_one 1 P (r := ‖z * ζ‖)
      (by simpa using hzζ1)).mul_left K).congr fun _ ↦ by ring
  have hprod := Summable.mul_of_nonneg hs_sum hj_col (fun _ ↦ by positivity)
    (fun j ↦ tsum_nonneg fun _ ↦ by positivity)
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun ⟨s, j⟩ ↦ ?_) hprod
  simp only [bcDoubleTerm]
  exact norm_bcGenTerm_le (u := z * ζ) (v := ζ * (1 - z)) hz1 hbound s j (hk_row j)

private theorem bcDoubleTerm_antidiag_eq (a b c z ζ : ℂ) {n s : ℕ} (hsn : s ≤ n) :
    bcDoubleTerm a b c z ζ (s, n - s) =
      (n.choose s : ℂ) * (ascPochhammer ℂ s).eval (c - a) * (ascPochhammer ℂ s).eval (c - b) *
        (ascPochhammer ℂ (n - s)).eval (c + s) * z ^ s * (1 - z) ^ (n - s) *
        regularizedGaussHGFun (a + n) (b + n) (c + n + s) z *
        ((regularizedGaussHGFunSeries a b c).coeff n * ζ ^ n) := by
  have hadd_n : s + (n - s) = n := Nat.add_sub_of_le hsn
  have hch : (n.choose s : ℂ) * (n ! : ℂ)⁻¹ = (s ! : ℂ)⁻¹ * ((n - s)! : ℂ)⁻¹ := by
    rw [mul_comm, Nat.inv_factorial_mul_choose (K := ℂ) n s (n - s) hadd_n]
  have hshift (x : ℂ) : x + (s : ℂ) + (n - s : ℕ) = x + n := by
    rw [add_assoc, ← Nat.cast_add, hadd_n]
  have hΓ := (inv_Gamma_eq_ascPochhammer_mul_inv_Gamma_add (c + s) (n - s)).symm
  rw [hshift c] at hΓ
  have hp (x : ℂ) : (ascPochhammer ℂ s).eval x * (ascPochhammer ℂ (n - s)).eval (x + s) =
      (ascPochhammer ℂ n).eval x := by
    rw [← TauCeti.ascPochhammer_add_eval, hadd_n]
  have hζn : ζ ^ s * ζ ^ (n - s) = ζ ^ n := by rw [← pow_add, hadd_n]
  have hc2_shift : c + 2 * (s : ℂ) + (n - s : ℕ) = c + n + s := by
    have htwo : c + 2 * (s : ℂ) = c + s + s := by ring
    rw [htwo, hshift (c + s), add_right_comm]
  simp only [bcDoubleTerm, bcGenPref, bcPref, coeff_regularizedGaussHGFunSeries, hshift a, hshift b,
    hc2_shift, div_eq_mul_inv, mul_inv, mul_pow]
  rw [← hΓ, ← hp a, ← hp b, ← hζn]
  linear_combination (ascPochhammer ℂ s).eval a * (ascPochhammer ℂ (n - s)).eval (a + s) *
    (ascPochhammer ℂ s).eval b * (ascPochhammer ℂ (n - s)).eval (b + s) *
    (ascPochhammer ℂ s).eval (c - a) * (ascPochhammer ℂ s).eval (c - b) *
    (ascPochhammer ℂ (n - s)).eval (c + s) * (Gamma (c + n))⁻¹ *
    z ^ s * ζ ^ s * ζ ^ (n - s) * (1 - z) ^ (n - s) *
    regularizedGaussHGFun (a + n) (b + n) (c + n + s) z * hch.symm

private theorem hasSum_bcTerm_of_add_norm_lt (a b c : ℂ) {z ζ : ℂ}
    (hzv : ‖z‖ + ‖ζ * (1 - z)‖ < 1) :
    HasSum (fun s : ℕ ↦ bcTerm a b c s z ζ)
      (regularizedGaussHGFun a b c z * regularizedGaussHGFun a b c ζ) := by
  let D := bcDoubleTerm a b c z ζ
  have hD : Summable D := (summable_norm_bcDoubleTerm a b c hzv).of_norm
  have hz1 : ‖z‖ < 1 := by linarith [norm_nonneg (ζ * (1 - z))]
  have hζ : ‖ζ‖ < 1 := norm_snd_lt_one_of_add_norm_mul_sub_lt_one hzv
  have hrow : HasSum (fun s : ℕ ↦ bcTerm a b c s z ζ) (∑' p, D p) := by
    refine hD.hasSum.prod_fiberwise fun s ↦ ?_
    have hadd := (hasSum_regularizedGaussHGFun_add (a + s) (b + s) (c + 2 * s) hzv).mul_left
      (bcPref a b c s (z * ζ))
    have hw : z + ζ * (1 - z) = z + ζ - z * ζ := by ring
    rw [hw] at hadd
    simpa only [D, bcDoubleTerm, bcGenPref, bcTerm, mul_assoc] using hadd
  have hdiag : HasSum
      (fun n : ℕ ↦ regularizedGaussHGFun a b c z *
        ((regularizedGaussHGFunSeries a b c).coeff n * ζ ^ n)) (∑' p, D p) := by
    have h := (HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff.2 hD.hasSum).sigma
      fun n ↦ hasSum_fintype _
    simp only [Function.comp_apply, HasAntidiagonal.sigmaAntidiagonalEquivProd_apply,
      sum_coe_sort (antidiagonal _) D] at h
    refine h.congr_fun fun n ↦ ?_
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun s j ↦ D (s, j)) n,
      regularizedGaussHGFun_eq_sum_choose_mul_regularizedGaussHGFun a b c hz1 n, sum_mul]
    exact sum_congr rfl fun s hs ↦
      (bcDoubleTerm_antidiag_eq a b c z ζ (mem_range_succ_iff.mp hs)).symm
  have hprod := (hasSum_regularizedGaussHGFun a b c hζ).mul_left (regularizedGaussHGFun a b c z)
  rwa [← hprod.unique hdiag] at hrow

private theorem convex_bcDomain (ζ : ℂ) :
    Convex ℝ {z : ℂ | ‖z‖ < 1 ∧ ‖z + ζ - z * ζ‖ < 1} := by
  have hset : {z : ℂ | ‖z‖ < 1 ∧ ‖z + ζ - z * ζ‖ < 1} =
      Metric.ball (0 : ℂ) 1 ∩
        (LinearMap.mulLeft ℝ (1 - ζ) ⁻¹' ((· + ζ) ⁻¹' Metric.ball (0 : ℂ) 1)) := by
    ext z
    have hmul : (1 - ζ) * z + ζ = z + ζ - z * ζ := by ring
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Metric.mem_ball,
      dist_zero_right, LinearMap.mulLeft_apply, hmul]
  rw [hset]
  exact (convex_ball (0 : ℂ) 1).inter
    (((convex_ball (0 : ℂ) 1).translate_preimage_left ζ).linear_preimage
      (LinearMap.mulLeft ℝ (1 - ζ)))

end BurchnallChaundyBounds

/-- **Burchnall–Chaundy two-variable product expansion for `regularizedGaussHGFun` (DLMF 15.16.3).**
Whenever `‖z‖ < 1`, `‖ζ‖ < 1`, and `‖z + ζ - z * ζ‖ < 1`, the product
`𝐅(a, b; c; z) * 𝐅(a, b; c; ζ)` expands as a series in
`(z * ζ) ^ s * 𝐅(a + s, b + s; c + 2s; z + ζ - z * ζ)`, for all complex parameters `a`, `b`, `c`
(including nonpositive integer poles of `Γ(c)`). -/
theorem hasSum_regularizedGaussHGFun_mul_regularizedGaussHGFun (a b c : ℂ) {z ζ : ℂ}
    (hz : ‖z‖ < 1) (hζ : ‖ζ‖ < 1) (hw : ‖z + ζ - z * ζ‖ < 1) :
    HasSum
      (fun s : ℕ ↦ (ascPochhammer ℂ s).eval a * (ascPochhammer ℂ s).eval b *
        (ascPochhammer ℂ s).eval (c - a) * (ascPochhammer ℂ s).eval (c - b) /
          (s ! * Gamma (c + s)) * (z * ζ) ^ s *
        regularizedGaussHGFun (a + s) (b + s) (c + 2 * s) (z + ζ - z * ζ))
      (regularizedGaussHGFun a b c z * regularizedGaussHGFun a b c ζ) := by
  let U : Set ℂ := {z' : ℂ | ‖z'‖ < 1 ∧ ‖z' + ζ - z' * ζ‖ < 1}
  have hf_an : AnalyticOnNhd ℂ (fun z' : ℂ ↦ ∑' s : ℕ, bcTerm a b c s z' ζ) U :=
    (differentiableOn_tsum_bcTerm a b c hζ).analyticOnNhd (isOpen_bcBall ζ 1)
  have hg_an : AnalyticOnNhd ℂ
      (fun z' : ℂ ↦ regularizedGaussHGFun a b c z' * regularizedGaussHGFun a b c ζ) U :=
    fun _ hz' ↦ (analyticAt_regularizedGaussHGFun a b c hz'.1).mul analyticAt_const
  have heq0 : (fun z' : ℂ ↦ ∑' s : ℕ, bcTerm a b c s z' ζ) =ᶠ[𝓝 (0 : ℂ)]
      fun z' : ℂ ↦ regularizedGaussHGFun a b c z' * regularizedGaussHGFun a b c ζ := by
    have hrad : 0 < (1 - ‖ζ‖) / 4 := by linarith
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hrad] with z' hz'
    rw [Metric.mem_ball, dist_zero_right] at hz'
    have hzv : ‖z'‖ + ‖ζ * (1 - z')‖ < 1 := by
      calc ‖z'‖ + ‖ζ * (1 - z')‖ = ‖z'‖ + ‖ζ‖ * ‖1 - z'‖ := by rw [norm_mul]
        _ ≤ ‖z'‖ + ‖ζ‖ * (1 + ‖z'‖) := by gcongr; exact (norm_sub_le 1 z').trans_eq (by simp)
        _ < 1 := by nlinarith [norm_nonneg ζ, norm_nonneg z']
    exact (hasSum_bcTerm_of_add_norm_lt a b c hzv).tsum_eq
  have heqU := hf_an.eqOn_of_preconnected_of_eventuallyEq hg_an
    (convex_bcDomain ζ).isPreconnected ⟨by simp, by simpa using hζ⟩ heq0
  obtain ⟨g, hg, hbound⟩ := exists_summable_norm_bcTerm_le a b c hζ (max_lt hz hw)
  have hsum_z : Summable fun s : ℕ ↦ bcTerm a b c s z ζ :=
    .of_norm_bounded hg fun s ↦ hbound s z (le_max_left _ _) (le_max_right _ _)
  simpa only [bcTerm, bcPref, ← heqU ⟨hz, hw⟩] using hsum_z.hasSum

/-- **Burchnall–Chaundy two-variable product expansion for `₂F₁` (DLMF 15.16.3, ordinary form).**
When `c` avoids the nonpositive integers and `‖z‖ < 1`, `‖ζ‖ < 1`, `‖z + ζ - z * ζ‖ < 1`,
`₂F₁(a, b; c; z) * ₂F₁(a, b; c; ζ)` expands as a series in
`((a)_s (b)_s (c - a)_s (c - b)_s / (s! (c)_s (c)_{2s})) (z * ζ) ^ s ₂F₁(a + s, b + s; c + 2s; w)`
with `w = z + ζ - z * ζ`. -/
theorem hasSum_ordinaryHypergeometric_mul_ordinaryHypergeometric (a b : ℂ) {c z ζ : ℂ}
    (hc : ∀ k : ℕ, c ≠ -k) (hz : ‖z‖ < 1) (hζ : ‖ζ‖ < 1) (hw : ‖z + ζ - z * ζ‖ < 1) :
    HasSum
      (fun s : ℕ ↦ (ascPochhammer ℂ s).eval a * (ascPochhammer ℂ s).eval b *
        (ascPochhammer ℂ s).eval (c - a) * (ascPochhammer ℂ s).eval (c - b) /
          (s ! * (ascPochhammer ℂ s).eval c * (ascPochhammer ℂ (2 * s)).eval c) * (z * ζ) ^ s *
        ₂F₁ (a + s) (b + s) (c + 2 * s) (z + ζ - z * ζ))
      (₂F₁ a b c z * ₂F₁ a b c ζ) := by
  have hΓc : Gamma c ≠ 0 := Gamma_ne_zero hc
  have hmul := (hasSum_regularizedGaussHGFun_mul_regularizedGaussHGFun a b c hz hζ hw).mul_left
    (Gamma c * Gamma c)
  have hprod : Gamma c * Gamma c *
      (regularizedGaussHGFun a b c z * regularizedGaussHGFun a b c ζ) =
      ₂F₁ a b c z * ₂F₁ a b c ζ := by
    rw [← ordinaryHypergeometric_div_Gamma_eq hc, ← ordinaryHypergeometric_div_Gamma_eq hc]
    field_simp
  rw [hprod] at hmul
  refine hmul.congr_fun fun s ↦ ?_
  have hc2s : ∀ k : ℕ, c + 2 * (s : ℂ) ≠ -k := fun k h ↦
    hc (2 * s + k) (by push_cast; linear_combination h)
  have hΓm (m : ℕ) : Gamma (c + m) = (ascPochhammer ℂ m).eval c * Gamma c := by
    rw [← Gamma_add_nat_div_Gamma_eq c hc, div_mul_cancel₀ _ hΓc]
  have hΓc2s : Gamma (c + 2 * (s : ℂ)) = (ascPochhammer ℂ (2 * s)).eval c * Gamma c := by
    simpa [Nat.cast_mul] using hΓm (2 * s)
  have hp (m : ℕ) : (ascPochhammer ℂ m).eval c ≠ 0 := by
    rw [ne_eq, ascPochhammer_eval_eq_zero_iff]
    rintro ⟨k, -, hk⟩; exact hc k (by linear_combination hk)
  have hps := hp s
  have hp2s := hp (2 * s)
  have hfs : (s ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero s)
  rw [← ordinaryHypergeometric_div_Gamma_eq hc2s, hΓm s, hΓc2s]
  field_simp

end Complex
