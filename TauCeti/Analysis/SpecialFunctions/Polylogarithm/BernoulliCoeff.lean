/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import TauCeti.NumberTheory.Bernoulli.Polynomials

/-!
# Bernoulli coefficients and parity cancellations for single-valued polylogarithms

Zagier's real single-valued polylogarithms weight the classical branches `Li_{n - k}(z)` against
powers of `log ‖z‖` with the rational coefficients

`cₖ = 2^k Bₖ / k!` (`TauCeti.Polylog.bernoulliCoeff`),

using Mathlib's `bernoulli` convention `B₁ = -1 / 2` so that `c₀ = 1`, `c₁ = -1`, `c₂ = 1 / 3` and
`cₖ = 0` for odd `k ≥ 3`. Their formal generating series `∑ cₖ Xᵏ` is `B(2X)`, satisfying
`B(2X) · (e^{2X} - 1) = 2X`. Multiplying by `e^X` produces the even characteristic series
`Â(2X) = X / sinh X` (`TauCeti.aHatSeries` rescaled by `2`), whose odd coefficients
`∑_{j ≤ k} cⱼ / (k - j)! = 2^k Bₖ(1/2) / k!` vanish.

That even transform is the algebraic mechanism behind both branch independence and inversion of
single-valued polylogarithms:

* Under a counterclockwise loop around `1`, a coherent determination of `Li_{n - k}` changes by
  `-2πi L^{n - 1 - k} / (n - 1 - k)!` where `L = ℓ + iθ` has real part `ℓ = log ‖z‖`. Weighting
  against `cₖ ℓ^k` extracts `-2πi` times the degree-`(n - 1)` coefficient of `Â(2ℓX) e^{iθX}`.
  Because the ring endomorphism `H(X) ↦ conj(H(-X))` of `ℂ⟦X⟧` fixes both `Â(2ℓX)` and `e^{iθX}`,
  its coefficients are real in even degree and purely imaginary in odd degree; after multiplying by
  `-2πi`, the parity projection (`Re` for odd `n`, `Im` for even `n`) vanishes for every `L ∈ ℂ`.
* Inserting Bernoulli's inversion identity
  `Liₘ(z) + (-1)^m Liₘ(z⁻¹) = -(2πi)^m Bₘ(1/2 + L/(2πi)) / m!` into the `cₖ`-weighted sum extracts
  the degree-`n` coefficient of `-Â(2ℓX) Â(2πi X) e^{iθX}` up to the boundary term `-cₙ ℓ^n`. Since
  `Â(2πi X)` is also fixed by `H(X) ↦ conj(H(-X))`, and for `n ≥ 2` the boundary term either
  vanishes (odd `n ≥ 3`) or is real (even `n`), the parity projection of the inversion defect
  vanishes as well.

Explicit weight-one and weight-two evaluations show that neither the unprojected complex monodromy
sum nor the sign choice `B₁ = +1 / 2` (`bernoulli'`), nor the `n = 1` case of inversion, enjoys
this cancellation.

## Main definitions

* `TauCeti.Polylog.bernoulliCoeff`: the rational sequence `cₖ = 2^k Bₖ / k!`.

## Main results

* `TauCeti.Polylog.mk_bernoulliCoeff_mul_rescale_two_exp_sub_one`:
  `(∑ cₖ Xᵏ) · (e^{2X} - 1) = 2X` in `ℚ⟦X⟧`.
* `TauCeti.Polylog.mk_bernoulliCoeff_mul_exp_eq_rescale_two_aHatSeries`,
  `TauCeti.Polylog.mk_bernoulliCoeff_mul_exp_mul_sub`,
  `TauCeti.Polylog.rescale_neg_one_mk_bernoulliCoeff_mul_exp`:
  `(∑ cₖ Xᵏ) · e^X = Â(2X)` is even and satisfies `((∑ cₖ Xᵏ) · e^X) · (e^X - e^{-X}) = 2X`.
* `TauCeti.Polylog.sum_bernoulliCoeff_div_factorial`,
  `TauCeti.Polylog.sum_bernoulliCoeff_div_factorial_eq_zero_of_odd`:
  `∑_{j ≤ k} cⱼ / (k - j)! = (2 - 2^k) Bₖ / k!`, which vanishes for odd `k`.
* `TauCeti.Polylog.re_sum_bernoulliCoeff_mul_pow_div_factorial_eq_zero`,
  `TauCeti.Polylog.im_sum_bernoulliCoeff_mul_pow_div_factorial_eq_zero`,
  `TauCeti.Polylog.ite_odd_re_im_sum_bernoulliCoeff_mul_pow_div_factorial_eq_zero`:
  parity vanishing of the peripheral monodromy defect for every `n` and `L ∈ ℂ`.
* `TauCeti.Polylog.re_sum_bernoulliCoeff_mul_aeval_bernoulli_eq_zero`,
  `TauCeti.Polylog.im_sum_bernoulliCoeff_mul_aeval_bernoulli_eq_zero`,
  `TauCeti.Polylog.ite_odd_re_im_sum_bernoulliCoeff_mul_aeval_bernoulli_eq_zero`:
  parity vanishing of the Bernoulli-inversion defect for `2 ≤ n` and every `L ∈ ℂ`.

## References

* Don Zagier, *Polylogarithms, Dedekind zeta functions and the algebraic K-theory of fields*,
  in *Arithmetic Algebraic Geometry* (Texel, 1989), Progress in Mathematics 89,
  Birkhäuser (1991), pp. 391–430, §7, (33)–(35), pp. 413–414.
* Joseph Oesterlé, *Polylogarithmes*, Séminaire Bourbaki, exposé 762, Astérisque 216 (1993),
  §3.1–3.2, (18)–(22), pp. 57–58.
-/

public section

open Nat Finset PowerSeries

namespace TauCeti.Polylog

/-! ### Definition and values of the Bernoulli coefficients -/

/-- The rational coefficients `cₖ = 2^k Bₖ / k!` of Zagier's single-valued polylogarithms, defined
with Mathlib's `bernoulli` (`B₁ = -1 / 2`). -/
def bernoulliCoeff (k : ℕ) : ℚ :=
  2 ^ k * bernoulli k / k.factorial

/-- Defining formula for `bernoulliCoeff`. -/
theorem bernoulliCoeff_def (k : ℕ) :
    bernoulliCoeff k = 2 ^ k * bernoulli k / k.factorial :=
  (rfl)

/-- `c₀ = 1`. -/
@[simp]
theorem bernoulliCoeff_zero : bernoulliCoeff 0 = 1 := by
  simp [bernoulliCoeff_def]

/-- `c₁ = -1`, reflecting the sign convention `B₁ = -1 / 2`. -/
@[simp]
theorem bernoulliCoeff_one : bernoulliCoeff 1 = -1 := by
  rw [bernoulliCoeff_def, bernoulli_one]
  norm_num

/-- `c₂ = 1 / 3`. -/
@[simp]
theorem bernoulliCoeff_two : bernoulliCoeff 2 = 1 / 3 := by
  rw [bernoulliCoeff_def, bernoulli_two]
  norm_num [Nat.factorial]

/-- `c₃ = 0`. -/
@[simp]
theorem bernoulliCoeff_three : bernoulliCoeff 3 = 0 := by
  rw [bernoulliCoeff_def, bernoulli_eq_zero_of_odd (by decide) (by decide)]
  simp

/-- `c₄ = -1 / 45`. -/
@[simp]
theorem bernoulliCoeff_four : bernoulliCoeff 4 = -1 / 45 := by
  rw [bernoulliCoeff_def, bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_four]
  norm_num [Nat.factorial]

/-- Odd Bernoulli coefficients of index greater than `1` vanish. -/
@[simp]
theorem bernoulliCoeff_eq_zero_of_odd {k : ℕ} (hk : Odd k) (hlt : 1 < k) :
    bernoulliCoeff k = 0 := by
  rw [bernoulliCoeff_def, bernoulli_eq_zero_of_odd hk hlt]
  simp

/-! ### Generating power series and the even transform -/

section GeneratingSeries

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- Rescaling Mathlib's `bernoulliPowerSeries` by `2` gives the series with coefficients
`bernoulliCoeff k`. -/
theorem coeff_rescale_two_bernoulliPowerSeries (k : ℕ) :
    PowerSeries.coeff k (PowerSeries.rescale 2 (bernoulliPowerSeries A)) =
      algebraMap ℚ A (bernoulliCoeff k) := by
  simp [bernoulliPowerSeries, bernoulliCoeff_def, coeff_rescale, mul_div_assoc, map_ofNat]

/-- Over any `ℚ`-algebra `A`, the formal power series of `bernoulliCoeff` is
`rescale 2 (bernoulliPowerSeries A)`. -/
theorem mk_algebraMap_bernoulliCoeff_eq_rescale_two_bernoulliPowerSeries :
    (PowerSeries.mk fun k => algebraMap ℚ A (bernoulliCoeff k)) =
      PowerSeries.rescale 2 (bernoulliPowerSeries A) := by
  ext k
  rw [coeff_mk, coeff_rescale_two_bernoulliPowerSeries]

/-- Away from degree `1`, `bernoulliCoeff k` agrees with the `k`-th coefficient of Hirzebruch's
`L` series `X / tanh X`. -/
theorem coeff_hirzebruchLSeries_eq_bernoulliCoeff {k : ℕ} (hk : k ≠ 1) :
    PowerSeries.coeff k (TauCeti.hirzebruchLSeries A) = algebraMap ℚ A (bernoulliCoeff k) := by
  rw [TauCeti.coeff_hirzebruchLSeries A hk, bernoulliCoeff_def]

/-- Over any `ℚ`-algebra `A`, `(∑ cₖ Xᵏ) · (e^{2X} - 1) = 2X`. -/
theorem mk_algebraMap_bernoulliCoeff_mul_rescale_two_exp_sub_one :
    (PowerSeries.mk fun k => algebraMap ℚ A (bernoulliCoeff k)) *
      (PowerSeries.rescale 2 (PowerSeries.exp A) - 1) = 2 * PowerSeries.X := by
  rw [mk_algebraMap_bernoulliCoeff_eq_rescale_two_bernoulliPowerSeries]
  simpa [rescale_X, map_ofNat] using
    congrArg (PowerSeries.rescale (2 : A)) (bernoulliPowerSeries_mul_exp_sub_one A)

/-- Multiplying the `bernoulliCoeff` generating series by `e^X` produces the rescaled Â series
`Â(2X) = X / sinh X`. -/
theorem mk_algebraMap_bernoulliCoeff_mul_exp_eq_rescale_two_aHatSeries :
    (PowerSeries.mk fun k => algebraMap ℚ A (bernoulliCoeff k)) * PowerSeries.exp A =
      PowerSeries.rescale 2 (TauCeti.aHatSeries A) := by
  rw [mk_algebraMap_bernoulliCoeff_eq_rescale_two_bernoulliPowerSeries,
    TauCeti.rescale_two_bernoulliPowerSeries_mul_exp]

end GeneratingSeries

/-- The formal power series `∑ cₖ Xᵏ` in `ℚ⟦X⟧` is `B(2X)`. -/
theorem mk_bernoulliCoeff_eq_rescale_two_bernoulliPowerSeries :
    PowerSeries.mk bernoulliCoeff = PowerSeries.rescale 2 (bernoulliPowerSeries ℚ) := by
  simpa using mk_algebraMap_bernoulliCoeff_eq_rescale_two_bernoulliPowerSeries ℚ

/-- **Generating identity of `bernoulliCoeff`**: `(∑ cₖ Xᵏ) · (e^{2X} - 1) = 2X` in `ℚ⟦X⟧`. -/
theorem mk_bernoulliCoeff_mul_rescale_two_exp_sub_one :
    PowerSeries.mk bernoulliCoeff * (PowerSeries.rescale 2 (PowerSeries.exp ℚ) - 1) =
      2 * PowerSeries.X := by
  simpa using mk_algebraMap_bernoulliCoeff_mul_rescale_two_exp_sub_one ℚ

/-- In `ℚ⟦X⟧`, `(∑ cₖ Xᵏ) · e^X` equals the rescaled Â series `Â(2X)`. -/
theorem mk_bernoulliCoeff_mul_exp_eq_rescale_two_aHatSeries :
    PowerSeries.mk bernoulliCoeff * PowerSeries.exp ℚ =
      PowerSeries.rescale 2 (TauCeti.aHatSeries ℚ) := by
  simpa using mk_algebraMap_bernoulliCoeff_mul_exp_eq_rescale_two_aHatSeries ℚ

/-- **Hyperbolic-sine quotient identity**: `((∑ cₖ Xᵏ) · e^X) · (e^X - e^{-X}) = 2X` in `ℚ⟦X⟧`,
expressing `(∑ cₖ Xᵏ) · e^X = X / sinh X` without dividing by `X`. -/
theorem mk_bernoulliCoeff_mul_exp_mul_sub :
    (PowerSeries.mk bernoulliCoeff * PowerSeries.exp ℚ) *
      (PowerSeries.exp ℚ - PowerSeries.rescale (-1) (PowerSeries.exp ℚ)) =
      2 * PowerSeries.X := by
  rw [mk_bernoulliCoeff_mul_exp_eq_rescale_two_aHatSeries]
  exact TauCeti.rescale_two_aHatSeries_mul_sub ℚ

/-- **Evenness of `(∑ cₖ Xᵏ) · e^X`**: negating `X` leaves the product invariant. -/
@[simp]
theorem rescale_neg_one_mk_bernoulliCoeff_mul_exp :
    PowerSeries.rescale (-1) (PowerSeries.mk bernoulliCoeff * PowerSeries.exp ℚ) =
      PowerSeries.mk bernoulliCoeff * PowerSeries.exp ℚ := by
  rw [mk_bernoulliCoeff_mul_exp_eq_rescale_two_aHatSeries, rescale_rescale,
    mul_comm (2 : ℚ) (-1), ← rescale_rescale,
    TauCeti.rescale_neg_one_aHatSeries]

/-- The `k`-th coefficient of `(∑ cₖ Xᵏ) · e^X` is the finite convolution
`∑_{j ≤ k} cⱼ / (k - j)!`. -/
theorem coeff_mk_bernoulliCoeff_mul_exp (k : ℕ) :
    PowerSeries.coeff k (PowerSeries.mk bernoulliCoeff * PowerSeries.exp ℚ) =
      ∑ j ∈ range (k + 1), bernoulliCoeff j / (k - j).factorial := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine sum_congr rfl fun j _ => ?_
  simp [div_eq_mul_inv]

/-- Midpoint-polynomial formula for the even transform of `bernoulliCoeff`:
`∑_{j ≤ k} cⱼ / (k - j)! = 2^k Bₖ(1/2) / k!`. -/
theorem sum_bernoulliCoeff_div_factorial_eq_eval_bernoulli (k : ℕ) :
    ∑ j ∈ range (k + 1), bernoulliCoeff j / (k - j).factorial =
      2 ^ k * (Polynomial.bernoulli k).eval 2⁻¹ / k.factorial := by
  rw [← coeff_mk_bernoulliCoeff_mul_exp, mk_bernoulliCoeff_mul_exp_eq_rescale_two_aHatSeries,
    coeff_rescale, TauCeti.coeff_aHatSeries, Algebra.algebraMap_self, RingHom.id_apply,
    TauCeti.bernoulli_eval_inv_two]
  field_simp

/-- Closed rational formula for the even transform of `bernoulliCoeff`:
`∑_{j ≤ k} cⱼ / (k - j)! = (2 - 2^k) Bₖ / k!`. -/
theorem sum_bernoulliCoeff_div_factorial (k : ℕ) :
    ∑ j ∈ range (k + 1), bernoulliCoeff j / (k - j).factorial =
      (2 - 2 ^ k) * bernoulli k / k.factorial := by
  rw [sum_bernoulliCoeff_div_factorial_eq_eval_bernoulli,
    TauCeti.two_pow_mul_bernoulli_eval_inv_two]

/-- **Odd vanishing of the even transform**: for odd `k`, `∑_{j ≤ k} cⱼ / (k - j)! = 0`. -/
theorem sum_bernoulliCoeff_div_factorial_eq_zero_of_odd {k : ℕ} (hk : Odd k) :
    ∑ j ∈ range (k + 1), bernoulliCoeff j / (k - j).factorial = 0 := by
  rw [sum_bernoulliCoeff_div_factorial_eq_eval_bernoulli,
    TauCeti.bernoulli_eval_inv_two_eq_zero_of_odd hk]
  simp

/-- At `k = 1`, `c₀ + c₁ = 0`. -/
theorem bernoulliCoeff_zero_add_bernoulliCoeff_one :
    bernoulliCoeff 0 + bernoulliCoeff 1 = 0 := by
  simp

/-- At `k = 2`, the even transform takes the nonzero value `-1 / 6`. -/
theorem sum_bernoulliCoeff_div_factorial_two :
    ∑ j ∈ range 3, bernoulliCoeff j / (2 - j).factorial = -1 / 6 := by
  rw [sum_bernoulliCoeff_div_factorial, bernoulli_two]
  norm_num [Nat.factorial]

/-- At `k = 3`, `1 / 6 - 1 / 2 + 1 / 3 + 0 = 0`. -/
theorem sum_bernoulliCoeff_div_factorial_three :
    ∑ j ∈ range 4, bernoulliCoeff j / (3 - j).factorial = 0 :=
  sum_bernoulliCoeff_div_factorial_eq_zero_of_odd (by decide)

/- Replacing `bernoulli` (`B₁ = -1 / 2`) by `bernoulli'` (`B₁ = +1 / 2`) gives `c₀' + c₁' = 2`
instead of `0`, breaking the degree-one cancellation. -/
example :
    ∑ j ∈ range 2, (2 ^ j * bernoulli' j / j.factorial) / (1 - j).factorial = 2 := by
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-! ### Zagier's parity cancellations for monodromy and Bernoulli inversion -/

/-- Auxiliary generating series `B(2 ℓ X) · e^{L X} = Â(2 ℓ X) · e^{i θ X}` in `ℂ⟦X⟧` governing
the peripheral monodromy defect around `1`, where `ℓ = L.re` and `θ = L.im`. -/
private noncomputable def monodromyGeneratingSeries (L : ℂ) : ℂ⟦X⟧ :=
  PowerSeries.rescale (L.re : ℂ) (PowerSeries.rescale 2 (bernoulliPowerSeries ℂ)) *
    PowerSeries.rescale L (PowerSeries.exp ℂ)

private theorem monodromyGeneratingSeries_eq_aHatSeries_mul_exp (L : ℂ) :
    monodromyGeneratingSeries L =
      PowerSeries.rescale ((2 * L.re : ℝ) : ℂ) (TauCeti.aHatSeries ℂ) *
        PowerSeries.rescale (Complex.I * (L.im : ℂ)) (PowerSeries.exp ℂ) := by
  have hL : L = (L.re : ℂ) + Complex.I * (L.im : ℂ) := by
    simpa [mul_comm] using (Complex.re_add_im L).symm
  calc
    monodromyGeneratingSeries L
        = PowerSeries.rescale (L.re : ℂ) (PowerSeries.rescale 2 (bernoulliPowerSeries ℂ)) *
            (PowerSeries.rescale (L.re : ℂ) (PowerSeries.exp ℂ) *
              PowerSeries.rescale (Complex.I * (L.im : ℂ)) (PowerSeries.exp ℂ)) := by
          rw [monodromyGeneratingSeries, PowerSeries.exp_mul_exp_eq_exp_add, ← hL]
    _ = (PowerSeries.rescale (L.re : ℂ)
            (PowerSeries.rescale 2 (bernoulliPowerSeries ℂ) * PowerSeries.exp ℂ)) *
          PowerSeries.rescale (Complex.I * (L.im : ℂ)) (PowerSeries.exp ℂ) := by
          rw [map_mul, mul_assoc]
    _ = PowerSeries.rescale ((2 * L.re : ℝ) : ℂ) (TauCeti.aHatSeries ℂ) *
          PowerSeries.rescale (Complex.I * (L.im : ℂ)) (PowerSeries.exp ℂ) := by
          rw [TauCeti.rescale_two_bernoulliPowerSeries_mul_exp, rescale_rescale]
          push_cast
          rfl

private theorem rescale_neg_one_map_conj_monodromyGeneratingSeries (L : ℂ) :
    PowerSeries.rescale (-1 : ℂ)
      (PowerSeries.map (starRingEnd ℂ) (monodromyGeneratingSeries L)) =
      monodromyGeneratingSeries L := by
  rw [monodromyGeneratingSeries_eq_aHatSeries_mul_exp, map_mul, map_mul]
  congr 1
  · rw [← PowerSeries.rescale_map, Complex.conj_ofReal, TauCeti.map_aHatSeries, rescale_rescale,
      mul_comm ((2 * L.re : ℝ) : ℂ) (-1),
      ← rescale_rescale, TauCeti.rescale_neg_one_aHatSeries]
  · rw [← PowerSeries.rescale_map, map_mul, Complex.conj_I, Complex.conj_ofReal,
      PowerSeries.map_exp, rescale_rescale]
    congr 2
    ring

private theorem two_pi_I_mul_coeff_monodromyGeneratingSeries (L : ℂ) (m : ℕ) :
    2 * Real.pi * Complex.I * PowerSeries.coeff m (monodromyGeneratingSeries L) =
      ∑ k ∈ range (m + 1), (bernoulliCoeff k : ℂ) *
        (2 * Real.pi * Complex.I * L ^ (m - k) / ((m - k).factorial : ℂ)) *
        (L.re : ℂ) ^ k := by
  rw [monodromyGeneratingSeries, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [coeff_rescale, coeff_rescale_two_bernoulliPowerSeries, coeff_rescale, coeff_exp]
  simp only [eq_ratCast, one_div, map_inv₀, map_natCast]
  ring

/-- **Odd-weight monodromy cancellation**: for odd `n` and every complex logarithm determination
`L`, the negated peripheral `T₁`-monodromy sum around `1` (omitting the leading `-` sign of the
counterclockwise jump) of Zagier's `bernoulliCoeff`-weighted sum is purely imaginary, so its real
part vanishes. -/
theorem re_sum_bernoulliCoeff_mul_pow_div_factorial_eq_zero {n : ℕ} (hn : Odd n) (L : ℂ) :
    (∑ k ∈ range n, (bernoulliCoeff k : ℂ) *
      (2 * Real.pi * Complex.I * L ^ (n - 1 - k) / ((n - 1 - k).factorial : ℂ)) *
      (L.re : ℂ) ^ k).re = 0 := by
  obtain ⟨r, rfl⟩ := hn
  have hsum :
      ∑ k ∈ range (2 * r + 1), (bernoulliCoeff k : ℂ) *
        (2 * Real.pi * Complex.I * L ^ (2 * r + 1 - 1 - k) /
          ((2 * r + 1 - 1 - k).factorial : ℂ)) * (L.re : ℂ) ^ k =
      2 * Real.pi * Complex.I * PowerSeries.coeff (2 * r) (monodromyGeneratingSeries L) := by
    simpa using (two_pi_I_mul_coeff_monodromyGeneratingSeries L (2 * r)).symm
  have hconj :=
    congrArg (PowerSeries.coeff (2 * r)) (rescale_neg_one_map_conj_monodromyGeneratingSeries L)
  simp only [coeff_rescale, coeff_map, Even.neg_one_pow (even_two_mul r), one_mul] at hconj
  have him : (PowerSeries.coeff (2 * r) (monodromyGeneratingSeries L)).im = 0 :=
    Complex.conj_eq_iff_im.mp hconj
  rw [hsum]
  set z := PowerSeries.coeff (2 * r) (monodromyGeneratingSeries L)
  have hz : z = (z.re : ℂ) := by
    apply Complex.ext <;> simp [him]
  rw [hz]
  simp

/-- **Even-weight monodromy cancellation**: for even `n` and every complex logarithm determination
`L`, the negated peripheral `T₁`-monodromy sum around `1` (omitting the leading `-` sign of the
counterclockwise jump) of Zagier's `bernoulliCoeff`-weighted sum is real, so its imaginary part
vanishes. -/
theorem im_sum_bernoulliCoeff_mul_pow_div_factorial_eq_zero {n : ℕ} (hn : Even n) (L : ℂ) :
    (∑ k ∈ range n, (bernoulliCoeff k : ℂ) *
      (2 * Real.pi * Complex.I * L ^ (n - 1 - k) / ((n - 1 - k).factorial : ℂ)) *
      (L.re : ℂ) ^ k).im = 0 := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  obtain ⟨r, rfl⟩ := hn
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
  have h2 : m + 1 + (m + 1) = (2 * m + 1) + 1 := by ring
  rw [h2]
  have hsum :
      ∑ k ∈ range (2 * m + 1 + 1), (bernoulliCoeff k : ℂ) *
        (2 * Real.pi * Complex.I * L ^ (2 * m + 1 + 1 - 1 - k) /
          ((2 * m + 1 + 1 - 1 - k).factorial : ℂ)) * (L.re : ℂ) ^ k =
      2 * Real.pi * Complex.I *
        PowerSeries.coeff (2 * m + 1) (monodromyGeneratingSeries L) := by
    simpa using (two_pi_I_mul_coeff_monodromyGeneratingSeries L (2 * m + 1)).symm
  have hconj := congrArg (PowerSeries.coeff (2 * m + 1))
    (rescale_neg_one_map_conj_monodromyGeneratingSeries L)
  have hodd : Odd (2 * m + 1) := ⟨m, rfl⟩
  simp only [coeff_rescale, coeff_map, hodd.neg_one_pow, neg_one_mul] at hconj
  have hre : (PowerSeries.coeff (2 * m + 1) (monodromyGeneratingSeries L)).re = 0 := by
    have hre' := congrArg Complex.re hconj
    simp only [Complex.neg_re, Complex.conj_re] at hre'
    linarith
  rw [hsum]
  set z := PowerSeries.coeff (2 * m + 1) (monodromyGeneratingSeries L)
  have hz : z = (z.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hre]
  rw [hz]
  have hreal : 2 * (Real.pi : ℂ) * Complex.I * ((z.im : ℂ) * Complex.I) =
      ((-2 * Real.pi * z.im : ℝ) : ℂ) := by
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hreal, Complex.ofReal_im]

/-- **Parity-projected monodromy cancellation**: in every weight `n`, the parity projection (`Re`
for odd `n`, `Im` for even `n`) of the negated peripheral `T₁`-monodromy sum around `1` (omitting
the leading `-` sign of the counterclockwise jump) vanishes. -/
theorem ite_odd_re_im_sum_bernoulliCoeff_mul_pow_div_factorial_eq_zero (n : ℕ) (L : ℂ) :
    (let w : ℂ := ∑ k ∈ range n, (bernoulliCoeff k : ℂ) *
        (2 * Real.pi * Complex.I * L ^ (n - 1 - k) / ((n - 1 - k).factorial : ℂ)) *
        (L.re : ℂ) ^ k
      if Odd n then w.re else w.im) = 0 := by
  dsimp only
  split_ifs with hn
  · exact re_sum_bernoulliCoeff_mul_pow_div_factorial_eq_zero hn L
  · exact im_sum_bernoulliCoeff_mul_pow_div_factorial_eq_zero (Nat.not_odd_iff_even.mp hn) L

/-- In weight two, the unprojected complex `T₁`-monodromy defect equals `2π Im L`, which is real
(so its imaginary part vanishes) yet nonzero whenever `Im L ≠ 0`. -/
theorem sum_bernoulliCoeff_mul_neg_two_pi_I_pow_div_factorial_two (L : ℂ) :
    (∑ k ∈ range 2, (bernoulliCoeff k : ℂ) *
      (-2 * Real.pi * Complex.I * L ^ (1 - k) / ((1 - k).factorial : ℂ)) *
      (L.re : ℂ) ^ k) = ((2 * Real.pi * L.im : ℝ) : ℂ) := by
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  simp only [bernoulliCoeff_zero, bernoulliCoeff_one, Nat.sub_zero, Nat.sub_self, pow_one,
    pow_zero, Nat.factorial_one, Nat.factorial_zero, Nat.cast_one, div_one, Rat.cast_one,
    Rat.cast_neg, mul_one, one_mul]
  nth_rw 1 [← Complex.re_add_im L]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/- Replacing `bernoulliCoeff 1 = -1` by `+1` (the `bernoulli'` convention `B₁ = +1 / 2`) leaves
imaginary part `-4π Re L` in weight two instead of `0`. -/
example (L : ℂ) :
    (∑ k ∈ range 2, ((2 ^ k * bernoulli' k / k.factorial : ℚ) : ℂ) *
      (-2 * Real.pi * Complex.I * L ^ (1 - k) / ((1 - k).factorial : ℂ)) *
      (L.re : ℂ) ^ k).im = -4 * Real.pi * L.re := by
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  norm_num [Nat.factorial]
  nth_rw 1 [← Complex.re_add_im L]
  simp
  ring

/-- Auxiliary generating series `Â(2πi X) · (B(2ℓX) · e^{LX}) = Â(2πi X) · Â(2ℓX) · e^{iθX}` in
`ℂ⟦X⟧` governing the Bernoulli-inversion defect in single-valued polylogarithms. -/
private noncomputable def inversionGeneratingSeries (L : ℂ) : ℂ⟦X⟧ :=
  PowerSeries.rescale (2 * Real.pi * Complex.I) (TauCeti.aHatSeries ℂ) *
    monodromyGeneratingSeries L

private theorem rescale_neg_one_map_conj_inversionGeneratingSeries (L : ℂ) :
    PowerSeries.rescale (-1 : ℂ)
      (PowerSeries.map (starRingEnd ℂ) (inversionGeneratingSeries L)) =
      inversionGeneratingSeries L := by
  rw [inversionGeneratingSeries, map_mul, map_mul,
    rescale_neg_one_map_conj_monodromyGeneratingSeries]
  congr 1
  rw [← PowerSeries.rescale_map, map_mul, map_mul, Complex.conj_ofNat, Complex.conj_ofReal,
    Complex.conj_I, TauCeti.map_aHatSeries, rescale_rescale]
  congr 2
  ring

private theorem neg_coeff_inversionGeneratingSeries (L : ℂ) (n : ℕ) :
    -PowerSeries.coeff n (inversionGeneratingSeries L) =
      ∑ k ∈ range (n + 1), (bernoulliCoeff k : ℂ) *
        (-(2 * Real.pi * Complex.I) ^ (n - k) / ((n - k).factorial : ℂ) *
          Polynomial.aeval ((1 / 2 : ℂ) + L / (2 * Real.pi * Complex.I))
            (Polynomial.bernoulli (n - k))) *
        (L.re : ℂ) ^ k := by
  set α : ℂ := 2 * Real.pi * Complex.I
  have hα : α ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  have hB :
      PowerSeries.rescale α (TauCeti.aHatSeries ℂ) *
        PowerSeries.rescale L (PowerSeries.exp ℂ) =
      PowerSeries.rescale α
        (PowerSeries.mk fun m =>
          Polynomial.aeval (algebraMap ℚ ℂ 2⁻¹ + L / α)
            ((1 / m ! : ℚ) • Polynomial.bernoulli m)) := by
    rw [TauCeti.mk_aeval_inv_two_add_bernoulli_eq_aHatSeries_mul_rescale_exp, map_mul,
      rescale_rescale, div_mul_cancel₀ L hα]
  have hseries :
      inversionGeneratingSeries L =
        PowerSeries.rescale (L.re : ℂ) (PowerSeries.rescale 2 (bernoulliPowerSeries ℂ)) *
          PowerSeries.rescale α
            (PowerSeries.mk fun m =>
              Polynomial.aeval (algebraMap ℚ ℂ 2⁻¹ + L / α)
                ((1 / m ! : ℚ) • Polynomial.bernoulli m)) := by
    calc
      inversionGeneratingSeries L
          = PowerSeries.rescale (L.re : ℂ) (PowerSeries.rescale 2 (bernoulliPowerSeries ℂ)) *
              (PowerSeries.rescale α (TauCeti.aHatSeries ℂ) *
                PowerSeries.rescale L (PowerSeries.exp ℂ)) := by
            rw [inversionGeneratingSeries, monodromyGeneratingSeries]
            ring
      _ = _ := by rw [hB]
  rw [hseries, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    ← Finset.sum_neg_distrib]
  refine sum_congr rfl fun k _ => ?_
  dsimp only
  rw [coeff_rescale, coeff_rescale_two_bernoulliPowerSeries, coeff_rescale, coeff_mk]
  have hhalf : algebraMap ℚ ℂ 2⁻¹ = (1 / 2 : ℂ) := by
    norm_num
  rw [hhalf, map_smul, Algebra.smul_def]
  simp only [eq_ratCast, one_div, map_inv₀, map_natCast]
  ring

/-- **Odd-weight Bernoulli-inversion cancellation**: for odd `n > 1` and every `L ∈ ℂ`, the
`bernoulliCoeff`-weighted Bernoulli-inversion sum is purely imaginary, so its real part vanishes. -/
theorem re_sum_bernoulliCoeff_mul_aeval_bernoulli_eq_zero {n : ℕ} (hn : Odd n) (hlt : 1 < n)
    (L : ℂ) :
    (∑ k ∈ range n, (bernoulliCoeff k : ℂ) *
      (-(2 * Real.pi * Complex.I) ^ (n - k) / ((n - k).factorial : ℂ) *
        Polynomial.aeval ((1 / 2 : ℂ) + L / (2 * Real.pi * Complex.I))
          (Polynomial.bernoulli (n - k))) *
      (L.re : ℂ) ^ k).re = 0 := by
  have hfull := neg_coeff_inversionGeneratingSeries L n
  rw [Finset.sum_range_succ, bernoulliCoeff_eq_zero_of_odd hn hlt, Rat.cast_zero, zero_mul,
    zero_mul, add_zero] at hfull
  rw [← hfull, Complex.neg_re, neg_eq_zero]
  have hconj :=
    congrArg (PowerSeries.coeff n) (rescale_neg_one_map_conj_inversionGeneratingSeries L)
  simp only [coeff_rescale, coeff_map, hn.neg_one_pow, neg_one_mul] at hconj
  have hre := congrArg Complex.re hconj
  simp only [Complex.neg_re, Complex.conj_re] at hre
  linarith

/-- **Even-weight Bernoulli-inversion cancellation**: for even `n` and every `L ∈ ℂ`, the
`bernoulliCoeff`-weighted Bernoulli-inversion sum is real, so its imaginary part vanishes. -/
theorem im_sum_bernoulliCoeff_mul_aeval_bernoulli_eq_zero {n : ℕ} (hn : Even n) (L : ℂ) :
    (∑ k ∈ range n, (bernoulliCoeff k : ℂ) *
      (-(2 * Real.pi * Complex.I) ^ (n - k) / ((n - k).factorial : ℂ) *
        Polynomial.aeval ((1 / 2 : ℂ) + L / (2 * Real.pi * Complex.I))
          (Polynomial.bernoulli (n - k))) *
      (L.re : ℂ) ^ k).im = 0 := by
  have hfull := neg_coeff_inversionGeneratingSeries L n
  rw [Finset.sum_range_succ, tsub_self, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
    Polynomial.bernoulli_zero, map_one, mul_one] at hfull
  have hconj :=
    congrArg (PowerSeries.coeff n) (rescale_neg_one_map_conj_inversionGeneratingSeries L)
  simp only [coeff_rescale, coeff_map, hn.neg_one_pow, one_mul] at hconj
  have him : (PowerSeries.coeff n (inversionGeneratingSeries L)).im = 0 :=
    Complex.conj_eq_iff_im.mp hconj
  have hterm : ((bernoulliCoeff n : ℂ) * -1 * (L.re : ℂ) ^ n).im = 0 := by
    have hcast : (bernoulliCoeff n : ℂ) * -1 * (L.re : ℂ) ^ n =
        ((-(bernoulliCoeff n : ℝ) * L.re ^ n : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hcast, Complex.ofReal_im]
  have him_neg : (-PowerSeries.coeff n (inversionGeneratingSeries L)).im = 0 := by
    simp [him]
  rw [hfull, Complex.add_im, hterm, add_zero] at him_neg
  exact him_neg

/-- **Parity-projected Bernoulli-inversion cancellation**: for every weight `n ≥ 2` and every
`L ∈ ℂ`, the parity projection (`Re` for odd `n`, `Im` for even `n`) of the Bernoulli-inversion
defect vanishes. -/
theorem ite_odd_re_im_sum_bernoulliCoeff_mul_aeval_bernoulli_eq_zero {n : ℕ} (hn : 2 ≤ n)
    (L : ℂ) :
    (let v : ℂ := ∑ k ∈ range n, (bernoulliCoeff k : ℂ) *
        (-(2 * Real.pi * Complex.I) ^ (n - k) / ((n - k).factorial : ℂ) *
          Polynomial.aeval ((1 / 2 : ℂ) + L / (2 * Real.pi * Complex.I))
            (Polynomial.bernoulli (n - k))) *
        (L.re : ℂ) ^ k
      if Odd n then v.re else v.im) = 0 := by
  dsimp only
  split_ifs with hodd
  · exact re_sum_bernoulliCoeff_mul_aeval_bernoulli_eq_zero hodd (by omega) L
  · exact im_sum_bernoulliCoeff_mul_aeval_bernoulli_eq_zero (Nat.not_odd_iff_even.mp hodd) L

/-- In weight `n = 1`, the Bernoulli-inversion defect sum equals `-L`, whose real part `-Re L` does
not vanish when `Re L ≠ 0`; the hypothesis `2 ≤ n` (or `1 < n` in odd weight) is therefore sharp. -/
theorem sum_bernoulliCoeff_mul_aeval_bernoulli_one (L : ℂ) :
    (∑ k ∈ range 1, (bernoulliCoeff k : ℂ) *
      (-(2 * Real.pi * Complex.I) ^ (1 - k) / ((1 - k).factorial : ℂ) *
        Polynomial.aeval ((1 / 2 : ℂ) + L / (2 * Real.pi * Complex.I))
          (Polynomial.bernoulli (1 - k))) *
      (L.re : ℂ) ^ k) = -L := by
  have hα : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  rw [Finset.sum_range_one]
  simp only [Nat.sub_zero, bernoulliCoeff_zero, Rat.cast_one, one_mul, pow_zero, mul_one,
    pow_one, Nat.factorial_one, Nat.cast_one, div_one, Polynomial.bernoulli_one, map_sub,
    Polynomial.aeval_X, Polynomial.aeval_C]
  have hhalf : algebraMap ℚ ℂ 2⁻¹ = (1 / 2 : ℂ) := by norm_num
  rw [hhalf]
  field_simp [hα]
  ring

end TauCeti.Polylog
