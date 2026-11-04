/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Bernoulli
public import TauCeti.Algebra.Algebra.NatCast
public import TauCeti.RingTheory.PowerSeries.Exp

/-!
# The characteristic power series of the Todd, Â and L genera

Over a `ℚ`-algebra `A`, the three classical multiplicative characteristic classes are built from
their characteristic power series

* `Td(X) = X / (1 - e^{-X})`, for the Todd class of a complex vector bundle;
* `Â(X) = (X / 2) / sinh (X / 2)`, for the Â class of an oriented real vector bundle;
* `L(X) = X / tanh X`, for Hirzebruch's L class of an oriented real vector bundle.

Each denominator is `X` times a unit of `A⟦X⟧`, so each quotient is a well-defined power series
with constant coefficient `1`. This file constructs the series and proves the displayed quotients
in the only form that makes sense in `A⟦X⟧`: multiplying the series by its denominator gives its
numerator. Conversely these identities characterize the series, since `X` is a non-zero-divisor.

The Todd series is Mathlib's exponential generating function `bernoulli'PowerSeries A` of the
Bernoulli numbers `bernoulli' n` (with `bernoulli' 1 = 1 / 2`), whose defining identity is
`bernoulli'PowerSeries_mul_exp_sub_one`. The Â and L series are defined here by rescaling
Mathlib's `bernoulliPowerSeries A`, the generating function `X / (e^X - 1)` of the Bernoulli
numbers `bernoulli n`. With `2 sinh (X / 2) = e^{X/2} - e^{-X/2}` and
`tanh X = (e^X - e^{-X}) / (e^X + e^{-X})`, the identities

`X / (e^{X/2} - e^{-X/2}) = 2 · (X/2) / (e^{X/2} - 1) - X / (e^X - 1)`,
`X (e^X + e^{-X}) / (e^X - e^{-X}) = 2X / (e^{2X} - 1) + X`

express them through Bernoulli numbers:
`Â(X) = ∑ (2 / 2ⁿ - 1) Bₙ Xⁿ / n!` and `L(X) = ∑_{n ≠ 1} 2ⁿ Bₙ Xⁿ / n!`.
Both series are even, and `Td(X) = e^{X/2} Â(X)`.

The low-order coefficients are computed explicitly: the Todd series is
`1 + X/2 + X²/12 + 0·X³ - X⁴/720 + …`, the Â series is `1 - X²/24 + 7X⁴/5760 + …` and the L
series is `1 + X²/3 - X⁴/45 + …`. The Todd series is applied to the Chern roots. The even series
Â and L are applied to one degree-two root `xⱼ` for each oriented real 2-plane, and the products
are expressed in the elementary symmetric polynomials `pᵢ` of the `xⱼ²`. These are the
coefficients behind the classical expansions `Td = 1 + c₁/2 + (c₁² + c₂)/12 + …`,
`Â = 1 - p₁/24 + …` and `L = 1 + p₁/3 + …`.

## Main definitions

* `TauCeti.aHatSeries A`: the series `(X / 2) / sinh (X / 2)`.
* `TauCeti.hirzebruchLSeries A`: the series `X / tanh X`.

## Main results

* `TauCeti.bernoulli'PowerSeries_mul_one_sub_exp_neg`: `Td(X) · (1 - e^{-X}) = X`.
* `TauCeti.aHatSeries_mul_sub`: `Â(X) · (e^{X/2} - e^{-X/2}) = X`.
* `TauCeti.hirzebruchLSeries_mul_sub`: `L(X) · (e^X - e^{-X}) = X (e^X + e^{-X})`.
* `TauCeti.eq_aHatSeries_iff`, `TauCeti.eq_hirzebruchLSeries_iff`,
  `TauCeti.eq_bernoulli'PowerSeries_iff`: these identities characterize the series.
* `TauCeti.coeff_aHatSeries`, `TauCeti.coeff_hirzebruchLSeries`: the coefficients in terms
  of Bernoulli numbers.
* `TauCeti.rescale_neg_one_aHatSeries`, `TauCeti.rescale_neg_one_hirzebruchLSeries`: the Â
  and L series are even.
* `TauCeti.bernoulli'PowerSeries_eq_rescale_exp_mul_aHatSeries`: `Td(X) = e^{X/2} Â(X)`.

## References

* F. Hirzebruch, *Topological Methods in Algebraic Geometry*, Springer (1966), §1.
* F. Hirzebruch, T. Berger, R. Jung, *Manifolds and Modular Forms*, Aspects of Mathematics E20,
  Vieweg (1992), Chapter 1.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §19 and Appendix B.
-/

public section

open Nat PowerSeries

namespace TauCeti

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-! ### The Todd series -/

/-- The coefficients of the Todd series `bernoulli'PowerSeries A` are the Bernoulli numbers
`bernoulli' n` divided by `n!`. -/
theorem coeff_bernoulli'PowerSeries (n : ℕ) :
    coeff n (bernoulli'PowerSeries A) = algebraMap ℚ A (bernoulli' n / n !) :=
  coeff_mk _ _

/-- The Todd series has constant coefficient `1`. -/
@[simp]
theorem constantCoeff_bernoulli'PowerSeries : constantCoeff (bernoulli'PowerSeries A) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_bernoulli'PowerSeries]
  simp

/-- **The Todd series** `Td(X) = X / (1 - e^{-X})` is Mathlib's generating function
`bernoulli'PowerSeries A` of the Bernoulli numbers `bernoulli' n`: its product with
`1 - e^{-X}` is `X`. -/
theorem bernoulli'PowerSeries_mul_one_sub_exp_neg :
    bernoulli'PowerSeries A * (1 - rescale (-1) (exp A)) = X := by
  have hTd := bernoulli'PowerSeries_mul_exp_sub_one A
  have hexp := rescale_exp_mul_rescale_neg_exp (1 : A)
  rw [rescale_one, RingHom.id_apply] at hexp
  linear_combination rescale (-1) (exp A) * hTd - (bernoulli'PowerSeries A - X) * hexp

/-- The identity `Td(X) · (1 - e^{-X}) = X` characterizes the Todd series. -/
theorem eq_bernoulli'PowerSeries_iff {f : A⟦X⟧} :
    f = bernoulli'PowerSeries A ↔ f * (1 - rescale (-1) (exp A)) = X :=
  ⟨fun h ↦ h ▸ bernoulli'PowerSeries_mul_one_sub_exp_neg A,
    fun h ↦ mul_X_cancel <| by
      linear_combination bernoulli'PowerSeries A * h -
        f * bernoulli'PowerSeries_mul_one_sub_exp_neg A⟩

/-- `Td(X) = 1 + X/2 + …`. -/
@[simp]
theorem coeff_one_bernoulli'PowerSeries :
    coeff 1 (bernoulli'PowerSeries A) = algebraMap ℚ A (1 / 2) := by
  simp [coeff_bernoulli'PowerSeries, bernoulli'_one]

/-- `Td(X) = 1 + X/2 + X²/12 + …`. -/
@[simp]
theorem coeff_two_bernoulli'PowerSeries :
    coeff 2 (bernoulli'PowerSeries A) = algebraMap ℚ A (1 / 12) := by
  rw [coeff_bernoulli'PowerSeries, bernoulli'_two]
  norm_num [Nat.factorial]

/-- The cubic coefficient of the Todd series vanishes. -/
@[simp]
theorem coeff_three_bernoulli'PowerSeries : coeff 3 (bernoulli'PowerSeries A) = 0 := by
  simp [coeff_bernoulli'PowerSeries, bernoulli'_three]

/-- `Td(X) = 1 + X/2 + X²/12 - X⁴/720 + …`. -/
@[simp]
theorem coeff_four_bernoulli'PowerSeries :
    coeff 4 (bernoulli'PowerSeries A) = algebraMap ℚ A (-1 / 720) := by
  rw [coeff_bernoulli'PowerSeries, bernoulli'_four]
  norm_num [Nat.factorial]

/-! ### The Â series -/

/-- **The Â series** `(X / 2) / sinh (X / 2) = X / (e^{X/2} - e^{-X/2})`, the characteristic
power series of the Â class of an oriented real vector bundle. It is defined as
`2 B(X / 2) - B(X)`, where `B(X) = X / (e^X - 1)` is `bernoulliPowerSeries A`;
`TauCeti.aHatSeries_mul_sub` proves that it is the displayed quotient. -/
noncomputable def aHatSeries : A⟦X⟧ :=
  2 * rescale (algebraMap ℚ A 2⁻¹) (bernoulliPowerSeries A) - bernoulliPowerSeries A

/-- The coefficients of the Â series: `Â(X) = ∑ (2 / 2ⁿ - 1) Bₙ Xⁿ / n!`. -/
theorem coeff_aHatSeries (n : ℕ) :
    coeff n (aHatSeries A) = algebraMap ℚ A ((2 / 2 ^ n - 1) * bernoulli n / n !) := by
  rw [aHatSeries, map_sub, ← map_ofNat C 2, coeff_C_mul, coeff_rescale]
  simp only [bernoulliPowerSeries, coeff_mk]
  rw [← map_ofNat (algebraMap ℚ A) 2, ← map_pow, ← map_mul, ← map_mul, ← map_sub]
  congr 1
  rw [inv_pow]
  field_simp

/-- The Â series has constant coefficient `1`. -/
@[simp]
theorem constantCoeff_aHatSeries : constantCoeff (aHatSeries A) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_aHatSeries]
  norm_num

/-- **The Â series is `(X / 2) / sinh (X / 2)`**: its product with
`2 sinh (X / 2) = e^{X/2} - e^{-X/2}` is `X`. -/
theorem aHatSeries_mul_sub :
    aHatSeries A * (rescale (algebraMap ℚ A 2⁻¹) (exp A) -
      rescale (-algebraMap ℚ A 2⁻¹) (exp A)) = X := by
  set c := algebraMap ℚ A 2⁻¹
  set h := rescale c (exp A)
  set k := rescale (-c) (exp A)
  set B := bernoulliPowerSeries A
  set B₂ := rescale c B
  -- `2 · (1 / 2) = 1`, in `A` and through the constant embedding in `A⟦X⟧`.
  have h2 : 2 * c = 1 := mod_cast natCast_mul_algebraMap_inv (K := A) two_ne_zero
  have h2C : (2 : A⟦X⟧) * C c = 1 := by rw [← map_ofNat C 2, ← map_mul, h2, map_one]
  have hk : h * k = 1 := rescale_exp_mul_rescale_neg_exp c
  have hh : h * h = exp A := by
    rw [rescale_exp_mul_self, h2, rescale_one, RingHom.id_apply]
  have hB : B * (exp A - 1) = X := bernoulliPowerSeries_mul_exp_sub_one A
  -- `B(X/2) (e^{X/2} - 1) = X / 2`.
  have hB₂ : B₂ * (h - 1) = C c * X := by
    simpa [B₂, h, rescale_X] using congrArg (rescale c) hB
  -- Multiply by the unit `e^{X/2}`: the factor becomes `e^X - 1 = (e^{X/2} - 1)(e^{X/2} + 1)`.
  refine (IsUnit.of_mul_eq_one k hk).mul_left_cancel ?_
  rw [aHatSeries]
  linear_combination (2 * B₂ - B - 2 * B₂) * hh - (2 * B₂ - B) * hk - hB +
    2 * (h + 1) * hB₂ + (h + 1) * X * h2C

/-- The identity `Â(X) · (e^{X/2} - e^{-X/2}) = X` characterizes the Â series. -/
theorem eq_aHatSeries_iff {f : A⟦X⟧} :
    f = aHatSeries A ↔ f * (rescale (algebraMap ℚ A 2⁻¹) (exp A) -
      rescale (-algebraMap ℚ A 2⁻¹) (exp A)) = X :=
  ⟨fun h ↦ h ▸ aHatSeries_mul_sub A, fun h ↦ mul_X_cancel <| by
    linear_combination aHatSeries A * h - f * aHatSeries_mul_sub A⟩

/-- **The Â series is even**: `Â(-X) = Â(X)`. -/
@[simp]
theorem rescale_neg_one_aHatSeries : rescale (-1) (aHatSeries A) = aHatSeries A := by
  rw [eq_aHatSeries_iff]
  have h := congrArg (rescale (-1)) (aHatSeries_mul_sub A)
  simp only [map_mul, map_sub, rescale_rescale, rescale_neg_one_X, mul_neg_one, neg_neg] at h
  linear_combination -h

/-- The odd coefficients of the Â series vanish. -/
@[simp]
theorem coeff_aHatSeries_of_odd {n : ℕ} (hn : Odd n) : coeff n (aHatSeries A) = 0 := by
  rw [coeff_aHatSeries]
  obtain rfl | hlt : n = 1 ∨ 1 < n := by have := hn.pos; omega
  · simp
  · simp [bernoulli_eq_zero_of_odd hn hlt]

/-- `Â(X) = 1 - X²/24 + …`. -/
@[simp]
theorem coeff_two_aHatSeries : coeff 2 (aHatSeries A) = algebraMap ℚ A (-1 / 24) := by
  rw [coeff_aHatSeries, bernoulli_two]
  norm_num [Nat.factorial]

/-- `Â(X) = 1 - X²/24 + 7X⁴/5760 + …`. -/
@[simp]
theorem coeff_four_aHatSeries : coeff 4 (aHatSeries A) = algebraMap ℚ A (7 / 5760) := by
  rw [coeff_aHatSeries, bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_four]
  norm_num [Nat.factorial]

/-- **The Todd series is `e^{X/2}` times the Â series**: `Td(X) = e^{X/2} Â(X)`. -/
theorem bernoulli'PowerSeries_eq_rescale_exp_mul_aHatSeries :
    bernoulli'PowerSeries A = rescale (algebraMap ℚ A 2⁻¹) (exp A) * aHatSeries A := by
  set c := algebraMap ℚ A 2⁻¹
  rw [eq_comm, eq_bernoulli'PowerSeries_iff]
  have h2 : 2 * c = 1 := mod_cast natCast_mul_algebraMap_inv (K := A) two_ne_zero
  have hk := rescale_exp_mul_rescale_neg_exp c
  have hkk : rescale (-c) (exp A) * rescale (-c) (exp A) = rescale (-1) (exp A) := by
    rw [rescale_exp_mul_self, mul_neg, h2]
  linear_combination aHatSeries_mul_sub A - aHatSeries A * rescale (-c) (exp A) * hk +
    rescale c (exp A) * aHatSeries A * hkk

/-! ### The L series -/

/-- **Hirzebruch's L series** `X / tanh X = X (e^X + e^{-X}) / (e^X - e^{-X})`, the characteristic
power series of the L class of an oriented real vector bundle. It is defined as `B(2X) + X`,
where `B(X) = X / (e^X - 1)` is `bernoulliPowerSeries A`;
`TauCeti.hirzebruchLSeries_mul_sub` proves that it is the displayed quotient. -/
noncomputable def hirzebruchLSeries : A⟦X⟧ :=
  rescale 2 (bernoulliPowerSeries A) + X

/-- The coefficients of the L series away from degree one: `L(X) = ∑_{n ≠ 1} 2ⁿ Bₙ Xⁿ / n!`. -/
theorem coeff_hirzebruchLSeries {n : ℕ} (hn : n ≠ 1) :
    coeff n (hirzebruchLSeries A) = algebraMap ℚ A (2 ^ n * bernoulli n / n !) := by
  simp [hirzebruchLSeries, bernoulliPowerSeries, coeff_rescale, coeff_X, hn, mul_div_assoc,
    map_ofNat]

/-- The L series has constant coefficient `1`. -/
@[simp]
theorem constantCoeff_hirzebruchLSeries : constantCoeff (hirzebruchLSeries A) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_hirzebruchLSeries A zero_ne_one]
  simp

/-- **The L series is `X / tanh X`**: its product with `e^X - e^{-X}` is `X (e^X + e^{-X})`. -/
theorem hirzebruchLSeries_mul_sub :
    hirzebruchLSeries A * (exp A - rescale (-1) (exp A)) =
      X * (exp A + rescale (-1) (exp A)) := by
  set e := exp A
  set k := rescale (-1) e
  set B := bernoulliPowerSeries A
  have hk : e * k = 1 := by
    simpa [e, k] using rescale_exp_mul_rescale_neg_exp (1 : A)
  have hee : rescale 2 e = e * e := by
    simpa [e] using (rescale_exp_mul_self (1 : A)).symm
  -- `B(2X) (e^{2X} - 1) = 2X`.
  have hB₂ : rescale 2 B * (rescale 2 e - 1) = 2 * X := by
    simpa [B, e, rescale_X, map_ofNat] using
      congrArg (rescale (2 : A)) (bernoulliPowerSeries_mul_exp_sub_one A)
  -- Multiply by the unit `e^X`: the factor becomes `e^{2X} - 1`.
  refine (IsUnit.of_mul_eq_one k hk).mul_left_cancel ?_
  rw [hirzebruchLSeries]
  rw [hee] at hB₂
  linear_combination hB₂ - (rescale 2 B + 2 * X) * hk

/-- The identity `L(X) · (e^X - e^{-X}) = X (e^X + e^{-X})` characterizes the L series. -/
theorem eq_hirzebruchLSeries_iff {f : A⟦X⟧} :
    f = hirzebruchLSeries A ↔
      f * (exp A - rescale (-1) (exp A)) = X * (exp A + rescale (-1) (exp A)) := by
  refine ⟨fun h ↦ h ▸ hirzebruchLSeries_mul_sub A, fun h ↦ ?_⟩
  -- `e^X + e^{-X}` has constant coefficient `2`, hence is a unit.
  have hu : IsUnit (exp A + rescale (-1) (exp A)) := by
    rw [isUnit_iff_constantCoeff, map_add, constantCoeff_rescale, constantCoeff_exp,
      one_add_one_eq_two, ← map_ofNat (algebraMap ℚ A) 2]
    exact (isUnit_iff_ne_zero.mpr (two_ne_zero' ℚ)).map _
  refine mul_X_cancel (hu.mul_right_cancel ?_)
  linear_combination hirzebruchLSeries A * h - f * hirzebruchLSeries_mul_sub A

/-- **The L series is even**: `L(-X) = L(X)`. -/
@[simp]
theorem rescale_neg_one_hirzebruchLSeries :
    rescale (-1) (hirzebruchLSeries A) = hirzebruchLSeries A := by
  rw [eq_hirzebruchLSeries_iff]
  have h := congrArg (rescale (-1)) (hirzebruchLSeries_mul_sub A)
  simp only [map_mul, map_sub, map_add, rescale_rescale, rescale_neg_one_X, mul_neg_one,
    neg_neg, rescale_one, RingHom.id_apply] at h
  linear_combination -h

/-- The odd coefficients of the L series vanish. -/
@[simp]
theorem coeff_hirzebruchLSeries_of_odd {n : ℕ} (hn : Odd n) :
    coeff n (hirzebruchLSeries A) = 0 := by
  obtain rfl | hlt : n = 1 ∨ 1 < n := by have := hn.pos; omega
  · rw [hirzebruchLSeries, map_add, coeff_rescale, coeff_one_X, pow_one, bernoulliPowerSeries,
      coeff_mk, ← map_ofNat (algebraMap ℚ A) 2, ← map_mul, ← map_one (algebraMap ℚ A),
      ← map_add, bernoulli_one]
    norm_num
  · simp [coeff_hirzebruchLSeries A hlt.ne', bernoulli_eq_zero_of_odd hn hlt]

/-- `L(X) = 1 + X²/3 + …`. -/
@[simp]
theorem coeff_two_hirzebruchLSeries :
    coeff 2 (hirzebruchLSeries A) = algebraMap ℚ A (1 / 3) := by
  rw [coeff_hirzebruchLSeries A (by decide), bernoulli_two]
  norm_num [Nat.factorial]

/-- `L(X) = 1 + X²/3 - X⁴/45 + …`. -/
@[simp]
theorem coeff_four_hirzebruchLSeries :
    coeff 4 (hirzebruchLSeries A) = algebraMap ℚ A (-1 / 45) := by
  rw [coeff_hirzebruchLSeries A (by decide), bernoulli_eq_bernoulli'_of_ne_one (by decide),
    bernoulli'_four]
  norm_num [Nat.factorial]

end TauCeti
