/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Multiplicative
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.FormalPoint
import TauCeti.RingTheory.PowerSeries.Derivative
import TauCeti.RingTheory.FormalGroup.Logarithm.Naturality

/-!
# The formal group of the Tate curve

The Tate curve `E_q : y² + xy = x³ + a₄(q) x + a₆(q)` over `ℤ⟦q⟧` is uniformised by the
coordinates `X(u)` and `Y(u)`, and its identity corresponds to the parameter `u = 1`. This file
shows that the formal group law of `E_q` is the multiplicative formal group law `X + Y + XY`
transported along an explicit formal coordinate, over the whole of `ℤ⟦q⟧`: the formal
multiplicative group is the formal group of the identity component of the Tate curve, including at
the nodal fibre `q = 0`.

Near the identity put `u = 1 + T`. The coordinates `X(1 + T)` and `Y(1 + T)` have poles of order
two and three at `T = 0`; with these cleared they are the power series `tateIdentityX = T² X(1 + T)`
and `tateIdentityY = -T³ Y(1 + T)` in `T` over `ℤ⟦q⟧`. They are obtained by evaluating the formal
Tate coordinates with polynomial coefficients (`TauCeti.tateClearedX`, `TauCeti.tateClearedY`) at
`u = 1 + T` and `v = q / (1 + T)`, as power series in `q` over `ℤ⟦T⟧`, and then exchanging the two
variables. So they satisfy the equation of the Tate curve
(`TauCeti.tateIdentityY_sq_sub_X_mul_tateIdentityX_mul_tateIdentityY`), and the parameter
`z = -x / y` of this point is the formal coordinate
`tateFormalCoordinate = T · tateIdentityX / tateIdentityY`, with linear coefficient `1`.

On each coefficient of `q`, the Tate coordinates satisfy `u X'(u) = 2Y(u) + X(u)`
(`TauCeti.one_add_X_mul_X_mul_derivative_tateIdentityX_sub`): the invariant differential
`dx / (2y + x)` is `du / u`. In the parameter `z`, where the invariant differential is
`dz / G(z)` with `G = WeierstrassCurve.formalInvariantDifferentialDenom`, this reads
`(1 + T) z' = G(z)` (`TauCeti.one_add_X_mul_derivative_tateFormalCoordinate`). Over the
`ℚ`-algebra `ℚ⟦q⟧` a formal group law is determined by its logarithm, and the logarithm of the
formal group of `E_q` pulled back along `z` is `log(1 + T)`, the logarithm of the multiplicative
formal group law. This identifies the two formal group laws over `ℚ⟦q⟧`, hence over `ℤ⟦q⟧`, and
then over every ring by base change. In particular, every specialisation of the Tate curve to a
field of characteristic `p` has formal group of height one.

At `q = 0` the Tate curve is the nodal cubic `y² + xy = x³`, and
`TauCeti.formalGroup_map_constantCoeff_tateCurve` identifies its formal group with the
multiplicative one along the different coordinate `T ↦ -T`.

## Main definitions

* `TauCeti.tateIdentityX`, `TauCeti.tateIdentityY`: the Tate coordinates at `u = 1 + T`, with
  their poles at `T = 0` cleared, as power series in `T` over `ℤ⟦q⟧`.
* `TauCeti.tateFormalCoordinate`: the parameter `z = -x / y` of the Tate point near the identity,
  a formal coordinate over `ℤ⟦q⟧`.

## Main results

* `TauCeti.formalGroup_map_constantCoeff_tateCurve`: the formal group law of the Tate
  curve at `q = 0` is the transport of the multiplicative formal group law along `T ↦ -T`.
* `TauCeti.tateIdentityY_sq_sub_X_mul_tateIdentityX_mul_tateIdentityY`: the Tate point near the
  identity lies on the Tate curve.
* `TauCeti.one_add_X_mul_X_mul_derivative_tateIdentityX_sub`: `u X'(u) = 2Y(u) + X(u)` near the
  identity.
* `TauCeti.one_add_X_mul_derivative_tateFormalCoordinate`: the invariant differential of the Tate
  curve pulls back to `du / u`.
* `TauCeti.formalGroup_tateCurve`: the formal group law of the Tate curve over `ℤ⟦q⟧` is the
  transport of the multiplicative formal group law along `tateFormalCoordinate`.
* `TauCeti.formalGroup_map_tateCurve`: the same for every specialisation of the Tate curve.
* `TauCeti.height_formalGroup_map_tateCurve`: over a field of characteristic `p`, every
  specialisation of the Tate curve has formal group of height `1`.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, §V.3.
* J. Tate, *A review of non-Archimedean elliptic functions*, in *Elliptic curves, modular forms,
  & Fermat's last theorem* (Hong Kong, 1993), International Press (1995), 162–184.
-/

public section

open PowerSeries

namespace TauCeti

open WeierstrassCurve FormalGroup in
/-- **The formal group of the Tate curve at `q = 0` is multiplicative**: the Tate curve over
`ℤ⟦q⟧` reduces at `q = 0` to the nodal cubic `y² + xy = x³`, whose formal group law
`X + Y - XY` is the transport of `X + Y + XY` along `T ↦ -T`. -/
theorem formalGroup_map_constantCoeff_tateCurve :
    formalGroup (tateCurve.map PowerSeries.constantCoeff) =
      FormalCoordinate.homothety (-1 : ℤˣ) • (𝔾ₘ : FormalGroup ℤ) := by
  simpa using formalGroup_eq_homothety_smul_𝔾ₘ (W := tateCurve.map PowerSeries.constantCoeff) 1
    (by simp) (by simp) (by simp) (by simp) (by simp)

/-! ### The Tate point near the identity -/

/-- The inverse `(1 + T)⁻¹ = 1 - T + T² - ⋯` in `ℤ⟦T⟧`. -/
private noncomputable abbrev invOneAddX : ℤ⟦X⟧ := mk fun n ↦ (-1) ^ n

private theorem invOneAddX_mul_one_add_X : invOneAddX * (1 + X) = 1 :=
  mk_neg_one_pow_mul_one_add_eq_one ℤ

private theorem derivative_invOneAddX : d⁄dX invOneAddX = -invOneAddX ^ 2 := by
  have h := derivative_inv
    ⟨1 + X, invOneAddX, by rw [mul_comm, invOneAddX_mul_one_add_X], invOneAddX_mul_one_add_X⟩
  rwa [Units.inv_mk, Units.val_mk, Units.val_mk, map_add, Derivation.map_one_eq_zero,
    derivative_X, zero_add, mul_one] at h

/-- Evaluation of `ℤ[u]⟦v⟧` at `u = 1 + T` and `v = q / (1 + T)`, with values in `ℤ⟦T⟧⟦q⟧`. -/
private noncomputable def unitEval : (Polynomial ℤ)⟦X⟧ →+* ℤ⟦X⟧⟦X⟧ :=
  (rescale invOneAddX).comp (map (Polynomial.aeval (1 + X : ℤ⟦X⟧)).toRingHom)

private theorem coeff_unitEval (F : (Polynomial ℤ)⟦X⟧) (N : ℕ) :
    coeff N (unitEval F) = invOneAddX ^ N * Polynomial.aeval (1 + X : ℤ⟦X⟧) (coeff N F) := by
  simp [unitEval, coeff_rescale]

private theorem unitEval_C (p : Polynomial ℤ) :
    unitEval (C p) = C (Polynomial.aeval (1 + X : ℤ⟦X⟧) p) := by
  refine PowerSeries.ext fun N ↦ ?_
  rw [coeff_unitEval, coeff_C, coeff_C]
  split_ifs with h <;> simp [h]

private theorem unitEval_tateClearedParamHom (f : ℤ⟦X⟧) :
    unitEval (tateClearedParamHom f) = map (C (R := ℤ)) f := by
  refine PowerSeries.ext fun N ↦ ?_
  rw [coeff_unitEval, coeff_tateClearedParamHom, coeff_map, map_mul, map_pow, Polynomial.aeval_X,
    Polynomial.aeval_C, ← mul_assoc, ← mul_pow, invOneAddX_mul_one_add_X, one_pow, one_mul]
  simp only [eq_intCast]

private theorem invOneAddX_pow_mul_one_add_X_pow (n : ℕ) : invOneAddX ^ n * (1 + X) ^ n = 1 := by
  rw [← mul_pow, invOneAddX_mul_one_add_X, one_pow]

/-- The coefficient of `qᴺ` in `T² X(1 + T)`. -/
private theorem coeff_unitEval_tateClearedX (N : ℕ) :
    coeff N (unitEval tateClearedX) = (if N = 0 then 1 + X else 0) +
      X ^ 2 * ∑ d ∈ N.divisors, (d : ℤ⟦X⟧) * ((1 + X) ^ d + invOneAddX ^ d - 2) := by
  rw [coeff_unitEval, tateClearedX_def, map_add, coeff_C, coeff_C_mul, coeff_mk]
  rcases eq_or_ne N 0 with rfl | hN
  · simp
  simp only [hN, ↓reduceIte, zero_add, map_mul, map_pow, map_sub, map_one,
    Polynomial.aeval_X, map_sum, map_natCast, map_add, map_ofNat, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le (Nat.divisor_le hd)
  rw [Nat.add_sub_cancel_left]
  have h₁ := invOneAddX_pow_mul_one_add_X_pow (d + e)
  have h₂ := invOneAddX_pow_mul_one_add_X_pow e
  have hX : (1 : ℤ⟦X⟧) - (1 + X) = -X := by ring
  rw [hX]
  generalize (1 : ℤ⟦X⟧) + X = u at h₁ h₂ ⊢
  generalize invOneAddX = c at h₁ h₂ ⊢
  linear_combination (X ^ 2 * (d : ℤ⟦X⟧) * (u ^ d - 2)) * h₁ + (X ^ 2 * (d : ℤ⟦X⟧) * c ^ d) * h₂

/-- The coefficient of `qᴺ` in `-T³ Y(1 + T)`. -/
private theorem coeff_unitEval_tateClearedY (N : ℕ) :
    coeff N (unitEval tateClearedY) = (if N = 0 then (1 + X) ^ 2 else 0) -
      X ^ 3 * ∑ d ∈ N.divisors, ((d.choose 2 : ℤ⟦X⟧) * (1 + X) ^ d -
        ((d + 1).choose 2 : ℤ⟦X⟧) * invOneAddX ^ d + (d : ℤ⟦X⟧)) := by
  rw [coeff_unitEval, tateClearedY_def, map_add, coeff_C, coeff_C_mul, coeff_mk]
  rcases eq_or_ne N 0 with rfl | hN
  · simp
  simp only [hN, ↓reduceIte, zero_sub, zero_add, map_mul, map_pow, map_sub, map_one,
    Polynomial.aeval_X, map_sum, map_natCast, map_add, Finset.mul_sum]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le (Nat.divisor_le hd)
  rw [Nat.add_sub_cancel_left]
  have h₁ := invOneAddX_pow_mul_one_add_X_pow (d + e)
  have h₂ := invOneAddX_pow_mul_one_add_X_pow e
  have hX : (1 : ℤ⟦X⟧) - (1 + X) = -X := by ring
  rw [hX]
  generalize (1 : ℤ⟦X⟧) + X = u at h₁ h₂ ⊢
  generalize invOneAddX = c at h₁ h₂ ⊢
  linear_combination (-X ^ 3 * ((d.choose 2 : ℤ⟦X⟧) * u ^ d + d)) * h₁ +
    (X ^ 3 * ((d + 1).choose 2 : ℤ⟦X⟧) * c ^ d) * h₂

/-- With `u = 1 + T` and `c = u⁻¹`, the divisor sums `S = ∑ d (uᵈ + cᵈ - 2)` and
`R = ∑ (d (d - 1) / 2 · uᵈ - d (d + 1) / 2 · cᵈ + d)` satisfy `u S' = S + 2 R`. -/
private theorem one_add_X_mul_derivative_sum (N : ℕ) :
    (1 + X) * d⁄dX (∑ d ∈ N.divisors, (d : ℤ⟦X⟧) * ((1 + X) ^ d + invOneAddX ^ d - 2)) =
      ∑ d ∈ N.divisors, (d : ℤ⟦X⟧) * ((1 + X) ^ d + invOneAddX ^ d - 2) +
        2 * ∑ d ∈ N.divisors, ((d.choose 2 : ℤ⟦X⟧) * (1 + X) ^ d -
          ((d + 1).choose 2 : ℤ⟦X⟧) * invOneAddX ^ d + (d : ℤ⟦X⟧)) := by
  rw [map_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (Nat.pos_of_mem_divisors hd).ne'
  have h₁ : (((k + 1).choose 2 : ℕ) : ℤ⟦X⟧) * 2 = (k + 1) * k := by
    have h : (k + 1).choose 2 * 2 = (k + 1) * k := by
      simpa using (Nat.add_one_mul_choose_eq k 1).symm
    simpa using congrArg (Nat.cast (R := ℤ⟦X⟧)) h
  have h₂ : (((k + 1 + 1).choose 2 : ℕ) : ℤ⟦X⟧) * 2 = (k + 1 + 1) * (k + 1) := by
    have h : (k + 1 + 1).choose 2 * 2 = (k + 1 + 1) * (k + 1) := by
      simpa using (Nat.add_one_mul_choose_eq (k + 1) 1).symm
    simpa using congrArg (Nat.cast (R := ℤ⟦X⟧)) h
  have h₀ : d⁄dX (2 : ℤ⟦X⟧) = 0 := by exact_mod_cast (derivative (R := ℤ)).map_natCast 2
  simp only [Derivation.leibniz, Derivation.leibniz_pow, map_sub, Derivation.map_natCast, h₀,
    map_add, Derivation.map_one_eq_zero, derivative_X, derivative_invOneAddX, smul_eq_mul,
    nsmul_eq_mul, zero_add, mul_zero, add_zero, sub_zero, Nat.add_sub_cancel]
  have h := invOneAddX_mul_one_add_X
  generalize (1 : ℤ⟦X⟧) + X = u at h ⊢
  generalize invOneAddX = c at h ⊢
  generalize (((k + 1).choose 2 : ℕ) : ℤ⟦X⟧) = A at h₁ ⊢
  generalize (((k + 1 + 1).choose 2 : ℕ) : ℤ⟦X⟧) = B at h₂ ⊢
  push_cast
  linear_combination (-(k + 1 : ℤ⟦X⟧) ^ 2 * c ^ (k + 1)) * h - u ^ (k + 1) * h₁ + c ^ (k + 1) * h₂

/-- `u dX/du = 2Y + X` on the coefficient of `qᴺ`. -/
private theorem one_add_X_mul_derivative_coeff_unitEval (N : ℕ) :
    (1 + X) * (X * d⁄dX (coeff N (unitEval tateClearedX)) -
        2 * coeff N (unitEval tateClearedX)) =
      X * coeff N (unitEval tateClearedX) - 2 * coeff N (unitEval tateClearedY) := by
  rw [coeff_unitEval_tateClearedX, coeff_unitEval_tateClearedY]
  rcases eq_or_ne N 0 with rfl | hN
  · simp only [↓reduceIte, Nat.divisors_zero, Finset.sum_empty, mul_zero, add_zero, sub_zero,
      map_add, derivative_X, Derivation.map_one_eq_zero, zero_add]
    ring
  simp only [hN, ↓reduceIte, zero_add, zero_sub, Derivation.leibniz, Derivation.leibniz_pow,
    derivative_X, smul_eq_mul]
  linear_combination X ^ 3 * one_add_X_mul_derivative_sum N

/-- `T² X(1 + T)`: the first Tate coordinate `X(u)` at the parameter `u = 1 + T` near the
identity, with its double pole at `T = 0` cleared, as a power series in `T` over `ℤ⟦q⟧`. Its
coefficient of `qᴺ`, a power series in `T`, is `1 + T` for `N = 0` and
`T² ∑_{d ∣ N} d ((1 + T)ᵈ + (1 + T)⁻ᵈ - 2)` for `N ≥ 1`, where
`(1 + T)⁻¹ = 1 - T + T² - ⋯`. -/
noncomputable def tateIdentityX : ℤ⟦X⟧⟦X⟧ :=
  swap (mk fun N ↦ (if N = 0 then 1 + X else 0) + X ^ 2 * ∑ d ∈ N.divisors,
    (d : ℤ⟦X⟧) * ((1 + X) ^ d + (mk fun n ↦ (-1) ^ n) ^ d - 2))

/-- The defining formula for `tateIdentityX`. -/
theorem tateIdentityX_def : tateIdentityX =
    swap (mk fun N ↦ (if N = 0 then 1 + X else 0) + X ^ 2 * ∑ d ∈ N.divisors,
      (d : ℤ⟦X⟧) * ((1 + X) ^ d + (mk fun n ↦ (-1) ^ n) ^ d - 2)) :=
  (rfl)

/-- `-T³ Y(1 + T)`: the second Tate coordinate `Y(u)` at the parameter `u = 1 + T` near the
identity, with its triple pole at `T = 0` cleared, as a power series in `T` over `ℤ⟦q⟧`. Its
coefficient of `qᴺ` is `(1 + T)²` for `N = 0` and
`-T³ ∑_{d ∣ N} (d (d - 1) / 2 · (1 + T)ᵈ - d (d + 1) / 2 · (1 + T)⁻ᵈ + d)` for `N ≥ 1`. -/
noncomputable def tateIdentityY : ℤ⟦X⟧⟦X⟧ :=
  swap (mk fun N ↦ (if N = 0 then (1 + X) ^ 2 else 0) -
    X ^ 3 * ∑ d ∈ N.divisors, ((d.choose 2 : ℤ⟦X⟧) * (1 + X) ^ d -
      ((d + 1).choose 2 : ℤ⟦X⟧) * (mk fun n ↦ (-1) ^ n) ^ d + (d : ℤ⟦X⟧)))

/-- The defining formula for `tateIdentityY`. -/
theorem tateIdentityY_def : tateIdentityY =
    swap (mk fun N ↦ (if N = 0 then (1 + X) ^ 2 else 0) -
      X ^ 3 * ∑ d ∈ N.divisors, ((d.choose 2 : ℤ⟦X⟧) * (1 + X) ^ d -
        ((d + 1).choose 2 : ℤ⟦X⟧) * (mk fun n ↦ (-1) ^ n) ^ d + (d : ℤ⟦X⟧))) :=
  (rfl)

private theorem swap_tateIdentityX : swap tateIdentityX = unitEval tateClearedX := by
  refine PowerSeries.ext fun N ↦ ?_
  rw [tateIdentityX_def, swap_swap, coeff_mk, coeff_unitEval_tateClearedX]

private theorem swap_tateIdentityY : swap tateIdentityY = unitEval tateClearedY := by
  refine PowerSeries.ext fun N ↦ ?_
  rw [tateIdentityY_def, swap_swap, coeff_mk, coeff_unitEval_tateClearedY]

/-- `T² X(1 + T)` has constant coefficient `1`. -/
@[simp]
theorem constantCoeff_tateIdentityX : constantCoeff tateIdentityX = 1 := by
  refine PowerSeries.ext fun a ↦ ?_
  rw [tateIdentityX_def, coeff_constantCoeff_swap, coeff_mk, coeff_one]
  split_ifs <;> simp

/-- `-T³ Y(1 + T)` has constant coefficient `1`. -/
@[simp]
theorem constantCoeff_tateIdentityY : constantCoeff tateIdentityY = 1 := by
  refine PowerSeries.ext fun a ↦ ?_
  rw [tateIdentityY_def, coeff_constantCoeff_swap, coeff_mk, coeff_one]
  split_ifs <;> simp

/-- **The Tate point near the identity lies on the Tate curve.** With `x = X(1 + T)` and
`y = Y(1 + T)`, the equation `y² + x y = x³ + a₄(q) x + a₆(q)`, multiplied by `T⁶`, holds in
`ℤ⟦q⟧⟦T⟧` for `T² x = tateIdentityX` and `-T³ y = tateIdentityY`. -/
theorem tateIdentityY_sq_sub_X_mul_tateIdentityX_mul_tateIdentityY :
    tateIdentityY ^ 2 - X * tateIdentityX * tateIdentityY =
      tateIdentityX ^ 3 + X ^ 4 * C tateCurve.a₄ * tateIdentityX + X ^ 6 * C tateCurve.a₆ := by
  have h := congrArg (fun F ↦ swap (unitEval F)) tateClearedY_sq_add_mul_eq
  simp only [map_add, map_mul, map_pow, unitEval_C, unitEval_tateClearedParamHom,
    ← swap_tateIdentityX, ← swap_tateIdentityY, swap_swap, swap_C, swap_map_C, map_sub, map_one,
    Polynomial.aeval_X, map_X] at h
  linear_combination h

/-- **`u dX/du = 2Y + X` near the identity.** With `u = 1 + T`, `x = X(1 + T)` and
`y = Y(1 + T)`, the derivative in `T` satisfies `u dx/dT = 2y + x`; for `T² x = tateIdentityX` and
`-T³ y = tateIdentityY` this reads `(1 + T)(T F' - 2F) = T F - 2G`, with `F = tateIdentityX` and
`G = tateIdentityY`. It says that the invariant differential `dx / (2y + x)` of the Tate curve is
`du / u`. -/
theorem one_add_X_mul_X_mul_derivative_tateIdentityX_sub :
    (1 + X) * (X * d⁄dX tateIdentityX - 2 * tateIdentityX) =
      X * tateIdentityX - 2 * tateIdentityY := by
  rw [← swap_swap ((1 + X) * _), ← swap_swap (X * tateIdentityX - _)]
  congr 1
  refine PowerSeries.ext fun N ↦ ?_
  have h₁ : (1 + C X : ℤ⟦X⟧⟦X⟧) = C (1 + X) := by rw [map_add, map_one]
  have h₂ : (2 : ℤ⟦X⟧⟦X⟧) = C 2 := (map_ofNat C 2).symm
  simp only [map_mul, map_sub, map_add, map_one, map_ofNat, swap_X]
  rw [h₁, h₂]
  simp only [coeff_C_mul, map_sub, coeff_swap_derivative, swap_tateIdentityX, swap_tateIdentityY]
  exact one_add_X_mul_derivative_coeff_unitEval N

/-! ### The formal parameter at the identity and the formal group -/

/-- `-T³ Y(1 + T)` as a unit of `ℤ⟦q⟧⟦T⟧`. -/
private noncomputable def tateIdentityYUnit : ℤ⟦X⟧⟦X⟧ˣ :=
  (isUnit_iff_constantCoeff (φ := tateIdentityY)).mpr (by simp) |>.unit

private theorem val_tateIdentityYUnit : (tateIdentityYUnit : ℤ⟦X⟧⟦X⟧) = tateIdentityY :=
  IsUnit.unit_spec _

/-- The inverse of `-T³ Y(1 + T)` in `ℤ⟦q⟧⟦T⟧`. -/
private noncomputable def tateIdentityYInv : ℤ⟦X⟧⟦X⟧ :=
  ((tateIdentityYUnit⁻¹ : ℤ⟦X⟧⟦X⟧ˣ) : ℤ⟦X⟧⟦X⟧)

private theorem tateIdentityY_mul_inv : tateIdentityY * tateIdentityYInv = 1 := by
  rw [← val_tateIdentityYUnit, tateIdentityYInv, Units.mul_inv]

private theorem constantCoeff_tateIdentityYInv : constantCoeff tateIdentityYInv = 1 := by
  simpa using congrArg constantCoeff tateIdentityY_mul_inv

/-- **The formal parameter of the Tate curve at the identity**: the series `z = -x / y` at the
point `(x, y) = (X(1 + T), Y(1 + T))` of the Tate curve, that is
`T · tateIdentityX / tateIdentityY`. It is a formal coordinate over `ℤ⟦q⟧` with linear coefficient
`1` (`TauCeti.coeff_one_tateFormalCoordinate`), and it carries the multiplicative formal group law
to the formal group law of the Tate curve (`TauCeti.formalGroup_tateCurve`). -/
noncomputable def tateFormalCoordinate : FormalCoordinate ℤ⟦X⟧ where
  toPowerSeries := X * tateIdentityX * tateIdentityYInv
  constantCoeff_toPowerSeries := by simp
  isUnit_coeff_one := by
    rw [mul_assoc, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply, map_mul,
      constantCoeff_tateIdentityX, constantCoeff_tateIdentityYInv, one_mul]
    exact isUnit_one

private theorem tateFormalCoordinate_toPowerSeries :
    tateFormalCoordinate.toPowerSeries = X * tateIdentityX * tateIdentityYInv :=
  (rfl)

/-- The defining property of `tateFormalCoordinate`: `z · tateIdentityY = T · tateIdentityX`. -/
theorem tateFormalCoordinate_toPowerSeries_mul_tateIdentityY :
    tateFormalCoordinate.toPowerSeries * tateIdentityY = X * tateIdentityX := by
  rw [tateFormalCoordinate_toPowerSeries, mul_assoc, mul_comm _ tateIdentityY,
    tateIdentityY_mul_inv, mul_one]

/-- The formal parameter at the identity has linear coefficient `1`. -/
@[simp]
theorem coeff_one_tateFormalCoordinate : coeff 1 tateFormalCoordinate.toPowerSeries = 1 := by
  rw [tateFormalCoordinate_toPowerSeries, mul_assoc, coeff_succ_X_mul,
    coeff_zero_eq_constantCoeff_apply, map_mul, constantCoeff_tateIdentityX,
    constantCoeff_tateIdentityYInv, one_mul]

/-- The `w`-expansion of the Tate curve at `z` is `T³ / tateIdentityY`: the series
`w = -1 / y = T³ / tateIdentityY` solves the `w`-equation at the parameter `z`, which is the
equation of the Tate point near the identity read in the coordinates `z = -x / y`, `w = -1 / y`. -/
private theorem subst_tateFormalCoordinate_formalW :
    (subst tateFormalCoordinate.toPowerSeries (WeierstrassCurve.formalW tateCurve) : ℤ⟦X⟧⟦X⟧) =
      X ^ 3 * tateIdentityYInv := by
  symm
  refine WeierstrassCurve.eq_subst_formalW_of_wEquation tateCurve (by simp) (by simp) ?_
  rw [WeierstrassCurve.wEquationRHS_powerSeries, tateFormalCoordinate_toPowerSeries]
  simp only [tateCurve_a₁, tateCurve_a₂, tateCurve_a₃, map_one, map_zero, one_mul, zero_mul,
    add_zero]
  have hE := tateIdentityY_sq_sub_X_mul_tateIdentityX_mul_tateIdentityY
  have hY := tateIdentityY_mul_inv
  generalize tateIdentityYInv = y' at hY ⊢
  linear_combination (X ^ 3 * y' ^ 3) * hE -
    (X ^ 3 * y' * (1 + tateIdentityY * y') - X ^ 4 * tateIdentityX * y' ^ 2) * hY

/-- **The invariant differential of the Tate curve is `du / u`.** In the parameter `z` at the
identity, the invariant differential of a Weierstrass curve is `ω = dz / G(z)` with
`G = WeierstrassCurve.formalInvariantDifferentialDenom`
(`WeierstrassCurve.invariantDifferential_formalGroup_mul_formalInvariantDifferentialDenom`). For the
Tate curve along `z = tateFormalCoordinate`, this is `(1 + T) z'(T) = G(z(T))`: `ω` pulls back to
`dT / (1 + T) = du / u` with `u = 1 + T`. -/
theorem one_add_X_mul_derivative_tateFormalCoordinate :
    (1 + X) * d⁄dX tateFormalCoordinate.toPowerSeries =
      subst tateFormalCoordinate.toPowerSeries tateCurve.formalInvariantDifferentialDenom := by
  -- Write `z = T x y'` and `w = T³ y'`, where `x = tateIdentityX`, `y = tateIdentityY` and
  -- `y y' = 1`, so that the claim becomes a ring identity in `x`, `y`, `y'` and their derivatives.
  have hz := tateFormalCoordinate.constantCoeff_toPowerSeries
  rw [WeierstrassCurve.subst_formalInvariantDifferentialDenom _
    (HasSubst.of_constantCoeff_zero' hz), subst_tateFormalCoordinate_formalW]
  simp only [tateCurve_a₁, tateCurve_a₂, tateCurve_a₃, one_smul, zero_smul, sub_zero, mul_zero,
    smul_eq_C_mul]
  have hY := tateIdentityY_mul_inv
  have hdy' : d⁄dX tateIdentityYInv = -tateIdentityYInv ^ 2 * d⁄dX tateIdentityY := by
    rw [← val_tateIdentityYUnit]
    exact derivative_inv tateIdentityYUnit
  have hz' := tateFormalCoordinate_toPowerSeries_mul_tateIdentityY
  have H := one_add_X_mul_X_mul_derivative_tateIdentityX_sub
  have hE := tateIdentityY_sq_sub_X_mul_tateIdentityX_mul_tateIdentityY
  have hYc := constantCoeff_tateIdentityY
  have hXc := constantCoeff_tateIdentityX
  generalize tateFormalCoordinate.toPowerSeries = z at hz hz' ⊢
  generalize tateIdentityYInv = y' at hY hdy' ⊢
  have hzz : z = X * tateIdentityX * y' := by linear_combination (-z) * hY + y' * hz'
  subst hzz
  generalize tateIdentityX = x at H hE hXc ⊢
  generalize tateIdentityY = y at H hE hYc hY hdy' ⊢
  clear hz hz'
  -- Differentiate the curve equation `hE`.
  have hDE := congrArg (d⁄dX) hE
  simp only [map_sub, map_add, Derivation.leibniz, Derivation.leibniz_pow, derivative_X,
    derivative_C, smul_eq_mul, nsmul_eq_mul, mul_zero] at hDE
  norm_num at hDE
  -- Cancel the nonzero factor `(2y - T x) y²` (its constant coefficient is `2`) in the domain
  -- `ℤ⟦q⟧⟦T⟧`.
  have hne : (2 * y - X * x) * y ^ 2 ≠ 0 := by
    refine mul_ne_zero (fun h ↦ ?_) (pow_ne_zero 2 fun h ↦ by simp [h] at hYc)
    have h' := congrArg (fun F ↦ constantCoeff (constantCoeff F)) h
    simp only [map_sub, map_mul, hXc, hYc, constantCoeff_X, map_ofNat, map_zero, mul_one,
      sub_zero] at h'
    norm_num at h'
  refine mul_left_cancel₀ hne ?_
  simp only [Derivation.leibniz, derivative_X, smul_eq_mul, hdy', map_mul, map_ofNat]
  generalize d⁄dX x = dx at H hDE ⊢
  generalize d⁄dX y = dy at hDE ⊢
  generalize C tateCurve.a₄ = a at hE hDE ⊢
  generalize C tateCurve.a₆ = b at hE hDE ⊢
  -- `(2y - T x) y²` times the claim is a combination of the curve equation `hE`, its derivative
  -- `hDE`, the identity `H` and `y y' = 1`.
  linear_combination (-(1 + X) * X * x) * hDE +
    (2 * y ^ 2 - 2 * X * x * y - 3 * x ^ 3 - a * X ^ 4 * x) * H +
    (-6 * y + 9 * X * x + 6 * x) * hE +
    ((2 * y - X * x) * ((1 + X) * (x * y + X * dx * y) - (1 + X) * X * x * (y * y' + 1) * dy +
      X * x * y + 2 * a * X ^ 4 * x * (y * y' + 1) + 3 * b * X ^ 6 * (y * y' + 1))) * hY

/-- Over `ℚ⟦q⟧`, the formal group of the Tate curve is the change of coordinate of the
multiplicative formal group law along the image of `tateFormalCoordinate`: both have logarithm
`log(1 + T)` in the coordinate `T`. -/
private theorem formalGroup_map_tateCurve_rat :
    (tateCurve.map (map (Int.castRingHom ℚ))).formalGroup =
      FormalCoordinate.map (map (Int.castRingHom ℚ)) tateFormalCoordinate • FormalGroup.𝔾ₘ := by
  set ψ := FormalCoordinate.map (map (Int.castRingHom ℚ)) tateFormalCoordinate with hψ_def
  set W := tateCurve.map (map (Int.castRingHom ℚ))
  have hψ : HasSubst ψ.toPowerSeries := ψ.hasSubst
  -- `(1 + T) ψ' = G(ψ)`, the base change of `one_add_X_mul_derivative_tateFormalCoordinate`
  have hG : (1 + X) * d⁄dX ψ.toPowerSeries =
      subst ψ.toPowerSeries W.formalInvariantDifferentialDenom := by
    have h := congrArg (map (map (Int.castRingHom ℚ))) one_add_X_mul_derivative_tateFormalCoordinate
    have hm : map (map (Int.castRingHom ℚ))
        (subst tateFormalCoordinate.toPowerSeries tateCurve.formalInvariantDifferentialDenom) =
          subst (map (map (Int.castRingHom ℚ)) tateFormalCoordinate.toPowerSeries)
            (map (map (Int.castRingHom ℚ)) tateCurve.formalInvariantDifferentialDenom) :=
      map_subst tateFormalCoordinate.hasSubst _
    rwa [map_mul, map_add, map_one, map_X, ← derivative_map, hm,
      ← WeierstrassCurve.map_formalInvariantDifferentialDenom,
      ← FormalCoordinate.toPowerSeries_map] at h
  -- so the logarithm of `W` pulled back along `ψ` has derivative `(1 + T)⁻¹`
  have hP := congrArg (subst ψ.toPowerSeries)
    W.invariantDifferential_formalGroup_mul_formalInvariantDifferentialDenom
  rw [subst_mul hψ, ← hG, ← coe_substAlgHom hψ, map_one] at hP
  have hlog : subst ψ.toPowerSeries W.formalGroup.log = (FormalGroup.𝔾ₘ (R := ℚ⟦X⟧)).log := by
    have : HasUniqueDiv ℚ⟦X⟧ := HasUniqueDiv.of_isTorsionFree ℚ ℚ⟦X⟧
    refine derivative.ext ?_ ?_
    · have h1 : (1 + X : ℚ⟦X⟧⟦X⟧) ≠ 0 := fun h ↦ by simpa using congrArg constantCoeff h
      refine mul_right_cancel₀ h1 ?_
      rw [derivative_subst hψ, FormalGroup.derivative_log, FormalGroup.derivative_log,
        FormalGroup.invariantDifferential_𝔾ₘ, mk_neg_one_pow_mul_one_add_eq_one]
      rw [coe_substAlgHom] at hP
      linear_combination hP
    · rw [FormalGroup.constantCoeff_log]
      exact constantCoeff_subst_eq_zero ψ.constantCoeff_toPowerSeries _
        (FormalGroup.constantCoeff_log _)
  have hu : FormalCoordinate.linearCoeff ψ = 1 := Units.ext (by
    rw [FormalCoordinate.val_linearCoeff, hψ_def, FormalCoordinate.toPowerSeries_map, coeff_map,
      coeff_one_tateFormalCoordinate, map_one, Units.val_one])
  refine FormalGroup.invariantDifferential_injective ?_
  rw [← FormalGroup.derivative_log, ← FormalGroup.derivative_log, FormalGroup.log_smul, hu,
    Units.val_one, one_smul, ← hlog, subst_comp_subst_apply hψ ψ⁻¹.hasSubst,
    ← FormalCoordinate.toPowerSeries_mul, FormalCoordinate.toPowerSeries_mul_inv, X_subst]

/-- **The formal group of the Tate curve is multiplicative.** Over `ℤ⟦q⟧`, the formal group law
of the Tate curve `y² + xy = x³ + a₄(q) x + a₆(q)` is the transport of the multiplicative formal
group law `X + Y + XY` along the formal coordinate `tateFormalCoordinate`, the parameter
`z = -x / y` of the Tate point `(X(1 + T), Y(1 + T))`. So `FormalGroup.smulIso` makes
`tateFormalCoordinate` a strict isomorphism from `𝔾̂ₘ` to the formal group of the Tate curve, over
the whole formal neighbourhood `ℤ⟦q⟧` of the cusp and not only at `q = 0`. -/
theorem formalGroup_tateCurve : tateCurve.formalGroup = tateFormalCoordinate • FormalGroup.𝔾ₘ := by
  refine FormalGroup.map_injective (f := map (Int.castRingHom ℚ))
    (map_injective _ Int.cast_injective) ?_
  simp only [← WeierstrassCurve.map_formalGroup, FormalGroup.map_smul, FormalGroup.map_𝔾ₘ]
  exact formalGroup_map_tateCurve_rat

/-- **Every specialisation of the Tate curve has multiplicative formal group**: for every ring
homomorphism `f : ℤ⟦q⟧ → R`, the formal group law of the Tate curve over `R` is the transport of
the multiplicative formal group law along the image of `tateFormalCoordinate`. -/
theorem formalGroup_map_tateCurve {R : Type*} [CommRing R] (f : ℤ⟦X⟧ →+* R) :
    (tateCurve.map f).formalGroup =
      FormalCoordinate.map f tateFormalCoordinate • FormalGroup.𝔾ₘ := by
  rw [WeierstrassCurve.map_formalGroup, formalGroup_tateCurve, FormalGroup.map_smul,
    FormalGroup.map_𝔾ₘ]

/-- Over a field of characteristic `p`, every specialisation of the Tate curve has formal group
of height `1`, in every characteristic including `2` and `3`. -/
theorem height_formalGroup_map_tateCurve {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (f : ℤ⟦X⟧ →+* K) : (tateCurve.map f).formalGroup.height p = 1 := by
  rw [formalGroup_map_tateCurve, FormalGroup.height_smul, FormalGroup.height_𝔾ₘ]

end TauCeti
