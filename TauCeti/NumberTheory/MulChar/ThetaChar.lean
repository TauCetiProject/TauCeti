/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.MulChar.Basic
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Root-indexed multiplicative characters for Green's cuspidal functions

Given a multiplicative character `T : MulChar K ℂ` and an integer `Q ≥ 2`, every `(Q - 1)`-th root
of unity `x ∈ K` maps under `T` to a `(Q - 1)`-th root of unity in `ℂ`, hence to a power
`exp (2πi / (Q - 1)) ^ e`. Defining `T.thetaChar Q x := T ^ e` produces a symmetric pairing on
`(Q - 1)`-th roots of unity used to parameterize Green's cuspidal functions `τ_P` on `GL_n(k)` by
irreducible polynomials `P`.

* `MulChar.thetaExponent`: chosen natural number `j` with `T x = exp (2πi / (Q - 1)) ^ j`.
* `MulChar.apply_eq_exp_pow_thetaExponent`: `T x = exp (2πi / (Q - 1)) ^ T.thetaExponent Q x`
  for `2 ≤ Q` and `x ^ (Q - 1) = 1`.
* `MulChar.thetaChar`: the multiplicative character `T ^ T.thetaExponent Q x`.
* `MulChar.thetaChar_def`: defining equation `T.thetaChar Q x = T ^ T.thetaExponent Q x`.
* `MulChar.thetaChar_apply_pow`: symmetry `T.thetaChar Q x (z ^ m) = (T ^ a) x`.
* `MulChar.thetaChar_comm`: root-pairing symmetry `T.thetaChar Q x z = T.thetaChar Q z x`.
* `MulChar.thetaChar_mul`: multiplicativity in the indexing root `x`.
* `MulChar.thetaChar_eq_apply_norm_pow`: base-change formula relating `Q` and `Q ^ r`
  via the norm exponent `∑ i ∈ Finset.range r, Q ^ i`.

## References

* J. A. Green, *The characters of the finite general linear groups*, Trans. Amer. Math. Soc. 80
  (1955), 402–447.

## Provenance

* Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic,
  PBC), file `src/Lib/LocalGL/Green/TauFunctions.lean` (`New.thetaExponent`,
  `New.apply_eq_exp_pow_thetaExponent`, `New.thetaChar`, `New.thetaChar_apply_pow`,
  `New.thetaChar_mul`, `New.thetaChar_eq_apply_norm_pow`).
-/

public section

open Complex Finset

namespace MulChar

variable {K : Type*} [CommMonoidWithZero K] (T : MulChar K ℂ) {Q m : ℕ} {x y z : K}

/-- A chosen natural number `j` with `T x = exp (2πi / (Q - 1)) ^ j` (arbitrary if none
exists). -/
noncomputable def thetaExponent (Q : ℕ) (x : K) : ℕ :=
  Classical.epsilon fun j : ℕ ↦ T x = exp (2 * Real.pi * I / (Q - 1 : ℕ)) ^ j

/-- If `2 ≤ Q` and `x ^ (Q - 1) = 1`, then `T x = exp (2πi / (Q - 1)) ^ T.thetaExponent Q x`. -/
theorem apply_eq_exp_pow_thetaExponent (hQ : 2 ≤ Q) (hx : x ^ (Q - 1) = 1) :
    T x = exp (2 * Real.pi * I / (Q - 1 : ℕ)) ^ T.thetaExponent Q x := by
  have : NeZero (Q - 1) := ⟨Nat.sub_ne_zero_of_lt hQ⟩
  have h_root : T x ^ (Q - 1) = 1 := by rw [← map_pow, hx, map_one]
  obtain ⟨j, -, hj⟩ :=
    (Complex.isPrimitiveRoot_exp (Q - 1) (NeZero.ne _)).eq_pow_of_pow_eq_one h_root
  exact Classical.epsilon_spec (p := fun j : ℕ ↦ T x = _ ^ j) ⟨j, hj.symm⟩

/-- The multiplicative character `θ_x = T ^ (T.thetaExponent Q x)`. -/
noncomputable def thetaChar (Q : ℕ) (x : K) : MulChar K ℂ :=
  T ^ T.thetaExponent Q x

/-- Defining equation for `MulChar.thetaChar`. -/
theorem thetaChar_def (Q : ℕ) (x : K) :
    T.thetaChar Q x = T ^ T.thetaExponent Q x := (rfl)

/-- Core symmetry for `MulChar.thetaChar`: if `x ^ (Q - 1) = 1`, `N = (Q - 1) * m ≠ 0`, and
`T z = exp (2πi / N) ^ a`, then `T.thetaChar Q x (z ^ m) = (T ^ a) x`. -/
theorem thetaChar_apply_pow (hx : x ^ (Q - 1) = 1) {a N : ℕ} (hN : N ≠ 0)
    (hN_eq : N = (Q - 1) * m) (hTz : T z = exp (2 * Real.pi * I / N) ^ a) :
    T.thetaChar Q x (z ^ m) = (T ^ a) x := by
  have hQ_sub : Q - 1 ≠ 0 := left_ne_zero_of_mul (hN_eq.symm.trans_ne hN)
  have hQ : 2 ≤ Q := by omega
  obtain ⟨x, rfl⟩ : IsUnit x := IsUnit.of_pow_eq_one hx hQ_sub
  obtain ⟨z, rfl⟩ : IsUnit z :=
    T.apply_ne_zero_iff.mp (hTz.trans_ne (pow_ne_zero a (exp_ne_zero _)))
  have hTx := T.apply_eq_exp_pow_thetaExponent hQ hx
  have hm_ne : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (right_ne_zero_of_mul (hN_eq.symm.trans_ne hN))
  rw [thetaChar_def, map_pow, MulChar.pow_apply_coe, MulChar.pow_apply_coe, hTz, hTx, hN_eq]
  have h_exp :
      (m : ℂ) * ((T.thetaExponent Q (x : K) : ℂ) *
          (a * (2 * Real.pi * I / ((Q - 1 : ℕ) * m)))) =
        a * ((T.thetaExponent Q (x : K) : ℂ) * (2 * Real.pi * I / (Q - 1 : ℕ))) := by
    field_simp
  simp only [← exp_nsmul, nsmul_eq_mul, Nat.cast_mul, h_exp]

/-- Symmetry of the root pairing `MulChar.thetaChar`: for `2 ≤ Q` and `(Q - 1)`-th roots of unity
`x, z ∈ K`, `T.thetaChar Q x z = T.thetaChar Q z x`. -/
theorem thetaChar_comm (hQ : 2 ≤ Q) (hx : x ^ (Q - 1) = 1) (hz : z ^ (Q - 1) = 1) :
    T.thetaChar Q x z = T.thetaChar Q z x := by
  have hTz := T.apply_eq_exp_pow_thetaExponent hQ hz
  simpa [thetaChar_def] using
    T.thetaChar_apply_pow hx (Nat.sub_ne_zero_of_lt hQ) (mul_one _).symm hTz

/-- Multiplicativity of `MulChar.thetaChar` in the indexing root: for `2 ≤ Q` and `(Q - 1)`-th
roots of unity `x, y, z ∈ K`,
`T.thetaChar Q (x * y) z = T.thetaChar Q x z * T.thetaChar Q y z`. -/
@[simp]
theorem thetaChar_mul (hQ : 2 ≤ Q) (hx : x ^ (Q - 1) = 1) (hy : y ^ (Q - 1) = 1)
    (hz : z ^ (Q - 1) = 1) :
    T.thetaChar Q (x * y) z = T.thetaChar Q x z * T.thetaChar Q y z := by
  rw [T.thetaChar_comm hQ hx hz, T.thetaChar_comm hQ hy hz,
    T.thetaChar_comm hQ (by rw [mul_pow, hx, hy, one_mul]) hz, map_mul]

/-- Base-change formula for `MulChar.thetaChar`: if `2 ≤ Q`, `r ≠ 0`, `x ^ (Q - 1) = 1`, and
`z ^ (Q ^ r - 1) = 1`, then
`T.thetaChar (Q ^ r) (x ^ a) z = T.thetaChar Q x (z ^ ∑ i ∈ Finset.range r, Q ^ i) ^ a`. -/
theorem thetaChar_eq_apply_norm_pow (hQ : 2 ≤ Q) {r : ℕ} (hr : r ≠ 0) (a : ℕ)
    (hx : x ^ (Q - 1) = 1) (hz : z ^ (Q ^ r - 1) = 1) :
    T.thetaChar (Q ^ r) (x ^ a) z = T.thetaChar Q x (z ^ ∑ i ∈ Finset.range r, Q ^ i) ^ a := by
  have hQr : 2 ≤ Q ^ r := by
    calc 2 ≤ Q := hQ
      _ = Q ^ 1 := (pow_one Q).symm
      _ ≤ Q ^ r := Nat.pow_le_pow_right (by omega) (Nat.one_le_iff_ne_zero.mpr hr)
  have hTz := T.apply_eq_exp_pow_thetaExponent hQr hz
  have hQr_sub : Q ^ r - 1 ≠ 0 := Nat.sub_ne_zero_of_lt hQr
  have h_geom : Q ^ r - 1 = (Q - 1) * ∑ i ∈ Finset.range r, Q ^ i := by
    rw [mul_comm, geom_sum_mul_of_one_le (by omega)]
  have hxa : (x ^ a) ^ (Q ^ r - 1) = 1 := by
    simp [pow_right_comm x a, h_geom, pow_mul, hx]
  rw [T.thetaChar_comm hQr hxa hz, thetaChar_def,
    T.thetaChar_apply_pow hx hQr_sub h_geom hTz, map_pow]

end MulChar
