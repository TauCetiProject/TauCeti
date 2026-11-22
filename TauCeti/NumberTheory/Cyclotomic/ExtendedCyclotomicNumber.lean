/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Norm.Defs
public import TauCeti.NumberTheory.Cyclotomic.CompatibleTower

import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import TauCeti.NumberTheory.Cyclotomic.DistributionRelation
import TauCeti.RingTheory.Norm.Basic

/-!
# The `p`-extended cyclotomic numbers

Fix a compatible cyclotomic tower `(ζ_m)_m` in a field `Ω`, a subfield `K` of `Ω` and a positive
integer `p` (a prime in the applications). For `m ≥ 1` the **`p`-extended cyclotomic number** is
the relative norm
`c_m = N_{K(ζ_{mp})/K(ζ_m)}(1 - ζ_{mp}) ∈ K(ζ_m)`, which Rubin writes with a tilde.
Over `K = ℚ` these are the numbers from which Rubin builds the Euler system of cyclotomic units:
the extra norm from level `mp` makes the family norm-compatible in the `p`-direction. In Rubin's
`ζ - 1` normalization the same norm is `(-1) ^ [K(ζ_{mp}) : K(ζ_m)] * c_m`.

When `Φ_{mp}` is irreducible over `K` (for instance `K = ℚ`), the distribution relation for `1 - ζ`
computes `c_m` at each level:

* if `p ∣ m`, then `c_m = 1 - ζ_m`;
* if `p` is a prime not dividing `m` and `p * p' ≡ 1 [MOD m]`, then
  `c_m * (1 - ζ_m ^ p') = 1 - ζ_m`, so for `m > 1` the number `c_m` is `(1 - ζ_m) ^ (1 - σ_p⁻¹)`;
  this is how the extra norm loses information when `p ∤ m`, and it can make an individual `c_m` a
  root of unity;
* `c_1 = p` for `p` prime.

Under the same irreducibility, the norm of `c_m` down to `K` is `Φ_{mp}(1)`. In particular
`N_{K(ζ_{p^k})/K}(c_{p^k}) = p` for every `k`, so when `K` has characteristic zero none of the
numbers `c_{p^k}` is a root of unity: unlike the torsion numbers `(ζ⁻¹ - 1) / (ζ - 1) = -ζ⁻¹`, the
family `c` is not torsion.

## Main definitions

* `TauCeti.CompatibleCyclotomicTower.extendedCyclotomicNumber`: the number `c_m ∈ K(ζ_m)`.

## Main results

* `TauCeti.CompatibleCyclotomicTower.extendedCyclotomicNumber_of_dvd`: `c_m = 1 - ζ_m` if
  `p ∣ m`.
* `TauCeti.CompatibleCyclotomicTower.extendedCyclotomicNumber_mul_one_sub_pow_of_not_dvd`:
  `c_m * (1 - ζ_m ^ p') = 1 - ζ_m` if `p` is a prime not dividing `m`.
* `TauCeti.CompatibleCyclotomicTower.extendedCyclotomicNumber_one`: `c_1 = p`.
* `TauCeti.CompatibleCyclotomicTower.extendedCyclotomicNumber_ne_zero`: `c_m ≠ 0` unless
  `m = p = 1`.
* `TauCeti.CompatibleCyclotomicTower.norm_zeta_mul_sub_one`: Rubin's normalization
  `N(ζ_{mp} - 1) = (-1) ^ [K(ζ_{mp}) : K(ζ_m)] * c_m`.
* `TauCeti.CompatibleCyclotomicTower.norm_extendedCyclotomicNumber`:
  `N_{K(ζ_m)/K}(c_m) = Φ_{mp}(1)`.
* `TauCeti.CompatibleCyclotomicTower.not_isOfFinOrder_extendedCyclotomicNumber_pow`: `c_{p^k}`
  is not a root of unity.

## References

* K. Rubin, *Euler Systems*, Annals of Mathematics Studies 147, Chapter III, §2.1 and Remark 2.1.
* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*,
  arXiv:2309.15692v2, §10.5.
-/

public section

noncomputable section

open IntermediateField Polynomial

namespace TauCeti.CompatibleCyclotomicTower

variable {Ω : Type*} [Field Ω] (T : CompatibleCyclotomicTower Ω)
variable (K : Type*) [Field K] [Algebra K Ω] (p : ℕ) [NeZero p]

/-- The **`p`-extended cyclotomic number** `c_m = N_{K(ζ_{mp})/K(ζ_m)}(1 - ζ_{mp})` of a compatible
cyclotomic tower, an element of `K(ζ_m)`. Here `K(ζ_{mp})` is a `K(ζ_m)`-algebra through the
inclusion of fields of the tower. -/
def extendedCyclotomicNumber (m : ℕ) [NeZero m] : T.field K m :=
  letI := (inclusion (T.field_le K (dvd_mul_right m p))).toAlgebra
  Algebra.norm (T.field K m) (1 - T.zeta K (m * p))

variable (m : ℕ) [NeZero m]

theorem extendedCyclotomicNumber_def :
    letI := (inclusion (T.field_le K (dvd_mul_right m p))).toAlgebra
    T.extendedCyclotomicNumber K p m = Algebra.norm (T.field K m) (1 - T.zeta K (m * p)) :=
  (rfl)

/-- Inside `K(ζ_{mp})`, the image of `ζ_m` is `ζ_{mp} ^ p`. -/
private theorem algebraMap_zeta :
    letI := (inclusion (T.field_le K (dvd_mul_right m p))).toAlgebra
    algebraMap (T.field K m) (T.field K (m * p)) (T.zeta K m) = T.zeta K (m * p) ^ p := by
  let _ := (inclusion (T.field_le K (dvd_mul_right m p))).toAlgebra
  rw [RingHom.algebraMap_toAlgebra]
  simp [Nat.mul_div_cancel_left p (NeZero.pos m)]

/-- `c_m` is nonzero unless `m = p = 1`, in which case it is `1 - ζ_1 = 0`. -/
theorem extendedCyclotomicNumber_ne_zero (h : m * p ≠ 1) :
    T.extendedCyclotomicNumber K p m ≠ 0 := by
  let _ := (inclusion (T.field_le K (dvd_mul_right m p))).toAlgebra
  have : IsScalarTower K (T.field K m) (T.field K (m * p)) := IsScalarTower.of_algebraMap_eq' rfl
  have : Module.Finite (T.field K m) (T.field K (m * p)) :=
    Module.Finite.of_restrictScalars_finite K _ _
  rw [extendedCyclotomicNumber_def, ne_eq, Algebra.norm_eq_zero_iff, sub_eq_zero]
  refine fun h1 ↦ (T.isPrimitiveRoot_zeta K (m * p)).ne_one ?_ h1.symm
  have := NeZero.ne (m * p)
  omega

/-- **Rubin's normalization.** The relative norm of `ζ_{mp} - 1` is `c_m` up to the sign
`(-1) ^ [K(ζ_{mp}) : K(ζ_m)]`. -/
theorem norm_zeta_mul_sub_one :
    letI := (inclusion (T.field_le K (dvd_mul_right m p))).toAlgebra
    Algebra.norm (T.field K m) (T.zeta K (m * p) - 1) =
      (-1) ^ Module.finrank (T.field K m) (T.field K (m * p)) *
        T.extendedCyclotomicNumber K p m := by
  let _ := (inclusion (T.field_le K (dvd_mul_right m p))).toAlgebra
  rw [← neg_sub, Algebra.norm_neg, extendedCyclotomicNumber_def]

variable {p}

/-- **`c_m` when `p ∣ m`**: if `p` divides `m`, then `c_m = 1 - ζ_m`, provided `Φ_{mp}` is
irreducible over `K`. -/
theorem extendedCyclotomicNumber_of_dvd (hirr : Irreducible (cyclotomic (m * p) K)) (h : p ∣ m) :
    T.extendedCyclotomicNumber K p m = 1 - T.zeta K m := by
  let _ := (inclusion (T.field_le K (dvd_mul_right m p))).toAlgebra
  have : IsScalarTower K (T.field K m) (T.field K (m * p)) := IsScalarTower.of_algebraMap_eq' rfl
  exact (T.isPrimitiveRoot_zeta K (m * p)).norm_one_sub_of_dvd hirr
    (T.algebraMap_zeta K p m) h

/-- **`c_m` when `p ∤ m`**: if the prime `p` does not divide `m` and `p * p' ≡ 1 [MOD m]`, then
`c_m * (1 - ζ_m ^ p') = 1 - ζ_m`, provided `Φ_{mp}` is irreducible over `K`. Here `ζ_m ^ p'` is
the image of `ζ_m` under the inverse of the arithmetic Frobenius at `p`, so for `m > 1` this says
`c_m = (1 - ζ_m) ^ (1 - σ_p⁻¹)`. -/
theorem extendedCyclotomicNumber_mul_one_sub_pow_of_not_dvd [Fact p.Prime]
    (hirr : Irreducible (cyclotomic (m * p) K)) (h : ¬p ∣ m) {p' : ℕ} (hp' : p * p' ≡ 1 [MOD m]) :
    T.extendedCyclotomicNumber K p m * (1 - T.zeta K m ^ p') = 1 - T.zeta K m := by
  let _ := (inclusion (T.field_le K (dvd_mul_right m p))).toAlgebra
  have : IsScalarTower K (T.field K m) (T.field K (m * p)) := IsScalarTower.of_algebraMap_eq' rfl
  exact (T.isPrimitiveRoot_zeta K (m * p)).norm_one_sub_mul_one_sub_pow_of_not_dvd hirr
    (T.algebraMap_zeta K p m) h hp'

/-- **The norm of `c_m` down to `K` is `Φ_{mp}(1)`**, when `Φ_{mp}` is irreducible over `K`. -/
theorem norm_extendedCyclotomicNumber (hirr : Irreducible (cyclotomic (m * p) K)) :
    Algebra.norm K (T.extendedCyclotomicNumber K p m) = (cyclotomic (m * p) K).eval 1 := by
  let _ := (inclusion (T.field_le K (dvd_mul_right m p))).toAlgebra
  have : IsScalarTower K (T.field K m) (T.field K (m * p)) := IsScalarTower.of_algebraMap_eq' rfl
  rw [extendedCyclotomicNumber_def, Algebra.norm_norm,
    (T.isPrimitiveRoot_zeta K (m * p)).norm_one_sub_eq_eval_cyclotomic hirr]

/-- **The conductor-one value** `c_1 = p`, for a prime `p` with `Φ_p` irreducible over `K`. -/
theorem extendedCyclotomicNumber_one [Fact p.Prime] (hirr : Irreducible (cyclotomic p K)) :
    T.extendedCyclotomicNumber K p 1 = p := by
  -- `K(ζ_1) = K`, so `c_1` is the image of its own norm down to `K`, which is `Φ_p(1) = p`.
  obtain ⟨a, ha⟩ : (T.extendedCyclotomicNumber K p 1 : Ω) ∈ (⊥ : IntermediateField K Ω) :=
    T.field_one K ▸ (T.extendedCyclotomicNumber K p 1).property
  have hx : T.extendedCyclotomicNumber K p 1 = algebraMap K (T.field K 1) a := Subtype.ext ha.symm
  have hnorm := T.norm_extendedCyclotomicNumber K 1 (by rwa [one_mul])
  rw [one_mul, eval_one_cyclotomic_prime, hx, Algebra.norm_algebraMap,
    finrank_eq_one_iff.2 (T.field_one K), pow_one] at hnorm
  rw [hx, hnorm, map_natCast]

/-- **The `p`-power cyclotomic numbers have norm `p`**: `N_{K(ζ_{p^k})/K}(c_{p^k}) = p` for every
`k`, for a prime `p` with `Φ_{p^{k+1}}` irreducible over `K`. -/
theorem norm_extendedCyclotomicNumber_pow [Fact p.Prime] (k : ℕ)
    (hirr : Irreducible (cyclotomic (p ^ (k + 1)) K)) :
    Algebra.norm K (T.extendedCyclotomicNumber K p (p ^ k)) = p := by
  rw [T.norm_extendedCyclotomicNumber K _ (by rwa [← pow_succ]), ← pow_succ,
    eval_one_cyclotomic_prime_pow]

/-- **The cyclotomic family is not torsion**: when `K` has characteristic zero, no `c_{p^k}` is a
root of unity, since its norm down to `K` is `p`. In contrast, an individual `c_m` with `p ∤ m`
can be a root of unity. -/
theorem not_isOfFinOrder_extendedCyclotomicNumber_pow [CharZero K] [Fact p.Prime] (k : ℕ)
    (hirr : Irreducible (cyclotomic (p ^ (k + 1)) K)) :
    ¬IsOfFinOrder (T.extendedCyclotomicNumber K p (p ^ k)) := by
  intro h
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  have := congrArg (Algebra.norm K) hpow
  rw [map_pow, map_one, T.norm_extendedCyclotomicNumber_pow K k hirr, ← Nat.cast_pow,
    Nat.cast_eq_one, Nat.pow_eq_one] at this
  have := (Fact.out : p.Prime).one_lt
  omega

end TauCeti.CompatibleCyclotomicTower

/-! For `p = 3`, `c_1 = 3`; for `p = 5`, `c_5 = 1 - ζ_5` and `c_3 = -ζ_3`, a root of unity. -/

section Examples

variable {Ω : Type*} [Field Ω] [CharZero Ω] (T : TauCeti.CompatibleCyclotomicTower Ω)

example : T.extendedCyclotomicNumber ℚ 3 1 = 3 :=
  T.extendedCyclotomicNumber_one ℚ (cyclotomic.irreducible_rat (by norm_num))

example : T.extendedCyclotomicNumber ℚ 5 5 = 1 - T.zeta ℚ 5 :=
  T.extendedCyclotomicNumber_of_dvd ℚ 5 (cyclotomic.irreducible_rat (by norm_num)) dvd_rfl

example : T.extendedCyclotomicNumber ℚ 5 3 = -T.zeta ℚ 3 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h := T.extendedCyclotomicNumber_mul_one_sub_pow_of_not_dvd ℚ (p := 5) 3
    (cyclotomic.irreducible_rat (by norm_num)) (by norm_num) (p' := 2) (by decide)
  have hζ := T.isPrimitiveRoot_zeta ℚ 3
  have hne : 1 - T.zeta ℚ 3 ≠ 0 := sub_ne_zero.2 (hζ.ne_one (by norm_num)).symm
  apply mul_right_cancel₀ hne
  -- Multiply `c_3 * (1 - ζ_3 ^ 2) = 1 - ζ_3` by `-ζ_3` and use `ζ_3 ^ 3 = 1`.
  linear_combination (-T.zeta ℚ 3) * h - T.extendedCyclotomicNumber ℚ 5 3 * hζ.pow_eq_one

end Examples
