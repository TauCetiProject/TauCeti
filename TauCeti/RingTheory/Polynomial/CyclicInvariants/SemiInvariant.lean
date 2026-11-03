/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.CyclicInvariants.Basic
import Mathlib.Algebra.Polynomial.Div

/-!
# Semi-invariants in a cyclic normal coordinate

Let `ζ` be a primitive `e`-th root of unity in a domain. A polynomial transforming by
`ζ ^ a` under `X ↦ ζ X`, with `a < e`, has a unique expression `X ^ a * q(X ^ e)`.
Its coefficients are supported in the residue class `a` modulo `e`.

For the inverse character this gives the factor `X ^ (e - 1)`. Applied with coefficients
in the coordinates along a reflecting hyperplane, this is the local divisibility statement
for a polynomial transforming by the inverse normal character, such as a Jacobian.
It does not assume that the cyclic action is an involution. No characteristic-zero or
field assumption is needed beyond the specified primitive root in a domain.

## References

* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge (1990), §3.5.
* R. Kane, *Reflection Groups and Invariant Theory*, Springer (2001), §18.

The invariant factor uses `Polynomial.comp_C_mul_X_eq_self_iff_existsUnique` and Mathlib's
`Polynomial.expand`; no separate invariant algebra is introduced.
-/

public section

namespace Polynomial

variable {R : Type*} [CommSemiring R] [IsDomain R] {e a : ℕ} {ζ : R}

/-- A semi-invariant for the character `ζ ^ a` has coefficients only in degrees congruent
to `a` modulo `e`, and this support condition also suffices for semi-invariance. -/
theorem comp_C_mul_X_eq_C_pow_mul_iff (p : R[X]) (he : 0 < e)
    (hζ : IsPrimitiveRoot ζ e) :
    p.comp (C ζ * X) = C (ζ ^ a) * p ↔
      ∀ n, n % e ≠ a % e → p.coeff n = 0 := by
  have hpow (n : ℕ) : ζ ^ n = ζ ^ a ↔ n % e = a % e := by
    rw [hζ.eq_orderOf]
    exact (hζ.isOfFinOrder he.ne').pow_inj_mod
  constructor
  · intro hp n hn
    have hc := congrArg (fun q : R[X] ↦ q.coeff n) hp
    rw [comp_C_mul_X_coeff, coeff_C_mul, mul_comm (ζ ^ a)] at hc
    exact (mul_eq_mul_left_iff.1 hc).resolve_left (fun h ↦ hn ((hpow n).1 h))
  · intro hp
    ext n
    rw [comp_C_mul_X_coeff, coeff_C_mul, mul_comm (ζ ^ a)]
    by_cases hn : n % e = a % e
    · rw [(hpow n).2 hn]
    · rw [hp n hn, zero_mul, zero_mul]

/-- If `p(ζX) = ζ ^ a * p(X)` for a primitive `e`-th root `ζ` and `a < e`, then
`X ^ a` divides `p`: the order of vanishing in the normal coordinate is at least `a`. -/
theorem X_pow_dvd_of_comp_C_mul_X_eq_C_pow_mul (p : R[X]) (ha : a < e)
    (hζ : IsPrimitiveRoot ζ e) (hp : p.comp (C ζ * X) = C (ζ ^ a) * p) :
    X ^ a ∣ p := by
  apply X_pow_dvd_iff.2
  intro n hn
  apply (p.comp_C_mul_X_eq_C_pow_mul_iff ((Nat.zero_le a).trans_lt ha) hζ).1 hp n
  rw [Nat.mod_eq_of_lt (hn.trans ha), Nat.mod_eq_of_lt ha]
  exact hn.ne

/-- A cyclic semi-invariant is uniquely a power of the normal coordinate times a
polynomial in `X ^ e`. This includes the trivial character and the trivial cyclic group. -/
theorem comp_C_mul_X_eq_C_pow_mul_iff_existsUnique (p : R[X]) (ha : a < e)
    (hζ : IsPrimitiveRoot ζ e) :
    p.comp (C ζ * X) = C (ζ ^ a) * p ↔
      ∃! q : R[X], X ^ a * expand R e q = p := by
  have he : 0 < e := (Nat.zero_le a).trans_lt ha
  have hz : IsLeftRegular (C (ζ ^ a) * (X ^ a : R[X])) :=
    (((hζ.isUnit he.ne').pow a).map C).isRegular.left.mul (isRegular_X_pow a).left
  constructor
  · intro hp
    obtain ⟨r, hr⟩ := p.X_pow_dvd_of_comp_C_mul_X_eq_C_pow_mul ha hζ hp
    have hrfix : r.comp (C ζ * X) = r := by
      rw [hr, mul_comp, pow_comp, X_comp, mul_pow] at hp
      apply hz
      simpa only [← C_pow, mul_assoc, mul_left_comm, mul_comm] using hp
    obtain ⟨q, hq, huniq⟩ :=
      (r.comp_C_mul_X_eq_self_iff_existsUnique he hζ).1 hrfix
    refine ⟨q, (congrArg (X ^ a * ·) hq).trans hr.symm, fun q' hq' ↦ ?_⟩
    apply huniq
    exact (isRegular_X_pow a).left (hq'.trans hr)
  · rintro ⟨q, rfl, -⟩
    have hq : (expand R e q).comp (C ζ * X) = expand R e q :=
      (comp_C_mul_X_eq_self_iff_existsUnique _ he hζ).2
        ⟨q, rfl, fun q' hq' ↦ expand_injective he hq'⟩
    simp only [mul_comp, pow_comp, X_comp, mul_pow, hq, C_pow, mul_assoc]

/-- A polynomial transforming by the inverse normal character is uniquely
`X ^ (e - 1)` times a polynomial in `X ^ e`. In particular `X ^ (e - 1)` divides `p`. -/
theorem C_mul_comp_C_mul_X_eq_self_iff_existsUnique (p : R[X]) (he : 0 < e)
    (hζ : IsPrimitiveRoot ζ e) :
    C ζ * p.comp (C ζ * X) = p ↔
      ∃! q : R[X], X ^ (e - 1) * expand R e q = p := by
  rw [← comp_C_mul_X_eq_C_pow_mul_iff_existsUnique p (Nat.sub_lt he one_pos) hζ]
  have hz : C ζ * C (ζ ^ (e - 1)) = (1 : R[X]) := by
    rw [← C_mul, ← pow_succ', Nat.sub_add_cancel he, hζ.pow_eq_one, C_1]
  constructor
  · intro hp
    calc
      p.comp (C ζ * X) = (C ζ * C (ζ ^ (e - 1))) * p.comp (C ζ * X) := by rw [hz, one_mul]
      _ = C (ζ ^ (e - 1)) * p := by rw [mul_comm (C ζ), mul_assoc, hp]
  · intro hp
    rw [hp, ← mul_assoc, hz, one_mul]

end Polynomial
