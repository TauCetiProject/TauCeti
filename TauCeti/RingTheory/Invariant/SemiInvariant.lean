/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Ring.Divisibility.Lemmas

/-!
# Vanishing orders of semi-invariants along a fixed divisor

Suppose an algebra endomorphism `σ` is the identity modulo a principal ideal `(x)` and
sends the nonzerodivisor `x` to `ζ • x`, where `ζ` is a primitive `e`-th root of unity.
An element transforming by `ζ ^ a`, with `a < e`, is divisible by `x ^ a`. The inverse normal
character forces divisibility by `x ^ (e - 1)`.

This formulation works directly in an algebra, without choosing polynomial coordinates
along the divisor. It applies to the determinant semi-invariant given by the Jacobian of
invariant polynomials. The coefficient field can have arbitrary characteristic; the
primitive-root hypothesis specifies the actual normal character.

## References

* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge (1990), Chapter 3.
* R. Kane, *Reflection Groups and Invariant Theory*, Springer (2001), §18.
-/

public section

namespace AlgHom

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

/-- If `σ` is the identity modulo `(x)`, scales the nonzerodivisor `x` by a primitive
`e`-th root `ζ`, and scales `p` by `ζ ^ a` with `a < e`, then `x ^ a` divides `p`. -/
theorem pow_dvd_of_apply_eq_pow_smul (σ : A →ₐ[K] A) {x : A} (hx : IsLeftRegular x)
    {ζ : K} {e a : ℕ} (hζ : IsPrimitiveRoot ζ e) (ha : a < e)
    (hσ : ∀ q, x ∣ q - σ q) (hσx : σ x = ζ • x)
    {p : A} (hp : σ p = ζ ^ a • p) : x ^ a ∣ p := by
  induction a generalizing p with
  | zero => simp
  | succ a ih =>
    have he : 0 < e := (Nat.zero_le _).trans_lt ha
    have hz : ζ ≠ 0 := (hζ.isUnit he.ne').ne_zero
    have hpow : 1 - ζ ^ (a + 1) ≠ 0 := by
      rw [sub_ne_zero]
      exact Ne.symm (((IsPrimitiveRoot.iff he).1 hζ).2 (a + 1) (by omega) ha)
    have hdvd : x ∣ p := by
      have h := hσ p
      have hdiff : p - σ p = (1 - ζ ^ (a + 1)) • p := by
        rw [hp, sub_smul, one_smul]
      rw [hdiff] at h
      simpa [hpow] using dvd_smul_of_dvd (1 - ζ ^ (a + 1))⁻¹ h
    obtain ⟨q, rfl⟩ := hdvd
    have hq : σ q = ζ ^ a • q := by
      apply hx
      apply smul_right_injective A hz
      simpa only [map_mul, hσx, smul_mul_assoc, mul_smul_comm, smul_smul, pow_succ']
        using hp
    obtain ⟨r, hr⟩ := ih (by omega) hq
    exact ⟨r, by rw [hr, pow_succ']; ac_rfl⟩

/-- An inverse normal character semi-invariant vanishes to order at least `e - 1`
along the divisor fixed by `σ`. -/
theorem pow_sub_one_dvd_of_smul_apply_eq (σ : A →ₐ[K] A) {x : A} (hx : IsLeftRegular x)
    {ζ : K} {e : ℕ} (he : 0 < e) (hζ : IsPrimitiveRoot ζ e)
    (hσ : ∀ q, x ∣ q - σ q) (hσx : σ x = ζ • x)
    {p : A} (hp : ζ • σ p = p) : x ^ (e - 1) ∣ p := by
  apply σ.pow_dvd_of_apply_eq_pow_smul hx hζ (Nat.sub_lt he one_pos) hσ hσx
  have hz : ζ ≠ 0 := (hζ.isUnit he.ne').ne_zero
  apply (smul_right_injective A hz)
  have hpow : ζ * ζ ^ (e - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel he, hζ.pow_eq_one]
  simpa only [smul_smul, hpow, one_smul] using hp

end AlgHom
