/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import TauCeti.Algebra.Algebra.Frobenius.Basic

/-!
# `R[X]/(g)` is a symmetric Frobenius algebra

Let `g` be a monic polynomial of degree `d` over a commutative ring `R`. The quotient
`AdjoinRoot g = R[X]/(g)` is free over `R` with power basis `1, x, …, x ^ (d - 1)`, where `x` is
the class of `X`. This file shows that the last coordinate in that basis, the coefficient of
`x ^ (d - 1)`, is a symmetric Frobenius functional on `R[X]/(g)`. No hypothesis on `R` (such as
being a field, or its characteristic) is needed.

The main example is the truncated polynomial algebra `k[x]/(x ^ n)`, where the functional is the
coefficient of `x ^ (n - 1)`. Over a field it is the basic example of a symmetric Frobenius
algebra that is not semisimple (for `n ≥ 2`), and so, being self-injective, the basic example of
an algebra whose finite-dimensional modules form a Frobenius exact category with a nontrivial
stable category.

## Main definitions

* `AdjoinRoot.lastCoeff`: the coefficient of `x ^ (d - 1)` in the power basis of `R[X]/(g)`, as a
  linear functional.

## Main results

* `AdjoinRoot.isSymmetricFrobeniusFunctional_lastCoeff`: `AdjoinRoot.lastCoeff` is a symmetric
  Frobenius functional.
* `AdjoinRoot.isSymmetricFrobeniusFunctional_lastCoeff_X_pow`: the coefficient of `x ^ (n - 1)`
  is a symmetric Frobenius functional on `R[X]/(X ^ n)`.

## References

* A. Skowroński, K. Yamagata, *Frobenius algebras I*, Chapter IV, Section 2 (Frobenius algebras
  and their examples).
-/

public section

namespace TauCeti

open Polynomial

variable {R : Type*} [CommRing R] {g : R[X]}

/-- For a monic polynomial `g` of degree `d`, the coefficient of `x ^ (d - 1)` in the power basis
`1, x, …, x ^ (d - 1)` of `R[X]/(g)`, where `x = AdjoinRoot.root g`: it sends the class of `p` to
the coefficient of `X ^ (d - 1)` in the remainder `p %ₘ g`. -/
noncomputable def _root_.AdjoinRoot.lastCoeff (hg : g.Monic) : AdjoinRoot g →ₗ[R] R :=
  lcoeff R (g.natDegree - 1) ∘ₗ AdjoinRoot.modByMonicHom hg

/-- The value of `AdjoinRoot.lastCoeff` on the class of a polynomial `p`. -/
@[simp]
theorem _root_.AdjoinRoot.lastCoeff_mk (hg : g.Monic) (p : R[X]) :
    AdjoinRoot.lastCoeff hg (AdjoinRoot.mk g p) = (p %ₘ g).coeff (g.natDegree - 1) := by
  simp [AdjoinRoot.lastCoeff]

/-- On the basis vectors `x ^ i` with `i < d`, `AdjoinRoot.lastCoeff` is `1` at `x ^ (d - 1)`
and `0` elsewhere. -/
theorem _root_.AdjoinRoot.lastCoeff_root_pow (hg : g.Monic) {i : ℕ} (hi : i < g.natDegree) :
    AdjoinRoot.lastCoeff hg (AdjoinRoot.root g ^ i) = if i + 1 = g.natDegree then 1 else 0 := by
  nontriviality R
  have hdeg : (X ^ i : R[X]).degree < g.degree := by
    rw [degree_X_pow, degree_eq_natDegree hg.ne_zero]
    exact_mod_cast hi
  rw [← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.lastCoeff_mk, (modByMonic_eq_self_iff hg).mpr hdeg,
    coeff_X_pow]
  grind

/-- `AdjoinRoot.lastCoeff` is the last coordinate in the power basis `AdjoinRoot.powerBasis'`. -/
theorem _root_.AdjoinRoot.lastCoeff_eq_repr (hg : g.Monic) (hd : 0 < g.natDegree)
    (a : AdjoinRoot g) :
    AdjoinRoot.lastCoeff hg a =
      (AdjoinRoot.powerBasis' hg).basis.repr a ⟨g.natDegree - 1, Nat.sub_one_lt_of_lt hd⟩ := by
  -- Both sides are linear in `a`; compare them on the basis vectors `x ^ j`.
  have : AdjoinRoot.lastCoeff hg = Finsupp.lapply ⟨g.natDegree - 1, Nat.sub_one_lt_of_lt hd⟩ ∘ₗ
      (AdjoinRoot.powerBasis' hg).basis.repr.toLinearMap :=
    (AdjoinRoot.powerBasis' hg).basis.ext fun j => by
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self, Finsupp.lapply_apply,
        Finsupp.single_apply, PowerBasis.coe_basis, AdjoinRoot.powerBasis'_gen,
        AdjoinRoot.lastCoeff_root_pow hg j.isLt]
      simp only [Fin.ext_iff]
      grind
  rw [this, LinearMap.comp_apply, Finsupp.lapply_apply, LinearEquiv.coe_coe]

/-- An element `a` with `lastCoeff (a * b) = 0` for every `b` is zero. -/
private theorem eq_zero_of_forall_lastCoeff_mul (hg : g.Monic) {a : AdjoinRoot g}
    (h : ∀ b, AdjoinRoot.lastCoeff hg (a * b) = 0) : a = 0 := by
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective a
  -- Replace `q` by its remainder `p`, whose degree is less than that of `g`.
  have hq : AdjoinRoot.mk g (q %ₘ g) = AdjoinRoot.mk g q := by
    simpa using AdjoinRoot.mk_leftInverse hg (AdjoinRoot.mk g q)
  rw [← hq] at h ⊢
  set p := q %ₘ g
  -- If `p ≠ 0` has degree `e < d`, pairing it with `x ^ k`, `k = d - 1 - e`, gives its leading
  -- coefficient.
  by_contra ha
  have hp : p ≠ 0 := fun hp => ha (by rw [hp, map_zero])
  have : Nontrivial R := nontrivial_iff.mp (nontrivial_of_ne p 0 hp)
  have hlt : p.natDegree < g.natDegree := natDegree_lt_natDegree hp (degree_modByMonic_lt q hg)
  obtain ⟨k, hk⟩ : ∃ k, p.natDegree + k = g.natDegree - 1 := ⟨_, Nat.add_sub_of_le (by omega)⟩
  -- The product `p * X ^ k` has degree `d - 1 < d`, so it is its own remainder.
  have hpk : (p * X ^ k) %ₘ g = p * X ^ k := by
    rw [modByMonic_eq_self_iff hg]
    exact degree_lt_degree (by rw [natDegree_mul_X_pow k hp]; omega)
  have := h (AdjoinRoot.mk g (X ^ k))
  rw [← map_mul, AdjoinRoot.lastCoeff_mk, hpk, ← hk, coeff_mul_X_pow, coeff_natDegree] at this
  exact leadingCoeff_ne_zero.mpr hp this

/-- For a monic polynomial `g` of degree `d` over a commutative ring, the coefficient of
`x ^ (d - 1)` in the power basis is a symmetric Frobenius functional on `R[X]/(g)`. -/
theorem _root_.AdjoinRoot.isSymmetricFrobeniusFunctional_lastCoeff (hg : g.Monic) :
    (AdjoinRoot.lastCoeff hg).IsSymmetricFrobeniusFunctional where
  isFrobeniusFunctional := LinearMap.isFrobeniusFunctional_iff.mpr
    ⟨fun _ => eq_zero_of_forall_lastCoeff_mul hg,
      fun _ h => eq_zero_of_forall_lastCoeff_mul hg fun a => by rw [mul_comm]; exact h a⟩
  apply_mul_comm a b := by rw [mul_comm]

/-! ### The truncated polynomial algebra `R[X]/(X ^ n)` -/

/-- On `R[X]/(X ^ n)`, `AdjoinRoot.lastCoeff` extracts the coefficient of `x ^ (n - 1)`: it is
`1` on `x ^ (n - 1)` and `0` on every other power of `x`. -/
@[simp]
theorem _root_.AdjoinRoot.lastCoeff_X_pow_root_pow (n i : ℕ) :
    AdjoinRoot.lastCoeff (monic_X_pow n) (AdjoinRoot.root (X ^ n : R[X]) ^ i) =
      if i + 1 = n then 1 else 0 := by
  nontriviality R
  rcases lt_or_ge i n with hi | hi
  · rw [AdjoinRoot.lastCoeff_root_pow _ (by rwa [natDegree_X_pow]), natDegree_X_pow]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
    rw [pow_add, ← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.mk_self, zero_mul, map_zero]
    grind

/-- **The truncated polynomial algebra `R[X]/(X ^ n)` is a symmetric Frobenius algebra**: the
coefficient of `x ^ (n - 1)` is a symmetric Frobenius functional on it, over any commutative
ring `R`. -/
theorem _root_.AdjoinRoot.isSymmetricFrobeniusFunctional_lastCoeff_X_pow (n : ℕ) :
    (AdjoinRoot.lastCoeff (monic_X_pow n : (X ^ n : R[X]).Monic)).IsSymmetricFrobeniusFunctional :=
  AdjoinRoot.isSymmetricFrobeniusFunctional_lastCoeff _

end TauCeti
