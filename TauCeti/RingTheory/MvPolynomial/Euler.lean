/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Harmonic

/-!
# The Euler derivation on multivariate polynomials

The **Euler derivation** `MvPolynomial.euler` on `MvPolynomial σ R` is `mkDerivation R X`, sending
each variable `X i` to itself. It multiplies `monomial s a` by `s.degree`, acts as `d • ·` on
degree-`d` homogeneous polynomials, commutes with `homogeneousComponent`, agrees with
`∑ᵢ Xᵢ * pderiv i` for `[Fintype σ]`, and satisfies `Δ (E p) = E (Δ p) + 2 • Δ p`.

## Main definitions

* `MvPolynomial.euler`: the Euler derivation `mkDerivation R X` on `MvPolynomial σ R`.

## Main results

* `MvPolynomial.euler_monomial`, `MvPolynomial.IsHomogeneous.euler_eq`,
  `MvPolynomial.homogeneousComponent_euler`, `MvPolynomial.euler_apply_fintype`, and
  `MvPolynomial.laplacian_euler`.

## References

* S. Axler, P. Bourdon and W. Ramey, *Harmonic Function Theory*, 2nd ed., Springer (2001), Ch. 5.
-/

public section

namespace MvPolynomial

section General

variable {σ R : Type*} [CommSemiring R]

/-- The **Euler derivation** on `MvPolynomial σ R`, sending each `X i` to `X i`. -/
noncomputable def euler : Derivation R (MvPolynomial σ R) (MvPolynomial σ R) :=
  mkDerivation R (X : σ → MvPolynomial σ R)

theorem euler_def :
    (euler : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) =
      mkDerivation R (X : σ → MvPolynomial σ R) := (rfl)

@[simp] theorem euler_X (i : σ) : euler (X i : MvPolynomial σ R) = X i :=
  mkDerivation_X R (X : σ → MvPolynomial σ R) i

@[simp] theorem euler_eq_zero_of_isEmpty [IsEmpty σ] :
    (euler : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) = 0 := by
  ext i; exact IsEmpty.elim ‹IsEmpty σ› i

theorem euler_mul (p q : MvPolynomial σ R) : euler (p * q) = p * euler q + q * euler p :=
  euler.leibniz p q

/-- The Euler derivation multiplies `monomial s a` by its total degree `s.degree`. -/
@[simp] theorem euler_monomial (s : σ →₀ ℕ) (a : R) :
    euler (monomial s a) = s.degree • monomial s a := by
  classical
  rw [euler_def, mkDerivation_monomial, Finsupp.degree_apply, Finset.sum_smul]
  simp only [Finsupp.sum, Finset.smul_sum, smul_eq_mul]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have h : s - Finsupp.single i 1 + Finsupp.single i 1 = s := tsub_add_cancel_of_le
    (Finsupp.single_le_iff.mpr (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)))
  rw [X, monomial_mul_monomial, mul_one, h, smul_monomial, smul_eq_mul, mul_comm, ← nsmul_eq_mul,
    ← smul_monomial]

/-- **Euler's homogeneous identity**: if `p` is homogeneous of degree `d`, `euler p = d • p`. -/
theorem IsHomogeneous.euler_eq {p : MvPolynomial σ R} {d : ℕ} (hp : p.IsHomogeneous d) :
    euler p = d • p := by
  classical
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  rw [euler_monomial, Finsupp.degree_eq_weight_one]
  exact congrArg (· • _) (hp (mem_support_iff.mp hs))

protected theorem IsHomogeneous.euler {p : MvPolynomial σ R} {d : ℕ} (hp : p.IsHomogeneous d) :
    (euler p).IsHomogeneous d := by
  rw [hp.euler_eq, ← mem_homogeneousSubmodule]
  exact (homogeneousSubmodule σ R d).toAddSubmonoid.nsmul_mem hp d

@[simp] theorem homogeneousComponent_euler (d : ℕ) (p : MvPolynomial σ R) :
    homogeneousComponent d (euler p) = d • homogeneousComponent d p := by
  conv_lhs => rw [← sum_homogeneousComponent p]
  simp only [map_sum]
  rw [Finset.sum_eq_single d]
  · rw [(homogeneousComponent_isHomogeneous d p).euler_eq, map_nsmul,
      homogeneousComponent_eq_self (homogeneousComponent_isHomogeneous d p)]
  · intro i _ hi
    rw [(homogeneousComponent_isHomogeneous i p).euler_eq, map_nsmul,
      homogeneousComponent_of_mem (homogeneousComponent_isHomogeneous i p),
      ite_eq_right_iff.mpr fun h ↦ (hi h.symm).elim, smul_zero]
  · intro hd; simp [homogeneousComponent_eq_zero d p (by simpa using hd)]

end General

section Fintype

variable {σ R : Type*} [CommSemiring R] [Fintype σ]

/-- Over a finite variable type, the Euler derivation is `∑ᵢ Xᵢ ∂ᵢ`. -/
theorem euler_eq_sum :
    (euler : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) =
      ∑ i : σ, (X i : MvPolynomial σ R) • pderiv i := by
  classical ext j; simp [pderiv_X, Pi.single_apply]

/-- Coordinate expansion of the Euler derivation in finitely many variables. -/
theorem euler_apply_fintype (p : MvPolynomial σ R) : euler p = ∑ i : σ, X i * pderiv i p := by
  rw [euler_eq_sum]; simp

@[simp] theorem euler_normSq : euler (normSq σ R) = 2 • normSq σ R :=
  (isHomogeneous_normSq σ R).euler_eq

/-- **Commutation of the Laplacian and the Euler derivation**: `Δ (E p) = E (Δ p) + 2 • Δ p`. -/
theorem laplacian_euler (p : MvPolynomial σ R) :
    laplacian (euler p) = euler (laplacian p) + 2 • laplacian p := by
  conv_lhs => rw [← sum_homogeneousComponent p]
  conv_rhs => rw [← sum_homogeneousComponent p]
  simp only [map_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  have hq := homogeneousComponent_isHomogeneous d p
  rcases lt_or_ge d 2 with hd | hd
  · rw [hq.euler_eq, map_nsmul, hq.laplacian_eq_zero_of_le_one (by omega)]; simp
  · rw [hq.euler_eq, map_nsmul, hq.laplacian.euler_eq, ← add_smul]
    exact congrArg (· • _) (by omega)

end Fintype

end MvPolynomial
