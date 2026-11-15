/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Harmonic

/-!
# The Euler derivation on multivariate polynomials

The **Euler derivation** `MvPolynomial.euler` on `MvPolynomial σ R` is the unique `R`-derivation
sending each variable `X i` to itself (`mkDerivation R X`). For finitely many variables `σ`, it
equals `∑ᵢ Xᵢ ∂/∂Xᵢ`.

On any index type `σ`, `euler` multiplies each monomial `monomial s a` by its total degree
`s.degree`, acts on each homogeneous submodule `P_d` as scalar multiplication by `d`, and commutes
with `homogeneousComponent`. When `σ` is finite, it satisfies the commutation relation
`Δ (E p) = E (Δ p) + 2 Δ p` with the polynomial Laplacian `Δ = ∑ᵢ ∂²/∂Xᵢ²`.

## Main definitions

* `MvPolynomial.euler`: the Euler derivation `mkDerivation R X` on `MvPolynomial σ R`.

## Main results

* `MvPolynomial.euler_monomial`: `euler (monomial s a) = s.degree • monomial s a`.
* `MvPolynomial.IsHomogeneous.euler_eq`: `euler p = d • p` for `p` homogeneous of degree `d`.
* `MvPolynomial.homogeneousComponent_euler`:
  `homogeneousComponent d (euler p) = d • homogeneousComponent d p`.
* `MvPolynomial.euler_apply_fintype`: for `[Fintype σ]`, `euler p = ∑ᵢ Xᵢ * pderiv i p`.
* `MvPolynomial.laplacian_euler`: `laplacian (euler p) = euler (laplacian p) + 2 • laplacian p`.

## References

* S. Axler, P. Bourdon and W. Ramey, *Harmonic Function Theory*, 2nd ed., Springer GTM 137
  (2001), Chapter 5.
-/

public section

namespace MvPolynomial

section General

variable {σ R : Type*} [CommSemiring R]

/-- The **Euler derivation** on `MvPolynomial σ R`: the unique `R`-derivation sending every
variable `X i` to `X i`. For `[Fintype σ]`, `euler p = ∑ i, X i * pderiv i p`
(`MvPolynomial.euler_apply_fintype`). -/
noncomputable def euler : Derivation R (MvPolynomial σ R) (MvPolynomial σ R) :=
  mkDerivation R (X : σ → MvPolynomial σ R)

theorem euler_def :
    (euler : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) =
      mkDerivation R (X : σ → MvPolynomial σ R) :=
  (rfl)

@[simp]
theorem euler_X (i : σ) : euler (X i : MvPolynomial σ R) = X i :=
  mkDerivation_X R (X : σ → MvPolynomial σ R) i

@[simp]
theorem euler_eq_zero_of_isEmpty [IsEmpty σ] :
    (euler : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) = 0 := by
  ext i
  exact IsEmpty.elim ‹IsEmpty σ› i

theorem euler_mul (p q : MvPolynomial σ R) :
    euler (p * q) = p * euler q + q * euler p :=
  euler.leibniz p q

/-- The Euler derivation multiplies each monomial `monomial s a` by its total degree `s.degree`. -/
@[simp]
theorem euler_monomial (s : σ →₀ ℕ) (a : R) :
    euler (monomial s a) = s.degree • monomial s a := by
  classical
  rw [euler_def, mkDerivation_monomial, Finsupp.degree_apply, Finset.sum_smul]
  simp only [Finsupp.sum, Finset.smul_sum, smul_eq_mul]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have his : 1 ≤ s i := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
  rw [X, monomial_mul_monomial, mul_one, smul_monomial, smul_eq_mul, mul_comm,
    ← nsmul_eq_mul, ← smul_monomial]
  suffices h : s - Finsupp.single i 1 + Finsupp.single i 1 = s by rw [h]
  ext j
  by_cases hj : j = i
  · subst hj; simp; omega
  · simp [hj]

/-- **Euler's homogeneous identity** for `MvPolynomial.euler`: on a homogeneous polynomial of
degree `d`, `euler p = d • p`. -/
theorem IsHomogeneous.euler_eq {p : MvPolynomial σ R} {d : ℕ} (hp : p.IsHomogeneous d) :
    euler p = d • p := by
  classical
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  have hsdeg : s.degree = d := by
    simpa [Finsupp.degree_apply, Finsupp.weight_apply, Finsupp.sum] using
      hp (mem_support_iff.mp hs)
  rw [euler_monomial, hsdeg]

/-- The Euler derivation preserves homogeneity of every degree. -/
protected theorem IsHomogeneous.euler {p : MvPolynomial σ R} {d : ℕ} (hp : p.IsHomogeneous d) :
    (euler p).IsHomogeneous d := by
  rw [hp.euler_eq, ← mem_homogeneousSubmodule]
  exact (homogeneousSubmodule σ R d).toAddSubmonoid.nsmul_mem hp d

/-- On the degree-`d` homogeneous component of any polynomial, `euler` acts as multiplication by
`d`. -/
@[simp]
theorem homogeneousComponent_euler (d : ℕ) (p : MvPolynomial σ R) :
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
  · intro hd
    rw [homogeneousComponent_eq_zero d p (by simpa using hd)]
    simp

end General

section Fintype

variable {σ R : Type*} [CommSemiring R] [Fintype σ]

/-- For finitely many variables, the Euler derivation is `∑ᵢ Xᵢ ∂ᵢ`. -/
theorem euler_eq_sum :
    (euler : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) =
      ∑ i : σ, (X i : MvPolynomial σ R) • pderiv i := by
  classical
  ext j
  simp [pderiv_X, Pi.single_apply]

/-- Coordinate expansion of the Euler derivation in finitely many variables:
`euler p = ∑ᵢ Xᵢ * pderiv i p`. -/
theorem euler_apply_fintype (p : MvPolynomial σ R) :
    euler p = ∑ i : σ, X i * pderiv i p := by
  rw [euler_eq_sum]
  simp

/-- The Euler derivation multiplies `normSq σ R = ∑ᵢ Xᵢ²` by `2`. -/
@[simp]
theorem euler_normSq : euler (normSq σ R) = 2 • normSq σ R :=
  (isHomogeneous_normSq σ R).euler_eq

/-- **Commutation of the Laplacian and the Euler derivation**: `Δ (E p) = E (Δ p) + 2 Δ p`. -/
theorem laplacian_euler (p : MvPolynomial σ R) :
    laplacian (euler p) = euler (laplacian p) + 2 • laplacian p := by
  conv_lhs => rw [← sum_homogeneousComponent p]
  conv_rhs => rw [← sum_homogeneousComponent p]
  simp only [map_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  set q := homogeneousComponent d p
  have hq : q.IsHomogeneous d := homogeneousComponent_isHomogeneous d p
  rcases lt_or_ge d 2 with hd | hd
  · have hΔ : laplacian q = 0 := hq.laplacian_eq_zero_of_le_one (by omega)
    rw [hq.euler_eq, map_nsmul, hΔ, map_zero, smul_zero, smul_zero, zero_add]
  · rw [hq.euler_eq, map_nsmul, hq.laplacian.euler_eq, ← add_smul]
    congr 1
    omega

end Fintype

end MvPolynomial
