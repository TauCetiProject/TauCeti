/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Algebra.Module.Rat
public import TauCeti.RingTheory.MvPolynomial.Homogeneous

/-!
# The Poincaré lemma for polynomial vector fields

A family `P : σ → R[X_σ]` of polynomials in finitely many variables is a gradient field
`Pᵢ = ∂ᵢ Q` exactly when it satisfies the symmetry condition `∂ⱼ Pᵢ = ∂ᵢ Pⱼ`, provided the
coefficients form a `ℚ`-algebra. Moreover a symmetric family of polynomials of total degree at
most `m` has a potential of total degree at most `m + 1`.

This is the algebraic step in identifying the Sobolev functions whose derivatives of order
`m + 1` vanish with the polynomials of degree at most `m`: the first derivatives of such a
function are polynomials of degree at most `m - 1` satisfying the symmetry condition, and a
potential of degree at most `m` reduces the claim to a function with vanishing gradient.

The argument is the one with homogeneous components and Euler's identity
(`MvPolynomial.IsHomogeneous.sum_X_mul_pderiv`), the polynomial case of the homotopy formula in
the proof of the Poincaré lemma for closed differential forms. When `Pⱼ` is homogeneous of
degree `d` and `∂ⱼ Pᵢ = ∂ᵢ Pⱼ` for all `i`, Euler's identity shows that
`∂ⱼ (∑ᵢ Xᵢ Pᵢ) = (d + 1) Pⱼ`. The proof therefore takes as potential the sum over `d` of
`(d + 1)⁻¹ ∑ᵢ Xᵢ Pᵢᵈ`, where `Pᵢᵈ` is the degree-`d` homogeneous component of `Pᵢ`.

## Main results

* `MvPolynomial.homogeneousComponent_pderiv`: partial differentiation lowers homogeneous
  components by one degree.
* `MvPolynomial.pderiv_sum_X_mul_of_isHomogeneous`: if `Pⱼ` is homogeneous of degree `d` and
  `∂ⱼ Pᵢ = ∂ᵢ Pⱼ` for all `i`, then `∂ⱼ (∑ᵢ Xᵢ Pᵢ) = (d + 1) Pⱼ`.
* `MvPolynomial.exists_pderiv_eq`: a symmetric family of polynomials in finitely many variables
  of total degree at most `m` over a `ℚ`-algebra is the gradient of a polynomial of total degree
  at most `m + 1`.
* `MvPolynomial.exists_pderiv_eq_iff`: over a `ℚ`-algebra, a family of polynomials in finitely
  many variables is a gradient if and only if it satisfies the symmetry condition.
-/

public section

namespace MvPolynomial

open Finset

section CommSemiring

variable {R σ : Type*} [CommSemiring R]

/-- The degree-`d` homogeneous component of a partial derivative is the partial derivative of the
degree-`d + 1` homogeneous component. -/
theorem homogeneousComponent_pderiv (d : ℕ) (i : σ) (φ : MvPolynomial σ R) :
    homogeneousComponent d (pderiv i φ) = pderiv i (homogeneousComponent (d + 1) φ) := by
  ext m
  simp only [coeff_homogeneousComponent, coeff_pderiv, map_add, Finsupp.degree_single,
    Nat.add_right_cancel_iff, ite_mul, zero_mul]

/-- If `Pⱼ` is homogeneous of degree `d` and `∂ⱼ Pᵢ = ∂ᵢ Pⱼ` for all `i`, then
`∂ⱼ (∑ᵢ Xᵢ Pᵢ) = (d + 1) Pⱼ`. -/
theorem pderiv_sum_X_mul_of_isHomogeneous [Fintype σ] {d : ℕ} {P : σ → MvPolynomial σ R}
    {j : σ} (hP : (P j).IsHomogeneous d) (hsymm : ∀ i, pderiv j (P i) = pderiv i (P j)) :
    pderiv j (∑ i, X i * P i) = (d + 1) • P j := by
  simp_rw [map_sum, pderiv_mul, sum_add_distrib, hsymm, hP.sum_X_mul_pderiv]
  rw [sum_eq_single j (fun i _ hi ↦ by rw [pderiv_X_of_ne hi, zero_mul]) (by simp),
    pderiv_X_self, one_mul, add_smul, one_smul, add_comm]

end CommSemiring

section CommRing

variable {R σ : Type*} [CommRing R] [Algebra ℚ R] [Finite σ]

/-- **Polynomial Poincaré lemma.** Over a `ℚ`-algebra, a family `P` of polynomials in finitely
many variables of total degree at most `m` satisfying the symmetry condition `∂ⱼ Pᵢ = ∂ᵢ Pⱼ` is
the gradient of a polynomial of total degree at most `m + 1`. -/
theorem exists_pderiv_eq {m : ℕ} (P : σ → MvPolynomial σ R)
    (hP : ∀ i, P i ∈ restrictTotalDegree σ R m)
    (hsymm : ∀ i j, pderiv j (P i) = pderiv i (P j)) :
    ∃ Q ∈ restrictTotalDegree σ R (m + 1), ∀ i, pderiv i Q = P i := by
  have := Fintype.ofFinite σ
  refine ⟨∑ d ∈ range (m + 1), (d + 1 : ℚ)⁻¹ • ∑ i, X i * homogeneousComponent d (P i),
    Submodule.sum_mem _ fun d hd ↦ Submodule.smul_of_tower_mem _ _ <|
      Submodule.sum_mem _ fun i _ ↦ ?_, fun j ↦ ?_⟩
  · rw [mem_restrictTotalDegree, add_comm]
    exact ((isHomogeneous_X R i).mul (homogeneousComponent_isHomogeneous d _)).totalDegree_le.trans
      (by simpa using mem_range.1 hd)
  -- Each homogeneous component of `P` is again symmetric, so Euler's identity applies to it.
  have hcomponent (d : ℕ) :
      pderiv j (∑ i, X i * homogeneousComponent d (P i)) =
        (d + 1) • homogeneousComponent d (P j) := by
    refine pderiv_sum_X_mul_of_isHomogeneous (homogeneousComponent_isHomogeneous d _)
      (fun i ↦ ?_)
    rcases d with _ | d
    · simp
    · rw [← homogeneousComponent_pderiv, ← homogeneousComponent_pderiv, hsymm]
  simp_rw [map_sum, map_rat_smul, hcomponent, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
  refine (sum_congr rfl fun d _ ↦ ?_).trans
    (sum_homogeneousComponent_of_totalDegree_le ((mem_restrictTotalDegree _ _ _).1 (hP j)))
  rw [Nat.cast_add_one, inv_mul_cancel₀ (by positivity), one_smul]

/-- Over a `ℚ`-algebra, a family of polynomials in finitely many variables is the gradient of a
polynomial if and only if it satisfies the symmetry condition `∂ⱼ Pᵢ = ∂ᵢ Pⱼ`. -/
theorem exists_pderiv_eq_iff (P : σ → MvPolynomial σ R) :
    (∃ Q : MvPolynomial σ R, ∀ i, pderiv i Q = P i) ↔
      ∀ i j, pderiv j (P i) = pderiv i (P j) := by
  have := Fintype.ofFinite σ
  refine ⟨fun ⟨Q, hQ⟩ i j ↦ ?_, fun hsymm ↦ ?_⟩
  · rw [← hQ i, ← hQ j, pderiv_comm]
  · obtain ⟨Q, -, hQ⟩ := exists_pderiv_eq (m := univ.sup fun i ↦ (P i).totalDegree) P
      (fun i ↦ (mem_restrictTotalDegree _ _ _).2 (le_sup (f := fun i ↦ (P i).totalDegree)
        (mem_univ i))) hsymm
    exact ⟨Q, hQ⟩

end CommRing

end MvPolynomial
