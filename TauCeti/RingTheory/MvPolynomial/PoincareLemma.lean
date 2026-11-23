/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Rat
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import TauCeti.RingTheory.MvPolynomial.Homogeneous
import TauCeti.Algebra.MvPolynomial.PDeriv

/-!
# The Poincaré lemma for polynomial vector fields

A family `P : σ → R[X_σ]` of polynomials in finitely many variables is a gradient field
`Pᵢ = ∂ᵢ Q` exactly when it satisfies the symmetry condition `∂ⱼ Pᵢ = ∂ᵢ Pⱼ`, provided the
coefficients form a `ℚ`-algebra. Moreover a symmetric family of polynomials of total degree at
most `m` has a potential of total degree at most `m + 1`, uniquely determined after prescribing its
constant coefficient.

This is the algebraic step in identifying the Sobolev functions whose derivatives of order
`m + 1` vanish with the polynomials of degree at most `m`: the first derivatives of such a
function are polynomials of degree at most `m - 1` satisfying the symmetry condition, and a
potential of degree at most `m` reduces the claim to a function with vanishing gradient.

The argument is the one with homogeneous components and Euler's identity
(`MvPolynomial.IsHomogeneous.sum_X_mul_pderiv`), the polynomial case of the homotopy formula in
the proof of the Poincaré lemma for closed differential forms (Bott and Tu, §4). When `Pⱼ` is
homogeneous of degree `d` and `∂ⱼ Pᵢ = ∂ᵢ Pⱼ` for all `i`, Euler's identity shows that
`∂ⱼ (∑ᵢ Xᵢ Pᵢ) = (d + 1) Pⱼ`. The proof therefore takes as potential the sum over `d` of
`(d + 1)⁻¹ ∑ᵢ Xᵢ Pᵢᵈ`, where `Pᵢᵈ` is the degree-`d` homogeneous component of `Pᵢ`. Uniqueness
up to constants follows from `MvPolynomial.pderiv.ext` (in `TauCeti.Algebra.MvPolynomial.PDeriv`).

## Main results

* `MvPolynomial.homogeneousComponent_pderiv`: partial differentiation lowers homogeneous
  components by one degree.
* `MvPolynomial.pderiv_sum_X_mul_of_isHomogeneous`: if `Pⱼ` is homogeneous of degree `d` and
  `∂ⱼ Pᵢ = ∂ᵢ Pⱼ` for all `i`, then `∂ⱼ (∑ᵢ Xᵢ Pᵢ) = (d + 1) Pⱼ`.
* `MvPolynomial.exists_isHomogeneous_pderiv_eq`: homogeneous polynomial Poincaré lemma over a
  commutative `ℚ`-algebra semiring.
* `MvPolynomial.exists_pderiv_eq`: a symmetric family of polynomials in finitely many variables
  of total degree at most `m` over a `ℚ`-algebra is the gradient of a polynomial of total degree
  at most `m + 1`.
* `MvPolynomial.exists_pderiv_eq_iff`: over a `ℚ`-algebra, a family of polynomials in finitely
  many variables is a gradient if and only if it satisfies the symmetry condition.
* `MvPolynomial.existsUnique_mem_restrictTotalDegree_pderiv_eq`,
  `MvPolynomial.existsUnique_pderiv_eq`: unique polynomial potentials with prescribed constant
  coefficient.

## References

* R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*, Springer (1982), §4 (the homotopy
  operator construction underlying the homogeneous-component potential formula).
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

section AlgebraRatSemiring

variable {R σ : Type*} [CommSemiring R] [Algebra ℚ R] [Finite σ]

/-- **Homogeneous polynomial Poincaré lemma.** Over a commutative `ℚ`-algebra semiring, a symmetric
family of degree-`d` homogeneous polynomials in finitely many variables is the gradient of a
homogeneous polynomial of degree `d + 1`. -/
theorem exists_isHomogeneous_pderiv_eq {d : ℕ} (P : σ → MvPolynomial σ R)
    (hP : ∀ i, (P i).IsHomogeneous d) (hsymm : ∀ i j, pderiv j (P i) = pderiv i (P j)) :
    ∃ Q : MvPolynomial σ R, Q.IsHomogeneous (d + 1) ∧ ∀ i, pderiv i Q = P i := by
  have := Fintype.ofFinite σ
  set c : R := algebraMap ℚ R (d + 1 : ℚ)⁻¹
  refine ⟨c • ∑ i, X i * P i, ?_, fun j ↦ ?_⟩
  · refine (homogeneousSubmodule σ R (d + 1)).smul_mem c ?_
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    rw [mem_homogeneousSubmodule]
    simpa only [add_comm 1 d] using (isHomogeneous_X R i).mul (hP i)
  · have hcancel : c * (d + 1 : R) = 1 := by
      have hne : (d + 1 : ℚ) ≠ 0 := by positivity
      calc c * (d + 1 : R)
          = algebraMap ℚ R ((d + 1 : ℚ)⁻¹ * (d + 1 : ℚ)) := by simp [c]
        _ = 1 := by rw [inv_mul_cancel₀ hne, map_one]
    rw [(pderiv j).map_smul, pderiv_sum_X_mul_of_isHomogeneous (hP j) (fun i ↦ hsymm i j),
      ← Nat.cast_smul_eq_nsmul R, smul_smul, Nat.cast_add, Nat.cast_one, hcancel, one_smul]

end AlgebraRatSemiring

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

/-- A symmetric family of polynomials in finitely many variables of total degree at most `m` over a
`ℚ`-algebra has a unique potential of total degree at most `m + 1` with any prescribed constant
coefficient. -/
theorem existsUnique_mem_restrictTotalDegree_pderiv_eq {m : ℕ} (P : σ → MvPolynomial σ R)
    (hP : ∀ i, P i ∈ restrictTotalDegree σ R m)
    (hsymm : ∀ i j, pderiv j (P i) = pderiv i (P j)) (c : R) :
    ∃! Q : MvPolynomial σ R,
      Q ∈ restrictTotalDegree σ R (m + 1) ∧ (∀ i, pderiv i Q = P i) ∧ constantCoeff Q = c := by
  have : HasUniqueDiv R := .of_module_rat R
  obtain ⟨Q₀, hQ₀deg, hQ₀⟩ := exists_pderiv_eq P hP hsymm
  set Q := Q₀ + C (c - constantCoeff Q₀)
  have hQdeg : Q ∈ restrictTotalDegree σ R (m + 1) := by
    refine Submodule.add_mem _ hQ₀deg ?_
    rw [mem_restrictTotalDegree, totalDegree_C]
    exact Nat.zero_le _
  have hQp : ∀ i, pderiv i Q = P i := fun i ↦ by simp [Q, hQ₀ i]
  have hQc : constantCoeff Q = c := by simp [Q]
  exact ⟨Q, ⟨hQdeg, hQp, hQc⟩, fun Q' ⟨_, hQ'p, hQ'c⟩ ↦
    pderiv.ext (fun i ↦ (hQ'p i).trans (hQp i).symm) (hQ'c.trans hQc.symm)⟩

/-- Over a `ℚ`-algebra, every symmetric family of polynomials in finitely many variables has a
unique polynomial potential with any prescribed constant coefficient. -/
theorem existsUnique_pderiv_eq (P : σ → MvPolynomial σ R)
    (hsymm : ∀ i j, pderiv j (P i) = pderiv i (P j)) (c : R) :
    ∃! Q : MvPolynomial σ R, (∀ i, pderiv i Q = P i) ∧ constantCoeff Q = c := by
  have : HasUniqueDiv R := .of_module_rat R
  obtain ⟨Q₀, hQ₀⟩ := (exists_pderiv_eq_iff P).mpr hsymm
  set Q := Q₀ + C (c - constantCoeff Q₀)
  have hQp : ∀ i, pderiv i Q = P i := fun i ↦ by simp [Q, hQ₀ i]
  have hQc : constantCoeff Q = c := by simp [Q]
  exact ⟨Q, ⟨hQp, hQc⟩, fun Q' ⟨hQ'p, hQ'c⟩ ↦
    pderiv.ext (fun i ↦ (hQ'p i).trans (hQp i).symm) (hQ'c.trans hQc.symm)⟩

end CommRing

-- Sanity checks:
-- (1) `(-X 1, X 0)` is not symmetric and has no polynomial potential over `ℚ`.
-- (2) `[Finite σ]` is sharp: over `σ = ℕ`, `P _ = 1` is symmetric of degree `0` with no potential.
example :
    ¬ ∃ Q : MvPolynomial (Fin 2) ℚ, ∀ i, pderiv i Q = (![-X 1, X 0] : Fin 2 → _) i := by
  rw [exists_pderiv_eq_iff]
  intro h
  have h01 := congrArg constantCoeff (h 0 1)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, map_neg,
    pderiv_X_self, map_one] at h01
  norm_num at h01

example :
    (∀ i j : ℕ, pderiv j (1 : MvPolynomial ℕ ℚ) = pderiv i (1 : MvPolynomial ℕ ℚ)) ∧
      ¬ ∃ Q : MvPolynomial ℕ ℚ, ∀ i : ℕ, pderiv i Q = 1 := by
  refine ⟨fun _ _ ↦ by simp, ?_⟩
  rintro ⟨Q, hQ⟩
  set n : ℕ := Q.vars.sup id + 1
  have hn : n ∉ Q.vars := fun hmem ↦
    Nat.lt_irrefl _ (Nat.lt_succ_of_le (Finset.le_sup (f := id) hmem))
  have hzero : pderiv n Q = 0 := pderiv_eq_zero_of_notMem_vars hn
  have hone : pderiv n Q = 1 := hQ n
  exact one_ne_zero (hone.symm.trans hzero)

end MvPolynomial
