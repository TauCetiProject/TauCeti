/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Unitary
public import TauCeti.Algebra.Coalgebra.Star
public import TauCeti.Algebra.HopfAlgebra.Integral.Positive
public import TauCeti.Analysis.Matrix.GramFactorization

/-!
# Algebraic unitarization of finite comodules

Let `A` be a complex Hopf star algebra, that is a complex Hopf algebra with a compatible star
structure whose comultiplication is a star map, and let `h : A → ℂ` be a right invariant
integral, `(h ⊗ id) Δ(a) = h(a) 1`. For a comodule `M` with a finite basis `(eⱼ)` and coefficient
matrix `u`, so that `δ(eⱼ) = ∑ i, eᵢ ⊗ u i j`, the *Haar Gram matrix*

`G j l = h (∑ i, star (u i j) * u i l)`

is the Gram matrix in the basis `(eⱼ)` of the averaged form `⟪v, w⟫_h = h ⟪δ v, δ w⟫_A`, where
`⟪x ⊗ a, y ⊗ b⟫_A = ⟪x, y⟫ (star a * b)` is computed from the inner product making `(eⱼ)`
orthonormal. Right invariance of `h` says that this form is invariant:

`uᴴ G u = G`,

with `G` viewed as a scalar matrix over `A`. If `h` is moreover nonzero and positive,
`0 ≤ h (star a * a)`, then it is strictly positive, so `G` is positive definite: the counit
recovers a vector from its coaction. Writing `G = Pᴴ P`, the basis whose change-of-basis matrix
from `(eⱼ)` is `P⁻¹` has unitary coefficient matrix `P u P⁻¹`. Thus every comodule with a finite
basis is unitarizable, in the sense of `TauCeti.Comodule.IsUnitary`: it is unitary for the inner
product making this new basis orthonormal.

No norm or completion of `A` is involved: positivity is the algebraic condition on squares, and
this is the algebraic unitarization used before any C⋆-completion of a compact quantum group.

## Main declarations

* `TauCeti.Comodule.haarGramMatrix`: the Haar Gram matrix of a finite basis.
* `TauCeti.Comodule.conjTranspose_coefficientMatrix_mul_haarGramMatrix_mul`: Haar invariance
  `uᴴ G u = G` of the averaged form.
* `TauCeti.Comodule.posDef_haarGramMatrix`: for a strictly positive functional, such as a nonzero
  positive right invariant integral, the Haar Gram matrix is positive definite.
* `TauCeti.Comodule.haarGramMatrix_eq_smul_one`: on a basis with unitary coefficient matrix the
  averaged form is `h 1` times the original one.
* `TauCeti.Comodule.coefficientMatrix_mem_unitary_of_haarGramMatrix_eq`: a factorization
  `G = Pᴴ P` gives a basis with unitary coefficient matrix.
* `TauCeti.Comodule.exists_basis_coefficientMatrix_mem_unitary`: every comodule with a finite
  basis has a basis, indexed by the same type, with unitary coefficient matrix.

## References

* T. Timmermann, *An Invitation to Quantum Groups and Duality*, EMS, 2008, Section 3.2.
* A. Klimyk and K. Schmüdgen, *Quantum Groups and Their Representations*, Springer, 1997,
  Section 11.1.
-/

public section

open Module Matrix
open scoped ComplexOrder

namespace TauCeti.Comodule

variable {A M ι : Type*} [Ring A] [StarRing A] [AddCommGroup M] [Module ℂ M] [Fintype ι]

section Coalgebra

variable [Algebra ℂ A] [Coalgebra ℂ A] [Comodule ℂ A M]

/-- The Haar Gram matrix `h (uᴴ u)` of a finite basis with coefficient matrix `u`: the Gram matrix
of the averaged form `⟪v, w⟫_h = h ⟪δ v, δ w⟫_A` built from the inner product making the basis
orthonormal. -/
noncomputable def haarGramMatrix (h : A →ₗ[ℂ] ℂ) (b : Basis ι ℂ M) : Matrix ι ι ℂ :=
  ((coefficientMatrix (C := A) b)ᴴ * coefficientMatrix (C := A) b).map h

/-- The entries of the Haar Gram matrix: `G j l = h (∑ i, star (u i j) * u i l)`. -/
@[simp]
theorem haarGramMatrix_apply (h : A →ₗ[ℂ] ℂ) (b : Basis ι ℂ M) (j l : ι) :
    haarGramMatrix h b j l =
      h (∑ i, star (coefficientMatrix (C := A) b i j) * coefficientMatrix (C := A) b i l) := by
  simp [haarGramMatrix, Matrix.mul_apply]

variable {h : A →ₗ[ℂ] ℂ}

/-- On a basis with unitary coefficient matrix the averaged form is `h 1` times the inner product
making the basis orthonormal. -/
theorem haarGramMatrix_eq_smul_one [DecidableEq ι] (b : Basis ι ℂ M)
    (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) :
    haarGramMatrix h b = h 1 • (1 : Matrix ι ι ℂ) := by
  ext i j
  rw [haarGramMatrix, ← star_eq_conjTranspose, (Unitary.mem_iff.mp hu).1]
  by_cases hij : i = j <;> simp [hij]

variable [StarModule ℂ A]

/-- The Haar Gram matrix of a positive functional is hermitian. -/
theorem isHermitian_haarGramMatrix (hpos : ∀ a, 0 ≤ h (star a * a)) (b : Basis ι ℂ M) :
    (haarGramMatrix h b).IsHermitian := by
  refine IsHermitian.ext fun j l ↦ ?_
  have hstar (a : A) : star (h a) = h (star a) :=
    ((StarPositiveFunctional.mk h hpos).map_star a).symm
  simp [hstar, star_sum]

/-- For a strictly positive functional `h`, the Haar Gram matrix of a finite basis is positive
definite: the averaged form is an inner product. By
`LinearMap.IsRightInvariantIntegral.map_star_mul_self_pos` this applies to every nonzero positive
right invariant integral. -/
theorem posDef_haarGramMatrix (hpos : ∀ a, a ≠ 0 → 0 < h (star a * a)) (b : Basis ι ℂ M) :
    (haarGramMatrix h b).PosDef := by
  classical
  set u := coefficientMatrix (C := A) b
  have hnonneg (a : A) : 0 ≤ h (star a * a) := by
    obtain rfl | ha := eq_or_ne a 0
    · simp
    · exact (hpos a ha).le
  refine .of_dotProduct_mulVec_pos (isHermitian_haarGramMatrix hnonneg b) fun x hx ↦ ?_
  -- The quadratic form is `∑ i, h (star (y i) * y i)` for the coaction coefficients `y` of `x`.
  set y : ι → A := fun i ↦ ∑ l, x l • u i l
  have hq : star x ⬝ᵥ (haarGramMatrix h b *ᵥ x) = ∑ i, h (star (y i) * y i) := by
    simp only [dotProduct, mulVec, haarGramMatrix_apply, y, star_sum, star_smul, Finset.sum_mul,
      Finset.mul_sum, smul_mul_assoc, mul_smul_comm, map_sum, map_smul, smul_eq_mul, Pi.star_apply]
    conv_lhs => enter [2, j]; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun l _ ↦ by ring
  -- Applying the counit to `y` recovers `x`, so some `y i` is nonzero.
  obtain ⟨i, hi⟩ : ∃ i, y i ≠ 0 := by
    by_contra! H
    refine hx (funext fun i ↦ ?_)
    simpa [y, u, map_sum, counit_coefficientMatrix] using
      congrArg (Coalgebra.counit (R := ℂ)) (H i)
  rw [hq]
  exact Finset.sum_pos' (fun i _ ↦ hnonneg _) ⟨i, Finset.mem_univ _, hpos _ hi⟩

end Coalgebra

section Bialgebra

variable [Bialgebra ℂ A] [StarModule ℂ A] [StarCoalgebra ℂ A] [Comodule ℂ A M]
  {h : A →ₗ[ℂ] ℂ}

/-- **Haar invariance** of the averaged form: for a right invariant integral `h`, the coefficient
matrix `u` preserves the Haar Gram matrix, `uᴴ G u = G`. -/
theorem conjTranspose_coefficientMatrix_mul_haarGramMatrix_mul (hh : h.IsRightInvariantIntegral)
    (b : Basis ι ℂ M) :
    (coefficientMatrix (C := A) b)ᴴ * (haarGramMatrix h b).map (algebraMap ℂ A) *
        coefficientMatrix (C := A) b =
      (haarGramMatrix h b).map (algebraMap ℂ A) := by
  set u := coefficientMatrix (C := A) b
  -- The coproduct of each coefficient entry, `Δ (u i j) = ∑ k, u i k ⊗ u k j`.
  let r (i j : ι) : Coalgebra.Repr ℂ (u i j) ι :=
    ⟨Finset.univ, fun k ↦ u i k, fun k ↦ u k j, (comul_coefficientMatrix_eq_sum b i j).symm⟩
  ext j l
  calc _ = ∑ i, ∑ k, ∑ m, h (star (u i k) * u i m) • (star (u k j) * u m l) := by
        simp only [Matrix.mul_apply, Matrix.map_apply, conjTranspose_apply, haarGramMatrix_apply,
          map_sum, Finset.sum_mul, Finset.mul_sum, Algebra.algebraMap_eq_smul_one, mul_smul_comm,
          smul_mul_assoc, mul_one]
        conv_lhs => enter [2, k]; rw [Finset.sum_comm]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_comm
    _ = ∑ i, h (star (u i j) * u i l) • (1 : A) :=
        Finset.sum_congr rfl fun i _ ↦ by simpa [r] using hh.sum_sum_mul (r i j).star (r i l)
    _ = _ := by
        simp [map_sum, Algebra.algebraMap_eq_smul_one, u]

end Bialgebra

section HopfAlgebra

variable [HopfAlgebra ℂ A] [StarModule ℂ A] [StarCoalgebra ℂ A] [Comodule ℂ A M]
  [DecidableEq ι] {h : A →ₗ[ℂ] ℂ}

/-- **Algebraic unitarization.** If the Haar Gram matrix of `b` factors as `Pᴴ P` and the basis
`c` has change-of-basis matrix from `b` inverse to `P`, then the coefficient matrix of `c` is
unitary. -/
theorem coefficientMatrix_mem_unitary_of_haarGramMatrix_eq (hh : h.IsRightInvariantIntegral)
    {b c : Basis ι ℂ M} {P : Matrix ι ι ℂ}
    (hP : haarGramMatrix h b = Pᴴ * P) (hc : P * b.toMatrix c = 1) :
    coefficientMatrix (C := A) c ∈ unitary (Matrix ι ι A) := by
  set f := algebraMap ℂ A
  set u := coefficientMatrix (C := A) b
  set Pf := P.map f
  set Qf := (b.toMatrix c).map f
  have hstar : Function.Semiconj f star star := fun z ↦ algebraMap_star_comm z
  have hPQ : Pf * Qf = 1 := by
    rw [← Matrix.map_mul, hc, Matrix.map_one _ (map_zero f) (map_one f)]
  -- The change of basis gives `v = P u P⁻¹`, where `P⁻¹` is the change-of-basis matrix.
  have hv : coefficientMatrix (C := A) c = Pf * u * Qf := by
    rw [Matrix.mul_assoc, b.coefficientMatrix_mul_toMatrix c, ← Matrix.mul_assoc, hPQ,
      Matrix.one_mul]
  have hG : (haarGramMatrix h b).map f = Pfᴴ * Pf := by
    rw [hP, Matrix.map_mul, conjTranspose_map _ hstar]
  have hinv : uᴴ * (Pfᴴ * Pf) * u = Pfᴴ * Pf := by
    rw [← hG]
    exact conjTranspose_coefficientMatrix_mul_haarGramMatrix_mul hh b
  have hvv : (coefficientMatrix (C := A) c)ᴴ * coefficientMatrix (C := A) c = 1 := by
    calc _ = Qfᴴ * (uᴴ * (Pfᴴ * Pf) * u) * Qf := by
          simp only [hv, conjTranspose_mul, Matrix.mul_assoc]
      _ = (Pf * Qf)ᴴ * (Pf * Qf) := by
          simp only [hinv, conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hPQ, conjTranspose_one, Matrix.one_mul]
  -- A left inverse of `v` is its two-sided inverse, the antipode transform.
  have hS : (coefficientMatrix (C := A) c)ᴴ =
      (coefficientMatrix (C := A) c).map (HopfAlgebra.antipode ℂ) :=
    left_inv_eq_right_inv hvv (coefficientMatrix_mul_map_antipode c)
  rw [Unitary.mem_iff, star_eq_conjTranspose, hS]
  exact ⟨map_antipode_mul_coefficientMatrix c, coefficientMatrix_mul_map_antipode c⟩

/-- **Algebraic unitarization.** Over a complex Hopf star algebra with a nonzero positive right
invariant integral, every comodule with a finite basis has a basis, indexed by the same type,
whose coefficient matrix is unitary. -/
theorem exists_basis_coefficientMatrix_mem_unitary (hh : h.IsRightInvariantIntegral) (h0 : h ≠ 0)
    (hpos : ∀ a, 0 ≤ h (star a * a)) (b : Basis ι ℂ M) :
    ∃ c : Basis ι ℂ M, coefficientMatrix (C := A) c ∈ unitary (Matrix ι ι A) := by
  have hG := posDef_haarGramMatrix (fun a ↦ hh.map_star_mul_self_pos h0 hpos) b
  obtain ⟨P, hP⟩ := posSemidef_iff_eq_conjTranspose_mul_self.mp hG.posSemidef
  have hPdet : IsUnit P.det := by
    have := (isUnit_iff_isUnit_det _).mp hG.isUnit
    rw [hP, det_mul] at this
    exact isUnit_of_mul_isUnit_right this
  have hdet : IsUnit P⁻¹.det := isUnit_nonsing_inv_det P hPdet
  refine ⟨b.map (toLinearEquiv b P⁻¹ hdet),
    coefficientMatrix_mem_unitary_of_haarGramMatrix_eq hh hP ?_⟩
  have hQ : b.toMatrix (b.map (toLinearEquiv b P⁻¹ hdet)) = P⁻¹ := by
    ext i j
    simp [Basis.toMatrix_apply, Finsupp.single_apply]
  rw [hQ, mul_nonsing_inv _ hPdet]

end HopfAlgebra

end TauCeti.Comodule
