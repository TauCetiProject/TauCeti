/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import TauCeti.RingTheory.Polynomial.Resultant.Discriminant
import TauCeti.Algebra.MvPolynomial.Eval

/-!
# The characteristic discriminant of a Hermitian matrix

The discriminant of the characteristic polynomial of a Hermitian matrix is the product of
the squared gaps of its ordered real eigenvalues. It is therefore nonzero exactly when the
eigenvalues are distinct.

Along a real-linear family of matrices, the real part of the characteristic discriminant is a
real polynomial in the parameters. Applied to linear coordinates on the self-adjoint matrices, this
is the polynomial whose zero locus contains the matrices with a repeated eigenvalue.

The discriminant argument is the one used in Anderson, Guionnet and Zeitouni,
*An Introduction to Random Matrices* (2010), proof of Theorem 2.5.2.
-/

public section

open Finset Polynomial

namespace Matrix

variable {ι 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕜]

/-- The characteristic discriminant of a Hermitian matrix is the real product of
the squared gaps of its ordered eigenvalues. -/
theorem IsHermitian.charpoly_discr_eq {A : Matrix ι ι 𝕜} (hA : A.IsHermitian) :
    A.charpoly.discr =
      ((∏ i, ∏ j ∈ Ioi i, (hA.eigenvalues₀ i - hA.eigenvalues₀ j) ^ 2 : ℝ) : 𝕜) := by
  have h : A.charpoly = ∏ i, (X - C (hA.eigenvalues₀ i : 𝕜)) := by
    rw [hA.charpoly_eq]
    exact Equiv.prod_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
      fun i ↦ X - C (hA.eigenvalues₀ i : 𝕜)
  rw [h, discr_prod_X_sub_C]
  push_cast
  rfl

/-- A Hermitian matrix has nonzero characteristic discriminant exactly when its
eigenvalues are distinct. -/
theorem IsHermitian.charpoly_discr_ne_zero_iff {A : Matrix ι ι 𝕜} (hA : A.IsHermitian) :
    A.charpoly.discr ≠ 0 ↔ Function.Injective hA.eigenvalues := by
  rw [A.charpoly_monic.discr_ne_zero_iff, hA.charpoly_eq, separable_prod_X_sub_C_iff]
  exact RCLike.ofReal_injective.of_comp_iff _

/-- Along a real-linear family of matrices, the real part of the characteristic discriminant
is a real polynomial in the parameters. -/
theorem exists_eval_eq_re_charpoly_discr {κ : Type*} [Finite κ]
    (L : (κ → ℝ) →ₗ[ℝ] Matrix ι ι 𝕜) :
    ∃ q : MvPolynomial κ ℝ, ∀ x : κ → ℝ,
      MvPolynomial.eval x q = RCLike.re (L x).charpoly.discr := by
  classical
  let _ := Fintype.ofFinite κ
  let M : Matrix ι ι (MvPolynomial κ 𝕜) := of fun i j ↦
    ∑ k, MvPolynomial.C (L (fun l ↦ if k = l then 1 else 0) i j) * MvPolynomial.X k
  obtain ⟨q, hq⟩ := MvPolynomial.exists_eval_eq_linearMap (RCLike.reLm (K := 𝕜)) M.charpoly.discr
  refine ⟨q, fun x ↦ ?_⟩
  have hM : M.map (MvPolynomial.eval (algebraMap ℝ 𝕜 ∘ x)) = L x := by
    rw [L.pi_apply_eq_sum_univ x]
    ext i j
    simp [M, RCLike.real_smul_eq_coe_mul, mul_comm]
  rw [← hM, charpoly_map, M.charpoly_monic.discr_map]
  exact hq x

end Matrix
