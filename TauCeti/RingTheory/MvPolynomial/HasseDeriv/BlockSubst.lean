/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import TauCeti.RingTheory.MvPolynomial.HasseDeriv.ChainRule
public import TauCeti.RingTheory.MvPolynomial.LinearSubst
public import TauCeti.RingTheory.MvPolynomial.MultiHomogeneous
import Mathlib.Tactic.Linarith

/-!
# One linear change of variables in every block, and Hasse derivatives

Group the variables of a polynomial ring into blocks: `X (h, j)` is the variable `j : ι` of block
`h : κ`. For a square matrix `A` indexed by `ι`, `MvPolynomial.blockSubst A` substitutes
`X (h, j) ↦ ∑ i, A j i • X (h, i)` in every block at once. If the rows of `A` are linear forms
`L₀, …, Lₙ`, then `P = blockSubst A Q` means that `P(x₁, …, xₘ) = Q(A x₁, …, A xₘ)`, so the
coefficients of `Q = blockSubst A⁻¹ P` are the coefficients of `P` written in the monomials
`∏ h, ∏ i, Lᵢ(x_h) ^ N (h, i)`. In Schmidt's proof of the Subspace Theorem the auxiliary
polynomial is constructed so that these coefficients vanish whenever the weighted degree
`∑ h, N (h, i) / d h` in some form `Lᵢ` is small; this is the multihomogeneous analogue of
vanishing to high order at a point.

The point of this file is that such vanishing passes to Hasse derivatives with the expected loss.
By the chain rule for block-linear substitutions, a derivative of `P` of order `I` becomes, in the
coordinates of the forms, a combination of derivatives of `Q` whose orders `e` have the same block
degrees `∑ j, e (h, j) = ∑ j, I (h, j)` as `I`
(`MvPolynomial.blockSubst_inv_hasseDeriv`). Shifting an exponent vector by such an `e` raises its
weighted degree in a single form by at most the weighted order `∑ h, (∑ j, I (h, j)) / d h` of
`I`. No division by integers occurs, so no assumption on the characteristic is needed.

## Main definitions

* `MvPolynomial.blockSubst A`: the substitution `X (h, j) ↦ ∑ i, A j i • X (h, i)` in every block.

## Main results

* `MvPolynomial.blockSubst_mul`: block substitution is a right action of the matrix monoid, and
  `MvPolynomial.blockSubst_inv_blockSubst`, `MvPolynomial.blockSubst_blockSubst_inv`: an
  invertible matrix gives an automorphism.
* `MvPolynomial.eval_blockSubst`: evaluating `blockSubst A P` at `y` evaluates `P` at the point
  whose block `h` is `A` applied to block `h` of `y`.
* `MvPolynomial.IsMultiHomogeneous.blockSubst`: block substitution preserves the multidegree.
* `MvPolynomial.hasseDeriv_blockSubst`: the chain rule for a block substitution.
* `MvPolynomial.blockSubst_inv_hasseDeriv`: a Hasse derivative of `P`, written in the coordinates
  of the rows of `A`, is a combination of the derivatives of `blockSubst A⁻¹ P` of the same block
  degrees.
* `MvPolynomial.coeff_blockSubst_hasseDeriv_eq_zero`: if the coefficients of `blockSubst A⁻¹ P`
  vanish below the threshold `θ` in the weighted degree `∑ h, N (h, i) / d h`, then those of
  `blockSubst A⁻¹ (hasseDeriv I P)` vanish below `θ` minus the weighted order of `I`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press
  (2006), §7.5.14 and Lemma 7.5.15.
* W. M. Schmidt, *Diophantine Approximation*, Lecture Notes in Mathematics 785, Springer (1980),
  Chapter VI.
-/

public section

namespace MvPolynomial

open Finset Matrix
open scoped Kronecker

section CommSemiring

variable {R κ ι : Type*} [CommSemiring R] [Fintype ι]

/-- The linear change of variables `X (h, j) ↦ ∑ i, A j i • X (h, i)`, applied to every block
`h : κ` of the variables `X (h, j)`. -/
noncomputable def blockSubst (A : Matrix ι ι R) :
    MvPolynomial (κ × ι) R →ₐ[R] MvPolynomial (κ × ι) R :=
  aeval (blockLinearForm fun _ j i ↦ A j i)

theorem blockSubst_eq_aeval (A : Matrix ι ι R) :
    (blockSubst A : MvPolynomial (κ × ι) R →ₐ[R] _) = aeval (blockLinearForm fun _ j i ↦ A j i) :=
  (rfl)

@[simp]
theorem blockSubst_X (A : Matrix ι ι R) (h : κ) (j : ι) :
    blockSubst A (X (h, j) : MvPolynomial (κ × ι) R) = ∑ i, C (A j i) * X (h, i) := by
  rw [blockSubst_eq_aeval, aeval_X, blockLinearForm_apply]

/-- Evaluating `blockSubst A P` at `y` is evaluating `P` at the point whose block `h` is `A`
applied to the block `h` of `y`. -/
theorem eval_blockSubst (A : Matrix ι ι R) (y : κ × ι → R) (P : MvPolynomial (κ × ι) R) :
    eval y (blockSubst A P) = eval (fun p ↦ ∑ i, A p.2 i * y (p.1, i)) P :=
  eval_aeval_blockLinearForm _ y P

@[simp]
theorem blockSubst_one [DecidableEq ι] :
    (blockSubst (1 : Matrix ι ι R) : MvPolynomial (κ × ι) R →ₐ[R] _) = AlgHom.id R _ := by
  refine algHom_ext fun ⟨h, j⟩ ↦ ?_
  simp [Matrix.one_apply, apply_ite C, ite_mul]

/-- Block substitution is the linear substitution `MvPolynomial.linearSubst` of the
block-diagonal matrix `1 ⊗ₖ A`, with one copy of `A` for each block. -/
theorem blockSubst_eq_linearSubst [Fintype κ] [DecidableEq κ] (A : Matrix ι ι R) :
    (blockSubst A : MvPolynomial (κ × ι) R →ₐ[R] _) = linearSubst ((1 : Matrix κ κ R) ⊗ₖ A) := by
  refine algHom_ext fun ⟨h, j⟩ ↦ ?_
  simp [linearSubst_X, Fintype.sum_prod_type, Matrix.one_apply, ite_mul, apply_ite C]

/-- Block substitution is a right action of the matrix monoid. -/
theorem blockSubst_mul (A B : Matrix ι ι R) :
    (blockSubst (A * B) : MvPolynomial (κ × ι) R →ₐ[R] _) =
      (blockSubst B).comp (blockSubst A) := by
  refine algHom_ext fun ⟨h, j⟩ ↦ ?_
  simp only [blockSubst_X, AlgHom.comp_apply, map_sum, map_mul, algHom_C, algebraMap_eq,
    Matrix.mul_apply, sum_mul, mul_sum, mul_assoc]
  exact sum_comm

theorem blockSubst_mul_apply (A B : Matrix ι ι R) (P : MvPolynomial (κ × ι) R) :
    blockSubst (A * B) P = blockSubst B (blockSubst A P) := by
  rw [blockSubst_mul, AlgHom.comp_apply]

/-- Block substitution preserves multihomogeneity and the multidegree. -/
theorem IsMultiHomogeneous.blockSubst [DecidableEq κ] {d : κ → ℕ} {P : MvPolynomial (κ × ι) R}
    (hP : IsMultiHomogeneous d P) (A : Matrix ι ι R) :
    IsMultiHomogeneous d (MvPolynomial.blockSubst A P) :=
  isMultiHomogeneous_iff_forall_isWeightedHomogeneous.2 fun h ↦
    (hP.isWeightedHomogeneous h).aeval (isWeightedHomogeneous_blockLinearForm _ h)

variable [Fintype κ] [DecidableEq κ] [DecidableEq ι]

/-- **The chain rule for a block substitution**:
`∂^I (Q(A x)) = ∑_e c_{e,I} (∂^e Q)(A x)`, where `c_{e,I}` is the coefficient of `X ^ I` in the
substituted monomial `(A X) ^ e`, and the sum runs over the `e` with the block degrees
`∑ j, e (h, j) = ∑ j, I (h, j)` of `I`. -/
theorem hasseDeriv_blockSubst (A : Matrix ι ι R) (I : κ × ι →₀ ℕ) (Q : MvPolynomial (κ × ι) R) :
    hasseDeriv I (blockSubst A Q) =
      ∑ e ∈ univ.finsuppAntidiag I.degree with ∀ h, ∑ j, e (h, j) = ∑ j, I (h, j),
        (blockSubst A (monomial e (1 : R))).coeff I • blockSubst A (hasseDeriv e Q) := by
  simpa [blockSubst_eq_aeval] using hasseDeriv_aeval_blockLinearForm_hasseDeriv
    (fun _ j i ↦ A j i) Q 0 I

end CommSemiring

section CommRing

variable {R κ ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] {A : Matrix ι ι R}

@[simp]
theorem blockSubst_inv_blockSubst (hA : IsUnit A.det) (P : MvPolynomial (κ × ι) R) :
    blockSubst A⁻¹ (blockSubst A P) = P := by
  rw [← blockSubst_mul_apply, mul_nonsing_inv A hA, blockSubst_one, AlgHom.id_apply]

@[simp]
theorem blockSubst_blockSubst_inv (hA : IsUnit A.det) (P : MvPolynomial (κ × ι) R) :
    blockSubst A (blockSubst A⁻¹ P) = P := by
  rw [← blockSubst_mul_apply, nonsing_inv_mul A hA, blockSubst_one, AlgHom.id_apply]

/-- A Hasse derivative of `P`, written in the coordinates of the rows of an invertible matrix `A`,
is a combination of the derivatives of `blockSubst A⁻¹ P` (that is, of `P` in those coordinates)
whose orders have the same block degrees as the order `I`. -/
theorem blockSubst_inv_hasseDeriv [Fintype κ] [DecidableEq κ] (hA : IsUnit A.det) (I : κ × ι →₀ ℕ)
    (P : MvPolynomial (κ × ι) R) :
    blockSubst A⁻¹ (hasseDeriv I P) =
      ∑ e ∈ univ.finsuppAntidiag I.degree with ∀ h, ∑ j, e (h, j) = ∑ j, I (h, j),
        (blockSubst A (monomial e (1 : R))).coeff I • hasseDeriv e (blockSubst A⁻¹ P) := by
  conv_lhs => rw [← blockSubst_blockSubst_inv hA P]
  simp only [hasseDeriv_blockSubst, map_sum, map_smul, blockSubst_inv_blockSubst hA]

/-- If the coefficients of `blockSubst A⁻¹ P` vanish at every shift `J + e` of `J` by an order `e`
with the block degrees of `I`, then the coefficient of `blockSubst A⁻¹ (hasseDeriv I P)` at `J`
vanishes. -/
theorem coeff_blockSubst_hasseDeriv_eq_zero_of_forall_coeff_add [Finite κ]
    (hA : IsUnit A.det) {P : MvPolynomial (κ × ι) R} {I J : κ × ι →₀ ℕ}
    (hP : ∀ e : κ × ι →₀ ℕ, (∀ h, ∑ j, e (h, j) = ∑ j, I (h, j)) →
      (blockSubst A⁻¹ P).coeff (J + e) = 0) :
    (blockSubst A⁻¹ (hasseDeriv I P)).coeff J = 0 := by
  classical
  have := Fintype.ofFinite κ
  rw [blockSubst_inv_hasseDeriv hA, coeff_sum]
  refine sum_eq_zero fun e he ↦ ?_
  rw [coeff_smul, hasseDeriv_coeff, hP e (mem_filter.1 he).2, mul_zero, smul_zero]

/-- **Vanishing along a form passes to Hasse derivatives** (Bombieri–Gubler, §7.5.14). Fix a
row `i` of the invertible matrix `A` and a multidegree `d`. If the coefficients of
`blockSubst A⁻¹ P` vanish at every exponent vector `N` whose weighted degree
`∑ h, N (h, i) / d h` in the variables `X (h, i)` is below `θ`, then the coefficients of
`blockSubst A⁻¹ (hasseDeriv I P)` vanish at every `J` whose weighted degree is below `θ` minus the
weighted order `∑ h, (∑ j, I (h, j)) / d h` of `I`. -/
theorem coeff_blockSubst_hasseDeriv_eq_zero [Fintype κ] (hA : IsUnit A.det)
    {P : MvPolynomial (κ × ι) R} {d : κ → ℕ} {i : ι} {θ : ℝ}
    (hP : ∀ N : κ × ι →₀ ℕ, ∑ h, (N (h, i) : ℝ) / d h < θ → (blockSubst A⁻¹ P).coeff N = 0)
    {I J : κ × ι →₀ ℕ}
    (hJ : ∑ h, (J (h, i) : ℝ) / d h < θ - ∑ h, ((∑ j, I (h, j) : ℕ) : ℝ) / d h) :
    (blockSubst A⁻¹ (hasseDeriv I P)).coeff J = 0 := by
  refine coeff_blockSubst_hasseDeriv_eq_zero_of_forall_coeff_add hA fun e he ↦ hP _ ?_
  -- Shifting by `e` raises the weighted degree in row `i` by at most the weighted order of `I`.
  have hle : ∑ h, (e (h, i) : ℝ) / d h ≤ ∑ h, ((∑ j, I (h, j) : ℕ) : ℝ) / d h := by
    refine sum_le_sum fun h _ ↦ div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
    rw [← he h]
    exact_mod_cast single_le_sum (f := fun j ↦ e (h, j)) (fun _ _ ↦ Nat.zero_le _) (mem_univ i)
  simp only [Finsupp.coe_add, Pi.add_apply, Nat.cast_add, add_div, sum_add_distrib]
  linarith

end CommRing

/-! ### Examples -/

/-- The loss in `coeff_blockSubst_hasseDeriv_eq_zero` cannot be dropped. In one block of one
variable, with `A = 1` and `d = 1`, the coefficients of `X ^ 2` vanish at every exponent below
`2`, while its first Hasse derivative `2 X` has a nonzero coefficient at the exponent `1 < 2`;
the lemma only promises vanishing below `2 - 1`. -/
example : (blockSubst (1 : Matrix Unit Unit ℚ)⁻¹
    (hasseDeriv (Finsupp.single ((), ()) 1) (X ((), ()) ^ 2 : MvPolynomial (Unit × Unit) ℚ))).coeff
      (Finsupp.single ((), ()) 1) = 2 := by
  simp [X_pow_eq_monomial, hasseDeriv_monomial, coeff_monomial, ← Finsupp.single_tsub]

end MvPolynomial
