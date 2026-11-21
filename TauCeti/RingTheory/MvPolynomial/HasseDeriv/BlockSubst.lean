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
import Mathlib.Tactic.FieldSimp
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

The point of this file is that such vanishing passes to Hasse derivatives with the expected loss,
depends on each form individually rather than on the complementary rows of `A`, and for a
multihomogeneous polynomial upgrades automatically to two-sided concentration around the mean
`card κ / card ι`.
By the chain rule for block-linear substitutions, a derivative of `P` of order `I` becomes, in the
coordinates of the forms, a combination of derivatives of `Q` whose orders `e` have the same block
degrees `∑ j, e (h, j) = ∑ j, I (h, j)` as `I`
(`MvPolynomial.blockSubst_inv_hasseDeriv`). Shifting an exponent vector by such an `e` raises its
weighted degree in a single form by at most the weighted order `∑ h, (∑ j, I (h, j)) / d h` of
`I`. No division by integers occurs, so no assumption on the characteristic is needed.

## Main definitions

* `MvPolynomial.blockSubst A`: the substitution `X (h, j) ↦ ∑ i, A j i • X (h, i)` in every block.

## Main results

* `MvPolynomial.aeval_blockLinearForm_eq_linearSubst`, `MvPolynomial.blockSubst_eq_linearSubst`:
  substituting square block-linear forms is a block-diagonal `MvPolynomial.linearSubst`, and in
  particular `blockSubst A` is `linearSubst (1 ⊗ₖ A)`.
* `MvPolynomial.blockSubst_mul`: block substitution is a right action of the matrix monoid, and
  `MvPolynomial.blockSubst_inv_blockSubst`, `MvPolynomial.blockSubst_blockSubst_inv`: an
  invertible matrix gives an automorphism.
* `MvPolynomial.eval_blockSubst`: evaluating `blockSubst A P` at `y` evaluates `P` at the point
  whose block `h` is `A` applied to block `h` of `y`.
* `MvPolynomial.IsMultiHomogeneous.blockSubst`,
  `MvPolynomial.IsHomogeneous.blockSubst_smul`: block substitution preserves the multidegree,
  and scaling `A` by `c` scales a homogeneous polynomial of degree `n` by `c ^ n`.
* `MvPolynomial.blockSubst_coeff_mem_of_row`,
  `MvPolynomial.coeff_blockSubst_inv_eq_zero_of_row_eq`: vanishing of `blockSubst A⁻¹ P` below a
  weighted-degree threshold along row `i'` of an invertible matrix `A` passes to row `i` of any
  matrix `B` with `A i' = B i`.
* `MvPolynomial.hasseDeriv_blockSubst`: the chain rule for a block substitution.
* `MvPolynomial.blockSubst_inv_hasseDeriv`: a Hasse derivative of `P`, written in the coordinates
  of the rows of `A`, is a combination of the derivatives of `blockSubst A⁻¹ P` of the same block
  degrees.
* `MvPolynomial.coeff_blockSubst_hasseDeriv_eq_zero`,
  `MvPolynomial.coeff_blockSubst_hasseDeriv_eq_zero_of_le`: if the coefficients of
  `blockSubst A⁻¹ P` vanish below (or at most) the threshold `θ` in the weighted degree
  `∑ h, N (h, i) / d h`, then those of `blockSubst A⁻¹ (hasseDeriv I P)` vanish below (or at most)
  `θ` minus the weighted order of `I`.
* `MvPolynomial.coeff_blockSubst_hasseDeriv_eq_zero_of_notMem_Ioo`: for a multihomogeneous `P` in
  at least two variables per block, lower-tail vanishing at order zero along every row of `A`
  forces the coefficients of `blockSubst A⁻¹ (hasseDeriv I P)` to vanish outside the open interval
  `(m / card ι - 2 m η, m / card ι + 2 m (card ι - 1) η)`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press
  (2006), §7.5.14 and Lemma 7.5.15.
* J.-H. Evertse and H. P. Schlickewei, *A quantitative version of the Absolute Subspace Theorem*,
  J. Reine Angew. Math. 548 (2002), 21–127.
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

/-- Substituting square block-linear forms `MvPolynomial.blockLinearForm` is the linear
substitution `MvPolynomial.linearSubst` by the block-diagonal matrix with block `A h` on block
`h`. -/
theorem aeval_blockLinearForm_eq_linearSubst [Fintype κ] [DecidableEq κ] (A : κ → ι → ι → R) :
    aeval (blockLinearForm A) =
      linearSubst (Matrix.of fun p q : κ × ι ↦
        if p.1 = q.1 then A p.1 p.2 q.2 else 0) := by
  refine algHom_ext fun ⟨h, j⟩ ↦ ?_
  simp [blockLinearForm_apply, linearSubst_X, Fintype.sum_prod_type, apply_ite C, ite_mul]

/-- Block substitution is the linear substitution `MvPolynomial.linearSubst` of the
block-diagonal matrix `1 ⊗ₖ A`, with one copy of `A` for each block. -/
theorem blockSubst_eq_linearSubst [Fintype κ] [DecidableEq κ] (A : Matrix ι ι R) :
    (blockSubst A : MvPolynomial (κ × ι) R →ₐ[R] _) = linearSubst ((1 : Matrix κ κ R) ⊗ₖ A) := by
  rw [blockSubst_eq_aeval, aeval_blockLinearForm_eq_linearSubst]
  exact congrArg linearSubst (Matrix.ext fun _ _ ↦ by simp [Matrix.one_apply])

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

@[simp]
theorem blockSubst_zero (P : MvPolynomial (κ × ι) R) :
    blockSubst (0 : Matrix ι ι R) P = C (P.coeff 0) := by
  have h0 : blockLinearForm (fun (_ : κ) (_ _ : ι) ↦ (0 : R)) = 0 :=
    funext fun ⟨h, j⟩ ↦ by simp [blockLinearForm_apply]
  rw [blockSubst_eq_aeval]
  simp only [Matrix.zero_apply, h0, aeval_zero, algebraMap_eq, constantCoeff_eq]

/-- Block substitution preserves the constant coefficient. -/
@[simp]
theorem constantCoeff_blockSubst (A : Matrix ι ι R) (P : MvPolynomial (κ × ι) R) :
    constantCoeff (blockSubst A P) = constantCoeff P := by
  rw [← eval_zero, eval_blockSubst]
  simp

@[simp]
theorem coeff_zero_blockSubst (A : Matrix ι ι R) (P : MvPolynomial (κ × ι) R) :
    (blockSubst A P).coeff 0 = P.coeff 0 :=
  constantCoeff_blockSubst A P

/-- Changing the coefficients commutes with block substitution, after mapping the matrix entries. -/
theorem map_blockSubst {S : Type*} [CommSemiring S] (f : R →+* S) (A : Matrix ι ι R)
    (P : MvPolynomial (κ × ι) R) :
    map f (blockSubst A P) = blockSubst (A.map f) (map f P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [blockSubst_eq_aeval]
  | add p q hp hq => simp [hp, hq]
  | mul_X p q hp =>
    rcases q with ⟨h, j⟩
    simp [hp]

/-- Block substitution preserves multihomogeneity and the multidegree. -/
theorem IsMultiHomogeneous.blockSubst [DecidableEq κ] {d : κ → ℕ} {P : MvPolynomial (κ × ι) R}
    (hP : IsMultiHomogeneous d P) (A : Matrix ι ι R) :
    IsMultiHomogeneous d (MvPolynomial.blockSubst A P) :=
  isMultiHomogeneous_iff_forall_isWeightedHomogeneous.2 fun h ↦
    (hP.isWeightedHomogeneous h).aeval (isWeightedHomogeneous_blockLinearForm _ h)

/-- Rescaling the matrix by `c` rescales a homogeneous polynomial of degree `n` by `c ^ n`. -/
theorem IsHomogeneous.blockSubst_smul {P : MvPolynomial (κ × ι) R} {n : ℕ}
    (hp : P.IsHomogeneous n) (c : R) (A : Matrix ι ι R) :
    MvPolynomial.blockSubst (c • A) P = c ^ n • MvPolynomial.blockSubst A P := by
  have hlin : blockLinearForm (fun (_ : κ) j i ↦ (c • A) j i) =
      c • blockLinearForm (fun (_ : κ) j i ↦ A j i) := by
    funext ⟨h, j⟩
    simp [blockLinearForm_apply, Finset.smul_sum, smul_eq_C_mul, mul_assoc]
  rw [blockSubst_eq_aeval, blockSubst_eq_aeval, hlin, hp.aeval_smul_of_algebra]

/-- If row `i'` of `M` is the standard basis vector `Pi.single i 1`, then `blockSubst M` sends
`X (h, i')` to `X (h, i)`, so every monomial `N'` occurring in `blockSubst M (monomial N c)` has
exponent at least `N (h, i')` at `(h, i)` in every block `h`. -/
theorem coeff_blockSubst_monomial_eq_zero_of_lt [DecidableEq ι] {M : Matrix ι ι R} {i i' : ι}
    (hM : M i' = Pi.single i 1) {N N' : κ × ι →₀ ℕ} {c : R} {h : κ}
    (hlt : N' (h, i) < N (h, i')) :
    (blockSubst M (monomial N c)).coeff N' = 0 := by
  classical
  have hX : blockSubst M (X (h, i') : MvPolynomial (κ × ι) R) = X (h, i) := by
    simp [blockSubst_X, hM, Pi.single_apply, apply_ite C, ite_mul]
  have hsplit : monomial N c =
      monomial (N - Finsupp.single (h, i') (N (h, i'))) c * X (h, i') ^ N (h, i') := by
    rw [X_pow_eq_monomial, monomial_mul_monomial, mul_one,
      tsub_add_cancel_of_le (Finsupp.single_le_iff.2 le_rfl)]
  rw [hsplit, map_mul, map_pow, hX, X_pow_eq_monomial, coeff_mul_monomial', mul_one,
    ite_eq_right (mt Finsupp.single_le_iff.1 hlt.not_ge)]

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

/-- **Exponents along a shared row do not decrease** (Evertse–Schlickewei). Suppose `A` is
invertible and row `i'` of `A` equals row `i` of `B`. Every nonzero coefficient of
`blockSubst B⁻¹ P` at `N'` comes from some exponent vector `N` in the support of `blockSubst A⁻¹ P`
satisfying `N (h, i') ≤ N' (h, i)` in every block `h`. -/
theorem blockSubst_coeff_mem_of_row (hA : IsUnit A.det) {B : Matrix ι ι R} {i i' : ι}
    (hrow : A i' = B i) {P : MvPolynomial (κ × ι) R} {N' : κ × ι →₀ ℕ}
    (hN' : (blockSubst B⁻¹ P).coeff N' ≠ 0) :
    ∃ N ∈ (blockSubst A⁻¹ P).support, ∀ h, N (h, i') ≤ N' (h, i) := by
  classical
  by_cases hB : IsUnit B.det
  · -- Rewrite `blockSubst B⁻¹ P` as `blockSubst (A * B⁻¹) (blockSubst A⁻¹ P)`; row `i'` of
    -- `A * B⁻¹` is `Pi.single i 1`.
    have hAB : (A * B⁻¹) i' = Pi.single i 1 := by
      ext k
      have hk := congrArg (fun M : Matrix ι ι R ↦ M i k) (mul_nonsing_inv B hB)
      simpa [Matrix.mul_apply, congrFun hrow, Matrix.one_apply, Pi.single_apply, eq_comm] using hk
    have hsum : blockSubst B⁻¹ P = ∑ N ∈ (blockSubst A⁻¹ P).support,
        blockSubst (A * B⁻¹) (monomial N ((blockSubst A⁻¹ P).coeff N)) :=
      calc blockSubst B⁻¹ P
          = blockSubst (A * B⁻¹) (blockSubst A⁻¹ P) := by
            rw [blockSubst_mul_apply, blockSubst_blockSubst_inv hA]
        _ = _ := by
            conv_lhs => arg 2; rw [(blockSubst A⁻¹ P).as_sum]
            exact map_sum _ _ _
    rw [hsum, coeff_sum] at hN'
    obtain ⟨N, hN, hcoeff⟩ := exists_ne_zero_of_sum_ne_zero hN'
    refine ⟨N, hN, fun h ↦ not_lt.1 fun hlt ↦ hcoeff ?_⟩
    exact coeff_blockSubst_monomial_eq_zero_of_lt hAB hlt
  · -- When `B.det` is not a unit, `B⁻¹ = 0` and only `N' = 0` can occur, matched by `N = 0`.
    rw [nonsing_inv_apply_not_isUnit B hB, blockSubst_zero, coeff_C] at hN'
    split_ifs at hN' with h0
    · refine ⟨0, mem_support_iff.2 ?_, fun _ ↦ Nat.zero_le _⟩
      rwa [coeff_zero_blockSubst]
    · exact False.elim (hN' rfl)

/-- If the coefficients of `blockSubst A⁻¹ P` vanish whenever the weighted degree along row `i'` of
an invertible matrix `A` is at most `θ`, then the coefficients of `blockSubst B⁻¹ P` vanish
whenever the weighted degree along a matching row `B i = A i'` is at most `θ`. -/
theorem coeff_blockSubst_inv_eq_zero_of_row_eq [Fintype κ] (hA : IsUnit A.det) {B : Matrix ι ι R}
    {i i' : ι} (hrow : A i' = B i) {P : MvPolynomial (κ × ι) R} {d : κ → ℕ} {θ : ℝ}
    (hP : ∀ N : κ × ι →₀ ℕ, ∑ h, (N (h, i') : ℝ) / d h ≤ θ → (blockSubst A⁻¹ P).coeff N = 0)
    {N' : κ × ι →₀ ℕ} (hN' : ∑ h, (N' (h, i) : ℝ) / d h ≤ θ) :
    (blockSubst B⁻¹ P).coeff N' = 0 := by
  by_contra hc
  obtain ⟨N, hN, hle⟩ := blockSubst_coeff_mem_of_row hA hrow hc
  refine mem_support_iff.1 hN (hP N ((sum_le_sum fun h _ ↦ ?_).trans hN'))
  exact div_le_div_of_nonneg_right (Nat.cast_le.2 (hle h)) (Nat.cast_nonneg _)

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
  rw [AddMonoidAlgebra.coeff_smul_apply, hasseDeriv_coeff, hP e (mem_filter.1 he).2, mul_zero,
    smul_zero]

/-- **Vanishing along a form passes to Hasse derivatives** (Bombieri–Gubler, §7.5.14). Fix a
row `i` of the invertible matrix `A` and a multidegree `d`. If the coefficients of
`blockSubst A⁻¹ P` vanish at every exponent vector `N` whose weighted degree
`∑ h, N (h, i) / d h` in the variables `X (h, i)` is at most `θ`, then the coefficients of
`blockSubst A⁻¹ (hasseDeriv I P)` vanish at every `J` whose weighted degree is at most `θ` minus
the weighted order `∑ h, (∑ j, I (h, j)) / d h` of `I`. -/
theorem coeff_blockSubst_hasseDeriv_eq_zero_of_le [Fintype κ] (hA : IsUnit A.det)
    {P : MvPolynomial (κ × ι) R} {d : κ → ℕ} {i : ι} {θ : ℝ}
    (hP : ∀ N : κ × ι →₀ ℕ, ∑ h, (N (h, i) : ℝ) / d h ≤ θ → (blockSubst A⁻¹ P).coeff N = 0)
    {I J : κ × ι →₀ ℕ}
    (hJ : ∑ h, (J (h, i) : ℝ) / d h ≤ θ - ∑ h, ((∑ j, I (h, j) : ℕ) : ℝ) / d h) :
    (blockSubst A⁻¹ (hasseDeriv I P)).coeff J = 0 := by
  refine coeff_blockSubst_hasseDeriv_eq_zero_of_forall_coeff_add hA fun e he ↦ hP _ ?_
  -- Shifting by `e` raises the weighted degree in row `i` by at most the weighted order of `I`.
  have hle : ∑ h, (e (h, i) : ℝ) / d h ≤ ∑ h, ((∑ j, I (h, j) : ℕ) : ℝ) / d h := by
    refine sum_le_sum fun h _ ↦ div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
    rw [← he h]
    exact_mod_cast single_le_sum (f := fun j ↦ e (h, j)) (fun _ _ ↦ Nat.zero_le _) (mem_univ i)
  simp only [Finsupp.coe_add, Pi.add_apply, Nat.cast_add, add_div, sum_add_distrib]
  linarith

/-- Strict form of `coeff_blockSubst_hasseDeriv_eq_zero_of_le`: if the coefficients of
`blockSubst A⁻¹ P` vanish whenever `∑ h, N (h, i) / d h < θ`, then those of
`blockSubst A⁻¹ (hasseDeriv I P)` vanish whenever `∑ h, J (h, i) / d h` is strictly below `θ`
minus the weighted order of `I`. -/
theorem coeff_blockSubst_hasseDeriv_eq_zero [Fintype κ] (hA : IsUnit A.det)
    {P : MvPolynomial (κ × ι) R} {d : κ → ℕ} {i : ι} {θ : ℝ}
    (hP : ∀ N : κ × ι →₀ ℕ, ∑ h, (N (h, i) : ℝ) / d h < θ → (blockSubst A⁻¹ P).coeff N = 0)
    {I J : κ × ι →₀ ℕ}
    (hJ : ∑ h, (J (h, i) : ℝ) / d h < θ - ∑ h, ((∑ j, I (h, j) : ℕ) : ℝ) / d h) :
    (blockSubst A⁻¹ (hasseDeriv I P)).coeff J = 0 :=
  coeff_blockSubst_hasseDeriv_eq_zero_of_le hA
    (θ := ∑ h, (J (h, i) : ℝ) / d h + ∑ h, ((∑ j, I (h, j) : ℕ) : ℝ) / d h)
    (fun N hN ↦ hP N (hN.trans_lt (add_lt_of_lt_sub_right hJ))) (add_sub_cancel_right _ _).ge

/-- **Two-sided concentration from lower-tail vanishing** (Bombieri–Gubler, Lemma 7.5.15). Suppose
`ι` has at least two elements, `P` is multihomogeneous of multidegree `d`, and the coefficients of
`blockSubst A⁻¹ P` vanish whenever the weighted degree along any row `i'` of `A` is at most
`card κ / card ι - card κ * η`. Then for every order `I` of weighted order at most `card κ * η`,
the coefficients of `blockSubst A⁻¹ (hasseDeriv I P)` vanish at every `J` whose weighted degree
along some row `i` lies outside the open interval
`(card κ / card ι - 2 * card κ * η, card κ / card ι + 2 * card κ * (card ι - 1) * η)`. -/
theorem coeff_blockSubst_hasseDeriv_eq_zero_of_notMem_Ioo [Fintype κ] [DecidableEq κ] [Nontrivial ι]
    (hA : IsUnit A.det) {P : MvPolynomial (κ × ι) R} {d : κ → ℕ} (hP_hom : IsMultiHomogeneous d P)
    {η : ℝ} (hP : ∀ (i' : ι) (N : κ × ι →₀ ℕ),
      ∑ h, (N (h, i') : ℝ) / d h ≤ (Fintype.card κ : ℝ) / Fintype.card ι - Fintype.card κ * η →
      (blockSubst A⁻¹ P).coeff N = 0)
    {I J : κ × ι →₀ ℕ} (hI : ∑ h, ((∑ j, I (h, j) : ℕ) : ℝ) / d h ≤ Fintype.card κ * η)
    {i : ι} (hJ : ∑ h, (J (h, i) : ℝ) / d h ∉
      Set.Ioo ((Fintype.card κ : ℝ) / Fintype.card ι - 2 * Fintype.card κ * η)
        ((Fintype.card κ : ℝ) / Fintype.card ι + 2 * Fintype.card κ * (Fintype.card ι - 1) * η)) :
    (blockSubst A⁻¹ (hasseDeriv I P)).coeff J = 0 := by
  by_contra hne
  apply hJ
  -- Every row `i'` satisfies the strict lower bound, since `coeff J ≠ 0`.
  have hlow (i' : ι) :
      (Fintype.card κ : ℝ) / Fintype.card ι - 2 * Fintype.card κ * η <
        ∑ h, (J (h, i') : ℝ) / d h := by
    by_contra! hle
    exact hne (coeff_blockSubst_hasseDeriv_eq_zero_of_le hA (hP i') (by linarith))
  refine ⟨hlow i, ?_⟩
  -- Multihomogeneity bounds the sum over all rows by `card κ`; summing `hlow` over the remaining
  -- `card ι - 1 ≥ 1` rows bounds row `i` strictly from above.
  have htot : ∑ i', ∑ h, (J (h, i') : ℝ) / d h ≤ Fintype.card κ := by
    rw [sum_comm]
    refine (sum_le_sum (g := fun _ : κ ↦ (1 : ℝ)) fun h _ ↦ ?_).trans_eq (by simp)
    rcases eq_or_ne (d h) 0 with hd0 | hd0
    · simp [hd0]
    · simp_rw [div_eq_mul_inv, ← sum_mul, ← div_eq_mul_inv]
      refine (div_le_one (Nat.cast_pos.2 (Nat.pos_of_ne_zero hd0))).2 ?_
      have hdeg := isMultiHomogeneous_iff.1 ((hP_hom.hasseDeriv I).blockSubst A⁻¹) J hne h
      exact_mod_cast hdeg.trans_le (Nat.sub_le _ _)
  obtain ⟨i₁, hi₁⟩ := exists_ne i
  have hne_erase : (univ.erase i).Nonempty := ⟨i₁, mem_erase.2 ⟨hi₁, mem_univ _⟩⟩
  have herase : ((Fintype.card ι : ℝ) - 1) *
      ((Fintype.card κ : ℝ) / Fintype.card ι - 2 * Fintype.card κ * η) <
      ∑ i' ∈ univ.erase i, ∑ h, (J (h, i') : ℝ) / d h := by
    have hcard : (#(univ.erase i) : ℝ) = (Fintype.card ι : ℝ) - 1 := by
      have hk : 1 ≤ Fintype.card ι := Nat.one_le_iff_ne_zero.2 Fintype.card_ne_zero
      rw [card_erase_of_mem (mem_univ i), card_univ, Nat.cast_sub hk, Nat.cast_one]
    simpa only [sum_const, nsmul_eq_mul, hcard] using
      sum_lt_sum_of_nonempty hne_erase fun i' _ ↦ hlow i'
  have hsplit := add_sum_erase univ (fun i' ↦ ∑ h, (J (h, i') : ℝ) / d h) (mem_univ i)
  have hk0 : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hid : (Fintype.card κ : ℝ) - ((Fintype.card ι : ℝ) - 1) *
      ((Fintype.card κ : ℝ) / Fintype.card ι - 2 * Fintype.card κ * η) =
      (Fintype.card κ : ℝ) / Fintype.card ι + 2 * Fintype.card κ * (Fintype.card ι - 1) * η := by
    field_simp
    ring
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

/-- `Nontrivial ι` cannot be dropped in `coeff_blockSubst_hasseDeriv_eq_zero_of_notMem_Ioo`: with
`ι = Unit`, `κ = Unit`, `d = 1`, `A = 1`, `P = X`, and `η = 1 / 2`, the polynomial vanishes at the
only exponent `N = 0` below `1 - 1 / 2 = 1 / 2`, yet at `I = 0` and `J = 1` the weighted degree `1`
lies outside `Set.Ioo 0 1` while the coefficient of `P` at `J` is `1`. -/
example :
    let P : MvPolynomial (Unit × Unit) ℚ := X ((), ())
    (∀ (_ : Unit) (N : Unit × Unit →₀ ℕ),
      (N ((), ()) : ℝ) / 1 ≤ 1 / 1 - 1 * (1 / 2) →
      (blockSubst (1 : Matrix Unit Unit ℚ)⁻¹ P).coeff N = 0) ∧
    ((1 : ℝ) / 1 ∉ Set.Ioo (1 / 1 - 2 * 1 * (1 / 2)) (1 / 1 + 2 * 1 * (1 - 1) * (1 / 2))) ∧
    (blockSubst (1 : Matrix Unit Unit ℚ)⁻¹ (hasseDeriv 0 P)).coeff
      (Finsupp.single ((), ()) 1) = 1 := by
  refine ⟨fun _ N hN ↦ ?_, by norm_num, by simp [coeff_X]⟩
  have h0 : N = 0 := by
    ext ⟨⟨⟩, ⟨⟩⟩
    have : (N ((), ()) : ℝ) < 1 := by linarith
    exact_mod_cast Nat.lt_one_iff.1 (by exact_mod_cast this)
  simp [h0]

end MvPolynomial
