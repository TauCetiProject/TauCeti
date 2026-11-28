/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import TauCeti.RingTheory.MvPolynomial.LinearSubst
public import TauCeti.RingTheory.MvPolynomial.MultiHomogeneous
import TauCeti.Data.Finsupp.Weight
import TauCeti.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Linear changes of variables within polynomial blocks

Group the variables of a polynomial ring into blocks: `X (h, l)` is the variable `l` of block
`h`. Given blockwise coefficients `A : ι → κ → τ → R`, `MvPolynomial.blockLinearForm A` replaces
each variable `X (h, l)` by the linear form `∑ a, A h l a • X (h, a)` in the parameters of
the same block `h`. For a single square matrix `A : Matrix ι ι R` applied identically to every
block, `MvPolynomial.blockSubst A` substitutes `X (h, j) ↦ ∑ i, A j i • X (h, i)`.

When `A` is invertible, `blockSubst A⁻¹ P` writes `P` in the coordinates of the rows of `A`, and
if row `i'` of `A` coincides with row `i` of another matrix `B`, lower-tail vanishing of the
coefficients of `blockSubst A⁻¹ P` along row `i'` transfers to row `i` of `blockSubst B⁻¹ P`
(`MvPolynomial.coeff_blockSubst_inv_eq_zero_of_row_eq`).

## Main definitions

* `MvPolynomial.blockLinearForm A`: the block-linear forms `X (h, l) ↦ ∑ a, A h l a • X (h, a)`.
* `MvPolynomial.blockSubst A`: the substitution `X (h, j) ↦ ∑ i, A j i • X (h, i)` in every
  block.

## Main results

* `MvPolynomial.eval_blockLinearForm`, `MvPolynomial.eval_aeval_blockLinearForm`: evaluation of
  block-linear substitutions.
* `MvPolynomial.isHomogeneous_blockLinearForm`,
  `MvPolynomial.isWeightedHomogeneous_blockLinearForm`: homogeneity and block-indicator
  weighted homogeneity of `blockLinearForm`.
* `MvPolynomial.sum_eq_sum_of_coeff_aeval_blockLinearForm_ne_zero`,
  `MvPolynomial.degreeOf_aeval_blockLinearForm_le`: preservation of block degrees under
  block-linear substitution.
* `MvPolynomial.aeval_blockLinearForm_eq_linearSubst`, `MvPolynomial.blockSubst_eq_linearSubst`,
  `MvPolynomial.linearSubst_eq_aeval_blockLinearForm_of_block`: equivalence with block-diagonal
  `MvPolynomial.linearSubst`.
* `MvPolynomial.blockSubst_mul`, `MvPolynomial.blockSubst_inv_blockSubst`,
  `MvPolynomial.blockSubst_blockSubst_inv`: right monoid action and inversion for invertible
  matrices.
* `MvPolynomial.eval_blockSubst`, `MvPolynomial.blockSubst_zero`,
  `MvPolynomial.constantCoeff_blockSubst`, `MvPolynomial.map_blockSubst`: evaluation, zero matrix,
  constant coefficient, and coefficient maps.
* `MvPolynomial.IsMultiHomogeneous.aeval_blockLinearForm`,
  `MvPolynomial.IsMultiHomogeneous.blockSubst`,
  `MvPolynomial.IsMultiHomogeneous.linearSubst_of_block`,
  `MvPolynomial.IsHomogeneous.blockSubst_smul`: preservation of multihomogeneity and rescaling.
* `MvPolynomial.exists_mem_support_blockSubst_inv_le_of_coeff_ne_zero_of_row_eq`,
  `MvPolynomial.coeff_blockSubst_inv_eq_zero_of_row_eq`: shared-row exponent monotonicity and
  transfer of lower-tail vanishing.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  §7.5.14.
* J.-H. Evertse and H. P. Schlickewei, *A quantitative version of the Absolute Subspace Theorem*,
  J. Reine Angew. Math. 548 (2002), 21–127.
-/

public section

namespace MvPolynomial

open Finset Matrix
open scoped Kronecker

section BlockLinear

variable {R ι κ τ : Type*} [CommSemiring R] [Fintype τ]

/-- The block-linear forms `X_{h,l} ↦ ∑ₐ A_{h,l,a} Y_{h,a}`: the variable `l` of block `h` becomes
a linear form in the parameters `Y_{h,a}` of the same block. -/
noncomputable def blockLinearForm (A : ι → κ → τ → R) (p : ι × κ) : MvPolynomial (ι × τ) R :=
  ∑ a, C (A p.1 p.2 a) * X (p.1, a)

theorem blockLinearForm_apply (A : ι → κ → τ → R) (p : ι × κ) :
    blockLinearForm A p = ∑ a, C (A p.1 p.2 a) * X (p.1, a) :=
  (rfl)

/-- The value of a block-linear form at `y` is `∑ₐ A_{h,l,a} y_{h,a}`. -/
@[simp]
theorem eval_blockLinearForm (A : ι → κ → τ → R) (y : ι × τ → R) (p : ι × κ) :
    eval y (blockLinearForm A p) = ∑ a, A p.1 p.2 a * y (p.1, a) := by
  simp [blockLinearForm_apply]

/-- Evaluating after the block-linear substitution is evaluating at the point `Ay`. -/
theorem eval_aeval_blockLinearForm (A : ι → κ → τ → R) (y : ι × τ → R)
    (F : MvPolynomial (ι × κ) R) :
    eval y (aeval (blockLinearForm A) F) = eval (fun p ↦ ∑ a, A p.1 p.2 a * y (p.1, a)) F := by
  simpa only [aeval_eq_eval, eval_blockLinearForm] using
    comp_aeval_apply (blockLinearForm A) (aeval y) F

/-- Block-linear forms are linear forms: homogeneous of degree one. -/
theorem isHomogeneous_blockLinearForm (A : ι → κ → τ → R) (p : ι × κ) :
    (blockLinearForm A p).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun _ _ ↦ isHomogeneous_C_mul_X _ _

/-- With the indicator weight of block `b`, the block-linear form of a variable of block `h` is
weighted homogeneous of weight `1` if `h = b` and `0` otherwise. -/
theorem isWeightedHomogeneous_blockLinearForm [DecidableEq ι] (A : ι → κ → τ → R)
    (b : ι) (p : ι × κ) :
    (blockLinearForm A p).IsWeightedHomogeneous (fun q : ι × τ ↦ if q.1 = b then 1 else 0)
      (if p.1 = b then 1 else 0) :=
  IsWeightedHomogeneous.sum _ _ _ fun a _ ↦ (isWeightedHomogeneous_X _ _ (p.1, a)).C_mul _

/-- **Block degrees of the substitution coefficients.** If the coefficient
`c_{e,k} = [Y^k] ∏_{h,l} (∑ₐ A_{h,l,a} Y_{h,a})^(e_{h,l})` is nonzero, then `e` and `k` have the
same degree in every block: `∑ₗ e_{b,l} = ∑ₐ k_{b,a}`. -/
theorem sum_eq_sum_of_coeff_aeval_blockLinearForm_ne_zero [Fintype κ]
    {A : ι → κ → τ → R} {e : ι × κ →₀ ℕ} {k : ι × τ →₀ ℕ}
    (h : (aeval (blockLinearForm A) (monomial e (1 : R))).coeff k ≠ 0) (b : ι) :
    ∑ l, e (b, l) = ∑ a, k (b, a) := by
  classical
  have hw := IsWeightedHomogeneous.aeval
    (isWeightedHomogeneous_monomial (fun p : ι × κ ↦ if p.1 = b then 1 else 0) e (1 : R) rfl)
    (isWeightedHomogeneous_blockLinearForm A b)
  rw [← Finsupp.weight_ite_fst_eq_sum, ← Finsupp.weight_ite_fst_eq_sum, hw h]

/-- **Degrees after a block-linear substitution.** If every monomial of `F` has degree at most
`d h` in each block `h`, then the substituted polynomial `F(AY)` has degree at most `d h` in each
parameter `Y_{h,a}` of block `h`. -/
theorem degreeOf_aeval_blockLinearForm_le [Fintype κ] (A : ι → κ → τ → R)
    {F : MvPolynomial (ι × κ) R} {d : ι → ℕ} (hF : ∀ μ ∈ F.support, ∀ h, ∑ l, μ (h, l) ≤ d h)
    (q : ι × τ) : (aeval (blockLinearForm A) F).degreeOf q ≤ d q.1 := by
  classical
  refine degreeOf_le_iff.2 fun ν hν ↦ ?_
  rw [← support_sum_monomial_coeff F, map_sum] at hν
  obtain ⟨μ, hμ, hν⟩ := mem_biUnion.1 (support_sum hν)
  -- The substituted monomial `μ` has the block degree of `μ` in block `q.1`, hence so does `ν`.
  have hw := IsWeightedHomogeneous.aeval
    (isWeightedHomogeneous_monomial (fun p : ι × κ ↦ if p.1 = q.1 then 1 else 0) μ
      (F.coeff μ) rfl)
    (isWeightedHomogeneous_blockLinearForm A q.1)
  have hblock := hw (mem_support_iff.1 hν)
  rw [Finsupp.weight_ite_fst_eq_sum, Finsupp.weight_ite_fst_eq_sum] at hblock
  calc ν q ≤ ∑ a, ν (q.1, a) :=
        single_le_sum (f := fun a ↦ ν (q.1, a)) (fun _ _ ↦ Nat.zero_le _) (mem_univ q.2)
    _ = ∑ l, μ (q.1, l) := hblock
    _ ≤ d q.1 := hF μ hμ q.1

end BlockLinear

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

omit [Fintype ι] in
/-- Substituting block-linear forms preserves multihomogeneity and the multidegree. -/
theorem IsMultiHomogeneous.aeval_blockLinearForm [DecidableEq κ] {τ : Type*} [Fintype τ]
    {d : κ → ℕ} {P : MvPolynomial (κ × ι) R} (hP : IsMultiHomogeneous d P) (A : κ → ι → τ → R) :
    IsMultiHomogeneous d (aeval (blockLinearForm A) P) :=
  isMultiHomogeneous_iff_forall_isWeightedHomogeneous.2 fun h ↦
    (hP.isWeightedHomogeneous h).aeval (isWeightedHomogeneous_blockLinearForm _ h)

/-- Block substitution preserves multihomogeneity and the multidegree. -/
theorem IsMultiHomogeneous.blockSubst [DecidableEq κ] {d : κ → ℕ} {P : MvPolynomial (κ × ι) R}
    (hP : IsMultiHomogeneous d P) (A : Matrix ι ι R) :
    IsMultiHomogeneous d (MvPolynomial.blockSubst A P) :=
  hP.aeval_blockLinearForm _

/-- A linear substitution whose matrix is block diagonal, `M x y = 0` whenever `x` and `y` lie in
different blocks, is the substitution of the block-linear forms `MvPolynomial.blockLinearForm`
given by the diagonal blocks of `M`. -/
theorem linearSubst_eq_aeval_blockLinearForm_of_block [Fintype κ]
    {M : Matrix (κ × ι) (κ × ι) R} (hM : ∀ x y, x.1 ≠ y.1 → M x y = 0) :
    linearSubst M = aeval (blockLinearForm fun h p q ↦ M (h, p) (h, q)) := by
  classical
  rw [aeval_blockLinearForm_eq_linearSubst]
  congr 1
  ext ⟨h, p⟩ ⟨h', q⟩
  by_cases hh : h = h'
  · subst hh
    simp
  · simp [hh, hM (h, p) (h', q) hh]

/-- A linear substitution whose matrix is block diagonal, `M x y = 0` whenever `x` and `y` lie in
different blocks, preserves multihomogeneity and the multidegree. -/
theorem IsMultiHomogeneous.linearSubst_of_block [Fintype κ] [DecidableEq κ] {d : κ → ℕ}
    {P : MvPolynomial (κ × ι) R} (hP : IsMultiHomogeneous d P) {M : Matrix (κ × ι) (κ × ι) R}
    (hM : ∀ x y, x.1 ≠ y.1 → M x y = 0) :
    IsMultiHomogeneous d (linearSubst M P) := by
  rw [linearSubst_eq_aeval_blockLinearForm_of_block hM]
  exact hP.aeval_blockLinearForm _

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
theorem exists_mem_support_blockSubst_inv_le_of_coeff_ne_zero_of_row_eq (hA : IsUnit A.det)
    {B : Matrix ι ι R} {i i' : ι} (hrow : A i' = B i) {P : MvPolynomial (κ × ι) R}
    {N' : κ × ι →₀ ℕ} (hN' : (blockSubst B⁻¹ P).coeff N' ≠ 0) :
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
  obtain ⟨N, hN, hle⟩ := exists_mem_support_blockSubst_inv_le_of_coeff_ne_zero_of_row_eq hA hrow hc
  refine mem_support_iff.1 hN (hP N ((sum_le_sum fun h _ ↦ ?_).trans hN'))
  exact div_le_div_of_nonneg_right (Nat.cast_le.2 (hle h)) (Nat.cast_nonneg _)

end CommRing

end MvPolynomial
