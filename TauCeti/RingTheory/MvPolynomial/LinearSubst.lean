/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.RepresentationTheory.Basic
public import TauCeti.Algebra.MvPolynomial.PDeriv
public import TauCeti.RingTheory.MvPolynomial.Homogeneous
public import TauCeti.RingTheory.MvPolynomial.Rescale
import Mathlib.Algebra.MvPolynomial.Coeff
import TauCeti.Algebra.MvPolynomial.Monomial
import TauCeti.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Linear changes of variables in multivariate polynomials

For a square matrix `M` indexed by the variables, `MvPolynomial.linearSubst M` is the
`R`-algebra endomorphism of `R[Xᵢ : i ∈ σ]` substituting `Xᵢ ↦ ∑ⱼ Mᵢⱼ Xⱼ`. Evaluated at a
point `x`, the polynomial `linearSubst M p` is `p` evaluated at `M *ᵥ x`: the substitution is
the pullback of polynomial functions along `M`. It is therefore a *right* action of the matrix
monoid, `linearSubst (M * N) = (linearSubst N).comp (linearSubst M)`.

The substitution preserves homogeneity, and on forms of degree `n` a scalar matrix `c • 1`
acts by `cⁿ`. Restricted to the forms of a fixed degree `n` it is the representation
`MvPolynomial.linearSubstRep` of the opposite matrix monoid on `homogeneousSubmodule σ R n`.
In two variables this is the action `P ↦ P(aX + bY, cX + dY)` of `2 × 2` matrices on binary
forms of degree `n`, through which the modular group acts on period polynomials.

Its transpose `TauCeti.polynomialAction g` substitutes the standard vectors instead: the variable
`X j`, the `j`-th standard vector of `Rˢ`, goes to its image `∑ᵢ gᵢⱼ X i` under `g`. In two
variables, with `x = X 0` and `y = X 1`, the matrix `!![a, b; c, d]` substitutes `x ↦ a x + c y`
and `y ↦ b x + d y`. It is a left action,
`polynomialAction (g * h) = polynomialAction g ∘ polynomialAction h`, and restricted to the forms of
degree `d` it is the representation `TauCeti.polynomialRep` of the general linear group.

## Main definitions

* `MvPolynomial.linearSubst`: the substitution `Xᵢ ↦ ∑ⱼ Mᵢⱼ Xⱼ`.
* `MvPolynomial.linearSubstRep`: its restriction to forms of degree `n`, as a representation of
  `(Matrix σ σ R)ᵐᵒᵖ`.
* `TauCeti.polynomialAction`: the substitution of standard vectors by a square matrix.
* `TauCeti.polynomialRep`: its restriction to forms of degree `d`, as a representation of
  `GL σ R`.

## Main results

* `MvPolynomial.aeval_linearSubst`: `linearSubst M p` evaluated at `x` is `p` evaluated at
  `M *ᵥ x`.
* `MvPolynomial.linearSubst_mul`: the substitution is a right action.
* `MvPolynomial.pderiv_linearSubst`: the chain rule
  `∂/∂Xⱼ (linearSubst M p) = ∑ᵢ Mᵢⱼ linearSubst M (∂p/∂Xᵢ)`.
* `MvPolynomial.exists_aeval_pderiv_linearSubst_ne_zero`: a substitution with nonzero
  determinant preserves nonvanishing of the gradient at nonzero zeros over a faithful algebra
  without zero divisors.
* `MvPolynomial.map_linearSubst`: changing coefficients commutes with substitution.
* `MvPolynomial.linearSubst_diagonal`: a diagonal matrix rescales the variables by its
  diagonal entries.
* `MvPolynomial.linearSubst_diagonal_monomial`: a diagonal matrix scales each monomial by
  the product of its diagonal entries raised to the corresponding exponents.
* `MvPolynomial.coeff_linearSubst_X_pow_mul_X_pow`: the coefficients of a linear change of
  variables of a monomial in two variables.
* `MvPolynomial.coeff_linearSubst_upperTriangular_monomial`: under an upper-triangular
  substitution in two variables, the coefficient of `X₀ᵏ X₁ˡ` in its own image is `aᵏ dˡ`.
* `MvPolynomial.IsHomogeneous.linearSubst`: the substitution preserves homogeneity.
* `MvPolynomial.IsHomogeneous.linearSubst_smul`: rescaling the matrix by `c` rescales a form
  of degree `n` by `cⁿ`.
* `MvPolynomial.homogeneousComponent_linearSubst`: the substitution commutes with taking
  homogeneous components.
* `MvPolynomial.eq_zero_of_add_self_eq_zero`: a polynomial is zero if adding it to itself is
  zero and multiplication by `2` is injective on coefficients.
* `TauCeti.polynomialAction_mul`: the substitution of standard vectors is a left action.
* `TauCeti.polynomialAction_sum_C_mul_X`: on linear forms it is matrix-vector multiplication of
  the coefficient vector.
-/

public section

open Matrix MulOpposite

namespace MvPolynomial

variable {σ R : Type*} [Fintype σ] [CommSemiring R]

omit [Fintype σ] in
/-- A polynomial is zero if adding it to itself is zero and multiplication by `2` is injective
on coefficients. -/
theorem eq_zero_of_add_self_eq_zero (h2 : Function.Injective fun r : R ↦ 2 * r)
    {p : MvPolynomial σ R} (h : p + p = 0) : p = 0 := by
  ext m
  apply h2
  simpa [two_mul] using congrArg (fun q : MvPolynomial σ R ↦ q.coeff m) h

/-- The linear change of variables `Xᵢ ↦ ∑ⱼ Mᵢⱼ Xⱼ` given by a square matrix `M`. -/
noncomputable def linearSubst (M : Matrix σ σ R) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  aeval fun i ↦ ∑ j, C (M i j) * X j

theorem linearSubst_eq_aeval (M : Matrix σ σ R) :
    linearSubst M = aeval fun i ↦ ∑ j, C (M i j) * X j :=
  (rfl)

@[simp]
theorem linearSubst_X (M : Matrix σ σ R) (i : σ) :
    linearSubst M (X i) = ∑ j, C (M i j) * X j :=
  aeval_X _ _

/-- Changing the coefficients commutes with substitution, after mapping the matrix entries. -/
theorem map_linearSubst {S : Type*} [CommSemiring S] (f : R →+* S) (M : Matrix σ σ R)
    (p : MvPolynomial σ R) :
    map f (linearSubst M p) = linearSubst (M.map f) (map f p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [linearSubst_eq_aeval]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

/-- A diagonal change of variables is the rescaling of the variables by the diagonal entries. -/
theorem linearSubst_diagonal [DecidableEq σ] (v : σ → R) :
    linearSubst (Matrix.diagonal v) = rescale v := by
  refine algHom_ext fun i ↦ ?_
  rw [linearSubst_X, rescale_X, Finset.sum_eq_single i (fun j _ hji ↦ by simp [Ne.symm hji])
    (by simp), diagonal_apply_eq]

/-- A diagonal change of variables scales a monomial by the product of its eigenvalues. -/
@[simp]
theorem linearSubst_diagonal_monomial [DecidableEq σ] (v : σ → R) (s : σ →₀ ℕ) :
    linearSubst (Matrix.diagonal v) (monomial s 1) =
      (s.prod fun i k => v i ^ k) • monomial s 1 := by
  rw [linearSubst_diagonal, rescale_monomial, smul_eq_C_mul, C_mul_monomial]

/-- The coefficients of a linear change of variables of a monomial in two variables: the
coefficient of `X₀ʲ X₁ⁱ⁺ᵏ⁻ʲ` in `(A₀₀ X₀ + A₀₁ X₁)ⁱ (A₁₀ X₀ + A₁₁ X₁)ᵏ` is
`∑ₗ C(i, l) C(k, j - l) A₀₀ˡ A₀₁ⁱ⁻ˡ A₁₀ʲ⁻ˡ A₁₁ᵏ⁻⁽ʲ⁻ˡ⁾`, the sum over `l ≤ i` with `l ≤ j` and
`j - l ≤ k`. -/
theorem coeff_linearSubst_X_pow_mul_X_pow (A : Matrix (Fin 2) (Fin 2) R) (i k j : ℕ) :
    (linearSubst A (X 0 ^ i * X 1 ^ k)).coeff
        (Finsupp.single 0 j + Finsupp.single 1 (i + k - j)) =
      ∑ l ∈ Finset.range (i + 1), if l ≤ j ∧ j - l ≤ k then
        i.choose l * k.choose (j - l) * A 0 0 ^ l * A 0 1 ^ (i - l) * A 1 0 ^ (j - l) *
          A 1 1 ^ (k - (j - l)) else 0 := by
  have hsingle {a b c d : ℕ} : Finsupp.single (0 : Fin 2) a + Finsupp.single 1 b =
      Finsupp.single 0 c + Finsupp.single 1 d ↔ a = c ∧ b = d := by
    simp [Finsupp.ext_iff, Fin.forall_fin_two]
  simp only [map_mul, map_pow, linearSubst_X, Fin.sum_univ_two, C_mul_X_add_C_mul_X_pow,
    Finset.sum_mul_sum, monomial_mul_monomial, coeff_sum, coeff_monomial, add_add_add_comm,
    ← Finsupp.single_add, hsingle]
  refine Finset.sum_congr rfl fun l hl ↦ ?_
  split_ifs with h
  · rw [Finset.sum_eq_single_of_mem (j - l) (by grind) fun m _ hm ↦ ite_eq_right (by omega),
      ite_eq_left (by grind)]
    grind
  · exact Finset.sum_eq_zero fun _ hm ↦ ite_eq_right (by grind)

/-- An upper-triangular change of variables in two variables is triangular on monomials: the
coefficient of `X₀ᵏ X₁ˡ` in the image of `X₀ᵏ X₁ˡ` is `aᵏ dˡ`, independently of `b`. -/
theorem coeff_linearSubst_upperTriangular_monomial (a b d : R) (s : Fin 2 →₀ ℕ) :
    (linearSubst !![a, b; 0, d] (monomial s 1)).coeff s = a ^ s 0 * d ^ s 1 := by
  have hs : Finsupp.single 0 (s 0) + Finsupp.single 1 (s 0 + s 1 - s 0) = s := by
    ext i
    fin_cases i <;> simp
  have hm : monomial s (1 : R) = X 0 ^ s 0 * X 1 ^ s 1 := by
    simpa using monomial_fin_two s (1 : R)
  have h := coeff_linearSubst_X_pow_mul_X_pow !![a, b; 0, d] (s 0) (s 1) (s 0)
  rw [hs] at h
  rw [hm, h, Finset.sum_eq_single (s 0) (fun l _ hne ↦ ?_) (by simp)]
  · simp
  · split_ifs with hl'
    · have hsub : s 0 - l ≠ 0 := by grind
      simp [hsub]
    · rfl

/-- Evaluating `linearSubst M p` at `x` is evaluating `p` at `M *ᵥ x`. -/
theorem aeval_linearSubst {S : Type*} [CommSemiring S] [Algebra R S] (M : Matrix σ σ R)
    (x : σ → S) (p : MvPolynomial σ R) :
    aeval x (linearSubst M p) = aeval (M.map (algebraMap R S) *ᵥ x) p := by
  rw [← AlgHom.comp_apply]
  congr 1
  refine algHom_ext fun i ↦ ?_
  simp [mulVec, dotProduct]

/-- Evaluating `linearSubst M p` at `x` is evaluating `p` at `M *ᵥ x`. -/
theorem eval_linearSubst (M : Matrix σ σ R) (x : σ → R) (p : MvPolynomial σ R) :
    eval x (linearSubst M p) = eval (M *ᵥ x) p := by
  simpa using aeval_linearSubst M x p

/-- **The chain rule for a linear change of variables**:
`∂/∂Xⱼ (linearSubst M p) = ∑ᵢ Mᵢⱼ linearSubst M (∂p/∂Xᵢ)`. -/
theorem pderiv_linearSubst (M : Matrix σ σ R) (j : σ) (p : MvPolynomial σ R) :
    pderiv j (linearSubst M p) = ∑ i, C (M i j) * linearSubst M (pderiv i p) := by
  classical
  rw [linearSubst_eq_aeval, pderiv_aeval]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp [pderiv_X, Pi.single_apply, mul_comm]

/-- A linear substitution with nonzero determinant preserves nonvanishing of the gradient at
nonzero zeros: if at every nonzero zero `b ∈ Kˢ` of `p` some partial derivative of `p` is
nonzero, then the same holds for `linearSubst M p`. The coefficient ring embeds faithfully
into the evaluation algebra `K`, which has no zero divisors. -/
theorem exists_aeval_pderiv_linearSubst_ne_zero [DecidableEq σ] {k K : Type*} [CommRing k]
    [CommRing K] [NoZeroDivisors K] [Algebra k K] [FaithfulSMul k K]
    {p : MvPolynomial σ k} {M : Matrix σ σ k} (hM : M.det ≠ 0)
    (hp : ∀ b : σ → K, b ≠ 0 → aeval b p = 0 → ∃ l, aeval b (pderiv l p) ≠ 0)
    {b : σ → K} (hb : b ≠ 0) (hpb : aeval b (linearSubst M p) = 0) :
    ∃ l, aeval b (pderiv l (linearSubst M p)) ≠ 0 := by
  set M' := M.map (algebraMap k K)
  have hM' : M'.det ≠ 0 := by
    simpa only [M', ← RingHom.mapMatrix_apply, ← RingHom.map_det] using
      (FaithfulSMul.algebraMap_eq_zero_iff k K).not.mpr hM
  rw [aeval_linearSubst] at hpb
  obtain ⟨l, hl⟩ := hp (M' *ᵥ b) (fun h ↦ hb (eq_zero_of_mulVec_eq_zero hM' h)) hpb
  by_contra! h
  -- The gradient of `p` at `M b`, multiplied by `M`, is the gradient of `linearSubst M p` at `b`.
  have hvec : (fun i ↦ aeval (M' *ᵥ b) (pderiv i p)) ᵥ* M' = 0 := by
    ext j
    have hj := h j
    rw [pderiv_linearSubst] at hj
    simpa [vecMul, dotProduct, aeval_linearSubst, M', mul_comm] using hj
  exact hl (congrFun (eq_zero_of_vecMul_eq_zero hM' hvec) l)

@[simp]
theorem linearSubst_one [DecidableEq σ] : linearSubst (1 : Matrix σ σ R) = AlgHom.id R _ :=
  algHom_ext fun i ↦ by simp [Matrix.one_apply]

/-- The substitution is a right action of the matrix monoid: substituting along `M * N` is
substituting along `M` and then along `N`. -/
theorem linearSubst_mul (M N : Matrix σ σ R) :
    linearSubst (M * N) = (linearSubst N).comp (linearSubst M) := by
  refine algHom_ext fun i ↦ ?_
  simp only [map_sum C, Finset.sum_mul, mul_assoc, linearSubst_X, AlgHom.comp_apply, map_sum,
    map_mul, algHom_C, Matrix.mul_apply, Finset.mul_sum, algebraMap_eq]
  exact Finset.sum_comm

theorem linearSubst_mul_apply (M N : Matrix σ σ R) (p : MvPolynomial σ R) :
    linearSubst (M * N) p = linearSubst N (linearSubst M p) := by
  rw [linearSubst_mul, AlgHom.comp_apply]

/-- A linear change of variables preserves homogeneity. -/
theorem IsHomogeneous.linearSubst {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsHomogeneous n)
    (M : Matrix σ σ R) : (MvPolynomial.linearSubst M p).IsHomogeneous n := by
  rw [linearSubst_eq_aeval, ← one_mul n]
  exact hp.aeval _ fun i ↦ IsHomogeneous.sum _ _ _ fun j _ ↦ isHomogeneous_C_mul_X (M i j) j

/-- Rescaling the matrix by `c` rescales a form of degree `n` by `cⁿ`. -/
theorem IsHomogeneous.linearSubst_smul {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsHomogeneous n)
    (c : R) (M : Matrix σ σ R) :
    MvPolynomial.linearSubst (c • M) p = c ^ n • MvPolynomial.linearSubst M p := by
  simpa only [linearSubst_eq_aeval, Pi.smul_def, Finset.smul_sum, Matrix.smul_apply,
    smul_eq_mul, smul_eq_C_mul, map_mul, mul_assoc] using
    hp.aeval_smul_of_algebra (S := R) (A := MvPolynomial σ R) (fun i ↦ ∑ j, C (M i j) * X j) c

/-- On forms of degree `n`, negating the matrix multiplies by `(-1)ⁿ`. -/
theorem IsHomogeneous.linearSubst_neg {R : Type*} [CommRing R] {p : MvPolynomial σ R} {n : ℕ}
    (hp : p.IsHomogeneous n) (M : Matrix σ σ R) :
    MvPolynomial.linearSubst (-M) p = (-1 : R) ^ n • MvPolynomial.linearSubst M p := by
  rw [← neg_one_smul R M, hp.linearSubst_smul]

/-- A linear change of variables commutes with taking homogeneous components. -/
theorem homogeneousComponent_linearSubst (M : Matrix σ σ R) (n : ℕ) (p : MvPolynomial σ R) :
    homogeneousComponent n (linearSubst M p) = linearSubst M (homogeneousComponent n p) :=
  weightedHomogeneousComponent_aeval (w := 1)
    (fun i ↦ IsHomogeneous.sum _ _ _ fun j _ ↦ isHomogeneous_C_mul_X (M i j) j) p n

variable (σ R) in
/-- The linear changes of variables restricted to the forms of degree `n`, as a representation
of the opposite matrix monoid: `op M` acts by `p ↦ linearSubst M p`. -/
noncomputable def linearSubstRep [DecidableEq σ] (n : ℕ) :
    Representation R (Matrix σ σ R)ᵐᵒᵖ (homogeneousSubmodule σ R n) where
  toFun M := (linearSubst M.unop).toLinearMap.restrict fun _ hp ↦ IsHomogeneous.linearSubst hp _
  map_one' := LinearMap.ext fun p ↦ Subtype.ext <| by simp
  map_mul' M N := LinearMap.ext fun p ↦ Subtype.ext <| linearSubst_mul_apply _ _ _

@[simp]
theorem coe_linearSubstRep_apply [DecidableEq σ] {n : ℕ} (M : (Matrix σ σ R)ᵐᵒᵖ)
    (p : homogeneousSubmodule σ R n) :
    (linearSubstRep σ R n M p : MvPolynomial σ R) = linearSubst M.unop p :=
  (rfl)

end MvPolynomial

namespace TauCeti

open MvPolynomial

section Action

variable {σ R : Type*} [Fintype σ] [CommSemiring R]

/-- The substitution of standard vectors by a square matrix `g`: the variable `X j`, the `j`-th
standard vector, goes to its image `∑ᵢ gᵢⱼ X i` under `g`. In two variables the matrix
`!![a, b; c, d]` substitutes `X 0 ↦ a X 0 + c X 1` and `X 1 ↦ b X 0 + d X 1`. -/
noncomputable def polynomialAction (g : Matrix σ σ R) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  linearSubst gᵀ

/-- The substitution of standard vectors is the change of variables along the transpose. -/
theorem polynomialAction_eq_linearSubst_transpose (g : Matrix σ σ R) :
    polynomialAction g = linearSubst gᵀ :=
  (rfl)

@[simp]
theorem polynomialAction_X (g : Matrix σ σ R) (j : σ) :
    polynomialAction g (X j) = ∑ i, C (g i j) * X i := by
  simp [polynomialAction_eq_linearSubst_transpose]

@[simp]
theorem polynomialAction_one [DecidableEq σ] :
    polynomialAction (1 : Matrix σ σ R) = AlgHom.id R _ := by
  simp [polynomialAction_eq_linearSubst_transpose]

/-- The substitution of standard vectors is a left action of the matrix monoid. -/
theorem polynomialAction_mul (g h : Matrix σ σ R) :
    polynomialAction (g * h) = (polynomialAction g).comp (polynomialAction h) := by
  rw [polynomialAction_eq_linearSubst_transpose, transpose_mul, linearSubst_mul]
  rfl

theorem polynomialAction_mul_apply (g h : Matrix σ σ R) (p : MvPolynomial σ R) :
    polynomialAction (g * h) p = polynomialAction g (polynomialAction h p) := by
  rw [polynomialAction_mul, AlgHom.comp_apply]

/-- On linear forms the substitution of standard vectors is matrix-vector multiplication of the
coefficient vector: the linear form with coefficients `v` goes to the one with coefficients
`g *ᵥ v`. -/
theorem polynomialAction_sum_C_mul_X (g : Matrix σ σ R) (v : σ → R) :
    polynomialAction g (∑ j, C (v j) * X j) = ∑ i, C ((g *ᵥ v) i) * X i := by
  simp only [map_sum, map_mul, polynomialAction_X, algHom_C, algebraMap_eq, Finset.mul_sum,
    mulVec, dotProduct, map_sum C, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  ring

/-- A diagonal matrix rescales each variable by its diagonal entry. -/
theorem polynomialAction_diagonal [DecidableEq σ] (t : σ → R) :
    polynomialAction (diagonal t) = rescale t := by
  rw [polynomialAction_eq_linearSubst_transpose, diagonal_transpose, linearSubst_diagonal]

/-- The substitution of standard vectors preserves homogeneity. -/
theorem _root_.MvPolynomial.IsHomogeneous.polynomialAction {p : MvPolynomial σ R} {n : ℕ}
    (hp : p.IsHomogeneous n) (g : Matrix σ σ R) :
    (TauCeti.polynomialAction g p).IsHomogeneous n :=
  hp.linearSubst gᵀ

/-- The substitution of standard vectors commutes with taking homogeneous components. -/
theorem homogeneousComponent_polynomialAction (g : Matrix σ σ R) (n : ℕ) (p : MvPolynomial σ R) :
    homogeneousComponent n (polynomialAction g p) = polynomialAction g (homogeneousComponent n p) :=
  homogeneousComponent_linearSubst gᵀ n p

/-- Evaluating `polynomialAction g p` at `x` is evaluating `p` at `gᵀ *ᵥ x`. -/
theorem eval_polynomialAction (g : Matrix σ σ R) (x : σ → R) (p : MvPolynomial σ R) :
    eval x (polynomialAction g p) = eval (gᵀ *ᵥ x) p :=
  eval_linearSubst gᵀ x p

variable (σ R) in
/-- The substitution of standard vectors restricted to the forms of degree `d`, as a
representation of the general linear group. -/
noncomputable def polynomialRep [DecidableEq σ] (d : ℕ) :
    Representation R (GL σ R) (homogeneousSubmodule σ R d) :=
  (linearSubstRep σ R d).comp ((transposeRingEquiv σ R).toMonoidHom.comp (Units.coeHom _))

@[simp]
theorem coe_polynomialRep_apply [DecidableEq σ] {d : ℕ} (g : GL σ R)
    (p : homogeneousSubmodule σ R d) :
    (polynomialRep σ R d g p : MvPolynomial σ R) = polynomialAction (g : Matrix σ σ R) p := by
  simp [polynomialRep, polynomialAction_eq_linearSubst_transpose]

end Action

end TauCeti
