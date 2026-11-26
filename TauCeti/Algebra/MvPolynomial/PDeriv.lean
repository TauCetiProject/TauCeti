/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.RingTheory.Ideal.Operations

import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.MvPowerSeries.Derivative
import TauCeti.Algebra.MvPolynomial.Eval

/-!
# Partial derivatives of multivariate polynomials: chain rule, degree and coefficients

Substituting polynomials `fᵢ ∈ R[Y_τ]` for the variables `Xᵢ` of `p ∈ R[X_σ]` and differentiating
with respect to `Y_j` obeys the chain rule

`∂/∂Y_j (p(f)) = ∑ᵢ (∂p/∂Xᵢ)(f) · ∂fᵢ/∂Y_j`,

where the sum runs over any finite set of indices containing the variables of `p`. The same rule
holds for a substitution of univariate polynomials, with the derivative `d/dY` in place of
`∂/∂Y_j`. Likewise a derivation `D` dual to a family `x` along the index `i`, that is, with
`D xⱼ = 1` for `j = i` and `D xⱼ = 0` otherwise, acts on `p(x)` as the partial derivative `∂/∂Xᵢ`.

Partial differentiation lowers the total degree, and the degree in the differentiated variable,
by at least one, so the `k`-th iterated partial derivative along `Xᵢ` of a polynomial of degree
less than `k` in `Xᵢ` vanishes; it also keeps the coefficients in any additive submonoid of the
coefficient ring, such as a subring. These are the facts needed to clear the denominators of
derivatives of polynomials evaluated at algebraic points.

Over a commutative ring the gradient at a point `t` linearises a polynomial up to a divisibility
or ideal-product error: if `xᵢ - tᵢ ∈ I`, `x'ᵢ - tᵢ ∈ I` and `x'ᵢ - xᵢ ∈ J`, then
`p(x') - p(x) - ∑ⱼ ∂ⱼp(t) (x'ⱼ - xⱼ)` lies in `I * J` (and is divisible by `d * e` when `I = (d)`,
`J = (e)` with `d ∣ e`). Specialising `x = t` and `I = J` linearises `p(x') - p(t)` modulo `I ^ 2`
over any finite set `s` containing the variables of `p` at which `x'` and `t` differ. This is the
several-variable form of `Polynomial.mul_dvd_eval_sub_eval_sub_mul` and the estimate behind
Newton's method with an approximately invertible Jacobian.

Over a commutative ring with `HasUniqueDiv`, a polynomial is uniquely determined by its formal
partial derivatives and its constant coefficient (`MvPolynomial.pderiv.ext`, inherited from
`MvPowerSeries.pderiv.ext`); in particular, all partial derivatives vanish if and only if the
polynomial is constant, and two polynomials with equal partial derivatives differ by the constant
difference of their constant coefficients.

Over an infinite domain, a polynomial vanishing on the line through `a` in the direction of a
coordinate axis has vanishing partial derivative along that axis at `a`: its restriction to the
line is the zero polynomial, and the chain rule identifies the derivative of the restriction.
Hence a polynomial vanishing on a submodule containing the `i`-th standard basis vector has all
its iterated partial derivatives in `Xᵢ` vanishing there too.

## Main results

* `MvPolynomial.pderiv_X_mul_of_ne`: multiplication by `Xᵢ` commutes with `∂/∂Xⱼ` for `j ≠ i`.
* `MvPolynomial.pderiv_aeval`: the chain rule, summed over all variables of a finite type.
* `MvPolynomial.derivative_aeval`: the chain rule for a substitution of univariate polynomials.
* `MvPolynomial.pderiv_aeval_of_vars_subset`: the chain rule, summed over a finite set containing
  the variables of `p`.
* `Derivation.map_aeval_eq_aeval_pderiv`: a derivation dual to `x` along the index `i` acts on
  `p(x)` as the partial derivative `∂/∂Xᵢ`.
* `MvPolynomial.vars_pderiv_subset`: partial differentiation introduces no new variables.
* `MvPolynomial.hasFiniteSupport_pderiv`: only finitely many partial derivatives of a polynomial
  are nonzero.
* `MvPolynomial.derivation_apply_eq_sum_vars`: every derivation `D` on `MvPolynomial σ R` satisfies
  `D p = ∑ i ∈ p.vars, pderiv i p • D (X i)`.
* `MvPolynomial.totalDegree_iterate_pderiv_le`: the `k`-th iterated partial derivative has total
  degree at most `totalDegree p - k`.
* `MvPolynomial.degreeOf_iterate_pderiv_le`: the `k`-th iterated partial derivative along `Xᵢ` has
  degree at most `degreeOf i p - k` in `Xᵢ`.
* `MvPolynomial.iterate_pderiv_eq_zero_of_degreeOf_lt`: the `k`-th iterated partial derivative
  along `Xᵢ` vanishes when `degreeOf i p < k`.
* `MvPolynomial.coeff_iterate_pderiv_mem`: iterated partial derivatives keep the coefficients in
  an additive submonoid.
* `MvPolynomial.iterate_pderiv_map`: iterated partial derivatives commute with coefficient maps.
* `MvPolynomial.iterate_pderiv_monomial`: the `k`-th iterated partial derivative along `Xᵢ` of the
  monomial `a X^m` is `a mᵢ (mᵢ - 1) ⋯ (mᵢ - k + 1) X^(m - k eᵢ)`.
* `MvPolynomial.iterate_pderiv_prod_aeval_X`: on a separated product `∏ⱼ Qⱼ(Xⱼ)` of one-variable
  polynomials, the `k`-th iterated partial derivative along `Xᵢ` is `Qᵢ⁽ᵏ⁾(Xᵢ) ∏_{j ≠ i} Qⱼ(Xⱼ)`.
* `MvPolynomial.eval_sub_eval_sub_sum_pderiv_mem_mul`,
  `MvPolynomial.eval_sub_eval_sub_sum_pderiv_mem_sq`: Taylor's ideal-product estimate
  `p(x') - p(x) - ∑ⱼ ∂ⱼp(t) (x'ⱼ - xⱼ) ∈ I * J`, and its first-order specialisation modulo `I ^ 2`
  over an arbitrary variable type.
* `MvPolynomial.sq_dvd_eval_add_smul_sub_sum_pderiv`: the first-order Taylor estimate
  `d ^ 2 ∣ p(a + d b) - p(a) - d ∑ⱼ ∂ⱼp(a) bⱼ`.
* `MvPolynomial.mul_dvd_eval_sub_eval_sub_sum_pderiv`: Taylor's divisibility estimate
  `d * e ∣ p(x') - p(x) - ∑ⱼ ∂ⱼp(t) (x'ⱼ - xⱼ)`.
* `MvPolynomial.pderiv.ext`: over a commutative ring with `HasUniqueDiv`, a polynomial is
  determined by its formal partial derivatives and its constant coefficient.
* `MvPolynomial.eq_C_constantCoeff_of_forall_pderiv_eq_zero`,
  `MvPolynomial.forall_pderiv_eq_zero_iff`: a polynomial has vanishing formal gradient if and only
  if it is constant.
* `MvPolynomial.sub_eq_C_of_forall_pderiv_eq`: two polynomials with equal formal partial
  derivatives differ by the difference of their constant coefficients.
* `MvPolynomial.eval_pderiv_eq_zero_of_forall_eval_add_smul_single`: over an infinite domain, a
  polynomial vanishing on the line through `a` along `Xᵢ` has `∂p/∂Xᵢ` vanishing at `a`.
* `MvPolynomial.eval_iterate_pderiv_eq_zero_of_forall_mem`: a polynomial vanishing on a submodule
  containing the `i`-th standard basis vector has its iterated partial derivatives along `Xᵢ`
  vanishing there.
-/

public section

namespace MvPolynomial

section CommSemiring

variable {R σ τ : Type*} [CommSemiring R]

/-- Multiplication by a variable `Xᵢ` commutes with the partial derivative along another
variable `Xⱼ`. -/
theorem pderiv_X_mul_of_ne {i j : σ} (hij : i ≠ j) (p : MvPolynomial σ R) :
    pderiv j (X i * p) = X i * pderiv j p := by
  rw [Derivation.leibniz, pderiv_X_of_ne hij, smul_zero, add_zero, smul_eq_mul]

/-- **The chain rule**: `∂/∂Y_j (p(f)) = ∑ᵢ (∂p/∂Xᵢ)(f) · ∂fᵢ/∂Y_j` for a substitution
`Xᵢ ↦ fᵢ` of polynomials in the variables `Y`. -/
theorem pderiv_aeval [Fintype σ] (f : σ → MvPolynomial τ R) (j : τ) (p : MvPolynomial σ R) :
    pderiv j (aeval f p) = ∑ i, aeval f (pderiv i p) * pderiv j (f i) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p i hp =>
    simp [Derivation.leibniz, hp, add_mul, Finset.sum_add_distrib, Finset.mul_sum, Pi.single_apply,
      apply_ite, mul_assoc]

/-- **The chain rule** for a substitution `Xᵢ ↦ fᵢ` of univariate polynomials:
`(p(f))' = ∑ᵢ (∂p/∂Xᵢ)(f) · fᵢ'`. -/
theorem derivative_aeval [Fintype σ] (f : σ → Polynomial R) (p : MvPolynomial σ R) :
    Polynomial.derivative (aeval f p) =
      ∑ i, aeval f (pderiv i p) * Polynomial.derivative (f i) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p i hp =>
    simp only [map_mul, aeval_X, Polynomial.derivative_mul, hp, Derivation.leibniz, pderiv_X,
      smul_eq_mul, map_add, Pi.single_apply, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
    simp [mul_comm, mul_left_comm, add_comm]

/-- **The chain rule** over an arbitrary type of variables:
`∂/∂Y_j (p(f)) = ∑ᵢ (∂p/∂Xᵢ)(f) · ∂fᵢ/∂Y_j`, the sum running over any finite set `s` containing the
variables of `p`. -/
theorem pderiv_aeval_of_vars_subset (f : σ → MvPolynomial τ R) (j : τ) {p : MvPolynomial σ R}
    {s : Finset σ} (hs : p.vars ⊆ s) :
    pderiv j (aeval f p) = ∑ i ∈ s, aeval f (pderiv i p) * pderiv j (f i) := by
  -- Write `p` as a polynomial in the variables indexed by `s` and apply the finite chain rule.
  obtain ⟨q, rfl⟩ := exists_rename_eq_of_vars_subset_range p ((↑) : s → σ) Subtype.val_injective
    (by simpa using hs)
  rw [aeval_rename, pderiv_aeval, ← Finset.sum_coe_sort s]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [pderiv_rename Subtype.val_injective, aeval_rename, Function.comp_apply]

/-- Partial differentiation introduces no new variables. -/
theorem vars_pderiv_subset (i : σ) (p : MvPolynomial σ R) : (pderiv i p).vars ⊆ p.vars := by
  classical
  intro j hj
  obtain ⟨m, hm, hjm⟩ := (mem_vars_iff_mem_support j).1 hj
  rw [mem_support_iff, coeff_pderiv] at hm
  refine (mem_vars_iff_mem_support j).2
    ⟨m + Finsupp.single i 1, mem_support_iff.2 (left_ne_zero_of_mul hm), ?_⟩
  simp only [Finsupp.mem_support_iff, Finsupp.add_apply] at hjm ⊢
  omega

/-- Partial derivatives vanish outside the finitely many variables of a polynomial, so any family
built from the partial derivatives along an injective family of variables by zero-preserving maps
has finite support. -/
theorem hasFiniteSupport_pderiv {κ M : Type*} [Zero M] {e : κ → σ} (he : Function.Injective e)
    (p : MvPolynomial σ R) (φ : κ → MvPolynomial σ R → M) (hφ : ∀ k, φ k 0 = 0) :
    Function.HasFiniteSupport fun k ↦ φ k (pderiv (e k) p) := by
  refine (p.vars.finite_toSet.preimage he.injOn).subset fun k hk ↦ ?_
  by_contra h
  exact hk (by simp only [pderiv_eq_zero_of_notMem_vars h, hφ])

/-- Every `R`-linear derivation `D` on `MvPolynomial σ R` (with `σ` possibly infinite) expands in
the variables of `p`: `D p = ∑ i ∈ p.vars, pderiv i p • D (X i)`. -/
theorem derivation_apply_eq_sum_vars {M : Type*} [AddCommMonoid M] [Module R M]
    [Module (MvPolynomial σ R) M] [IsScalarTower R (MvPolynomial σ R) M]
    (D : Derivation R (MvPolynomial σ R) M) (p : MvPolynomial σ R) :
    D p = ∑ i ∈ p.vars, pderiv i p • D (X i) := by
  classical
  -- `q ↦ ∑ i ∈ p.vars, pderiv i q • D (X i)` is a derivation agreeing with `D` on `p.vars`
  let D' : Derivation R (MvPolynomial σ R) M :=
    ∑ i ∈ p.vars, (LinearMap.toSpanSingleton _ _ (D (X i))).compDer (pderiv i)
  have hD' : ∀ q, D' q = ∑ i ∈ p.vars, pderiv i q • D (X i) := fun q ↦ by simp [D']
  rw [← hD']
  exact derivation_eq_of_forall_mem_vars fun j hj ↦ by simp [hD', pderiv_X, Pi.single_apply, hj]

/-- Partial differentiation lowers the total degree by at least one. -/
theorem totalDegree_pderiv_le (i : σ) (p : MvPolynomial σ R) :
    (pderiv i p).totalDegree ≤ p.totalDegree - 1 := by
  classical
  refine Finset.sup_le fun m hm ↦ ?_
  rw [mem_support_iff, coeff_pderiv] at hm
  have h := le_totalDegree (mem_support_iff.2 (left_ne_zero_of_mul hm))
  rw [Finsupp.sum_add_index' (fun _ ↦ rfl) (fun _ _ _ ↦ rfl),
    Finsupp.sum_single_index rfl] at h
  omega

/-- The `k`-th iterated partial derivative lowers the total degree by at least `k`. -/
theorem totalDegree_iterate_pderiv_le (i : σ) (k : ℕ) (p : MvPolynomial σ R) :
    ((pderiv i)^[k] p).totalDegree ≤ p.totalDegree - k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have := totalDegree_pderiv_le i ((pderiv i)^[k] p)
    omega

/-- Partial differentiation along `Xᵢ` lowers the degree in `Xᵢ` by at least one. -/
theorem degreeOf_pderiv_le (i : σ) (p : MvPolynomial σ R) :
    (pderiv i p).degreeOf i ≤ p.degreeOf i - 1 := by
  classical
  refine degreeOf_le_iff.2 fun m hm ↦ ?_
  rw [mem_support_iff, coeff_pderiv] at hm
  have h := monomial_le_degreeOf i (mem_support_iff.2 (left_ne_zero_of_mul hm))
  simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same] at h
  omega

/-- The `k`-th iterated partial derivative along `Xᵢ` lowers the degree in `Xᵢ` by at least
`k`. -/
theorem degreeOf_iterate_pderiv_le (i : σ) (k : ℕ) (p : MvPolynomial σ R) :
    ((pderiv i)^[k] p).degreeOf i ≤ p.degreeOf i - k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have := degreeOf_pderiv_le i ((pderiv i)^[k] p)
    omega

/-- The `k`-th iterated partial derivative along `Xᵢ` of a polynomial of degree less than `k` in
`Xᵢ` vanishes. -/
theorem iterate_pderiv_eq_zero_of_degreeOf_lt {i : σ} {k : ℕ} {p : MvPolynomial σ R}
    (h : p.degreeOf i < k) : (pderiv i)^[k] p = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h
  rw [Function.iterate_succ_apply']
  refine pderiv_eq_zero_of_notMem_vars fun hi ↦ mem_vars_iff_degreeOf_ne_zero.1 hi ?_
  have := degreeOf_iterate_pderiv_le i (p.degreeOf i + k) p
  omega

/-- Partial differentiation keeps the coefficients in an additive submonoid of the coefficient
ring, such as a subring. -/
theorem coeff_pderiv_mem {S : Type*} [SetLike S R] [AddSubmonoidClass S R] {s : S}
    {p : MvPolynomial σ R} (hp : ∀ m, p.coeff m ∈ s) (i : σ) (m : σ →₀ ℕ) :
    (pderiv i p).coeff m ∈ s := by
  rw [coeff_pderiv, ← Nat.cast_succ, mul_comm, ← nsmul_eq_mul]
  exact nsmul_mem (hp _) _

/-- Iterated partial differentiation keeps the coefficients in an additive submonoid of the
coefficient ring, such as a subring. -/
theorem coeff_iterate_pderiv_mem {S : Type*} [SetLike S R] [AddSubmonoidClass S R] {s : S}
    {p : MvPolynomial σ R} (hp : ∀ m, p.coeff m ∈ s) (i : σ) (k : ℕ) (m : σ →₀ ℕ) :
    ((pderiv i)^[k] p).coeff m ∈ s := by
  induction k generalizing m with
  | zero => exact hp m
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact coeff_pderiv_mem ih i m

/-- Iterated partial differentiation commutes with mapping the coefficients along a ring
homomorphism. -/
@[simp]
theorem iterate_pderiv_map {S : Type*} [CommSemiring S] (φ : R →+* S) (i : σ) (k : ℕ)
    (p : MvPolynomial σ R) : (pderiv i)^[k] (p.map φ) = ((pderiv i)^[k] p).map φ := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, pderiv_map, Function.iterate_succ_apply']

/-- The `k`-th iterated partial derivative along `Xᵢ` of a monomial is
`∂ᵏ/∂Xᵢᵏ (a X^m) = a mᵢ (mᵢ - 1) ⋯ (mᵢ - k + 1) X^(m - k eᵢ)`; it vanishes for `k > mᵢ`. -/
@[simp]
theorem iterate_pderiv_monomial (i : σ) (k : ℕ) (m : σ →₀ ℕ) (a : R) :
    (pderiv i)^[k] (monomial m a) =
      monomial (m - Finsupp.single i k) (a * (m i).descFactorial k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hm : m - Finsupp.single i k - Finsupp.single i 1 = m - Finsupp.single i (k + 1) := by
      rw [tsub_tsub, ← Finsupp.single_add]
    rw [Function.iterate_succ_apply', ih, pderiv_monomial, hm]
    congr 1
    simp [Nat.descFactorial_succ]
    ring

/-- Iterated partial differentiation along `Xᵢ` of a one-variable polynomial in `Xᵢ` is iterated
differentiation of the polynomial. -/
theorem iterate_pderiv_aeval_X_self (i : σ) (k : ℕ) (p : Polynomial R) :
    (pderiv i)^[k] (Polynomial.aeval (X i : MvPolynomial σ R) p) =
      Polynomial.aeval (X i) (Polynomial.derivative^[k] p) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [Function.iterate_succ_apply', ih]

/-- **Partial derivatives of a separated product.** For one-variable polynomials `Qⱼ` and
`i ∈ s`, the `k`-th iterated partial derivative along `Xᵢ` of `∏_{j ∈ s} Qⱼ(Xⱼ)` is
`Qᵢ⁽ᵏ⁾(Xᵢ) ∏_{j ∈ s, j ≠ i} Qⱼ(Xⱼ)`: the other factors do not involve `Xᵢ`. -/
theorem iterate_pderiv_prod_aeval_X [DecidableEq σ] {s : Finset σ} {i : σ} (hi : i ∈ s)
    (Q : σ → Polynomial R) (k : ℕ) :
    (pderiv i)^[k] (∏ j ∈ s, Polynomial.aeval (X j : MvPolynomial σ R) (Q j)) =
      Polynomial.aeval (X i) (Polynomial.derivative^[k] (Q i)) *
        ∏ j ∈ s.erase i, Polynomial.aeval (X j) (Q j) := by
  -- The factors other than the `i`-th do not involve `Xᵢ`, so their product is a constant for
  -- `∂/∂Xᵢ`.
  have hg : pderiv i (∏ j ∈ s.erase i, Polynomial.aeval (X j : MvPolynomial σ R) (Q j)) = 0 :=
    Finset.prod_induction _ (fun g ↦ pderiv i g = 0)
      (fun a b ha hb ↦ by simp [Derivation.leibniz, ha, hb]) pderiv_one
      fun j hj ↦ by simp [Derivation.map_aeval, pderiv_X_of_ne (Finset.ne_of_mem_erase hj)]
  rw [← Finset.mul_prod_erase s _ hi]
  induction k with
  | zero => rfl
  | succ k ih =>
    simp [Function.iterate_succ_apply', ih, Derivation.leibniz, Derivation.map_aeval, hg, mul_comm]

end CommSemiring

section CommRing

variable {R σ : Type*} [CommRing R]

/-- **Ideal-product Taylor estimate in several variables.** If `xᵢ - tᵢ ∈ I`, `x'ᵢ - tᵢ ∈ I` and
`x'ᵢ - xᵢ ∈ J` for every `i`, then the gradient at `t` linearises `p` from `x` to `x'` up to an
error in `I * J`. -/
theorem eval_sub_eval_sub_sum_pderiv_mem_mul [Fintype σ] (p : MvPolynomial σ R) {I J : Ideal R}
    {t x x' : σ → R} (hx : ∀ i, x i - t i ∈ I) (hx' : ∀ i, x' i - t i ∈ I)
    (hxx' : ∀ i, x' i - x i ∈ J) :
    eval x' p - eval x p - ∑ j, eval t (pderiv j p) * (x' j - x j) ∈ I * J := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    have hlin : eval x' (p + q) - eval x (p + q) -
          ∑ j, eval t (pderiv j (p + q)) * (x' j - x j) =
        (eval x' p - eval x p - ∑ j, eval t (pderiv j p) * (x' j - x j)) +
          (eval x' q - eval x q - ∑ j, eval t (pderiv j q) * (x' j - x j)) := by
      simp only [map_add, add_mul, Finset.sum_add_distrib]
      ring
    rw [hlin]
    exact (I * J).add_mem hp hq
  | mul_X p i hp =>
    classical
    set S := ∑ j, eval t (pderiv j p) * (x' j - x j)
    have hS : S ∈ J := J.sum_mem fun j _ ↦ J.mul_mem_left _ (hxx' j)
    have hsum : ∑ j, eval t (pderiv j (p * X i)) * (x' j - x j) =
        t i * S + eval t p * (x' i - x i) := by
      simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, map_mul, eval_X, add_mul,
        Finset.sum_add_distrib, S, Finset.mul_sum, Pi.single_apply]
      simp only [apply_ite (eval t), map_one, map_zero, mul_ite, ite_mul, mul_one, mul_zero,
        zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, mul_assoc]
      ring
    have hlin : eval x' (p * X i) - eval x (p * X i) -
          ∑ j, eval t (pderiv j (p * X i)) * (x' j - x j) =
        (eval x' p - eval x p - S) * x' i + (x' i - t i) * S +
          (eval x p - eval t p) * (x' i - x i) := by
      rw [hsum]
      simp only [map_mul, eval_X]
      ring
    rw [hlin]
    exact (I * J).add_mem
      ((I * J).add_mem ((I * J).mul_mem_right _ hp) (Ideal.mul_mem_mul (hx' i) hS))
      (Ideal.mul_mem_mul (eval_sub_eval_mem p hx) (hxx' i))

/-- **First-order Taylor estimate modulo `I ^ 2` over an arbitrary variable type.** Let `s` be a
finite set of indices containing every variable of `p` at which `b` and `a` differ. If `bᵢ - aᵢ ∈ I`
for every `i ∈ s`, then `p(b) - p(a) - ∑_{j ∈ s} ∂ⱼp(a) (bⱼ - aⱼ) ∈ I ^ 2`. -/
theorem eval_sub_eval_sub_sum_pderiv_mem_sq (p : MvPolynomial σ R) {I : Ideal R}
    {a b : σ → R} {s : Finset σ} (hs : ∀ i ∈ p.vars, b i ≠ a i → i ∈ s)
    (hb : ∀ i ∈ s, b i - a i ∈ I) :
    eval b p - eval a p - ∑ j ∈ s, eval a (pderiv j p) * (b j - a j) ∈ I ^ 2 := by
  classical
  let u : Finset σ := s ∪ p.vars
  have hpv : p.vars ⊆ u := Finset.subset_union_right
  obtain ⟨q, hq⟩ := exists_rename_eq_of_vars_subset_range p ((↑) : u → σ) Subtype.val_injective
    (by simpa using hpv)
  have hcoord (k : u) : (b ∘ Subtype.val) k - (a ∘ Subtype.val) k ∈ I := by
    by_cases hks : (k : σ) ∈ s
    · exact hb k hks
    · have hk : b k = a k := by
        by_contra hne
        rcases Finset.mem_union.mp k.property with hks' | hkv
        · exact hks hks'
        · exact hks (hs k hkv hne)
      simp [hk]
  have hmem := eval_sub_eval_sub_sum_pderiv_mem_mul q (I := I) (J := I)
    (t := a ∘ Subtype.val) (x := a ∘ Subtype.val) (x' := b ∘ Subtype.val)
    (fun _ ↦ by simp) hcoord hcoord
  rw [← sq] at hmem
  have hsum : (∑ k : u, eval (a ∘ Subtype.val) (pderiv k q) * (b k - a k)) =
      ∑ j ∈ s, eval a (pderiv j p) * (b j - a j) := by
    have h1 : (∑ k : u, eval (a ∘ Subtype.val) (pderiv k q) * (b k - a k)) =
        ∑ j ∈ u, eval a (pderiv j p) * (b j - a j) := by
      rw [← Finset.sum_coe_sort u]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [← hq, pderiv_rename Subtype.val_injective, eval_rename]
    rw [h1]
    refine (Finset.sum_subset Finset.subset_union_left fun j _ hjs ↦ ?_).symm
    by_cases hjv : j ∈ p.vars
    · have hjb : b j = a j := by
        by_contra hne
        exact hjs (hs j hjv hne)
      simp [hjb]
    · simp [pderiv_eq_zero_of_notMem_vars hjv]
  have heval_b : eval (b ∘ Subtype.val) q = eval b p := by
    rw [← hq, eval_rename]
  have heval_a : eval (a ∘ Subtype.val) q = eval a p := by
    rw [← hq, eval_rename]
  simpa only [Function.comp_apply, heval_b, heval_a, hsum] using hmem

/-- **First-order Taylor estimate modulo `d ^ 2` along the translates `a + d • b`.** Summing
over the finitely many variables of `p`, `p(a + d b) - p(a) - d ∑ⱼ ∂ⱼp(a) bⱼ` is divisible by
`d ^ 2`. -/
theorem sq_dvd_eval_add_smul_sub_sum_pderiv (p : MvPolynomial σ R) (d : R) (a b : σ → R) :
    d ^ 2 ∣ eval (a + d • b) p - eval a p - d * ∑ j ∈ p.vars, eval a (pderiv j p) * b j := by
  have h := eval_sub_eval_sub_sum_pderiv_mem_sq p (I := Ideal.span {d}) (a := a)
    (b := a + d • b) (s := p.vars) (fun i hi _ ↦ hi)
    (fun i _ ↦ Ideal.mem_span_singleton.2 ⟨b i, by simp⟩)
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
  convert h using 2
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ ↦ by simp [mul_left_comm]

/-- **Taylor's estimate in several variables.** If `d ∣ xᵢ - tᵢ`, `d ∣ e` and `e ∣ x'ᵢ - xᵢ` for
every `i`, then the gradient at `t` linearises `p` from `x` to `x'` up to an error divisible by
`d * e`. -/
theorem mul_dvd_eval_sub_eval_sub_sum_pderiv [Fintype σ] (p : MvPolynomial σ R) {d e : R}
    {t x x' : σ → R} (hx : ∀ i, d ∣ x i - t i) (hde : d ∣ e) (hxx' : ∀ i, e ∣ x' i - x i) :
    d * e ∣ eval x' p - eval x p - ∑ j, eval t (pderiv j p) * (x' j - x j) := by
  rw [← Ideal.mem_span_singleton, ← Ideal.span_singleton_mul_span_singleton]
  refine eval_sub_eval_sub_sum_pderiv_mem_mul p (fun i ↦ Ideal.mem_span_singleton.mpr (hx i))
    (fun i ↦ Ideal.mem_span_singleton.mpr ?_) (fun i ↦ Ideal.mem_span_singleton.mpr (hxx' i))
  simpa using dvd_add (hde.trans (hxx' i)) (hx i)

end CommRing

section UniqueDiv

variable {R σ : Type*} [CommRing R] [HasUniqueDiv R]

/-- Over a commutative ring with `HasUniqueDiv`, a multivariate polynomial is uniquely determined
by its formal partial derivatives and its constant coefficient. -/
theorem pderiv.ext {φ ψ : MvPolynomial σ R}
    (hD : ∀ i, pderiv i φ = pderiv i ψ) (hc : constantCoeff φ = constantCoeff ψ) :
    φ = ψ := by
  apply coe_injective σ R
  apply MvPowerSeries.pderiv.ext
  · intro i
    rw [MvPowerSeries.pderiv_coe, MvPowerSeries.pderiv_coe, hD i]
  · simpa only [← MvPowerSeries.coeff_zero_eq_constantCoeff, coeff_coe,
      ← constantCoeff_eq] using hc

/-- If all formal partial derivatives of `φ` vanish, then `φ` equals its constant term. -/
theorem eq_C_constantCoeff_of_forall_pderiv_eq_zero {φ : MvPolynomial σ R}
    (hφ : ∀ i, pderiv i φ = 0) :
    φ = C (constantCoeff φ) :=
  pderiv.ext (fun i ↦ by rw [hφ i, pderiv_C]) (by simp)

/-- Over a commutative ring with `HasUniqueDiv`, all formal partial derivatives of `φ` vanish if
and only if `φ` is constant. -/
theorem forall_pderiv_eq_zero_iff {φ : MvPolynomial σ R} :
    (∀ i, pderiv i φ = 0) ↔ ∃ c : R, φ = C c :=
  ⟨fun h ↦ ⟨constantCoeff φ, eq_C_constantCoeff_of_forall_pderiv_eq_zero h⟩,
    fun ⟨_, hc⟩ _ ↦ hc ▸ pderiv_C⟩

/-- Two polynomials with the same formal partial derivatives differ by the constant given by the
difference of their constant coefficients. -/
theorem sub_eq_C_of_forall_pderiv_eq {φ ψ : MvPolynomial σ R}
    (hD : ∀ i, pderiv i φ = pderiv i ψ) :
    φ - ψ = C (constantCoeff φ - constantCoeff ψ) := by
  simpa only [map_sub] using
    eq_C_constantCoeff_of_forall_pderiv_eq_zero (φ := φ - ψ) fun i ↦ by simp [hD i]

end UniqueDiv

section InfiniteDomain

variable {R σ : Type*} [CommRing R] [IsDomain R] [Infinite R]

/-- If a polynomial vanishes on the affine line through `a` in the direction of the `i`-th
coordinate, then so does its partial derivative `∂p/∂Xᵢ` at `a`. -/
theorem eval_pderiv_eq_zero_of_forall_eval_add_smul_single [DecidableEq σ]
    {p : MvPolynomial σ R} {a : σ → R} {i : σ}
    (h : ∀ t : R, eval (a + t • Pi.single i 1) p = 0) : eval a (pderiv i p) = 0 := by
  -- Restrict `p` to the line `u ↦ a + u eᵢ`, as a polynomial in one variable `u`.
  let f : σ → MvPolynomial Unit R := fun j ↦ C (a j) + C ((Pi.single i 1 : σ → R) j) * X ()
  have heval (q : MvPolynomial σ R) (u : Unit → R) :
      eval u (aeval f q) = eval (a + u () • Pi.single i 1) q := by
    have hpt : (fun j ↦ eval u (f j)) = a + u () • Pi.single i 1 := by
      funext j
      simp [f, mul_comm]
    rw [← hpt]
    simpa only [aeval_eq_eval] using comp_aeval_apply (f := f) (aeval u) q
  have hline : aeval f p = 0 := MvPolynomial.funext fun u ↦ by simp [heval, h]
  have hderiv : pderiv () (aeval f p) = aeval f (pderiv i p) := by
    rw [pderiv_aeval_of_vars_subset f () (Finset.subset_insert i p.vars),
      Finset.sum_eq_single i (fun j _ hj ↦ by simp [f, hj]) (by simp)]
    simp [f]
  rw [hline, map_zero] at hderiv
  have h0 := congrArg (eval fun _ ↦ 0) hderiv
  rwa [heval, map_zero, zero_smul, add_zero, eq_comm] at h0

/-- If a polynomial vanishes on a submodule `W` containing the `i`-th standard basis vector, then
so do all its iterated partial derivatives `∂ᵏp/∂Xᵢᵏ`. -/
theorem eval_iterate_pderiv_eq_zero_of_forall_mem [DecidableEq σ]
    {W : Submodule R (σ → R)} {i : σ} (hi : Pi.single i 1 ∈ W) {p : MvPolynomial σ R}
    (hp : ∀ w ∈ W, eval w p = 0) (k : ℕ) : ∀ w ∈ W, eval w ((pderiv i)^[k] p) = 0 := by
  induction k with
  | zero => exact hp
  | succ k ih =>
    intro w hw
    rw [Function.iterate_succ_apply']
    exact eval_pderiv_eq_zero_of_forall_eval_add_smul_single fun t ↦
      ih _ (W.add_mem hw (W.smul_mem t hi))

end InfiniteDomain

end MvPolynomial

namespace Derivation

open MvPolynomial

variable {k R σ : Type*} [CommSemiring k] [CommSemiring R] [Algebra k R] [DecidableEq σ]

/-- **A derivation dual to a family of elements acts as a partial derivative.** If
`D (x j) = 1` for `j = i` and `D (x j) = 0` otherwise, then `D (p(x)) = (∂p/∂Xᵢ)(x)` for every
polynomial `p`. -/
theorem map_aeval_eq_aeval_pderiv (D : Derivation k R R) {x : σ → R} {i : σ}
    (hx : ∀ j, D (x j) = if i = j then 1 else 0) (p : MvPolynomial σ k) :
    D (aeval x p) = aeval x (pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
    by_cases h : i = j <;> simp [leibniz, hp, hx, h, mul_comm, add_comm]

end Derivation
