/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.Variables
public import TauCeti.Data.Finsupp.Filter

/-!
# Variables of products and renamings of multivariate polynomials

If `P` and `Q` involve disjoint sets of variables, no two products of a monomial of `P` and a
monomial of `Q` coincide: an exponent `a + b`, with `a` supported on the variables of `P` and `b`
on those of `Q`, determines `a` as its restriction to the variables of `P`
(`Finsupp.injOn_add_of_disjoint`). Hence the coefficients
of `P * Q` are exactly the products of a coefficient of `P` and a coefficient of `Q`, with no
cancellation or addition between them. This is what makes the height of such a product the product
of the heights, as used in the inductive step of Roth's lemma, where a generalized Wronskian in
some variables is multiplied by a Wronskian in another variable.

The file also bounds the variables of renamed polynomials, using Mathlib's
`MvPolynomial.vars_rename`: every variable of `rename f a` is the image under `f` of a variable
of `a`. Over a commutative ring and a well-founded variable order, a triangular substitution
`X i ↦ c i • X i + r i`, where each `c i` is a unit and `r i` involves only variables strictly
below `i`, is an automorphism of `MvPolynomial σ R`: its inverse is constructed by well-founded
recursion along the variable order.

## Main results

* `MvPolynomial.coeff_add_mul_of_disjoint_vars`: `(P * Q).coeff (a + b) = P.coeff a * Q.coeff b`
  for exponents `a` and `b` supported on the variables of `P` and of `Q`.
* `MvPolynomial.vars_X_sub_X`: over a nontrivial commutative ring, the variables of `X i - X j`
  for `i ≠ j` are `{i, j}`.
* `MvPolynomial.vars_rename_subset_Ioi`: if `f` sends every variable of `a` above `i`, then
  every variable of `rename f a` lies above `i`.
* `MvPolynomial.exists_rename_eq_of_vars_subset_range'`: a polynomial whose variables all lie in
  the range of `f` is the renaming along `f` of a polynomial, with no injectivity assumption on `f`.
* `MvPolynomial.bijective_aeval_of_vars_sub_smul_X_lt` and
  `MvPolynomial.bijective_aeval_of_vars_sub_X_lt`: a triangular substitution with unit diagonal
  coefficients along a well-founded variable order is bijective.
* `Polynomial.vars_toMvPolynomial_subset`: a one-variable polynomial placed in the coordinate `i`
  involves at most the variable `i`.
-/

public section

open Finset

namespace MvPolynomial

variable {R σ : Type*} [CommSemiring R] {P Q : MvPolynomial σ R}

/-- **Coefficients of a product in disjoint variables.** If `P` and `Q` involve disjoint sets of
variables, and the exponents `a` and `b` are supported on the variables of `P` and of `Q`
respectively, then the coefficient of `P * Q` at `a + b` is `P.coeff a * Q.coeff b`. -/
theorem coeff_add_mul_of_disjoint_vars (h : Disjoint P.vars Q.vars) {a b : σ →₀ ℕ}
    (ha : a.support ⊆ P.vars) (hb : b.support ⊆ Q.vars) :
    (P * Q).coeff (a + b) = P.coeff a * Q.coeff b := by
  refine AddMonoidAlgebra.coeff_mul_add_of_uniqueAdd fun ⦃a' b'⦄ ha' hb' he ↦
    Prod.mk.inj (Finsupp.injOn_add_of_disjoint (Finset.disjoint_coe.2 h) ?_
      ⟨Finset.coe_subset.2 ha, Finset.coe_subset.2 hb⟩ he)
  -- Exponents in the supports of `P` and `Q` are supported on their variables.
  rw [finsupp_support_eq_support] at ha' hb'
  exact ⟨Finset.coe_subset.2 (support_subset_vars_of_mem_support ha'),
    Finset.coe_subset.2 (support_subset_vars_of_mem_support hb')⟩

/-- Over a nontrivial commutative ring, the variables of `X i - X j` for `i ≠ j` are `{i, j}`. -/
theorem vars_X_sub_X {σ R : Type*} [DecidableEq σ] [CommRing R] [Nontrivial R] {i j : σ}
    (hij : i ≠ j) :
    (X i - X j : MvPolynomial σ R).vars = {i, j} := by
  have hd : Disjoint (X i : MvPolynomial σ R).vars (X j : MvPolynomial σ R).vars := by
    simp [hij]
  rw [vars_sub_of_disjoint (X i) hd, vars_X, vars_X]
  rfl

/-- If `f` sends every variable of `a` above `i`, then every variable of `rename f a` lies
above `i`. -/
theorem vars_rename_subset_Ioi {τ : Type*} [Preorder τ] [LocallyFiniteOrderTop τ]
    (f : σ → τ) {a : MvPolynomial σ R} {i : τ} (h : ∀ j ∈ a.vars, i < f j) :
    (rename f a).vars ⊆ Ioi i := by
  classical
  exact (vars_rename f a).trans (image_subset_iff.2 fun j hj ↦ mem_Ioi.2 (h j hj))

/-- A polynomial whose variables all lie in the range of `f` is the renaming along `f` of a
polynomial. Unlike `MvPolynomial.exists_rename_eq_of_vars_subset_range`, this needs no
injectivity of `f`. -/
theorem exists_rename_eq_of_vars_subset_range' {τ : Type*} (p : MvPolynomial σ R) (f : τ → σ)
    (hf : ↑p.vars ⊆ Set.range f) : ∃ q : MvPolynomial τ R, rename f q = p := by
  rw [coe_vars_subset_iff, AlgHom.mem_range] at hf
  obtain ⟨q, hq⟩ := hf
  refine ⟨rename (fun x : Set.range f ↦ x.property.choose) q, ?_⟩
  rw [rename_rename, ← hq]
  exact congrArg (fun f ↦ rename f q) (funext fun x ↦ x.property.choose_spec)

section Triangular

variable {R σ : Type*} [CommRing R] [LT σ] [WellFoundedLT σ]

/-- **Triangular polynomial substitutions are automorphisms.** Over a commutative ring and a
well-founded order on the variables, if `f i = c i • X i + r i` where each `c i` is a unit and
every variable occurring in `r i = f i - c i • X i` is strictly below `i`, then `aeval f` is
bijective. -/
theorem bijective_aeval_of_vars_sub_smul_X_lt {f : σ → MvPolynomial σ R} {c : σ → R}
    (hc : ∀ i, IsUnit (c i)) (hvars : ∀ i, ∀ j ∈ (f i - c i • X i).vars, j < i) :
    Function.Bijective (aeval (R := R) f) := by
  classical
  -- Solve `c i • g i = X i - (f i - c i • X i)(g)` recursively along the well-founded order.
  let g : σ → MvPolynomial σ R :=
    WellFoundedLT.fix fun i ih ↦
      (↑(hc i).unit⁻¹ : R) •
        (X i - aeval (R := R) (fun j ↦ if hj : j < i then ih j hj else 0) (f i - c i • X i))
  have hg (i : σ) : g i = (↑(hc i).unit⁻¹ : R) • (X i - aeval (R := R) g (f i - c i • X i)) := by
    dsimp only [g]
    rw [WellFoundedLT.fix_eq]
    congr 2
    rw [aeval_eq_eval₂Hom, aeval_eq_eval₂Hom]
    exact eval₂Hom_congr' rfl (fun j hj _ ↦ by simp [hvars i j hj]) rfl
  have hgf : (aeval (R := R) g).comp (aeval (R := R) f) = AlgHom.id R (MvPolynomial σ R) := by
    refine algHom_ext fun i ↦ ?_
    have hci : c i • g i = X i - (aeval (R := R) g (f i) - c i • g i) := by
      conv_lhs => rw [hg i]
      rw [smul_smul, (hc i).mul_val_inv, one_smul, map_sub, map_smul, aeval_X]
    rw [AlgHom.comp_apply, AlgHom.id_apply, aeval_X, ← sub_eq_zero]
    convert sub_eq_zero.mpr hci using 1
    abel
  have hfg : (aeval (R := R) f).comp (aeval (R := R) g) = AlgHom.id R (MvPolynomial σ R) := by
    suffices ∀ i, aeval (R := R) f (g i) = X i from algHom_ext fun i ↦ by simpa using this i
    intro i
    induction i using WellFoundedLT.induction with
    | ind i ih =>
      have hrem : aeval (R := R) f (aeval (R := R) g (f i - c i • X i)) = f i - c i • X i := by
        rw [comp_aeval_apply]
        conv_rhs => rw [← aeval_X_left_apply (R := R) (f i - c i • X i)]
        rw [aeval_eq_eval₂Hom, aeval_eq_eval₂Hom]
        exact eval₂Hom_congr' rfl (fun j hj _ ↦ ih j (hvars i j hj)) rfl
      rw [hg i, map_smul, map_sub, aeval_X, hrem, sub_sub_cancel, smul_smul,
        (hc i).val_inv_mul, one_smul]
  exact Function.bijective_iff_has_inverse.mpr
    ⟨aeval (R := R) g, fun p ↦ DFunLike.congr_fun hgf p, fun p ↦ DFunLike.congr_fun hfg p⟩

/-- **Unitriangular polynomial substitutions are automorphisms.** Over a commutative ring and a
well-founded order on the variables, if every variable occurring in `f i - X i` is strictly below
`i`, then `aeval f` is bijective. -/
theorem bijective_aeval_of_vars_sub_X_lt {f : σ → MvPolynomial σ R}
    (hvars : ∀ i, ∀ j ∈ (f i - X i).vars, j < i) :
    Function.Bijective (aeval (R := R) f) :=
  bijective_aeval_of_vars_sub_smul_X_lt (c := fun _ ↦ 1) (fun _ ↦ isUnit_one) (by simpa using hvars)

end Triangular

end MvPolynomial

namespace Polynomial

variable {R σ : Type*} [CommSemiring R]

/-- A one-variable polynomial placed in the coordinate `i` involves at most the variable `i`. -/
theorem vars_toMvPolynomial_subset (p : R[X]) (i : σ) : (p.toMvPolynomial i).vars ⊆ {i} := by
  classical
  rw [toMvPolynomial_eq_rename_comp, AlgHom.comp_apply]
  exact (MvPolynomial.vars_rename _ _).trans (image_subset_iff.2 fun _ _ ↦ mem_singleton_self i)

end Polynomial
