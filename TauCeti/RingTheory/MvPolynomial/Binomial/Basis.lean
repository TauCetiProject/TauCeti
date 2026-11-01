/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.BinomialBasis
public import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.AlgebraTower
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Regular.SMul

/-!
# Multivariable binomial polynomials

For finitely many variables over a nontrivial commutative `ℚ`-algebra, the products
`∏ i, (X i choose n i)` form a polynomial basis. Restricting scalars gives an integral
basis of their additive span, so expansions with integer coefficients are unique.
These are the polynomial normal forms for products of toral binomial coefficients.
No assertion about integral root-vector straightening is involved.

The construction iterates the univariate basis from
`TauCeti.RingTheory.Polynomial.BinomialBasis` using Mathlib's scalar-tower basis.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.
-/

public section

namespace TauCeti

open MvPolynomial

attribute [local instance] moduleNNRat BinomialRing.toHasUniqueDiv

variable (K : Type*) [CommRing K] [Algebra ℚ K] [Nontrivial K]

private theorem exists_fin_mvBinomialPolynomialBasis (r : ℕ) :
    ∃ b : Module.Basis (Fin r → ℕ) K (MvPolynomial (Fin r) K),
      ∀ n, b n = ∏ i, Ring.choose (X i) (n i) := by
  classical
  induction r with
  | zero =>
      refine ⟨(Module.Basis.singleton (Fin 0 → ℕ) K).map
        (isEmptyAlgEquiv K (Fin 0)).symm.toLinearEquiv, ?_⟩
      intro n
      simp
  | succ r ih =>
      obtain ⟨b, hb⟩ := ih
      let e : ((Fin r → ℕ) × ℕ) ≃ (Fin (r + 1) → ℕ) :=
        { toFun := fun p => Fin.cons p.2 p.1
          invFun := fun n => (Fin.tail n, n 0)
          left_inv := fun p => by simp
          right_inv := fun n => by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl }
      refine ⟨((b.smulTower (binomialPolynomialBasis (MvPolynomial (Fin r) K))).map
        (finSuccEquiv K r).symm.toLinearEquiv).reindex e, ?_⟩
      intro n
      apply (finSuccEquiv K r).injective
      simp only [Module.Basis.reindex_apply, Module.Basis.map_apply,
        Module.Basis.smulTower_apply, binomialPolynomialBasis_apply,
        AlgEquiv.toLinearEquiv_apply, AlgEquiv.apply_symm_apply, hb]
      simp [e, Algebra.smul_def, map_prod, Ring.map_choose, Fin.prod_univ_succ,
        finSuccEquiv_X_zero, finSuccEquiv_X_succ, Fin.tail_def, mul_comm]

/-- The products of binomial polynomials in finitely many variables form a basis. -/
private theorem exists_mvBinomialPolynomialBasis (σ : Type*) [Fintype σ] :
    ∃ b : Module.Basis (σ → ℕ) K (MvPolynomial σ K),
      ∀ n, b n = ∏ i, Ring.choose (X i) (n i) := by
  classical
  obtain ⟨b, hb⟩ := exists_fin_mvBinomialPolynomialBasis K (Fintype.card σ)
  let e := Fintype.equivFin σ
  refine ⟨(b.map (renameEquiv K e.symm).toLinearEquiv).reindex
    (Equiv.arrowCongr e.symm (Equiv.refl ℕ)), ?_⟩
  intro n
  simp only [Module.Basis.reindex_apply, Module.Basis.map_apply,
    AlgEquiv.toLinearEquiv_apply, hb, renameEquiv_apply, map_prod, Ring.map_choose,
    rename_X]
  exact e.symm.prod_comp fun i => Ring.choose (X i) (n i)

/-- The basis of multivariable polynomials given by products of the binomial polynomials
`(X i choose n i)`. The index records the degree in each variable. -/
noncomputable def mvBinomialPolynomialBasis (σ : Type*) [Fintype σ] :
    Module.Basis (σ → ℕ) K (MvPolynomial σ K) :=
  (exists_mvBinomialPolynomialBasis K σ).choose

/-- The basis vector of multidegree `n` is the product of the binomial polynomials. -/
@[simp]
theorem mvBinomialPolynomialBasis_apply (σ : Type*) [Fintype σ] (n : σ → ℕ) :
    mvBinomialPolynomialBasis K σ n = ∏ i, Ring.choose (X i) (n i) :=
  (exists_mvBinomialPolynomialBasis K σ).choose_spec n

/-- Products of binomial polynomials are linearly independent over the coefficient ring. -/
theorem linearIndependent_prod_ringChoose_X (σ : Type*) [Fintype σ] :
    LinearIndependent K (fun n : σ → ℕ => ∏ i, Ring.choose (X i : MvPolynomial σ K) (n i)) := by
  have heq : ⇑(mvBinomialPolynomialBasis K σ) =
      fun n : σ → ℕ => ∏ i, Ring.choose (X i) (n i) :=
    funext (mvBinomialPolynomialBasis_apply K σ)
  rw [← heq]
  exact (mvBinomialPolynomialBasis K σ).linearIndependent

/-- Products of binomial polynomials remain independent over the integers. -/
theorem linearIndependent_prod_ringChoose_X_int (σ : Type*) [Fintype σ] :
    LinearIndependent ℤ (fun n : σ → ℕ => ∏ i, Ring.choose (X i : MvPolynomial σ K) (n i)) :=
  (linearIndependent_prod_ringChoose_X K σ).restrict_scalars' ℤ

/-- The integral span of products of binomial polynomials is free on those products. -/
noncomputable def mvBinomialSpanBasis (σ : Type*) [Fintype σ] :
    Module.Basis (σ → ℕ) ℤ
      (AddSubgroup.closure (Set.range fun n : σ → ℕ =>
        ∏ i, Ring.choose (X i : MvPolynomial σ K) (n i))).toIntSubmodule :=
  (mvBinomialPolynomialBasis K σ).addSubgroupOfClosure _ (by
    congr 1
    ext p
    simp)

/-- The integral basis has the same binomial-product vectors as the polynomial basis. -/
@[simp]
theorem coe_mvBinomialSpanBasis_apply (σ : Type*) [Fintype σ] (n : σ → ℕ) :
    (mvBinomialSpanBasis K σ n : MvPolynomial σ K) =
      ∏ i, Ring.choose (X i) (n i) := by
  simp [mvBinomialSpanBasis]

/-- Membership in the integral binomial span is equivalent to a unique finite expansion
with integer coefficients. -/
theorem mem_closure_prod_ringChoose_X_iff_existsUnique (σ : Type*) [Fintype σ]
    (p : MvPolynomial σ K) :
    p ∈ AddSubgroup.closure (Set.range fun n : σ → ℕ =>
        ∏ i, Ring.choose (X i : MvPolynomial σ K) (n i)) ↔
      ∃! a : (σ → ℕ) →₀ ℤ,
        a.sum (fun n z => z • ∏ i, Ring.choose (X i : MvPolynomial σ K) (n i)) = p := by
  rw [← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup]
  exact LinearIndependent.mem_span_range_iff_existsUnique
    (linearIndependent_prod_ringChoose_X_int K σ) p

end TauCeti
