/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Binomial.Basis
public import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.AlgebraTower
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Regular.SMul

/-!
# Multivariable binomial polynomials

Over a nontrivial commutative `ℚ`-algebra, the finite products
`n.prod (fun i k => (X i choose k))`, indexed by `n : σ →₀ ℕ`, form a polynomial basis.
Restricting scalars gives an integral basis of their additive span, so expansions with
integer coefficients are unique.
These are the polynomial normal forms for products of toral binomial coefficients.

The construction iterates the univariate basis from
`TauCeti.RingTheory.Polynomial.Binomial.Basis` using Mathlib's scalar-tower basis.

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
      let e := (Equiv.prodComm (Fin r → ℕ) ℕ).trans
        (Fin.consEquiv fun _ : Fin (r + 1) => ℕ)
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
private theorem exists_fintype_mvBinomialPolynomialBasis (σ : Type*) [Fintype σ] :
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

omit [Nontrivial K] in
private theorem prod_ringChoose_X_eq_rename {σ : Type*} (s : Finset σ) (n : σ →₀ ℕ)
    (hn : n.support ⊆ s) :
    n.prod (fun i k => Ring.choose (X i : MvPolynomial σ K) k) =
      rename ((↑) : s → σ) (∏ i : s, Ring.choose (X i : MvPolynomial s K) (n i)) := by
  classical
  simp only [map_prod, Ring.map_choose, rename_X]
  exact (n.prod_of_support_subset hn _ (fun _ _ => Ring.choose_zero_right _)).trans
    (Finset.prod_coe_sort s (fun i => Ring.choose (X i : MvPolynomial σ K) (n i))).symm

private theorem exists_mvBinomialPolynomialBasis (σ : Type*) :
    ∃ b : Module.Basis (σ →₀ ℕ) K (MvPolynomial σ K),
      ∀ n, b n = n.prod (fun i k => Ring.choose (X i) k) := by
  classical
  let v := fun n : σ →₀ ℕ => n.prod (fun i k => Ring.choose (X i : MvPolynomial σ K) k)
  -- Each finite family is contained in a finite-variable polynomial ring.
  have hli : LinearIndependent K v := by
    apply linearIndependent_iff_finset_linearIndependent.mpr
    intro t
    let s := t.biUnion Finsupp.support
    have hs (n : t) : n.val.support ⊆ s :=
      Finset.subset_biUnion_of_mem Finsupp.support n.property
    obtain ⟨b, hb⟩ := exists_fintype_mvBinomialPolynomialBasis K s
    let f := (rename ((↑) : s → σ) : MvPolynomial s K →ₐ[K] MvPolynomial σ K).toLinearMap
    have hinj : Function.Injective (fun n : t => fun i : s => n.val i) := by
      intro n m h
      apply Subtype.ext
      apply Finsupp.ext
      intro i
      by_cases hi : i ∈ s
      · exact congrFun h ⟨i, hi⟩
      · rw [Finsupp.notMem_support_iff.mp (fun hn => hi (hs n hn)),
          Finsupp.notMem_support_iff.mp (fun hm => hi (hs m hm))]
    have heq : v ∘ (Subtype.val : t → σ →₀ ℕ) =
        fun n : t => f (b (fun i : s => n.val i)) := by
      funext n
      simp only [Function.comp_apply, f, AlgHom.toLinearMap_apply, hb]
      exact prod_ringChoose_X_eq_rename K s n.val (hs n)
    rw [heq]
    exact (b.linearIndependent.map' f
      (LinearMap.ker_eq_bot.mpr (rename_injective _ Subtype.val_injective))).comp _ hinj
  -- Likewise, each polynomial is spanned after restricting to finitely many variables.
  have hsp : ⊤ ≤ Submodule.span K (Set.range v) := by
    intro p _
    obtain ⟨s, q, rfl⟩ := p.exists_finset_rename
    obtain ⟨b, hb⟩ := exists_fintype_mvBinomialPolynomialBasis K s
    let f := (rename ((↑) : s → σ) : MvPolynomial s K →ₐ[K] MvPolynomial σ K).toLinearMap
    have h : Submodule.span K (Set.range b) ≤
        (Submodule.span K (Set.range v)).comap f := by
      apply Submodule.span_le.mpr
      rintro _ ⟨n, rfl⟩
      simp only [f]
      apply Submodule.subset_span
      refine ⟨(Finsupp.equivFunOnFinite.symm n).embDomain (.subtype (· ∈ s)), ?_⟩
      simp only [v, Finsupp.prod_embDomain, AlgHom.toLinearMap_apply, hb, map_prod,
        Ring.map_choose, rename_X]
      rw [Finsupp.prod_fintype _ _ (fun _ => Ring.choose_zero_right _)]
      simp only [Function.Embedding.subtype_apply, Finsupp.coe_equivFunOnFinite_symm]
    exact h (by rw [b.span_eq]; trivial)
  exact ⟨Module.Basis.mk hli hsp, Module.Basis.mk_apply _ _⟩

/-- The basis of multivariable polynomials given by finite products of the binomial
polynomials. The finitely supported index records the degree in each variable. -/
noncomputable def mvBinomialPolynomialBasis (σ : Type*) :
    Module.Basis (σ →₀ ℕ) K (MvPolynomial σ K) :=
  (exists_mvBinomialPolynomialBasis K σ).choose

/-- The basis vector of multidegree `n` is the finite product of the binomial polynomials. -/
@[simp]
theorem mvBinomialPolynomialBasis_apply (σ : Type*) (n : σ →₀ ℕ) :
    mvBinomialPolynomialBasis K σ n = n.prod (fun i k => Ring.choose (X i) k) :=
  (exists_mvBinomialPolynomialBasis K σ).choose_spec n

/-- Products of binomial polynomials are linearly independent over the coefficient ring. -/
theorem linearIndependent_prod_ringChoose_X (σ : Type*) :
    LinearIndependent K (fun n : σ →₀ ℕ =>
      n.prod (fun i k => Ring.choose (X i : MvPolynomial σ K) k)) := by
  have heq : ⇑(mvBinomialPolynomialBasis K σ) =
      fun n : σ →₀ ℕ => n.prod (fun i k => Ring.choose (X i) k) :=
    funext (mvBinomialPolynomialBasis_apply K σ)
  rw [← heq]
  exact (mvBinomialPolynomialBasis K σ).linearIndependent

/-- Products of binomial polynomials remain independent over the integers. -/
theorem linearIndependent_prod_ringChoose_X_int (σ : Type*) :
    LinearIndependent ℤ (fun n : σ →₀ ℕ =>
      n.prod (fun i k => Ring.choose (X i : MvPolynomial σ K) k)) :=
  (linearIndependent_prod_ringChoose_X K σ).restrict_scalars' ℤ

/-- The integral span of products of binomial polynomials is free on those products. -/
noncomputable def mvBinomialSpanBasis (σ : Type*) :
    Module.Basis (σ →₀ ℕ) ℤ
      (prodRingChooseSpan (X : σ → MvPolynomial σ K)).toIntSubmodule :=
  (mvBinomialPolynomialBasis K σ).addSubgroupOfClosure _ (by
    have heq : ⇑(mvBinomialPolynomialBasis K σ) =
        fun n => n.prod (fun i k => Ring.choose (X i) k) :=
      funext (mvBinomialPolynomialBasis_apply K σ)
    rw [heq, ← Submodule.span_int_eq_addSubgroupClosure, span_int_range_prod_ringChoose,
      AddSubgroup.toIntSubmodule_toAddSubgroup])

/-- The integral basis has the same binomial-product vectors as the polynomial basis. -/
@[simp]
theorem coe_mvBinomialSpanBasis_apply (σ : Type*) (n : σ →₀ ℕ) :
    (mvBinomialSpanBasis K σ n : MvPolynomial σ K) =
      n.prod (fun i k => Ring.choose (X i) k) := by
  simp [mvBinomialSpanBasis]

/-- Membership in the integral binomial span is equivalent to a unique finite expansion
with integer coefficients. -/
theorem mem_prodRingChooseSpan_X_iff_existsUnique (σ : Type*) (p : MvPolynomial σ K) :
    p ∈ prodRingChooseSpan (X : σ → MvPolynomial σ K) ↔
      ∃! a : (σ →₀ ℕ) →₀ ℤ,
        a.sum (fun n z => z • n.prod (fun i k => Ring.choose (X i : MvPolynomial σ K) k)) =
          p :=
  mem_prodRingChooseSpan_iff_existsUnique (linearIndependent_prod_ringChoose_X_int K σ) p

end TauCeti
