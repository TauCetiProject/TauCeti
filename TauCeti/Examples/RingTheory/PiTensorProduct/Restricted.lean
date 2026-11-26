/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.RingTheory.MvPolynomial.Basic
public import TauCeti.RingTheory.PiTensorProduct.Restricted

/-!
# Checks for restricted tensor products of algebras: polynomial rings

Stabilizing the polynomial rings `R[X_i]` by the idempotents `1` gives the polynomial ring in the
variables `X_i`: the restricted tensor product algebra
`TauCeti.RestrictedTensorAlgebra R (fun _ ↦ R[X]) (fun _ ↦ 1) _` is isomorphic to
`MvPolynomial ι R` (`TauCeti.RestrictedTensorAlgebra.PolynomialCheck.bijective_eval`), by the
morphism of nonunital algebras `eval` sending the restricted pure tensor `⨂ X^{s i}` to the
monomial `∏ X_i ^ s i` (`TauCeti.RestrictedTensorAlgebra.PolynomialCheck.eval_tprod_X_pow`).
Every element comes from a finite stage, so only monomials in finitely many variables occur: the
exponents of `MvPolynomial ι R` are finitely supported functions `ι →₀ ℕ`, and a monomial using
infinitely many variables is absent.
-/

public noncomputable section

open scoped TensorProduct Polynomial

namespace TauCeti.RestrictedTensorAlgebra.PolynomialCheck

variable {ι : Type*} [DecidableEq ι] (R : Type*) [CommSemiring R]

omit [DecidableEq ι] in
variable (ι) in
/-- The unit `1` of every `R[X_i]` is idempotent. -/
theorem isIdempotentElem_one : ∀ _ : ι, IsIdempotentElem (1 : R[X]) :=
  fun _ ↦ .one

variable (ι) in
/-- The restricted tensor product of the polynomial rings `R[X_i]`, stabilized by `1`. -/
abbrev PolynomialRTA : Type _ :=
  RestrictedTensorAlgebra R (fun _ : ι ↦ R[X]) (fun _ ↦ 1) (isIdempotentElem_one ι R)

omit [DecidableEq ι] in
/-- On a finite stage `S`, evaluation `⨂_{i ∈ S} f_i ↦ ∏_{i ∈ S} f_i(X_i)`. -/
def stageEval (S : Finset ι) : (⨂[R] _ : S, R[X]) →ₐ[R] MvPolynomial ι R :=
  PiTensorProduct.liftAlgHom
    ((MultilinearMap.mkPiAlgebra R S (MvPolynomial ι R)).compLinearMap
      fun i ↦ (Polynomial.aeval (MvPolynomial.X (i : ι))).toLinearMap)
    (by simp) fun f g ↦ by simp [Finset.prod_mul_distrib]

omit [DecidableEq ι] in
@[simp]
theorem stageEval_tprod (S : Finset ι) (f : S → R[X]) :
    stageEval R S (⨂ₜ[R] i, f i) = ∏ i : S, Polynomial.aeval (MvPolynomial.X (i : ι)) (f i) := by
  change PiTensorProduct.lift _ (PiTensorProduct.tprod R f) = _
  rw [PiTensorProduct.lift.tprod]
  rfl

/-- Evaluation is compatible with adjoining the idempotents `1`. -/
theorem stageEval_stageMap {S T : Finset ι} (h : S ⊆ T) (x : ⨂[R] _ : S, R[X]) :
    stageEval R T (RestrictedTensor.stageMap R (fun _ : ι ↦ (1 : R[X])) h x) =
      stageEval R S x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    simp only [map_smul, RestrictedTensor.stageMap_tprod, stageEval_tprod]
    congr 1
    set F : ι → MvPolynomial ι R := fun i ↦
      Polynomial.aeval (MvPolynomial.X i) (Function.updateFinset (fun _ ↦ (1 : R[X])) S f i)
    have hT : ∀ i : T, Polynomial.aeval (MvPolynomial.X (i : ι))
        (T.restrict (Function.updateFinset (fun _ ↦ (1 : R[X])) S f) i) = F i := fun _ ↦ rfl
    have hS : ∀ i : S, Polynomial.aeval (MvPolynomial.X (i : ι)) (f i) = F i := fun i ↦ by
      simp [F]
    rw [Fintype.prod_congr _ _ hT, Fintype.prod_congr _ _ hS, Finset.prod_coe_sort,
      Finset.prod_coe_sort, Finset.prod_subset h fun i _ hi ↦ by
        simp [F, Function.updateFinset_apply_of_notMem hi]]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

/-- Evaluation `⨂ f_i ↦ ∏ f_i(X_i)` on the restricted tensor product of the `R[X_i]`. -/
def eval : PolynomialRTA ι R →ₙₐ[R] MvPolynomial ι R :=
  lift _ (fun S ↦ (stageEval R S).toNonUnitalAlgHom) fun _ _ h x ↦ stageEval_stageMap R h x

@[simp]
theorem eval_ofFinite (S : Finset ι) (x : ⨂[R] _ : S, R[X]) :
    eval R (ofFinite (isIdempotentElem_one ι R) S x) = stageEval R S x :=
  lift_ofFinite _ _ _ _

/-- The restricted pure tensor `⨂ X^{s i}` of an exponent `s : ι →₀ ℕ`. -/
def tprodXPow (s : ι →₀ ℕ) : PolynomialRTA ι R :=
  tprod R _ (fun i ↦ (Polynomial.X : R[X]) ^ s i) (s.support.finite_toSet.subset fun i hi ↦ by
    by_contra h
    exact hi (by rw [Finsupp.notMem_support_iff.mp h, pow_zero]))

theorem tprodXPow_eq_ofFinite (s : ι →₀ ℕ) (S : Finset ι) (hS : ∀ i ∉ S, s i = 0) :
    tprodXPow R s =
      ofFinite (isIdempotentElem_one ι R) S (⨂ₜ[R] i : S, (Polynomial.X : R[X]) ^ s i) :=
  tprod_eq_ofFinite _ _ S fun i hi ↦ by rw [hS i hi, pow_zero]

/-- **Restricted pure tensors of powers of `X` evaluate to monomials**:
`⨂ X^{s i} ↦ ∏ X_i^{s i}`. -/
theorem eval_tprod_X_pow (s : ι →₀ ℕ) :
    eval R (tprodXPow R s) = MvPolynomial.monomial s 1 := by
  rw [tprodXPow_eq_ofFinite R s s.support fun i hi ↦ Finsupp.notMem_support_iff.mp hi,
    eval_ofFinite, stageEval_tprod, MvPolynomial.monomial_eq, map_one, one_mul, Finsupp.prod]
  simp only [map_pow, Polynomial.aeval_X]
  exact Finset.prod_coe_sort s.support fun i ↦ MvPolynomial.X i ^ s i

/-- The inverse of `eval`: the monomial `∏ X_i^{s i}` goes to `⨂ X^{s i}`. -/
def ofMvPolynomial : MvPolynomial ι R →ₗ[R] PolynomialRTA ι R :=
  (MvPolynomial.basisMonomials ι R).constr R (tprodXPow R)

theorem ofMvPolynomial_monomial (s : ι →₀ ℕ) :
    ofMvPolynomial R (MvPolynomial.monomial s 1) = tprodXPow R s := by
  have h := (MvPolynomial.basisMonomials ι R).constr_basis R (tprodXPow R) s
  rwa [MvPolynomial.coe_basisMonomials] at h

theorem eval_ofMvPolynomial (q : MvPolynomial ι R) : eval R (ofMvPolynomial R q) = q := by
  have : LinearMap.ofClass (eval R) ∘ₗ ofMvPolynomial R = LinearMap.id :=
    (MvPolynomial.basisMonomials ι R).ext fun s ↦ by
      simp [MvPolynomial.coe_basisMonomials, ofMvPolynomial_monomial, eval_tprod_X_pow]
  exact LinearMap.congr_fun this q

theorem ofMvPolynomial_eval (z : PolynomialRTA ι R) : ofMvPolynomial R (eval R z) = z := by
  obtain ⟨S, x, rfl⟩ := exists_ofFinite z
  let o : (⨂[R] _ : S, R[X]) →ₗ[R] PolynomialRTA ι R :=
    LinearMap.ofClass (ofFinite (R := R) (isIdempotentElem_one ι R) S)
  have : ofMvPolynomial R ∘ₗ LinearMap.ofClass (eval R) ∘ₗ o = o :=
    (Basis.piTensorProduct fun _ : S ↦ Polynomial.basisMonomials R).ext fun p ↦ by
      set s : ι →₀ ℕ := ∑ i : S, Finsupp.single (i : ι) (p i)
      have hs : ∀ i : S, s i = p i := fun i ↦ by
        rw [Finsupp.finsetSum_apply]
        refine (Fintype.sum_eq_single i fun j hj ↦ ?_).trans Finsupp.single_eq_same
        exact Finsupp.single_eq_of_ne fun h ↦ hj (Subtype.ext h.symm)
      have hsS : ∀ j ∉ S, s j = 0 := fun j hj ↦ by
        rw [Finsupp.finsetSum_apply]
        exact Finset.sum_eq_zero fun i _ ↦ Finsupp.single_eq_of_ne fun h ↦ hj (h ▸ i.property)
      have hprod : ∏ i : S, (MvPolynomial.X (i : ι) : MvPolynomial ι R) ^ p i =
          MvPolynomial.monomial s 1 := by
        rw [MvPolynomial.monomial_sum_index, map_one, one_mul]
        exact Fintype.prod_congr _ _ fun i ↦ MvPolynomial.X_pow_eq_monomial
      simp only [Basis.piTensorProduct_apply, Polynomial.coe_basisMonomials, LinearMap.coe_comp,
        Function.comp_apply, o, LinearMap.coe_ofClass, eval_ofFinite, stageEval_tprod,
        Polynomial.aeval_monomial, map_one, one_mul, hprod, ofMvPolynomial_monomial,
        tprodXPow_eq_ofFinite R s S hsS, hs, Polynomial.X_pow_eq_monomial]
  exact LinearMap.congr_fun this x

/-- **Stabilizing `R[X_i]` by `1` gives the polynomial ring in the variables `X_i`.** -/
theorem bijective_eval : Function.Bijective (eval R : PolynomialRTA ι R → MvPolynomial ι R) :=
  ⟨Function.LeftInverse.injective (ofMvPolynomial_eval R),
    Function.RightInverse.surjective (eval_ofMvPolynomial R)⟩

end TauCeti.RestrictedTensorAlgebra.PolynomialCheck
