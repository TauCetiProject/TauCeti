/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.RingTheory.MvPolynomial.Basic
public import TauCeti.Algebra.MvPolynomial.Monomial
public import TauCeti.RingTheory.PiTensorProduct.Restricted

/-!
# Checks for restricted tensor products of algebras: polynomial rings

Stabilizing the polynomial rings `R[X_i]` by the idempotents `1` gives the polynomial ring in the
variables `X_i`: the restricted tensor product algebra
`TauCeti.RestrictedTensorAlgebra R (fun _ ↦ R[X]) (fun _ ↦ 1) _` is isomorphic to
`MvPolynomial ι R` (`TauCeti.RestrictedTensorAlgebra.PolynomialCheck.eval_bijective`), by the
morphism of nonunital algebras `eval` sending the restricted pure tensor `⨂ X^{s i}` to the
monomial `∏ X_i ^ s i` (`TauCeti.RestrictedTensorAlgebra.PolynomialCheck.eval_tprodXPow`).
Every element comes from a finite stage, so only monomials in finitely many variables occur: the
exponents of `MvPolynomial ι R` are finitely supported functions `ι →₀ ℕ`, and a monomial using
infinitely many variables is absent.
-/

public noncomputable section

open scoped TensorProduct Polynomial

namespace TauCeti.RestrictedTensorAlgebra.PolynomialCheck

variable {ι : Type*} [DecidableEq ι] (R : Type*) [CommSemiring R]

variable (ι) in
/-- The restricted tensor product of the polynomial rings `R[X_i]`, stabilized by `1`. -/
abbrev PolynomialRTA : Type _ :=
  RestrictedTensorAlgebra R (fun _ : ι ↦ R[X]) (fun _ ↦ 1) fun _ ↦ IsIdempotentElem.one

omit [DecidableEq ι] in
/-- On a finite stage `S`, evaluation `⨂_{i ∈ S} f_i ↦ ∏_{i ∈ S} f_i(X_i)`. -/
def stageEval (S : Finset ι) : (⨂[R] _ : S, R[X]) →ₐ[R] MvPolynomial ι R :=
  PiTensorProduct.liftAlgHom
    ((MultilinearMap.mkPiAlgebra R S (MvPolynomial ι R)).compLinearMap
      fun i ↦ (Polynomial.aeval (MvPolynomial.X (i : ι))).toLinearMap)
    (by simp) fun f g ↦ by
      -- Unfold the multilinear map by its own lemmas first, so that the stored proof keeps the
      -- stated type and `PiTensorProduct.liftAlgHom_apply` can rewrite `stageEval` below.
      simp only [MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]
      simp [Finset.prod_mul_distrib]

omit [DecidableEq ι] in
@[simp]
theorem stageEval_tprod (S : Finset ι) (f : S → R[X]) :
    stageEval R S (⨂ₜ[R] i, f i) = ∏ i : S, Polynomial.aeval (MvPolynomial.X (i : ι)) (f i) := by
  rw [stageEval, PiTensorProduct.liftAlgHom_apply, PiTensorProduct.lift.tprod,
    MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]
  simp only [AlgHom.toLinearMap_apply]

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
        (T.restrict (Function.updateFinset (fun _ ↦ (1 : R[X])) S f) i) = F i := fun _ ↦ by
      simp [F]
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
    eval R (ofFinite (R := R) (A := fun _ : ι ↦ R[X]) (fun _ ↦ .one) S x) = stageEval R S x :=
  lift_ofFinite _ _ _ _

/-- The restricted pure tensor `⨂ X^{s i}` of an exponent `s : ι →₀ ℕ`. -/
def tprodXPow (s : ι →₀ ℕ) : PolynomialRTA ι R :=
  tprod R _ (fun i ↦ (Polynomial.X : R[X]) ^ s i) (s.support.finite_toSet.subset fun i hi ↦ by
    by_contra h
    exact hi (by rw [Finsupp.notMem_support_iff.mp h, pow_zero]))

theorem tprodXPow_eq_ofFinite (s : ι →₀ ℕ) (S : Finset ι) (hS : ∀ i ∉ S, s i = 0) :
    tprodXPow R s =
      ofFinite (R := R) (A := fun _ : ι ↦ R[X]) (fun _ ↦ .one) S
        (⨂ₜ[R] i : S, (Polynomial.X : R[X]) ^ s i) :=
  tprod_eq_ofFinite _ _ S fun i hi ↦ by rw [hS i hi, pow_zero]

/-- **Restricted pure tensors of powers of `X` evaluate to monomials**:
`⨂ X^{s i} ↦ ∏ X_i^{s i}`. -/
@[simp]
theorem eval_tprodXPow (s : ι →₀ ℕ) :
    eval R (tprodXPow R s) = MvPolynomial.monomial s 1 := by
  rw [tprodXPow_eq_ofFinite R s s.support fun i hi ↦ Finsupp.notMem_support_iff.mp hi,
    eval_ofFinite, stageEval_tprod]
  simp [Finset.prod_attach s.support fun i ↦ MvPolynomial.X i ^ s i]

/-- The inverse of `eval`: the monomial `∏ X_i^{s i}` goes to `⨂ X^{s i}`. -/
def ofMvPolynomial : MvPolynomial ι R →ₗ[R] PolynomialRTA ι R :=
  (MvPolynomial.basisMonomials ι R).constr R (tprodXPow R)

@[simp]
theorem ofMvPolynomial_monomial (s : ι →₀ ℕ) :
    ofMvPolynomial R (MvPolynomial.monomial s 1) = tprodXPow R s := by
  have h := (MvPolynomial.basisMonomials ι R).constr_basis R (tprodXPow R) s
  rwa [MvPolynomial.coe_basisMonomials] at h

@[simp]
theorem eval_ofMvPolynomial (q : MvPolynomial ι R) : eval R (ofMvPolynomial R q) = q := by
  have : LinearMap.ofClass (eval R) ∘ₗ ofMvPolynomial R = LinearMap.id :=
    (MvPolynomial.basisMonomials ι R).ext fun s ↦ by
      simp [MvPolynomial.coe_basisMonomials]
  exact LinearMap.congr_fun this q

@[simp]
theorem ofMvPolynomial_eval (z : PolynomialRTA ι R) : ofMvPolynomial R (eval R z) = z := by
  obtain ⟨S, x, rfl⟩ := exists_ofFinite z
  let o : (⨂[R] _ : S, R[X]) →ₗ[R] PolynomialRTA ι R :=
    LinearMap.ofClass (ofFinite (R := R) (A := fun _ : ι ↦ R[X]) (fun _ ↦ .one) S)
  have : ofMvPolynomial R ∘ₗ LinearMap.ofClass (eval R) ∘ₗ o = o :=
    (Basis.piTensorProduct fun _ : S ↦ Polynomial.basisMonomials R).ext fun p ↦ by
      set s : ι →₀ ℕ := (Finsupp.equivFunOnFinite.symm p).extendDomain
      have hs : ∀ i : S, s i = p i := fun i ↦ by simp [s]
      have hsS : ∀ j ∉ S, s j = 0 := fun j hj ↦ by simp [s, hj]
      have hprod : ∏ i ∈ S.attach, (MvPolynomial.X (i : ι) : MvPolynomial ι R) ^ p i =
          MvPolynomial.monomial s 1 := by
        simp [s, MvPolynomial.monomial_extendDomain]
      simp [o, hprod, hs, tprodXPow_eq_ofFinite R s S hsS, Basis.piTensorProduct_apply,
        Polynomial.coe_basisMonomials, Polynomial.X_pow_eq_monomial]
  exact LinearMap.congr_fun this x

/-- **Stabilizing `R[X_i]` by `1` gives the polynomial ring in the variables `X_i`.** -/
theorem eval_bijective : Function.Bijective (eval R : PolynomialRTA ι R → MvPolynomial ι R) :=
  ⟨Function.LeftInverse.injective (ofMvPolynomial_eval R),
    Function.RightInverse.surjective (eval_ofMvPolynomial R)⟩

end TauCeti.RestrictedTensorAlgebra.PolynomialCheck
