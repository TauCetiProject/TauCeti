/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PolynomialLaw.Determinant
public import Mathlib.Algebra.Polynomial.Splits
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.LinearAlgebra.TensorProduct.Basic
import TauCeti.RingTheory.TensorProduct.Maps

/-!
# Polynomial tests of a determinant

Let `D` be a homogeneous multiplicative polynomial law over `A`. If its characteristic
polynomial at `x` splits after mapping along `A →+* S` into an integral domain `S`, then the
scalar-extended law evaluated at `q(1 ⊗ x)` is the product of the values of `q : S[X]` at
those roots, counted with multiplicity. For `p : A[X]`, this product is the image of
`D(p(x))` in `S`. The coefficient map may have a kernel. In particular, polynomial tests
of the degree law of an abelian variety can be read from a single characteristic polynomial.

## References

* J. S. Milne, *Abelian Varieties*, version 2.00 (2008), Lemma 10.22.
-/

public section

open Polynomial TensorProduct

namespace TauCeti.Determinant

variable {A R : Type*} [CommRing A] [Semiring R] [Algebra A R] {d : ℕ}
  (D : Determinant A R d) (x : R)
variable {S : Type*} [CommRing S] [Algebra A S]

private theorem rid_toFun_aeval_eq_prod_aroots_of_isAlgClosed {K : Type*} [Field K]
    [IsAlgClosed K] [Algebra A K] (q : K[X]) :
    Algebra.TensorProduct.rid A A K (D.toLaw.toFun K (aeval (1 ⊗ₜ[A] x) q)) =
      (((D.charpoly x).aroots K).map fun a ↦ q.eval a).prod := by
  have : Nontrivial A := (algebraMap A K).domain_nontrivial
  have hcard : ((D.charpoly x).aroots K).card = d := by
    rw [IsAlgClosed.card_aroots_eq_natDegree_of_isUnit_leadingCoeff
      ((D.charpoly_monic x).leadingCoeff ▸ isUnit_one), charpoly_natDegree_eq_dim]
  -- Test at -x so that the linear generator X + s evaluates to s - x, as in the charpoly.
  have htest (q : K[X]) :
      Algebra.TensorProduct.rid A A K (D.toLaw.toFun K (aeval (-(1 ⊗ₜ[A] x) : K ⊗[A] R) q)) =
        (((D.charpoly x).aroots K).map fun a ↦ q.eval (-a)).prod := by
    induction IsAlgClosed.splits q using Submonoid.closure_induction with
    | mem q hq =>
      obtain (⟨s, rfl⟩ | ⟨s, rfl⟩) := hq
      · simp [Algebra.TensorProduct.algebraMap_apply, hcard, Multiset.map_const']
      · simpa [Algebra.TensorProduct.algebraMap_apply, sub_eq_neg_add, D.aeval_charpoly] using
          (IsAlgClosed.splits _).aeval_eq_prod_aroots_of_monic (D.charpoly_monic x) s
    | one => simp [D.isMultiplicative.toFun_one, Multiset.map_const']
    | mul q r _ _ hq hr =>
      simp only [_root_.map_mul, D.isMultiplicative.toFun_mul, eval_mul, Multiset.prod_map_mul,
        hq, hr]
  simpa only [aeval_comp, eval_comp, map_neg, aeval_X, eval_neg, eval_X, neg_neg] using
    htest (q.comp (-X))

/-- **Milne's root-product formula after scalar extension.** In an integral domain `S`
where the characteristic polynomial of `x` splits, the law over `S` evaluated at
`q(1 ⊗ x)` is the product of `q` over the characteristic roots, counted with multiplicity. -/
theorem rid_toFun_aeval_eq_prod_aroots [IsDomain S]
    (hx : ((D.charpoly x).map (algebraMap A S)).Splits) (q : S[X]) :
    Algebra.TensorProduct.rid A A S (D.toLaw.toFun S (aeval (1 ⊗ₜ[A] x) q)) =
      (((D.charpoly x).aroots S).map fun a ↦ q.eval a).prod := by
  let K := AlgebraicClosure (FractionRing S)
  have : FaithfulSMul S K := FaithfulSMul.trans S (FractionRing S) K
  let f := IsScalarTower.toAlgHom A S K
  have heval : f.toLinearMap.rTensor R (aeval (1 ⊗ₜ[A] x) q) =
      aeval (1 ⊗ₜ[A] x) (q.map (algebraMap S K)) := by
    let g := Algebra.TensorProduct.rTensor (R := A) R (Algebra.ofId S K)
    have hg : g.restrictScalars A = Algebra.TensorProduct.map f (AlgHom.id A R) :=
      Algebra.TensorProduct.ext' fun _ _ ↦ rfl
    rw [AlgHom.rTensor_toLinearMap_apply, ← hg, AlgHom.restrictScalars_apply,
      aeval_map_algebraMap K]
    simpa only [g, Algebra.TensorProduct.map_tmul, _root_.map_one, AlgHom.id_apply] using
      (aeval_algHom_apply g (1 ⊗ₜ[A] x) q).symm
  apply FaithfulSMul.algebraMap_injective S K
  rw [Algebra.TensorProduct.coe_rid]
  change f.toLinearMap (TensorProduct.rid A S _) = _
  rw [← LinearMap.rid_rTensor_apply f.toLinearMap,
    PolynomialLaw.isCompat_apply, heval, ← Algebra.TensorProduct.coe_rid A A K,
    D.rid_toFun_aeval_eq_prod_aroots_of_isAlgClosed x, ← hx.map_aroots_algebraMap (B := K),
    map_multiset_prod, Multiset.map_map, Multiset.map_map]
  exact congrArg Multiset.prod (Multiset.map_congr rfl fun a _ ↦ by
    rw [Function.comp_apply, Function.comp_apply, eval_map_algebraMap]
    exact aeval_algHom_apply (Algebra.ofId S K) a q)

/-- **Milne's root-product formula.** In any integral domain where the characteristic polynomial
of `x` splits, the image of `D(p(x))` is the product of `p` over its characteristic roots,
counted with multiplicity. -/
theorem algebraMap_apply_aeval_eq_prod_aroots [IsDomain S]
    (hx : ((D.charpoly x).map (algebraMap A S)).Splits) (p : A[X]) :
    algebraMap A S (D (aeval x p)) = (((D.charpoly x).aroots S).map fun a ↦ aeval a p).prod := by
  have h := D.rid_toFun_aeval_eq_prod_aroots x hx (p.map (algebraMap A S))
  rw [aeval_map_algebraMap, ← Algebra.TensorProduct.includeRight_apply,
    aeval_algHom_apply, Algebra.TensorProduct.includeRight_apply, ← PolynomialLaw.one_tmul_ground,
    ground_toLaw, Algebra.TensorProduct.rid_tmul, Algebra.smul_def, mul_one] at h
  simpa only [eval_map_algebraMap] using h

end TauCeti.Determinant
