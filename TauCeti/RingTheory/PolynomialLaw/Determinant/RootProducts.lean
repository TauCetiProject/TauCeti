/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PolynomialLaw.Determinant
public import Mathlib.Algebra.Polynomial.Splits
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Polynomial tests of a determinant

Let `D` be a homogeneous multiplicative polynomial law on an algebra and let `a₁, …, a_d` be
the roots of its characteristic polynomial at `x`, counted with multiplicity. For every
polynomial `p`, the value of `D` at `p(x)` is the product of the values `p(aᵢ)`. The roots
may lie in an extension of the coefficient ring. In particular, polynomial tests of the
degree law of an abelian variety can be read from a single characteristic polynomial.

## References

* J. S. Milne, *Abelian Varieties*, version 2.00 (2008), Lemma 10.22.
-/

public section

open Polynomial TensorProduct

namespace TauCeti.Determinant

variable {A R : Type*} [CommRing A] [Semiring R] [Algebra A R] {d : ℕ}
  (D : Determinant A R d) (x : R)
variable {S : Type*} [CommRing S] [Algebra A S]

/-- Evaluating the characteristic polynomial at a scalar `s` computes the law at
`s ⊗ 1 - 1 ⊗ x` over that scalar algebra. -/
theorem aeval_charpoly (s : S) :
    aeval s (D.charpoly x) =
      Algebra.TensorProduct.rid A A S (D.toLaw.toFun S (s ⊗ₜ 1 - 1 ⊗ₜ x)) := by
  rw [sub_eq_neg_add, ← neg_tmul, charpoly_eq_sum, toFun_tmul_add_tmul_one]
  simp only [map_sum, _root_.map_mul, aeval_C, _root_.map_pow, aeval_X,
    Algebra.TensorProduct.rid_tmul, Algebra.smul_def, map_neg, _root_.map_one]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

private theorem algebraMap_apply_aeval_eq_prod_of_isAlgClosed {K : Type*} [Field K]
    [IsAlgClosed K] [Algebra A K] (p : A[X]) :
    algebraMap A K (D (aeval x p)) =
      (((D.charpoly x).aroots K).map fun a ↦ aeval a p).prod := by
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
  -- Evaluating p(-X) at -x recovers p(x), whose value under the law comes from the base.
  have h := htest ((p.map (algebraMap A K)).comp (-X))
  simp only [aeval_comp, eval_comp, map_neg, aeval_X, eval_neg, eval_X, neg_neg,
    eval_map_algebraMap] at h
  have heval : (1 : K) ⊗ₜ[A] aeval x p = aeval (1 ⊗ₜ[A] x) (p.map (algebraMap A K)) := by
    simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply]
      using map_aeval_eq_aeval_map
        (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := A) (A := K) (B := R)) p x
  rwa [← heval, ← PolynomialLaw.one_tmul_ground, ground_toLaw, Algebra.TensorProduct.rid_tmul,
    Algebra.smul_def, mul_one] at h

/-- **Milne's root-product formula.** In any integral domain where the characteristic polynomial
of `x` splits, the image of `D(p(x))` is the product of `p` over its characteristic roots,
counted with multiplicity. -/
theorem algebraMap_apply_aeval_eq_prod_aroots [IsDomain S]
    (hx : ((D.charpoly x).map (algebraMap A S)).Splits) (p : A[X]) :
    algebraMap A S (D (aeval x p)) = (((D.charpoly x).aroots S).map fun a ↦ aeval a p).prod := by
  let K := AlgebraicClosure (FractionRing S)
  have : FaithfulSMul S K := FaithfulSMul.trans S (FractionRing S) K
  apply FaithfulSMul.algebraMap_injective S K
  rw [← IsScalarTower.algebraMap_apply, map_multiset_prod, Multiset.map_map,
    D.algebraMap_apply_aeval_eq_prod_of_isAlgClosed x p,
    ← hx.map_aroots_algebraMap (B := K), Multiset.map_map]
  exact congrArg Multiset.prod (Multiset.map_congr rfl fun a _ ↦
    aeval_algHom_apply (IsScalarTower.toAlgHom A S K) a p)

end TauCeti.Determinant
