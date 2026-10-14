/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# Simplicial cochains as functions on simplices

For a ring `k` and a `k`-module `M`, evaluation on the unit chain of each simplex identifies
`Hom_k(C_n(K; k), M)` with functions from the `n`-simplices of `K` to `M`. This identification
is integral-linear, including for noncommutative rings. The cochain differential becomes the
alternating sum of values on faces, and pullback becomes precomposition on simplices.

The construction uses Mathlib's coproduct-to-direct-sum isomorphism and `Finsupp.llift`, the
linear free-module universal property. These coordinates allow comparison of coefficient
rings without changing the underlying cochain values.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.1.
-/

public section

noncomputable section

open CategoryTheory Limits SSet
open scoped Simplicial

universe w

namespace TauCeti

variable (k : Type w) [Ring k] (M : ModuleCat.{w} k) (K : SSet.{w})

/-- Evaluation on unit simplex chains identifies simplicial cochains with functions on
simplices, as modules over the integers. -/
def cochainValuesEquiv (n : ℕ) :
    ((K.chainComplex (ModuleCat.of k k)).X n ⟶ M) ≃ₗ[ℤ] (K _⦋n⦌ → M) := by
  classical
  let e := (ModuleCat.coprodIsoDirectSum fun _ : K _⦋n⦌ ↦ ModuleCat.of k k).toLinearEquiv.trans
    (finsuppLequivDFinsupp k).symm
  exact (ModuleCat.homLinearEquiv.trans (LinearEquiv.congrLeft M ℤ e)).trans
    (Finsupp.llift M k ℤ (K _⦋n⦌)).symm

/-- The value coordinate of a cochain is its value on the unit chain of the simplex. -/
@[simp]
lemma cochainValuesEquiv_apply (n : ℕ)
    (φ : (K.chainComplex (ModuleCat.of k k)).X n ⟶ M) (σ : K _⦋n⦌) :
    cochainValuesEquiv k M K n φ σ = φ (K.ιChainComplex (R := ModuleCat.of k k) σ 1) := by
  classical
  dsimp [cochainValuesEquiv, Finsupp.llift_symm_apply, LinearEquiv.congrLeft,
    LinearEquiv.arrowCongrAddEquiv, ModuleCat.homLinearEquiv, ModuleCat.homAddEquiv,
    ModuleCat.homEquiv]
  apply congrArg φ.hom
  apply (ModuleCat.coprodIsoDirectSum fun _ : K _⦋n⦌ ↦ ModuleCat.of k k).toLinearEquiv.injective
  have h := ConcreteCategory.congr_hom
    (ModuleCat.ι_coprodIsoDirectSum_hom (fun _ : K _⦋n⦌ ↦ ModuleCat.of k k) σ) (1 : k)
  convert h.symm using 1
  · simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
      ConcreteCategory.hom_ofHom]
    exact Finsupp.toDFinsupp_single σ (1 : k)
  · rfl

/-- The cochain with prescribed values evaluates a simplex with coefficient `a` to `a` times
its prescribed value. -/
@[simp]
lemma cochainValuesEquiv_symm_apply (n : ℕ) (v : K _⦋n⦌ → M) (σ : K _⦋n⦌) (a : k) :
    (cochainValuesEquiv k M K n).symm v (K.ιChainComplex (R := ModuleCat.of k k) σ a) =
      a • v σ := by
  have h := congrFun ((cochainValuesEquiv k M K n).apply_symm_apply v) σ
  rw [cochainValuesEquiv_apply] at h
  calc
    _ = (cochainValuesEquiv k M K n).symm v
        (a • K.ιChainComplex (R := ModuleCat.of k k) σ 1) := by
      rw [← map_smul, smul_eq_mul, mul_one]
    _ = a • v σ := by rw [map_smul, h]

/-- The cochain differential, in simplex coordinates, is the alternating sum over faces. -/
lemma cochainValuesEquiv_d (n : ℕ)
    (φ : (K.chainComplex (ModuleCat.of k k)).X n ⟶ M) (σ : K _⦋n + 1⦌) :
    cochainValuesEquiv k M K (n + 1)
        ((K.chainComplex (ModuleCat.of k k)).d (n + 1) n ≫ φ) σ =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • cochainValuesEquiv k M K n φ (K.δ i σ) := by
  simp only [cochainValuesEquiv_apply]
  have h := ConcreteCategory.congr_hom
    (K.ιChainComplex_d (R := ModuleCat.of k k) σ) (1 : k)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_sum,
    ModuleCat.hom_zsmul, LinearMap.sum_apply, LinearMap.smul_apply] at h
  simpa using congrArg φ.hom h

/-- Pullback of cochains is precomposition of their value functions with the simplicial map. -/
lemma cochainValuesEquiv_chainComplexMap {L : SSet.{w}} (f : K ⟶ L) (n : ℕ)
    (φ : (L.chainComplex (ModuleCat.of k k)).X n ⟶ M) (σ : K _⦋n⦌) :
    cochainValuesEquiv k M K n ((chainComplexMap f (ModuleCat.of k k)).f n ≫ φ) σ =
      cochainValuesEquiv k M L n φ (f.app _ σ) := by
  simp only [cochainValuesEquiv_apply]
  have h := ConcreteCategory.congr_hom
    (ι_chainComplexMap_f (R := ModuleCat.of k k) K _ f σ) (1 : k)
  exact congrArg φ.hom h

end TauCeti
