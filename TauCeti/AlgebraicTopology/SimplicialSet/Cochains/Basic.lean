/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# Simplicial cochains as functions on simplices

For a ring `k` and a `k`-module `M`, evaluation on the unit chain of each simplex identifies
`Hom_k(C_n(K; k), M)` with functions from the `n`-simplices of `K` to `M`. This identification
is integral-linear, including for noncommutative rings. The cochain differential becomes the
alternating sum of values on faces, and pullback becomes precomposition on simplices.

The construction uses Mathlib's `SSet.isColimitChainComplexXCofan` and
`Cofan.IsColimit.desc`, the coproduct universal property also used by `TauCeti.chainsDesc`.
These coordinates allow comparison of coefficient rings without changing cochain values.

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
  let desc (v : K _⦋n⦌ → M) : (K.chainComplex (ModuleCat.of k k)).X n ⟶ M :=
    Cofan.IsColimit.desc (K.isColimitChainComplexXCofan (ModuleCat.of k k) n)
      (fun σ ↦ ModuleCat.ofHom (LinearMap.toSpanSingleton k M (v σ)))
  have desc_apply (v : K _⦋n⦌ → M) (σ : K _⦋n⦌) :
      desc v (K.ιChainComplex (R := ModuleCat.of k k) σ 1) = v σ := by
    have h : K.ιChainComplex σ ≫ desc v =
        ModuleCat.ofHom (LinearMap.toSpanSingleton k M (v σ)) :=
      Cofan.IsColimit.fac (K.isColimitChainComplexXCofan (ModuleCat.of k k) n)
        (fun σ ↦ ModuleCat.ofHom (LinearMap.toSpanSingleton k M (v σ))) σ
    rw [← ModuleCat.comp_apply, h]
    exact LinearMap.toSpanSingleton_apply_one k M (v σ)
  exact
    { toFun := fun φ σ ↦ φ (K.ιChainComplex (R := ModuleCat.of k k) σ 1)
      invFun := desc
      left_inv := fun φ ↦ by
        apply SSet.chainComplex_hom_ext
        intro σ
        apply ModuleCat.hom_ext
        apply LinearMap.ext_ring
        exact desc_apply _ σ
      right_inv := fun v ↦ funext (desc_apply v)
      map_add' := fun φ ψ ↦ by
        funext σ
        rfl
      map_smul' := fun a φ ↦ by
        funext σ
        rfl }

/-- The value coordinate of a cochain is its value on the unit chain of the simplex. -/
@[simp]
lemma cochainValuesEquiv_apply (n : ℕ)
    (φ : (K.chainComplex (ModuleCat.of k k)).X n ⟶ M) (σ : K _⦋n⦌) :
    cochainValuesEquiv k M K n φ σ = φ (K.ιChainComplex (R := ModuleCat.of k k) σ 1) :=
  (rfl)

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
  rw [cochainValuesEquiv_apply]
  change (K.ιChainComplex σ ≫ (K.chainComplex (ModuleCat.of k k)).d (n + 1) n ≫ φ) 1 = _
  rw [K.ιChainComplex_d_assoc]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, ModuleCat.hom_sum,
    ModuleCat.hom_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, ModuleCat.hom_comp,
    LinearMap.comp_apply, cochainValuesEquiv_apply]

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
