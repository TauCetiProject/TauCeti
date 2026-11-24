/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import TauCeti.Algebra.Homology.LinearYoneda

/-!
# Simplicial cochains as functions on simplices

For a ring `k` and a `k`-module `M`, evaluation on the unit chain of each simplex identifies
`Hom_k(C_n(K; k), M)` with functions from the `n`-simplices of `K` to `M`. This identification
is integral-linear, including for noncommutative rings. The cochain differential becomes the
alternating sum of values on faces, pullback becomes precomposition on simplices, and a change
of coefficients acts on the values.
The simplicial set `K : SSet.{u}` may live in a different universe from `k`. The file assumes
`HasCoproducts.{u} (ModuleCat k)`, that is, coproducts of `k`-modules indexed by every type in
the universe `u` of `K`, as Mathlib's `SSet.chainComplex` requires. They exist, for example, when
`u` is no larger than the universe of `k`.

The construction uses Mathlib's `SSet.isColimitChainComplexXCofan` and
`Cofan.IsColimit.desc`, the coproduct universal property also used by `TauCeti.chainsDesc`.
These coordinates allow comparison of coefficient rings without changing cochain values. Over a
commutative ring they are `k`-linear (`TauCeti.cochainValuesLinearEquiv`).

For chains with coefficients in an object `R` of a `k`-linear category with coproducts, a cochain
with values in `M` is likewise the family of its restrictions to the summands of the simplices,
a family of morphisms `R ⟶ M` (`TauCeti.cochainComponentsLinearEquiv`).

## References

* A. Hatcher, *Algebraic Topology*, Section 3.1.
-/

public section

noncomputable section

open CategoryTheory Limits SSet
open scoped Simplicial

universe u w

namespace TauCeti

section Ring

variable (k : Type w) [Ring k] (M : ModuleCat.{w} k) (K : SSet.{u})
  [HasCoproducts.{u} (ModuleCat.{w} k)]

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
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }

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
  rw [← h, ← map_smul, ← map_smul, smul_eq_mul, mul_one]

/-- The cochain differential, in simplex coordinates, is the alternating sum over faces. -/
lemma cochainValuesEquiv_d (n : ℕ)
    (φ : (K.chainComplex (ModuleCat.of k k)).X n ⟶ M) (σ : K _⦋n + 1⦌) :
    cochainValuesEquiv k M K (n + 1)
        ((K.chainComplex (ModuleCat.of k k)).d (n + 1) n ≫ φ) σ =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • cochainValuesEquiv k M K n φ (K.δ i σ) := by
  rw [cochainValuesEquiv_apply, ← ModuleCat.comp_apply, K.ιChainComplex_d_assoc]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, ModuleCat.hom_sum,
    ModuleCat.hom_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, ModuleCat.hom_comp,
    LinearMap.comp_apply, cochainValuesEquiv_apply]

/-- The value of the coboundary of a `0`-cochain on a `1`-simplex. -/
lemma cochainValuesEquiv_d_one_zero (φ : (K.chainComplex (ModuleCat.of k k)).X 0 ⟶ M)
    (σ : K _⦋1⦌) :
    cochainValuesEquiv k M K 1 ((K.chainComplex (ModuleCat.of k k)).d 1 0 ≫ φ) σ =
      cochainValuesEquiv k M K 0 φ (K.δ 0 σ) - cochainValuesEquiv k M K 0 φ (K.δ 1 σ) := by
  refine (cochainValuesEquiv_d k M K 0 φ σ).trans ?_
  simp [Fin.sum_univ_two, sub_eq_add_neg]

/-- The value of the coboundary of a `1`-cochain on a `2`-simplex. -/
lemma cochainValuesEquiv_d_two_one (φ : (K.chainComplex (ModuleCat.of k k)).X 1 ⟶ M)
    (σ : K _⦋2⦌) :
    cochainValuesEquiv k M K 2 ((K.chainComplex (ModuleCat.of k k)).d 2 1 ≫ φ) σ =
      cochainValuesEquiv k M K 1 φ (K.δ 0 σ) - cochainValuesEquiv k M K 1 φ (K.δ 1 σ) +
        cochainValuesEquiv k M K 1 φ (K.δ 2 σ) := by
  refine (cochainValuesEquiv_d k M K 1 φ σ).trans ?_
  simp [Fin.sum_univ_three, sub_eq_add_neg]

/-- Pullback of cochains is precomposition of their value functions with the simplicial map. -/
lemma cochainValuesEquiv_chainComplexMap {L : SSet.{u}} (f : K ⟶ L) (n : ℕ)
    (φ : (L.chainComplex (ModuleCat.of k k)).X n ⟶ M) (σ : K _⦋n⦌) :
    cochainValuesEquiv k M K n ((chainComplexMap f (ModuleCat.of k k)).f n ≫ φ) σ =
      cochainValuesEquiv k M L n φ (f.app _ σ) := by
  rw [cochainValuesEquiv_apply, cochainValuesEquiv_apply, ← ModuleCat.comp_apply,
    ι_chainComplexMap_f_assoc, ModuleCat.comp_apply]

/-- Changing the coefficients of a cochain along `g : M ⟶ N` applies `g` to each of its values. -/
lemma cochainValuesEquiv_comp {N : ModuleCat.{w} k} (n : ℕ)
    (φ : (K.chainComplex (ModuleCat.of k k)).X n ⟶ M) (g : M ⟶ N) (σ : K _⦋n⦌) :
    cochainValuesEquiv k N K n (φ ≫ g) σ = g (cochainValuesEquiv k M K n φ σ) := by
  rw [cochainValuesEquiv_apply, cochainValuesEquiv_apply, ModuleCat.comp_apply]

end Ring

section CommRing

variable (k : Type w) [CommRing k] (M : ModuleCat.{w} k) (K : SSet.{u})
  [HasCoproducts.{u} (ModuleCat.{w} k)]

/-- For a commutative ring `k`, the identification `TauCeti.cochainValuesEquiv` of cochains with
functions on simplices is `k`-linear. -/
def cochainValuesLinearEquiv (n : ℕ) :
    ((K.chainComplex (ModuleCat.of k k)).X n ⟶ M) ≃ₗ[k] (K _⦋n⦌ → M) :=
  { cochainValuesEquiv k M K n with map_smul' := fun _ _ ↦ rfl }

@[simp]
lemma coe_cochainValuesLinearEquiv (n : ℕ) :
    ⇑(cochainValuesLinearEquiv k M K n) = cochainValuesEquiv k M K n :=
  (rfl)

@[simp]
lemma coe_cochainValuesLinearEquiv_symm (n : ℕ) :
    ⇑(cochainValuesLinearEquiv k M K n).symm = (cochainValuesEquiv k M K n).symm :=
  (rfl)

/-- The values of the coboundary of a cochain in `Hom(C(K; k), M)` are alternating sums of its
values on faces. -/
lemma cochainValuesEquiv_linearYonedaObj_d (n : ℕ)
    (φ : ((K.chainComplex (ModuleCat.of k k)).linearYonedaObj k M).X n) (σ : K _⦋n + 1⦌) :
    cochainValuesEquiv k M K (n + 1)
        (((K.chainComplex (ModuleCat.of k k)).linearYonedaObj k M).d n (n + 1) φ) σ =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • cochainValuesEquiv k M K n φ (K.δ i σ) := by
  rw [ChainComplex.linearYonedaObj_d_apply]
  exact cochainValuesEquiv_d k M K n φ σ

/-- The values of the coboundary of a `0`-cochain in `Hom(C(K; k), M)` on a `1`-simplex `σ`: the
value at its endpoint `δ₀ σ` minus the value at its starting point `δ₁ σ`. -/
lemma cochainValuesEquiv_linearYonedaObj_d_zero_one
    (φ : ((K.chainComplex (ModuleCat.of k k)).linearYonedaObj k M).X 0) (σ : K _⦋1⦌) :
    cochainValuesEquiv k M K 1
        (((K.chainComplex (ModuleCat.of k k)).linearYonedaObj k M).d 0 1 φ) σ =
      cochainValuesEquiv k M K 0 φ (K.δ 0 σ) - cochainValuesEquiv k M K 0 φ (K.δ 1 σ) := by
  refine (cochainValuesEquiv_linearYonedaObj_d k M K 0 φ σ).trans ?_
  simp [Fin.sum_univ_two, sub_eq_add_neg]

/-- The values of the coboundary of a `1`-cochain in `Hom(C(K; k), M)` on a `2`-simplex `σ`: the
alternating sum of its values on the edges `δ₀ σ`, `δ₁ σ` and `δ₂ σ`. -/
lemma cochainValuesEquiv_linearYonedaObj_d_one_two
    (φ : ((K.chainComplex (ModuleCat.of k k)).linearYonedaObj k M).X 1) (σ : K _⦋2⦌) :
    cochainValuesEquiv k M K 2
        (((K.chainComplex (ModuleCat.of k k)).linearYonedaObj k M).d 1 2 φ) σ =
      cochainValuesEquiv k M K 1 φ (K.δ 0 σ) - cochainValuesEquiv k M K 1 φ (K.δ 1 σ) +
        cochainValuesEquiv k M K 1 φ (K.δ 2 σ) := by
  refine (cochainValuesEquiv_linearYonedaObj_d k M K 1 φ σ).trans ?_
  simp [Fin.sum_univ_three, sub_eq_add_neg]

end CommRing

section Linear

variable {C : Type*} [Category C] [HasCoproducts.{u} C] [Preadditive C] (k : Type*) [Ring k]
  [Linear k C] (K : SSet.{u}) (R M : C)

/-- **Cochains with coefficients in a linear category are families of morphisms, one per
simplex.** The simplicial `n`-chains of `K` with coefficients in `R` are a coproduct of copies of
`R`, one for each `n`-simplex, so a morphism from them to `M` is the family of its restrictions to
the summands. The identification is `k`-linear. -/
def cochainComponentsLinearEquiv (n : ℕ) :
    ((K.chainComplex R).X n ⟶ M) ≃ₗ[k] (K _⦋n⦌ → (R ⟶ M)) where
  toFun φ σ := K.ιChainComplex σ ≫ φ
  invFun v := Cofan.IsColimit.desc (K.isColimitChainComplexXCofan R n) v
  left_inv _ := SSet.chainComplex_hom_ext fun σ ↦
    Cofan.IsColimit.fac (K.isColimitChainComplexXCofan R n) _ σ
  right_inv v := funext fun σ ↦ Cofan.IsColimit.fac (K.isColimitChainComplexXCofan R n) v σ
  map_add' _ _ := funext fun _ ↦ Preadditive.comp_add _ _ _ _ _ _
  map_smul' _ _ := funext fun _ ↦ Linear.comp_smul _ _ _ _ _ _

/-- The component of a cochain at a simplex is its restriction to the summand of that simplex. -/
@[simp]
lemma cochainComponentsLinearEquiv_apply (n : ℕ) (φ : (K.chainComplex R).X n ⟶ M)
    (σ : K _⦋n⦌) : cochainComponentsLinearEquiv k K R M n φ σ = K.ιChainComplex σ ≫ φ :=
  (rfl)

/-- The cochain with prescribed components restricts to the prescribed component on the summand of
each simplex. -/
@[reassoc (attr := simp)]
lemma ιChainComplex_cochainComponentsLinearEquiv_symm_apply (n : ℕ) (v : K _⦋n⦌ → (R ⟶ M))
    (σ : K _⦋n⦌) : K.ιChainComplex σ ≫ (cochainComponentsLinearEquiv k K R M n).symm v = v σ :=
  Cofan.IsColimit.fac (K.isColimitChainComplexXCofan R n) v σ

end Linear

end TauCeti
