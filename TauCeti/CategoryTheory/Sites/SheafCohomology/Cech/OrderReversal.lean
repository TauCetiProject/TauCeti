/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Basic

import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Order reversal on Čech complexes

Let `C` be a category with finite products, let `U : ι → C` be a family of objects and let
`P : Cᵒᵖ ⥤ A` be a presheaf with values in a preadditive category with products. The
order-reversing operator `τ` on the Čech complex `Č(U, P)` acts in degree `n` by reversing each
`(n + 1)`-tuple of indices with the Koszul sign `(-1) ^ (n * (n + 1) / 2)`:
`(τ c)_(i₀ … iₙ) = (-1) ^ (n * (n + 1) / 2) • c_(iₙ … i₀)|_(U_(i₀) × ⋯ × U_(iₙ))`.

This file defines `TauCeti.CategoryTheory.cechOrderReversal U` as an involutive endomorphism of
`CategoryTheory.cechComplexFunctor U`, proves that it commutes with refinement maps, and constructs
a chain homotopy `TauCeti.CategoryTheory.cechOrderReversalHomotopy U P` from the identity to `τ`.
In particular, `τ` induces the identity on Čech cohomology in every degree
(`TauCeti.CategoryTheory.homologyMap_cechOrderReversal`).

The homotopy is obtained by dualizing a universal chain homotopy on free integral chains on tuples
`Fin (n + 1) → N`: `H₀ = 0` and `H_{n + 1} b = b 0 * (b - rev b - H_n (∂ b))` via the cone on the
first entry. Because `H_n` is natural in the index set `N`, evaluating it on `id : Fin (n + 1) →
Fin (n + 1)` yields a universal integer linear combination of reindexing maps
`Fin (n + 2) → Fin (n + 1)`, which dualizes to Čech cochains for any category with finite
products, without any thinness or ordering hypothesis.

## Main definitions

* `TauCeti.CategoryTheory.cechOrderReversal U`: the order-reversing endomorphism of
  `CategoryTheory.cechComplexFunctor U`.
* `TauCeti.CategoryTheory.cechOrderReversalHomotopy U P`: a chain homotopy from the identity of
  `Č(U, P)` to `(cechOrderReversal U).app P`.

## Main results

* `TauCeti.CategoryTheory.cechOrderReversal_app_f_π`: the factor of `τ` at a tuple `a`.
* `TauCeti.CategoryTheory.cechOrderReversal_comp_cechOrderReversal`: `τ` is an involution.
* `TauCeti.CategoryTheory.cechComplexMap_comp_cechOrderReversal`: `τ` commutes with refinement
  maps.
* `TauCeti.CategoryTheory.homologyMap_cechOrderReversal`: `τ` induces the identity on cohomology.

## References

* The Stacks Project, Cohomology of Sheaves, §20.25 (tag 01FP, pp. 49–50).
-/

public section

noncomputable section

open CategoryTheory Limits Opposite

universe w v v' u u'

namespace TauCeti.CategoryTheory

namespace CechOrderReversal

/-! ### Universal chains on tuples -/

/-- Free integral chains on `(n + 1)`-tuples in a type `N`. -/
private abbrev Chain (N : Type*) (n : ℕ) := (Fin (n + 1) → N) →₀ ℤ

/-- Two `ℤ`-linear maps out of `Chain N n` agree once they agree on all basis elements
`Finsupp.single b 1`. -/
private lemma chain_ext {N M : Type*} [AddCommGroup M] {n : ℕ} {f g : Chain N n →ₗ[ℤ] M}
    (h : ∀ b, f (Finsupp.single b 1) = g (Finsupp.single b 1)) (x : Chain N n) : f x = g x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | single b k =>
    rw [← mul_one k, ← smul_eq_mul, ← Finsupp.smul_single, map_zsmul, map_zsmul, h]

/-- Functorial pushforward of chains along a function `g : N₁ → N₂`. -/
private def push {N₁ N₂ : Type*} (g : N₁ → N₂) {n : ℕ} : Chain N₁ n →ₗ[ℤ] Chain N₂ n :=
  Finsupp.lmapDomain ℤ ℤ (g ∘ ·)

private lemma push_single {N₁ N₂ : Type*} (g : N₁ → N₂) {n : ℕ} (α : Fin (n + 1) → N₁) (k : ℤ) :
    push g (Finsupp.single α k) = Finsupp.single (g ∘ α) k :=
  Finsupp.mapDomain_single

/-- The alternating boundary map on chains on tuples. -/
private def bdry (N : Type*) (n : ℕ) : Chain N (n + 1) →ₗ[ℤ] Chain N n :=
  Finsupp.linearCombination ℤ fun b ↦
    ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) • Finsupp.single (b ∘ j.succAbove) 1

private lemma bdry_single (N : Type*) (n : ℕ) (b : Fin (n + 2) → N) :
    bdry N n (Finsupp.single b 1) =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) • Finsupp.single (b ∘ j.succAbove) 1 := by simp [bdry]

private lemma push_bdry {N₁ N₂ : Type*} (g : N₁ → N₂) (n : ℕ) (x : Chain N₁ (n + 1)) :
    push g (bdry N₁ n x) = bdry N₂ n (push g x) :=
  chain_ext (f := (push g).comp (bdry N₁ n)) (g := (bdry N₂ n).comp (push g)) (fun b ↦ by
    simp only [LinearMap.comp_apply, push_single, bdry_single, map_sum, map_zsmul,
      Function.comp_assoc]) x

/-- The first simplicial identity for `Fin.succAbove`. -/
private lemma succAbove_comp_succAbove {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 3)}
    (h : (j : ℕ) ≤ i) :
    j.succAbove ∘ i.succAbove = i.succ.succAbove ∘ (j.castLT (by omega)).succAbove :=
  (congrArg (fun f ↦ ⇑(SimplexCategory.Hom.toOrderHom f))
    (SimplexCategory.δ_comp_δ'' (i := j) (j := i) (Fin.le_def.2 h))).symm

/-- The boundary squares to zero. -/
private lemma bdry_bdry (N : Type*) (n : ℕ) (x : Chain N (n + 2)) :
    bdry N n (bdry N (n + 1) x) = 0 :=
  chain_ext (f := (bdry N n).comp (bdry N (n + 1))) (g := 0) (fun b ↦ by
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, bdry_single, map_sum, map_zsmul,
      Finset.smul_sum, smul_smul, ← Finset.sum_product']
    let S : Finset (Fin (n + 3) × Fin (n + 2)) := {ji | (ji.1 : ℕ) ≤ ji.2}
    rw [Finset.univ_product_univ, ← Finset.sum_add_sum_compl S, add_eq_zero_iff_eq_neg,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_bij'
      (fun ji h ↦ (ji.2.succ, ji.1.castLT (by have := (Finset.mem_filter.1 h).2; omega)))
      (fun ji h ↦ (ji.2.castSucc, ji.1.pred fun h0 ↦ by simp [S, h0] at h))
      (fun ji h ↦ by simp only [S, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
        Fin.val_succ, Fin.val_castLT, not_le] at h ⊢; omega)
      (fun ji h ↦ by simp only [S, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
        Fin.val_castSucc, Fin.val_pred, not_le] at h ⊢; omega)
      (fun _ _ ↦ by simp) (fun _ _ ↦ by simp) fun ⟨j, i⟩ h ↦ ?_
    have h' : (j : ℕ) ≤ i := (Finset.mem_filter.1 h).2
    rw [Function.comp_assoc, succAbove_comp_succAbove h', ← Function.comp_assoc, ← neg_smul,
      Fin.val_succ, Fin.val_castLT, pow_succ]
    congr 1; ring) x

/-- The order-reversing operator on chains on tuples, with sign `(-1) ^ (n * (n + 1) / 2)`. -/
private def rev (N : Type*) (n : ℕ) : Chain N n →ₗ[ℤ] Chain N n :=
  Finsupp.linearCombination ℤ fun b ↦
    (-1 : ℤ) ^ (n * (n + 1) / 2) • Finsupp.single (b ∘ Fin.rev) 1

private lemma rev_single (N : Type*) (n : ℕ) (b : Fin (n + 1) → N) :
    rev N n (Finsupp.single b 1) =
      (-1 : ℤ) ^ (n * (n + 1) / 2) • Finsupp.single (b ∘ Fin.rev) 1 := by simp [rev]

private lemma push_rev {N₁ N₂ : Type*} (g : N₁ → N₂) (n : ℕ) (x : Chain N₁ n) :
    push g (rev N₁ n x) = rev N₂ n (push g x) :=
  chain_ext (f := (push g).comp (rev N₁ n)) (g := (rev N₂ n).comp (push g)) (fun b ↦ by
    simp only [LinearMap.comp_apply, push_single, rev_single, map_zsmul, Function.comp_assoc]) x

private lemma rev_zero (N : Type*) (x : Chain N 0) : rev N 0 x = x :=
  chain_ext (f := rev N 0) (g := LinearMap.id) (fun b ↦ by
    have hrev : b ∘ Fin.rev = b := funext fun i ↦ by fin_cases i; rfl
    simp [rev_single, hrev]) x

private lemma rev_rev (N : Type*) (n : ℕ) (x : Chain N n) : rev N n (rev N n x) = x :=
  chain_ext (f := (rev N n).comp (rev N n)) (g := LinearMap.id) (fun b ↦ by
    have hrev : (b ∘ Fin.rev) ∘ Fin.rev = b := funext fun j ↦ congrArg b (Fin.rev_rev j)
    simp only [LinearMap.comp_apply, LinearMap.id_apply, rev_single, map_zsmul, smul_smul,
      ← pow_add, ← two_mul, pow_mul, hrev]
    norm_num) x

private lemma triangle_succ (n : ℕ) : (n + 1) * (n + 2) / 2 = n * (n + 1) / 2 + (n + 1) := by
  have : (n + 1) * (n + 2) = n * (n + 1) + 2 * (n + 1) := by ring
  omega

/-- The sign identity comparing `bdry ∘ rev` and `rev ∘ bdry`. -/
private lemma neg_one_pow_rev_bdry (n : ℕ) (j : Fin (n + 2)) :
    (-1 : ℤ) ^ ((n + 1) * (n + 2) / 2) * (-1 : ℤ) ^ (j : ℕ) =
      (-1 : ℤ) ^ (n * (n + 1) / 2) * (-1 : ℤ) ^ (j.rev : ℕ) := by
  rw [triangle_succ, pow_add, mul_assoc, Fin.val_rev, Nat.succ_sub_succ_eq_sub]
  congr 1
  rw [show (-1 : ℤ) ^ (n + 1) = (-1 : ℤ) ^ (n + 1 - (j : ℕ)) * (-1 : ℤ) ^ (j : ℕ) by
    rw [← pow_add, Nat.sub_add_cancel (Nat.le_of_lt_succ j.isLt)],
    mul_assoc, ← pow_add, ← two_mul, pow_mul]; norm_num

/-- `rev` commutes with the boundary map on chains. -/
private lemma bdry_rev (N : Type*) (n : ℕ) (x : Chain N (n + 1)) :
    bdry N n (rev N (n + 1) x) = rev N n (bdry N n x) :=
  chain_ext (f := (bdry N n).comp (rev N (n + 1))) (g := (rev N n).comp (bdry N n)) (fun b ↦ by
    simp only [LinearMap.comp_apply, rev_single, map_zsmul, bdry_single, map_sum, Finset.smul_sum]
    refine Fintype.sum_bijective Fin.rev Fin.rev_bijective _ _ fun j ↦ ?_
    have hcomp : b ∘ Fin.rev ∘ j.succAbove = b ∘ j.rev.succAbove ∘ Fin.rev :=
      funext fun i ↦ congrArg b (Fin.rev_succAbove j i)
    rw [smul_smul, smul_smul, neg_one_pow_rev_bdry, mul_comm ((-1 : ℤ) ^ _),
      Function.comp_assoc, hcomp, ← Function.comp_assoc]) x

/-- The cone on chains with apex `v : N`, prepending `v` to every tuple. -/
private def cone {N : Type*} (v : N) (n : ℕ) : Chain N n →ₗ[ℤ] Chain N (n + 1) :=
  Finsupp.linearCombination ℤ fun b ↦ Finsupp.single (Fin.cons v b) 1

private lemma cone_single {N : Type*} (v : N) (n : ℕ) (b : Fin (n + 1) → N) :
    cone v n (Finsupp.single b 1) = Finsupp.single (Fin.cons v b) 1 := by simp [cone]

private lemma push_cone {N₁ N₂ : Type*} (g : N₁ → N₂) (v : N₁) (n : ℕ) (x : Chain N₁ n) :
    push g (cone v n x) = cone (g v) n (push g x) :=
  chain_ext (f := (push g).comp (cone v n)) (g := (cone (g v) n).comp (push g)) (fun b ↦ by
    simp only [LinearMap.comp_apply, push_single, cone_single]
    congr 2; ext j; cases j using Fin.cases <;> rfl) x

/-- The cone identity `∂ (v * x) = x - v * ∂ x` in positive degrees. -/
private lemma bdry_cone {N : Type*} (v : N) (n : ℕ) (x : Chain N (n + 1)) :
    bdry N (n + 1) (cone v (n + 1) x) = x - cone v n (bdry N n x) :=
  chain_ext (f := (bdry N (n + 1)).comp (cone v (n + 1)))
    (g := LinearMap.id - (cone v n).comp (bdry N n)) (fun b ↦ by
    rw [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
      cone_single, bdry_single, bdry_single, map_sum, Fin.sum_univ_succ]
    have h0 : Fin.cons v b ∘ (0 : Fin (n + 3)).succAbove = b := funext fun _ ↦ rfl
    have hs (j : Fin (n + 2)) :
        Fin.cons v b ∘ j.succ.succAbove = Fin.cons v (b ∘ j.succAbove) := by
      ext i; cases i using Fin.cases with
      | zero => simp [Fin.succAbove]
      | succ i => simp [Fin.succ_succAbove_succ]
    simp only [Fin.val_zero, pow_zero, one_smul, h0, Fin.val_succ, pow_succ, hs, map_zsmul,
      cone_single, mul_neg_one, neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg]) x

/-- The universal chain homotopy between `id` and `rev`, constructed inductively using the cone on
the first entry. -/
private def hom (N : Type*) : (n : ℕ) → Chain N n →ₗ[ℤ] Chain N (n + 1)
  | 0 => 0
  | n + 1 =>
    Finsupp.linearCombination ℤ fun b ↦
      cone (b 0) (n + 1) (Finsupp.single b 1 - rev N (n + 1) (Finsupp.single b 1) -
        hom N n (bdry N n (Finsupp.single b 1)))

private lemma hom_succ_single (N : Type*) (n : ℕ) (b : Fin (n + 2) → N) :
    hom N (n + 1) (Finsupp.single b 1) =
      cone (b 0) (n + 1) (Finsupp.single b 1 - rev N (n + 1) (Finsupp.single b 1) -
        hom N n (bdry N n (Finsupp.single b 1))) := by simp [hom]

private lemma push_hom {N₁ N₂ : Type*} (g : N₁ → N₂) :
    ∀ (n : ℕ) (x : Chain N₁ n), push g (hom N₁ n x) = hom N₂ n (push g x)
  | 0, x => by simp [hom]
  | n + 1, x =>
    chain_ext (f := (push g).comp (hom N₁ (n + 1))) (g := (hom N₂ (n + 1)).comp (push g))
      (fun b ↦ by
        rw [LinearMap.comp_apply, LinearMap.comp_apply, push_single, hom_succ_single,
          hom_succ_single, push_cone]
        congr 1
        rw [map_sub, map_sub, push_single, push_rev, push_single, push_hom g n, push_bdry,
          push_single]) x

private lemma bdry_hom_zero (N : Type*) (x : Chain N 0) :
    bdry N 0 (hom N 0 x) = x - rev N 0 x := by
  rw [hom, LinearMap.zero_apply, map_zero, rev_zero, sub_self]

private lemma bdry_hom_succ (N : Type*) :
    ∀ (n : ℕ) (x : Chain N (n + 1)),
      bdry N (n + 1) (hom N (n + 1) x) + hom N n (bdry N n x) = x - rev N (n + 1) x
  | n, x =>
    chain_ext (f := (bdry N (n + 1)).comp (hom N (n + 1)) + (hom N n).comp (bdry N n))
      (g := LinearMap.id - rev N (n + 1)) (fun b ↦ by
        simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
          LinearMap.id_apply, hom_succ_single, bdry_cone]
        have hinner : bdry N n (Finsupp.single b 1 - rev N (n + 1) (Finsupp.single b 1) -
            hom N n (bdry N n (Finsupp.single b 1))) = 0 := by
          rw [map_sub, map_sub, bdry_rev]
          cases n with
          | zero => rw [bdry_hom_zero, sub_self]
          | succ m =>
            have ih := bdry_hom_succ N m (bdry N (m + 1) (Finsupp.single b 1))
            rw [bdry_bdry, map_zero, add_zero] at ih; rw [ih, sub_self]
        rw [hinner, map_zero, sub_zero, sub_add_cancel]) x

/-- Composition of universal chains: substituting `c₂` into each tuple of `c₁`. -/
private def compUniv {m k l : ℕ} (c₂ : Chain (Fin (k + 1)) l) (c₁ : Chain (Fin (m + 1)) k) :
    Chain (Fin (m + 1)) l :=
  Finsupp.linearCombination ℤ (fun α ↦ push α c₂) c₁

/-- For any natural family of chain maps `M`, universal composition agrees with composition. -/
private lemma compUniv_eq {m k l : ℕ} (M : ∀ N : Type, Chain N k →ₗ[ℤ] Chain N l)
    (hM : ∀ {N₁ N₂ : Type} (g : N₁ → N₂) (x : Chain N₁ k), push g (M N₁ x) = M N₂ (push g x))
    (c₁ : Chain (Fin (m + 1)) k) :
    compUniv (M (Fin (k + 1)) (Finsupp.single id 1)) c₁ = M (Fin (m + 1)) c₁ :=
  chain_ext (f := Finsupp.linearCombination ℤ (fun α ↦ push α (M _ (Finsupp.single id 1))))
    (g := M _) (fun α ↦ by
      rw [Finsupp.linearCombination_single, one_smul, hM α, push_single]; rfl) c₁

/-! ### Dualizing universal chains to Čech cochains -/

section Dual

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {A : Type u'} [Category.{v'} A]
  [Preadditive A] [HasProducts.{w} A] {ι : Type w} (U : ι → C) (P : Cᵒᵖ ⥤ A)

/-- The canonical projection `∏ⱼ U (b j) ⟶ ∏ⱼ U (b (α j))` induced by a reindexing `α`. -/
private def reproj {m k : ℕ} (b : Fin (m + 1) → ι) (α : Fin (k + 1) → Fin (m + 1)) :
    (∏ᶜ fun j : Fin (m + 1) ↦ U (b j)) ⟶ (∏ᶜ fun j : Fin (k + 1) ↦ U (b (α j))) :=
  Pi.lift fun j ↦ Pi.π (fun l ↦ U (b l)) (α j)

private lemma reproj_id {m : ℕ} (b : Fin (m + 1) → ι) : reproj U b id = 𝟙 _ :=
  Pi.hom_ext _ _ fun j ↦ by simp [reproj]

@[reassoc]
private lemma reproj_comp {m k l : ℕ} (b : Fin (m + 1) → ι) (α : Fin (k + 1) → Fin (m + 1))
    (β : Fin (l + 1) → Fin (k + 1)) :
    reproj U b α ≫ reproj U (b ∘ α) β = reproj U b (α ∘ β) :=
  Pi.hom_ext _ _ fun j ↦ by simp [reproj]

/-- The product forming the degree-`n` term of `Č(U, P)`. -/
private abbrev cechX (n : ℕ) : A :=
  ∏ᶜ fun a : Fin (n + 1) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (a j)))

/-- The degree-`n` differential of `Č(U, P)`, between the products which define its terms. -/
private abbrev cechD (n : ℕ) : cechX U P n ⟶ cechX U P (n + 1) :=
  ((cechComplexFunctor U).obj P).d n (n + 1)

/-- Evaluate a universal chain `c : Chain (Fin (m + 1)) k` at a tuple `b : Fin (m + 1) → ι`
as a linear combination of restricted projections out of `Čᵏ(U, P)`. -/
private def evalAt {m k : ℕ} (b : Fin (m + 1) → ι) :
    Chain (Fin (m + 1)) k →ₗ[ℤ] (cechX U P k ⟶ P.obj (op (∏ᶜ fun j ↦ U (b j)))) :=
  Finsupp.linearCombination ℤ fun α ↦
    Pi.π (fun a : Fin (k + 1) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (a j)))) (b ∘ α) ≫
      P.map (reproj U b α).op

private lemma evalAt_single {m k : ℕ} (b : Fin (m + 1) → ι) (α : Fin (k + 1) → Fin (m + 1))
    (z : ℤ) :
    evalAt U P b (Finsupp.single α z) =
      z • (Pi.π (fun a : Fin (k + 1) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (a j)))) (b ∘ α) ≫
        P.map (reproj U b α).op) := by simp [evalAt]

private lemma evalAt_push {m k l : ℕ} (b : Fin (m + 1) → ι) (α : Fin (k + 1) → Fin (m + 1))
    (c : Chain (Fin (k + 1)) l) :
    evalAt U P b (push α c) = evalAt U P (b ∘ α) c ≫ P.map (reproj U b α).op := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, map_add, Preadditive.add_comp, hx, hy]
  | single β z =>
    rw [push_single, evalAt_single, evalAt_single, Preadditive.zsmul_comp, Category.assoc,
      ← P.map_comp, ← op_comp, reproj_comp]; rfl

/-- The map of Čech cochains `Čᵏ(U, P) ⟶ Čᵐ(U, P)` dual to a universal chain
`c : Chain (Fin (m + 1)) k`. -/
private def evalUniv {m k : ℕ} (c : Chain (Fin (m + 1)) k) : cechX U P k ⟶ cechX U P m :=
  Pi.lift fun b ↦ evalAt U P b c

@[reassoc]
private lemma evalUniv_π {m k : ℕ} (c : Chain (Fin (m + 1)) k) (b : Fin (m + 1) → ι) :
    evalUniv U P c ≫ Pi.π _ b = evalAt U P b c :=
  Pi.lift_comp_π _ _

private lemma evalUniv_add {m k : ℕ} (c c' : Chain (Fin (m + 1)) k) :
    evalUniv U P (c + c') = evalUniv U P c + evalUniv U P c' :=
  Pi.hom_ext _ _ fun b ↦ by rw [Preadditive.add_comp, evalUniv_π, evalUniv_π, evalUniv_π, map_add]

private lemma evalUniv_sub {m k : ℕ} (c c' : Chain (Fin (m + 1)) k) :
    evalUniv U P (c - c') = evalUniv U P c - evalUniv U P c' :=
  Pi.hom_ext _ _ fun b ↦ by rw [Preadditive.sub_comp, evalUniv_π, evalUniv_π, evalUniv_π, map_sub]

private lemma evalUniv_single_id (m : ℕ) :
    evalUniv U P (Finsupp.single (id : Fin (m + 1) → Fin (m + 1)) 1) = 𝟙 _ :=
  Pi.hom_ext _ _ fun b ↦ by simp [evalUniv_π, evalAt_single, reproj_id]

private lemma evalUniv_comp {m k l : ℕ} (c₂ : Chain (Fin (k + 1)) l)
    (c₁ : Chain (Fin (m + 1)) k) :
    evalUniv U P c₂ ≫ evalUniv U P c₁ = evalUniv U P (compUniv c₂ c₁) := by
  refine Pi.hom_ext _ _ fun b ↦ ?_
  rw [Category.assoc, evalUniv_π, evalUniv_π]
  induction c₁ using Finsupp.induction_linear with
  | zero => simp [compUniv]
  | add x y hx hy =>
    rw [map_add, Preadditive.comp_add, compUniv, map_add, ← compUniv, ← compUniv, map_add, hx, hy]
  | single α z =>
    rw [evalAt_single, Preadditive.comp_zsmul, evalUniv_π_assoc, ← evalAt_push, compUniv,
      Finsupp.linearCombination_single, map_zsmul]

/-- The Čech differential as the dual of the universal boundary chain. -/
private lemma evalUniv_bdry (n : ℕ) :
    evalUniv U P (bdry (Fin (n + 2)) n (Finsupp.single id 1)) = cechD U P n := by
  refine Pi.hom_ext _ _ fun k ↦ (evalUniv_π U P _ k).trans <| Eq.trans ?_
    (cechComplexFunctor_obj_d_comp_π U P n k).symm
  rw [bdry_single, map_sum]
  exact Finset.sum_congr rfl fun m _ ↦ by rw [map_zsmul, evalAt_single, one_smul]; rfl

end Dual

end CechOrderReversal

open CechOrderReversal

section

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {A : Type u'} [Category.{v'} A]
  [Preadditive A] [HasProducts.{w} A] {ι : Type w} (U : ι → C)

/-- The degree-`n` component of `cechOrderReversal U` on a presheaf `P`. -/
private def cechOrderReversalX (P : Cᵒᵖ ⥤ A) (n : ℕ) : cechX U P n ⟶ cechX U P n :=
  evalUniv U P (rev (Fin (n + 1)) n (Finsupp.single id 1))

@[reassoc]
private lemma cechOrderReversalX_π (P : Cᵒᵖ ⥤ A) (n : ℕ) (a : Fin (n + 1) → ι) :
    cechOrderReversalX U P n ≫
      Pi.π (fun b : Fin (n + 1) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (b j)))) a =
      (-1 : ℤ) ^ (n * (n + 1) / 2) •
        (Pi.π (fun b : Fin (n + 1) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (b j)))) (a ∘ Fin.rev) ≫
          P.map (Pi.lift fun j ↦ Pi.π (fun l ↦ U (a l)) (Fin.rev j)).op) :=
  (evalUniv_π U P _ a).trans <| by rw [rev_single, map_zsmul, evalAt_single, one_smul]; rfl

private lemma cechOrderReversalX_comm (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    cechOrderReversalX U P n ≫ cechD U P n = cechD U P n ≫ cechOrderReversalX U P (n + 1) := by
  rw [cechOrderReversalX, cechOrderReversalX, ← evalUniv_bdry, evalUniv_comp, evalUniv_comp,
    compUniv_eq (fun N ↦ rev N n) (fun g x ↦ push_rev g n x),
    compUniv_eq (fun N ↦ bdry N n) (fun g x ↦ push_bdry g n x), bdry_rev]

private lemma cechOrderReversalX_naturality {P Q : Cᵒᵖ ⥤ A} (α : P ⟶ Q) (n : ℕ) :
    ((cechComplexFunctor U).map α).f n ≫ cechOrderReversalX U Q n =
      cechOrderReversalX U P n ≫ ((cechComplexFunctor U).map α).f n := by
  let f : cechX U P n ⟶ cechX U Q n := ((cechComplexFunctor U).map α).f n
  refine Pi.hom_ext _ _ fun a ↦ ?_
  have hπ (c : Fin (n + 1) → ι) : f ≫
      Pi.π (fun b : Fin (n + 1) → ι ↦ Q.obj (op (∏ᶜ fun j ↦ U (b j)))) c =
      Pi.π (fun b : Fin (n + 1) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (b j)))) c ≫ α.app _ :=
    cechComplexFunctor_map_f_π U P α n c
  change (f ≫ cechOrderReversalX U Q n) ≫ _ = (cechOrderReversalX U P n ≫ f) ≫ _
  rw [Category.assoc, Category.assoc, cechOrderReversalX_π, Preadditive.comp_zsmul,
    ← Category.assoc, hπ (a ∘ Fin.rev), Category.assoc, ← α.naturality, hπ a,
    cechOrderReversalX_π_assoc, Preadditive.zsmul_comp, Category.assoc]

/-- **The order-reversing endomorphism of the Čech complex**, natural in the presheaf. In degree
`n` it sends the factor indexed by `a` to the factor indexed by `a ∘ Fin.rev`, restricted along
the coordinate reversal of the product, times `(-1) ^ (n * (n + 1) / 2)`
(`cechOrderReversal_app_f_π`). It is an involution (`cechOrderReversal_comp_cechOrderReversal`),
commutes with refinement maps (`cechComplexMap_comp_cechOrderReversal`), and is chain homotopic to
the identity (`cechOrderReversalHomotopy`). -/
def cechOrderReversal :
    cechComplexFunctor (A := A) U ⟶ cechComplexFunctor U where
  app P :=
    { f := cechOrderReversalX U P
      comm' := by rintro i _ rfl; exact cechOrderReversalX_comm U P i }
  naturality _ _ α := HomologicalComplex.hom_ext _ _ (cechOrderReversalX_naturality U α)

/-- The factor of `(cechOrderReversal U).app P` in degree `n` indexed by `a` is `(-1)^(n*(n+1)/2)`
times the factor indexed by `a ∘ Fin.rev`, restricted along the coordinate reversal. -/
@[reassoc]
theorem cechOrderReversal_app_f_π (P : Cᵒᵖ ⥤ A) (n : ℕ) (a : Fin (n + 1) → ι) :
    ((cechOrderReversal U).app P).f n ≫ Pi.π _ a =
      (-1 : ℤ) ^ (n * (n + 1) / 2) •
        (Pi.π _ (a ∘ Fin.rev) ≫ P.map (Pi.lift fun j ↦ Pi.π (fun l ↦ U (a l)) (Fin.rev j)).op) :=
  cechOrderReversalX_π U P n a

/-- Order reversal on the Čech complex is an involution. -/
@[reassoc (attr := simp)]
theorem cechOrderReversal_comp_cechOrderReversal :
    cechOrderReversal (A := A) U ≫ cechOrderReversal U = 𝟙 _ := by
  ext P n : 3
  change cechOrderReversalX U P n ≫ cechOrderReversalX U P n = 𝟙 _
  rw [cechOrderReversalX, evalUniv_comp,
    compUniv_eq (fun N ↦ rev N n) (fun g x ↦ push_rev g n x), rev_rev, evalUniv_single_id]

/-- **Order reversal is homotopic to the identity.** Dualizing the universal chain homotopy `hom`
yields a chain homotopy from `𝟙 (Č(U, P))` to `(cechOrderReversal U).app P` for any category with
finite products and any preadditive coefficient category with products. -/
def cechOrderReversalHomotopy (P : Cᵒᵖ ⥤ A) :
    Homotopy (𝟙 ((cechComplexFunctor U).obj P)) ((cechOrderReversal U).app P) :=
  let H (j : ℕ) : ((cechComplexFunctor U).obj P).X (j + 1) ⟶ ((cechComplexFunctor U).obj P).X j :=
    evalUniv U P (hom (Fin (j + 1)) j (Finsupp.single id 1))
  Homotopy.equivSubZero.symm <| (Homotopy.ofEq <| by
    ext n : 1
    rw [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f]
    cases n with
    | zero =>
      rw [Homotopy.nullHomotopicMap'_f_of_not_rel_right (rfl : (ComplexShape.up ℕ).Rel 0 1)
        fun l hl ↦ Nat.succ_ne_zero l hl, eqToHom_refl, Category.id_comp]
      change 𝟙 (cechX U P 0) - cechOrderReversalX U P 0 =
        cechD U P 0 ≫ evalUniv U P (hom (Fin 1) 0 (Finsupp.single id 1))
      rw [← evalUniv_single_id, cechOrderReversalX, ← evalUniv_sub, ← bdry_hom_zero,
        ← evalUniv_bdry, evalUniv_comp, compUniv_eq (fun N ↦ bdry N 0) (fun g x ↦ push_bdry g 0 x)]
    | succ n =>
      rw [Homotopy.nullHomotopicMap'_f (c := ComplexShape.up ℕ) (k₂ := n) (k₁ := n + 1)
        (k₀ := n + 2) rfl rfl, eqToHom_refl, eqToHom_refl, Category.id_comp, Category.id_comp]
      change 𝟙 (cechX U P (n + 1)) - cechOrderReversalX U P (n + 1) =
        cechD U P (n + 1) ≫ evalUniv U P (hom (Fin (n + 2)) (n + 1) (Finsupp.single id 1)) +
          evalUniv U P (hom (Fin (n + 1)) n (Finsupp.single id 1)) ≫ cechD U P n
      rw [← evalUniv_single_id, cechOrderReversalX, ← evalUniv_sub, ← bdry_hom_succ, evalUniv_add,
        ← evalUniv_bdry, ← evalUniv_bdry, evalUniv_comp, evalUniv_comp,
        compUniv_eq (fun N ↦ bdry N (n + 1)) (fun g x ↦ push_bdry g (n + 1) x),
        compUniv_eq (fun N ↦ hom N n) (fun g x ↦ push_hom g n x)]).trans
    (Homotopy.nullHomotopy' fun i j (h : (ComplexShape.up ℕ).Rel j i) ↦
      eqToHom (by rw [← (h : j + 1 = i)]) ≫ H j)

/-- **Order reversal induces the identity on Čech cohomology** in every degree. -/
@[simp]
theorem homologyMap_cechOrderReversal [CategoryWithHomology A] (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    HomologicalComplex.homologyMap ((cechOrderReversal U).app P) n = 𝟙 _ :=
  ((cechOrderReversalHomotopy U P).homologyMap_eq n).symm.trans
    (HomologicalComplex.homologyMap_id _ n)

end

/-- Order reversal commutes with the map of Čech complexes induced by any morphism of families. -/
@[reassoc]
theorem cechComplexMap_comp_cechOrderReversal {C : Type u} [Category.{v} C] [HasFiniteProducts C]
    {A : Type u'} [Category.{v'} A] [Preadditive A] [HasProducts.{w} A]
    {ι κ : Type w} {U : ι → C} {V : κ → C} (P : Cᵒᵖ ⥤ A)
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    cechComplexMap P φ ≫ (cechOrderReversal U).app P =
      (cechOrderReversal V).app P ≫ cechComplexMap P φ := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
  let f : cechX V P n ⟶ cechX U P n := (cechComplexMap P φ).f n
  change f ≫ cechOrderReversalX U P n = cechOrderReversalX V P n ≫ f
  refine Pi.hom_ext _ _ fun a ↦ ?_
  have hπ (c : Fin (n + 1) → ι) : f ≫
      Pi.π (fun b : Fin (n + 1) → ι ↦ P.obj (op (∏ᶜ fun j ↦ U (b j)))) c =
      Pi.π (fun b : Fin (n + 1) → κ ↦ P.obj (op (∏ᶜ fun j ↦ V (b j)))) (φ.f ∘ c) ≫
        P.map (Limits.Pi.map fun j ↦ φ.φ (c j)).op :=
    cechComplexMap_f_π P φ n c
  have hprod :
      (Pi.lift fun j : Fin (n + 1) ↦ Pi.π (fun l ↦ U (a l)) (Fin.rev j)) ≫
          Limits.Pi.map (fun j ↦ φ.φ ((a ∘ Fin.rev) j)) =
        Limits.Pi.map (fun j ↦ φ.φ (a j)) ≫
          Pi.lift fun j : Fin (n + 1) ↦ Pi.π (fun l ↦ V ((φ.f ∘ a) l)) (Fin.rev j) :=
    Pi.hom_ext _ _ fun j ↦ by simp [Limits.Pi.map_π]
  rw [Category.assoc, Category.assoc, cechOrderReversalX_π, Preadditive.comp_zsmul,
    ← Category.assoc, hπ (a ∘ Fin.rev), Category.assoc, hπ a, cechOrderReversalX_π_assoc,
    Preadditive.zsmul_comp, Category.assoc, ← P.map_comp, ← P.map_comp, ← op_comp, ← op_comp,
    hprod]; rfl

end TauCeti.CategoryTheory
