/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Order.Sum.Order
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# Infinite products and sums over finite fibers and lexicographic sums

This file supplements Mathlib's results on infinite products and sums with:
* `HasProd.prod_fiberwise_of_fintype`, `HasSum.sum_fiberwise_of_fintype`: grouping over `β × γ`
  for finite `γ`.
* `HasProd.sumLex`, `HasSum.sumLex`, `Multipliable.sumLex`, `Summable.sumLex`,
  `Multipliable.tprod_sumLex`, `Summable.tsum_sumLex`,
  `Multipliable.tprod_sumLex_elim_const`, `Summable.tsum_sumLex_elim_const`:
  splitting over `ι ⊕ₗ κ`.
-/

public section

/-- **Summing over the finite fibers of a product**: if a family `f` on `β × γ`, for a finite type
`γ`, has product `a`, then so does the family of products `b ↦ ∏_c f (b, c)` over the fibers. No
continuity of the multiplication and no separation axiom is needed, since the fibers are finite. -/
@[to_additive /-- **Summing over the finite fibers of a product**: if a family `f` on `β × γ`, for
a finite type `γ`, has sum `a`, then so does the family of sums `b ↦ ∑_c f (b, c)` over the fibers.
No continuity of the addition and no separation axiom is needed, since the fibers are finite. -/]
theorem HasProd.prod_fiberwise_of_fintype {β γ E : Type*} [CommMonoid E] [TopologicalSpace E]
    [Fintype γ] {f : β × γ → E} {a : E} (hf : HasProd f a) :
    HasProd (fun b ↦ ∏ c, f (b, c)) a := by
  classical
  have h : Filter.Tendsto (fun T : Finset β ↦ T ×ˢ (Finset.univ : Finset γ)) Filter.atTop
      Filter.atTop := Filter.tendsto_atTop_atTop.2 fun S ↦ ⟨S.image Prod.fst, fun _ hT _ hx ↦
    Finset.mem_product.2 ⟨hT (Finset.mem_image_of_mem _ hx), Finset.mem_univ _⟩⟩
  rw [HasProd, SummationFilter.unconditional_filter] at hf ⊢
  exact (hf.comp h).congr fun T ↦ by simp [Finset.prod_product]

/-- An infinite product over `ι ⊕ₗ κ` splits into its two summands. -/
@[to_additive /-- An infinite sum over `ι ⊕ₗ κ` splits into its two summands. -/]
theorem HasProd.sumLex {ι κ M : Type*} [CommMonoid M] [TopologicalSpace M] [ContinuousMul M]
    {f : ι ⊕ₗ κ → M} {a b : M} (hf : HasProd (fun i ↦ f (Sum.inlₗ i)) a)
    (hg : HasProd (fun k ↦ f (Sum.inrₗ k)) b) : HasProd f (a * b) :=
  toLex.hasProd_iff.mp (HasProd.sum (f := f ∘ toLex) hf hg)

/-- A family on `ι ⊕ₗ κ` is multipliable when both branches are multipliable. -/
@[to_additive /-- A family on `ι ⊕ₗ κ` is summable when both branches are summable. -/]
theorem Multipliable.sumLex {ι κ M : Type*} [CommMonoid M] [TopologicalSpace M] [ContinuousMul M]
    {f : ι ⊕ₗ κ → M} (hf : Multipliable fun i ↦ f (Sum.inlₗ i))
    (hg : Multipliable fun k ↦ f (Sum.inrₗ k)) : Multipliable f :=
  ⟨_, hf.hasProd.sumLex hg.hasProd⟩

/-- Evaluating an infinite product over `ι ⊕ₗ κ` as the product of its two branches. -/
@[to_additive /-- Evaluating an infinite sum over `ι ⊕ₗ κ` as the sum of its two branches. -/]
theorem Multipliable.tprod_sumLex {ι κ M : Type*} [CommMonoid M] [TopologicalSpace M]
    [ContinuousMul M] [T2Space M] {f : ι ⊕ₗ κ → M}
    (hf : Multipliable fun i ↦ f (Sum.inlₗ i)) (hg : Multipliable fun k ↦ f (Sum.inrₗ k)) :
    ∏' x, f x = (∏' i, f (Sum.inlₗ i)) * ∏' k, f (Sum.inrₗ k) :=
  (hf.hasProd.sumLex hg.hasProd).tprod_eq

/-- Evaluating an infinite product over `ι ⊕ₗ κ` for a finite constant second branch. -/
@[to_additive /-- Evaluating an infinite sum over `ι ⊕ₗ κ` for a finite constant second branch. -/]
theorem Multipliable.tprod_sumLex_elim_const {ι κ M : Type*} [Fintype κ] [CommMonoid M]
    [TopologicalSpace M] [ContinuousMul M] [T2Space M] {f : ι → M} (hf : Multipliable f) (c : M) :
    ∏' a : ι ⊕ₗ κ, Sum.elim f (fun _ ↦ c) (ofLex a) = (∏' i, f i) * c ^ Fintype.card κ := by
  simpa [tprod_fintype] using Multipliable.tprod_sumLex
    (f := fun a : ι ⊕ₗ κ ↦ Sum.elim f (fun _ ↦ c) (ofLex a)) hf (hasProd_fintype _).multipliable
