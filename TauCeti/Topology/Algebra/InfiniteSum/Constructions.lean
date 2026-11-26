/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Grouping infinite products over fibers

This file supplements Mathlib's results on infinite products and sums with:

* grouping a product or sum indexed by `β × γ`, for a finite type `γ`, into the products or sums
  over its finite fibers, with no hypothesis on the topology of the target;
* preservation of finite support under fiberwise products and sums along any map `π : α → β`.

## Main results

* `HasProd.prod_fiberwise_of_fintype`, `HasSum.sum_fiberwise_of_fintype`: a family on `β × γ` for
  a finite type `γ` has the same product (sum) as the products (sums) of its finite fibers.
* `Function.HasFiniteMulSupport.tprod_fiber`, `Function.HasFiniteSupport.tsum_fiber`: pushing a
  finitely supported function forward by fiberwise `tprod` (`tsum`) along any map preserves finite
  support.
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
      Filter.atTop := by
    refine Filter.tendsto_atTop_atTop.2 fun S ↦ ⟨S.image Prod.fst, fun T hT x hx ↦ ?_⟩
    exact Finset.mem_product.2 ⟨hT (Finset.mem_image_of_mem _ hx), Finset.mem_univ _⟩
  rw [HasProd, SummationFilter.unconditional_filter] at hf ⊢
  exact (hf.comp h).congr fun T ↦ by simp [Finset.prod_product]

/-- Fiberwise infinite product along any map `π : α → β` preserves finite multiplicative support,
since every fiber outside `π '' f.mulSupport` consists of points where `f = 1`. -/
@[to_additive /-- Fiberwise infinite sum along any map `π : α → β` preserves finite support, since
every fiber outside `π '' f.support` consists of points where `f = 0`. -/]
theorem Function.HasFiniteMulSupport.tprod_fiber {α β E : Type*} [CommMonoid E] [TopologicalSpace E]
    {f : α → E} (hf : f.HasFiniteMulSupport) (π : α → β) :
    (fun y : β ↦ ∏' x : π ⁻¹' {y}, f x).HasFiniteMulSupport := by
  refine (hf.image π).subset fun y hy ↦ ?_
  by_contra hnot
  have h1 (x : π ⁻¹' {y}) : f x = 1 := by
    by_contra hfx
    exact hnot ⟨x.val, hfx, x.property⟩
  exact hy (by simp [h1])
