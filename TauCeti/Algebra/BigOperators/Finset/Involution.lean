/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Group.Submonoid.BigOperators

/-!
# Submonoid membership of finite products and sums over an involution

When an involution `τ` preserves a finite set `s`, grouping `s` by its orbits `{x, τ x}` partitions
any commutative product or sum over `s` into singletons at fixed points and two-element pairs on
free orbits. If every fixed point contributes an element of a submonoid `S` and every two-element
orbit has its paired product (or sum) in `S`, then the whole product (or sum) over `s` lies in `S`.
Unlike `Finset.prod_involution`, which requires paired factors to cancel to `1`, this needs no
inverses or quotients and applies directly to submonoids such as squares (`Submonoid.square`) and
even elements (`AddSubmonoid.even`).

## Main results

* `Finset.prod_mem_of_involution`, `Finset.sum_mem_of_involution`: submonoid (or additive
  submonoid) membership of a finite product (or sum) over a `τ`-invariant `Finset`.
-/

public section

namespace Finset

/-- **Submonoid membership of a product over an involution.** Let `τ` map `s` into itself with
`τ (τ x) = x` on `s`. If `f x ∈ S` at every fixed point of `τ` in `s` and `f x * f (τ x) ∈ S` on
every non-fixed element of `s`, then `∏ x ∈ s, f x ∈ S`. -/
@[to_additive /-- **Additive-submonoid membership of a sum over an involution.** Let `τ` map `s`
into itself with `τ (τ x) = x` on `s`. If `f x ∈ S` at every fixed point of `τ` in `s` and
`f x + f (τ x) ∈ S` on every non-fixed element of `s`, then `∑ x ∈ s, f x ∈ S`. -/]
theorem prod_mem_of_involution {ι M B : Type*} [CommMonoid M] [SetLike B M] [SubmonoidClass B M]
    (s : Finset ι) {S : B} {f : ι → M} (τ : ι → ι)
    (hmem : ∀ x ∈ s, τ x ∈ s) (hτ : ∀ x ∈ s, τ (τ x) = x)
    (hfix : ∀ x ∈ s, τ x = x → f x ∈ S)
    (horb : ∀ x ∈ s, τ x ≠ x → f x * f (τ x) ∈ S) :
    ∏ x ∈ s, f x ∈ S := by
  classical
  let orb : ι → Finset ι := fun x ↦ {x, τ x}
  rw [← prod_fiberwise_of_maps_to (s := s) (g := orb) (fun x hx ↦ mem_image_of_mem orb hx)]
  refine prod_mem fun o ho ↦ ?_
  obtain ⟨x, hx, rfl⟩ := mem_image.1 ho
  have hfib : {y ∈ s | orb y = orb x} = {x, τ x} := by
    ext y
    simp only [orb, mem_filter]
    refine ⟨fun ⟨_, hy⟩ ↦ hy ▸ mem_insert_self y {τ y}, ?_⟩
    rw [mem_insert, mem_singleton]
    rintro (rfl | rfl)
    · exact ⟨hx, rfl⟩
    · exact ⟨hmem x hx, by rw [hτ x hx, pair_comm]⟩
  rw [hfib]
  rcases eq_or_ne (τ x) x with h | h
  · simpa [h] using hfix x hx h
  · rw [prod_pair h.symm]
    exact horb x hx h

end Finset
