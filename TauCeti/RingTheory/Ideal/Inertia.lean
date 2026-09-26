/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.Tactic.Ring

/-!
# Testing the inertia subgroup of an ideal on algebra generators

Let `G` act by ring automorphisms on a commutative ring `S`, and let `I` be an ideal of `S`.
Mathlib's `Ideal.inertia G I` collects the `σ` with `σ x - x ∈ I` for every `x`. That condition is
multiplicative and additive in `x` up to `I`, so the elements it holds for form a subalgebra over
any base ring `R` whose elements `G` fixes: it is enough to test it on a generating set of `S`
over `R`.

This is the ring-theoretic content of Serre's Lemme 1 in *Corps Locaux*, Chapter IV, §1, where it
is used for `I` a power of the maximal ideal of a discrete valuation ring and `s` a single
generator.

## Main results

* `TauCeti.Ideal.mem_inertia_iff_of_adjoin_eq_top`: membership in `Ideal.inertia G I` is decided
  on a generating set.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §1, Lemme 1.
-/

public section

namespace TauCeti.Ideal

variable {G : Type*} [Group G] {S : Type*} [CommRing S] [MulSemiringAction G S]
variable {R : Type*} [CommSemiring R] [Algebra R S] [SMulCommClass G R S]

/-- **Serre's criterion.** When `S` is generated over `R` by a set `s` and `G` acts by `R`-algebra
automorphisms, membership in the inertia subgroup of an ideal `I` is decided on `s` alone: the
elements moved into `I` form an `R`-subalgebra. -/
theorem mem_inertia_iff_of_adjoin_eq_top {I : Ideal S} {s : Set S}
    (hs : Algebra.adjoin R s = ⊤) {σ : G} :
    σ ∈ I.inertia G ↔ ∀ x ∈ s, σ • x - x ∈ I := by
  rw [Ideal.mem_inertia]
  refine ⟨fun h x _ ↦ h x, fun h x ↦ ?_⟩
  have hx : x ∈ Algebra.adjoin R s := hs ▸ Algebra.mem_top
  induction hx using Algebra.adjoin_induction with
  | mem y hy => exact h y hy
  | algebraMap r =>
      have hr : σ • algebraMap R S r = algebraMap R S r := by simp
      rw [hr, sub_self]
      exact zero_mem _
  | add y z _ _ hy hz =>
      have hyz : σ • (y + z) - (y + z) = (σ • y - y) + (σ • z - z) := by
        rw [smul_add]; ring
      rw [hyz]
      exact add_mem hy hz
  | mul y z _ _ hy hz =>
      have hyz : σ • (y * z) - y * z = σ • y * (σ • z - z) + (σ • y - y) * z := by
        rw [smul_mul']; ring
      rw [hyz]
      exact add_mem (Ideal.mul_mem_left _ _ hz) (Ideal.mul_mem_right _ _ hy)

/-- The monogenic case of **Serre's criterion**: when `S` is generated over `R` by a single
element `ξ`, membership in the inertia subgroup of `I` is decided at `ξ` alone. -/
theorem mem_inertia_iff_of_adjoin_singleton_eq_top {I : Ideal S} {ξ : S}
    (hξ : Algebra.adjoin R {ξ} = ⊤) {σ : G} :
    σ ∈ I.inertia G ↔ σ • ξ - ξ ∈ I := by
  simp [mem_inertia_iff_of_adjoin_eq_top hξ]

end TauCeti.Ideal
