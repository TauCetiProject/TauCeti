/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Basic

/-!
# The cycles of a permutation acting on one factor of a product

`Equiv.prodCongrLeft fun _ => σ` permutes `α × β` by `σ` on the first factor and fixes the second
factor; `Equiv.prodCongrRight fun _ => τ` permutes the second factor by `τ` and fixes the first.
Their powers act by the powers of `σ` and `τ`, so their cycles are the cycles of `σ` and `τ`
paired with single points of the fixed factor. This is how the cyclic order of the intersection
points along each circle of a family of parallel circles, such as the horizontal or vertical
circles of a toroidal grid, is read off a single permutation.

## Main results

* `Equiv.Perm.prodCongrLeft_const_zpow`, `Equiv.Perm.prodCongrRight_const_zpow`: powers are taken
  on the permuted factor.
* `Equiv.Perm.sameCycle_prodCongrLeft_const_iff`, `Equiv.Perm.sameCycle_prodCongrRight_const_iff`:
  two points share a cycle exactly when they agree on the fixed factor and their other
  coordinates share a cycle.
* `Equiv.Perm.IsCycleOn.prodCongrLeft_const`, `Equiv.Perm.IsCycleOn.prodCongrRight_const`: a
  permutation which is one cycle on `s` is one cycle on each slice `s ×ˢ {b}`, respectively
  `{a} ×ˢ t`.
-/

public section

namespace Equiv.Perm

variable {α β : Type*}

/-- The powers of a permutation of the first factor of a product act on that factor. -/
theorem prodCongrLeft_const_zpow (σ : Perm α) (k : ℤ) :
    (Equiv.prodCongrLeft fun _ : β => σ) ^ k = Equiv.prodCongrLeft fun _ : β => σ ^ k :=
  (map_zpow ({ toFun := fun σ : Perm α => (Equiv.prodCongrLeft fun _ : β => σ : Perm (α × β))
               map_one' := rfl
               map_mul' := fun _ _ => rfl } : Perm α →* Perm (α × β)) σ k).symm

/-- The powers of a permutation of the second factor of a product act on that factor. -/
theorem prodCongrRight_const_zpow (τ : Perm β) (k : ℤ) :
    (Equiv.prodCongrRight fun _ : α => τ) ^ k = Equiv.prodCongrRight fun _ : α => τ ^ k :=
  (map_zpow ({ toFun := fun τ : Perm β => (Equiv.prodCongrRight fun _ : α => τ : Perm (α × β))
               map_one' := rfl
               map_mul' := fun _ _ => rfl } : Perm β →* Perm (α × β)) τ k).symm

/-- Two points share a cycle of a permutation of the first factor exactly when their first
coordinates share a cycle and their second coordinates agree. -/
theorem sameCycle_prodCongrLeft_const_iff (σ : Perm α) {x y : α × β} :
    SameCycle (Equiv.prodCongrLeft fun _ : β => σ) x y ↔ σ.SameCycle x.1 y.1 ∧ x.2 = y.2 := by
  obtain ⟨a, b⟩ := x
  obtain ⟨a', b'⟩ := y
  simp only [SameCycle, prodCongrLeft_const_zpow, Equiv.prodCongrLeft_apply, Prod.mk.injEq]
  exact ⟨fun ⟨k, ha, hb⟩ => ⟨⟨k, ha⟩, hb⟩, fun ⟨⟨k, ha⟩, hb⟩ => ⟨k, ha, hb⟩⟩

/-- Two points share a cycle of a permutation of the second factor exactly when their first
coordinates agree and their second coordinates share a cycle. -/
theorem sameCycle_prodCongrRight_const_iff (τ : Perm β) {x y : α × β} :
    SameCycle (Equiv.prodCongrRight fun _ : α => τ) x y ↔ x.1 = y.1 ∧ τ.SameCycle x.2 y.2 := by
  obtain ⟨a, b⟩ := x
  obtain ⟨a', b'⟩ := y
  simp only [SameCycle, prodCongrRight_const_zpow, Equiv.prodCongrRight_apply, Prod.mk.injEq]
  exact ⟨fun ⟨k, ha, hb⟩ => ⟨ha, k, hb⟩, fun ⟨ha, k, hb⟩ => ⟨k, ha, hb⟩⟩

/-- A permutation which is one cycle on `s` acts on the first factor of a product as one cycle
on each slice `s ×ˢ {b}`. -/
theorem IsCycleOn.prodCongrLeft_const {σ : Perm α} {s : Set α} (h : σ.IsCycleOn s) (b : β) :
    IsCycleOn (Equiv.prodCongrLeft fun _ : β => σ) (s ×ˢ {b}) := by
  refine ⟨Equiv.bijOn _ fun p => ?_, fun p hp q hq => ?_⟩
  · obtain ⟨a, b'⟩ := p
    simp only [Equiv.prodCongrLeft_apply, Set.mem_prod, h.apply_mem_iff]
  · exact (sameCycle_prodCongrLeft_const_iff σ).2 ⟨h.2 hp.1 hq.1, hp.2.trans hq.2.symm⟩

/-- A permutation which is one cycle on `t` acts on the second factor of a product as one cycle
on each slice `{a} ×ˢ t`. -/
theorem IsCycleOn.prodCongrRight_const {τ : Perm β} {t : Set β} (h : τ.IsCycleOn t) (a : α) :
    IsCycleOn (Equiv.prodCongrRight fun _ : α => τ) ({a} ×ˢ t) := by
  refine ⟨Equiv.bijOn _ fun p => ?_, fun p hp q hq => ?_⟩
  · obtain ⟨a', b⟩ := p
    simp only [Equiv.prodCongrRight_apply, Set.mem_prod, h.apply_mem_iff]
  · exact (sameCycle_prodCongrRight_const_iff τ).2 ⟨hp.1.trans hq.1.symm, h.2 hp.2 hq.2⟩

end Equiv.Perm
