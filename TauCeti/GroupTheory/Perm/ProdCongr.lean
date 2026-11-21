/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Basic

/-!
# The cycles of a permutation acting on one factor of a product

`Equiv.prodCongrLeft σ` permutes `α × β` by `σ b` on the first factor over each point `b` of the
second factor and fixes the second factor; `Equiv.prodCongrRight τ` permutes the second factor by
`τ a` over each point `a` of the first factor and fixes the first. Their powers act by the powers
of the `σ b` and `τ a`, so their cycles are the cycles of the `σ b` and `τ a` paired with single
points of the fixed factor. This is how the cyclic order of the intersection
points along each circle of a family of parallel circles, such as the horizontal or vertical
circles of a toroidal grid, is read off a single permutation.

## Main results

* `Equiv.Perm.prodCongrLeft_zpow`, `Equiv.Perm.prodCongrRight_zpow`: powers are taken on the
  permuted factor.
* `Equiv.Perm.sameCycle_prodCongrLeft_iff`, `Equiv.Perm.sameCycle_prodCongrRight_iff`: two points
  share a cycle exactly when they agree on the fixed factor and their other coordinates share a
  cycle of the permutation over that point.
* `Equiv.Perm.IsCycleOn.prodCongrLeft`, `Equiv.Perm.IsCycleOn.prodCongrRight`: if the permutation
  over `b` is one cycle on `s`, then the product permutation is one cycle on the slice
  `s ×ˢ {b}`, respectively `{a} ×ˢ t`.
-/

public section

namespace Equiv.Perm

variable {α β : Type*}

/-- The powers of a family of permutations of the first factor of a product act on that factor. -/
theorem prodCongrLeft_zpow (σ : β → Perm α) (k : ℤ) :
    Equiv.prodCongrLeft σ ^ k = Equiv.prodCongrLeft fun b => σ b ^ k := by
  let f : (β → Perm α) →* Perm (α × β) :=
    { toFun := Equiv.prodCongrLeft
      map_one' := Equiv.ext fun ⟨_, _⟩ => by simp [Equiv.prodCongrLeft_apply]
      map_mul' := fun _ _ => Equiv.ext fun ⟨_, _⟩ => by simp [Equiv.prodCongrLeft_apply] }
  rw [← Pi.pow_def]
  exact (map_zpow f σ k).symm

/-- The powers of a family of permutations of the second factor of a product act on that
factor. -/
theorem prodCongrRight_zpow (τ : α → Perm β) (k : ℤ) :
    Equiv.prodCongrRight τ ^ k = Equiv.prodCongrRight fun a => τ a ^ k := by
  let f : (α → Perm β) →* Perm (α × β) :=
    { toFun := Equiv.prodCongrRight
      map_one' := Equiv.ext fun ⟨_, _⟩ => by simp [Equiv.prodCongrRight_apply]
      map_mul' := fun _ _ => Equiv.ext fun ⟨_, _⟩ => by simp [Equiv.prodCongrRight_apply] }
  rw [← Pi.pow_def]
  exact (map_zpow f τ k).symm

/-- Two points share a cycle of a family of permutations of the first factor exactly when their
first coordinates share a cycle of the permutation over their second coordinate and their second
coordinates agree. -/
theorem sameCycle_prodCongrLeft_iff (σ : β → Perm α) {x y : α × β} :
    SameCycle (Equiv.prodCongrLeft σ) x y ↔ (σ x.2).SameCycle x.1 y.1 ∧ x.2 = y.2 := by
  obtain ⟨a, b⟩ := x
  obtain ⟨a', b'⟩ := y
  simp only [SameCycle, prodCongrLeft_zpow, Equiv.prodCongrLeft_apply, Prod.mk.injEq]
  exact ⟨fun ⟨k, ha, hb⟩ => ⟨⟨k, ha⟩, hb⟩, fun ⟨⟨k, ha⟩, hb⟩ => ⟨k, ha, hb⟩⟩

/-- Two points share a cycle of a family of permutations of the second factor exactly when their
first coordinates agree and their second coordinates share a cycle of the permutation over their
first coordinate. -/
theorem sameCycle_prodCongrRight_iff (τ : α → Perm β) {x y : α × β} :
    SameCycle (Equiv.prodCongrRight τ) x y ↔ x.1 = y.1 ∧ (τ x.1).SameCycle x.2 y.2 := by
  obtain ⟨a, b⟩ := x
  obtain ⟨a', b'⟩ := y
  simp only [SameCycle, prodCongrRight_zpow, Equiv.prodCongrRight_apply, Prod.mk.injEq]
  exact ⟨fun ⟨k, ha, hb⟩ => ⟨ha, k, hb⟩, fun ⟨ha, k, hb⟩ => ⟨k, ha, hb⟩⟩

/-- If the permutation of the first factor over `b` is one cycle on `s`, then the family acts on
the product as one cycle on the slice `s ×ˢ {b}`. -/
theorem IsCycleOn.prodCongrLeft {σ : β → Perm α} {s : Set α} {b : β} (h : (σ b).IsCycleOn s) :
    IsCycleOn (Equiv.prodCongrLeft σ) (s ×ˢ {b}) := by
  refine ⟨Equiv.bijOn _ fun p => ?_, fun p hp q hq => ?_⟩
  · obtain ⟨a, b'⟩ := p
    simp only [Equiv.prodCongrLeft_apply, Set.mem_prod, Set.mem_singleton_iff]
    exact and_congr_left fun hb => hb ▸ h.apply_mem_iff
  · refine (sameCycle_prodCongrLeft_iff σ).2 ⟨?_, hp.2.trans hq.2.symm⟩
    rw [Set.mem_singleton_iff.1 hp.2]
    exact h.2 hp.1 hq.1

/-- If the permutation of the second factor over `a` is one cycle on `t`, then the family acts on
the product as one cycle on the slice `{a} ×ˢ t`. -/
theorem IsCycleOn.prodCongrRight {τ : α → Perm β} {t : Set β} {a : α} (h : (τ a).IsCycleOn t) :
    IsCycleOn (Equiv.prodCongrRight τ) ({a} ×ˢ t) := by
  refine ⟨Equiv.bijOn _ fun p => ?_, fun p hp q hq => ?_⟩
  · obtain ⟨a', b⟩ := p
    simp only [Equiv.prodCongrRight_apply, Set.mem_prod, Set.mem_singleton_iff]
    exact and_congr_right fun ha => ha ▸ h.apply_mem_iff
  · refine (sameCycle_prodCongrRight_iff τ).2 ⟨hp.1.trans hq.1.symm, ?_⟩
    rw [Set.mem_singleton_iff.1 hp.1]
    exact h.2 hp.2 hq.2

end Equiv.Perm
