/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.Homotopy.Basic

/-!
# Pointwise operations on homotopies into a topological group

For maps into a topological monoid, the pointwise product of two homotopies is a homotopy between
the pointwise products, and in a topological group the same holds for pointwise inverses. So
homotopy classes of maps into a topological group form a group under pointwise multiplication.

In a topological group, a free homotopy between two maps that agree at a point `x₀` can be
corrected into a homotopy relative to `x₀`: if `F` is a homotopy from `f` to `g`, then
`(t, x) ↦ F (t, x) * F (t, x₀)⁻¹ * f x₀` is a homotopy from `f` to `g` which is constant at `x₀`.
Thus for maps into a topological group, being homotopic as based maps is the same as being freely
homotopic; this is how a free nullhomotopy of a loop in a group becomes a based one.

## Main results

* `ContinuousMap.Homotopic.mul`, `ContinuousMap.Homotopic.add`: pointwise products of homotopic
  maps are homotopic.
* `ContinuousMap.Homotopic.inv`, `ContinuousMap.Homotopic.neg`: pointwise inverses of homotopic
  maps are homotopic.
* `ContinuousMap.Homotopic.homotopicRel_singleton_of_group`,
  `ContinuousMap.Homotopic.homotopicRel_singleton_of_addGroup`: maps into a topological group
  which are homotopic and agree at a point are homotopic relative to that point.
-/

public section

namespace ContinuousMap.Homotopic

variable {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]

/-- **Pointwise products of homotopic maps are homotopic.** -/
@[to_additive /-- **Pointwise sums of homotopic maps are homotopic.** -/]
theorem mul [Mul G] [ContinuousMul G] {f₀ f₁ g₀ g₁ : C(X, G)} (hf : f₀.Homotopic f₁)
    (hg : g₀.Homotopic g₁) : (f₀ * g₀).Homotopic (f₁ * g₁) := by
  obtain ⟨F⟩ := hf
  obtain ⟨H⟩ := hg
  exact ⟨{ toFun := fun p ↦ F p * H p
           continuous_toFun := by fun_prop
           map_zero_left := fun x ↦ by simp
           map_one_left := fun x ↦ by simp }⟩

/-- **Pointwise inverses of homotopic maps are homotopic.** -/
@[to_additive /-- **Pointwise negations of homotopic maps are homotopic.** -/]
theorem inv [Inv G] [ContinuousInv G] {f₀ f₁ : C(X, G)} (hf : f₀.Homotopic f₁) :
    f₀⁻¹.Homotopic f₁⁻¹ := by
  obtain ⟨F⟩ := hf
  exact ⟨{ toFun := fun p ↦ (F p)⁻¹
           continuous_toFun := by fun_prop
           map_zero_left := fun x ↦ by simp
           map_one_left := fun x ↦ by simp }⟩

/-- **Homotopic maps into a topological group are homotopic relative to a point where they
agree.** In particular a loop at `1` which is freely homotopic to the constant loop is
nullhomotopic as a based loop. -/
@[to_additive
  /-- **Homotopic maps into a topological additive group are homotopic relative to a point where
  they agree.** In particular a loop at `0` which is freely homotopic to the constant loop is
  nullhomotopic as a based loop. -/]
theorem homotopicRel_singleton_of_group [Group G] [IsTopologicalGroup G] {f g : C(X, G)}
    (h : f.Homotopic g) {x₀ : X} (hx₀ : f x₀ = g x₀) : f.HomotopicRel g {x₀} := by
  obtain ⟨F⟩ := h
  exact ⟨{ toFun := fun p ↦ F p * (F (p.1, x₀))⁻¹ * f x₀
           continuous_toFun := by fun_prop
           map_zero_left := fun x ↦ by simp
           map_one_left := fun x ↦ by simp [hx₀]
           prop' := fun t x hx ↦ by
             rw [Set.mem_singleton_iff.1 hx]
             simp }⟩

end ContinuousMap.Homotopic
