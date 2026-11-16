/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.Homotopy.Basic

/-!
# Pointwise operations and basepoint correction for homotopies into topological groups

When the target `G` of continuous maps is a topological monoid or group, pointwise multiplication
and inversion preserve homotopies between continuous maps `X → G`.

Furthermore, in a topological group `G`, any free homotopy `H` between two continuous maps
`f₀, f₁ : C(X, G)` that agree at a basepoint `x₀` can be corrected to a homotopy relative to
`{x₀}` by setting `H'(t, x) = H(t, x) * H(t, x₀)⁻¹ * f₀ x₀`. Consequently, two continuous maps
into a topological group are homotopic relative to `{x₀}` if and only if they are freely
homotopic and take the same value at `x₀`.

## Main definitions

* `ContinuousMap.Homotopy.mul`, `ContinuousMap.Homotopy.add`: pointwise multiplication (or
  addition) of homotopies.
* `ContinuousMap.Homotopy.inv`, `ContinuousMap.Homotopy.neg`: pointwise inversion (or negation)
  of a homotopy.
* `ContinuousMap.Homotopy.toHomotopyRelSingleton`: basepoint correction of a free homotopy into a
  topological group to a homotopy relative to `{x₀}`.

## Main results

* `ContinuousMap.Homotopic.mul`, `ContinuousMap.Homotopic.add`: pointwise multiplication (or
  addition) preserves homotopy.
* `ContinuousMap.Homotopic.inv`, `ContinuousMap.Homotopic.neg`: pointwise inversion (or negation)
  preserves homotopy.
* `ContinuousMap.Homotopic.homotopicRel_singleton`: freely homotopic maps into a topological group
  that agree at `x₀` are homotopic relative to `{x₀}`.
* `ContinuousMap.homotopicRel_singleton_iff`: characterization of homotopy relative to `{x₀}` in a
  topological group.
-/

public section

open scoped unitInterval

namespace ContinuousMap

variable {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]

section Mul

variable [Mul G] [ContinuousMul G] {f₀ f₁ g₀ g₁ : C(X, G)}

/-- Pointwise multiplication of two homotopies into a space with continuous multiplication. -/
@[to_additive /-- Pointwise addition of two homotopies into a space with continuous addition. -/]
def Homotopy.mul (F : Homotopy f₀ f₁) (H : Homotopy g₀ g₁) :
    Homotopy (f₀ * g₀) (f₁ * g₁) where
  toFun p := F p * H p
  continuous_toFun := F.continuous.mul H.continuous
  map_zero_left x := by simp [F.apply_zero, H.apply_zero]
  map_one_left x := by simp [F.apply_one, H.apply_one]

/-- Pointwise multiplication of homotopies evaluates to the product of their values. -/
@[to_additive (attr := simp) /-- Pointwise addition of homotopies evaluates to the sum of their
values. -/]
theorem Homotopy.mul_apply (F : Homotopy f₀ f₁) (H : Homotopy g₀ g₁) (p : I × X) :
    (F.mul H) p = F p * H p :=
  (rfl)

/-- Pointwise multiplication preserves homotopy of continuous maps. -/
@[to_additive /-- Pointwise addition preserves homotopy of continuous maps. -/]
theorem Homotopic.mul (hF : Homotopic f₀ f₁) (hH : Homotopic g₀ g₁) :
    Homotopic (f₀ * g₀) (f₁ * g₁) :=
  hF.elim fun F ↦ hH.elim fun H ↦ ⟨F.mul H⟩

end Mul

section Inv

variable [Inv G] [ContinuousInv G] {f₀ f₁ : C(X, G)}

/-- Pointwise inversion of a homotopy into a space with continuous inversion. -/
@[to_additive /-- Pointwise negation of a homotopy into a space with continuous negation. -/]
def Homotopy.inv (F : Homotopy f₀ f₁) : Homotopy f₀⁻¹ f₁⁻¹ where
  toFun p := (F p)⁻¹
  continuous_toFun := F.continuous.inv
  map_zero_left x := by simp [F.apply_zero]
  map_one_left x := by simp [F.apply_one]

/-- Pointwise inversion of a homotopy evaluates to the inverse of its value. -/
@[to_additive (attr := simp) /-- Pointwise negation of a homotopy evaluates to the negation of its
value. -/]
theorem Homotopy.inv_apply (F : Homotopy f₀ f₁) (p : I × X) :
    F.inv p = (F p)⁻¹ :=
  (rfl)

/-- Pointwise inversion preserves homotopy of continuous maps. -/
@[to_additive /-- Pointwise negation preserves homotopy of continuous maps. -/]
theorem Homotopic.inv (hF : Homotopic f₀ f₁) : Homotopic f₀⁻¹ f₁⁻¹ :=
  hF.map Homotopy.inv

end Inv

section Group

variable [Group G] [IsTopologicalGroup G] {f₀ f₁ : C(X, G)}

/-- **Basepoint correction in a topological group.** A free homotopy `F` between two continuous maps
`f₀, f₁ : C(X, G)` agreeing at `x₀` yields a homotopy relative to `{x₀}` given by
`(t, x) ↦ F (t, x) * (F (t, x₀))⁻¹ * f₀ x₀`. -/
@[to_additive toHomotopyRelSingletonAdd
/-- **Basepoint correction in an additive topological group.** A free homotopy `F` between two
continuous maps `f₀, f₁ : C(X, G)` agreeing at `x₀` yields a homotopy relative to `{x₀}` given by
`(t, x) ↦ F (t, x) + (-F (t, x₀)) + f₀ x₀`. -/]
def Homotopy.toHomotopyRelSingleton (F : Homotopy f₀ f₁) {x₀ : X}
    (hx₀ : f₀ x₀ = f₁ x₀) : HomotopyRel f₀ f₁ {x₀} where
  toFun p := F p * (F (p.1, x₀))⁻¹ * f₀ x₀
  continuous_toFun :=
    (F.continuous.mul ((F.continuous.comp (continuous_fst.prodMk continuous_const)).inv)).mul
      continuous_const
  map_zero_left x := by simp [F.apply_zero]
  map_one_left x := by simp [F.apply_one, hx₀]
  prop' t x hx := by
    rw [Set.mem_singleton_iff.mp hx]
    simp

/-- Evaluating the basepoint-corrected homotopy applies
`F (t, x) * (F (t, x₀))⁻¹ * f₀ x₀`. -/
@[to_additive (attr := simp) toHomotopyRelSingletonAdd_apply
/-- Evaluating the basepoint-corrected homotopy applies
`F (t, x) + (-F (t, x₀)) + f₀ x₀`. -/]
theorem Homotopy.toHomotopyRelSingleton_apply (F : Homotopy f₀ f₁) {x₀ : X}
    (hx₀ : f₀ x₀ = f₁ x₀) (p : I × X) :
    F.toHomotopyRelSingleton hx₀ p = F p * (F (p.1, x₀))⁻¹ * f₀ x₀ :=
  (rfl)

/-- **In a topological group, freely homotopic maps agreeing at a point are homotopic relative to
that point.** -/
@[to_additive homotopicRel_singleton_of_addGroup
/-- **In an additive topological group, freely homotopic maps agreeing at a point are
homotopic relative to that point.** -/]
theorem Homotopic.homotopicRel_singleton (hF : Homotopic f₀ f₁) {x₀ : X}
    (hx₀ : f₀ x₀ = f₁ x₀) : HomotopicRel f₀ f₁ {x₀} :=
  hF.map fun F ↦ F.toHomotopyRelSingleton hx₀

/-- Two continuous maps into a topological group are homotopic relative to `{x₀}` if and only if
they are freely homotopic and agree at `x₀`. -/
@[to_additive homotopicRel_singleton_iff_of_addGroup
/-- Two continuous maps into an additive topological group are homotopic relative to
`{x₀}` if and only if they are freely homotopic and agree at `x₀`. -/]
theorem homotopicRel_singleton_iff {x₀ : X} :
    HomotopicRel f₀ f₁ {x₀} ↔ Homotopic f₀ f₁ ∧ f₀ x₀ = f₁ x₀ :=
  ⟨fun h ↦ ⟨h.homotopic, h.fst_eq_snd (Set.mem_singleton x₀)⟩,
    fun ⟨hF, hx₀⟩ ↦ hF.homotopicRel_singleton hx₀⟩

end Group

end ContinuousMap
