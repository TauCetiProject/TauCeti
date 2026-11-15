/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Subdifferential
public import Mathlib.Analysis.Convex.Cone.Dual

/-!
# Normal cones and constrained subgradients

The normal cone of a set `C` at `x`, relative to a real pairing `B`, consists of the
elements nonpositive on every displacement from `x` to `C`. Taking `B v f = f v`
recovers the usual normal cone in the continuous dual of a real normed space.

`convexIndicator C` is zero on `C` and positive infinity elsewhere (unlike
`Set.indicator`, which is zero outside the set). At a point of `C`, its subdifferential
is exactly the normal cone. Adding this indicator converts a constrained minimum of
a real-valued energy into the zero-subgradient condition. The inclusion from the sum
of the energy subdifferential and the normal cone holds without a qualification
condition; no reverse sum rule is asserted here.

The normal cone is bundled as a `PointedCone`, using Mathlib's `PointedCone.dual`
of the translated constraint with the negated pairing. Thus the usual closure under
addition and nonnegative scalar multiplication is available without extra lemmas.

Neither convexity nor closedness of `C` is needed for these identities. In particular,
we define the normal cone even at points outside `C`; the indicator subdifferential
is empty there, so its identification with the normal cone requires membership.

## References

* R. T. Rockafellar, *Convex Analysis*, §23 (normal cones and subgradients), §27
  (constrained minima).
-/

public section

noncomputable section

open Set
open scoped Pointwise

namespace TauCeti

section Indicator

variable {E : Type*} {C : Set E} {x : E}

open Classical in
/-- The convex-analytic indicator: zero on the set, positive infinity outside it.
The definition makes sense for any set, not only a convex one. -/
def convexIndicator (C : Set E) (x : E) : EReal :=
  if x ∈ C then 0 else ⊤

open Classical in
/-- The defining formula for the convex-analytic indicator. -/
theorem convexIndicator_apply (C : Set E) (x : E) :
    convexIndicator C x = if x ∈ C then 0 else ⊤ := (rfl)

/-- The indicator vanishes on its set. -/
@[simp] theorem convexIndicator_of_mem (hx : x ∈ C) : convexIndicator C x = 0 := by
  simp [convexIndicator, hx]

/-- The indicator is positive infinity outside its set. -/
@[simp] theorem convexIndicator_of_notMem (hx : x ∉ C) : convexIndicator C x = ⊤ := by
  simp [convexIndicator, hx]

/-- The zero set of the indicator is exactly its underlying set. -/
@[simp] theorem convexIndicator_eq_zero_iff : convexIndicator C x = 0 ↔ x ∈ C := by
  by_cases hx : x ∈ C <;> simp [hx]

/-- The indicator is infinite exactly outside its underlying set. -/
@[simp] theorem convexIndicator_eq_top_iff : convexIndicator C x = ⊤ ↔ x ∉ C := by
  by_cases hx : x ∈ C <;> simp [hx]

/-- The indicator never takes the value negative infinity. -/
@[simp] theorem convexIndicator_ne_bot : convexIndicator C x ≠ ⊥ := by
  by_cases hx : x ∈ C <;> simp [hx]

/-- The unconstrained indicator is the zero function. -/
@[simp] theorem convexIndicator_univ : convexIndicator (univ : Set E) = 0 := by
  funext x
  simp

/-- The empty constraint has everywhere infinite indicator. -/
@[simp] theorem convexIndicator_empty : convexIndicator (∅ : Set E) = fun _ ↦ ⊤ := by
  funext x
  simp

end Indicator

section NormalCone

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommMonoid F] [Module ℝ F]
  (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) {C D : Set E} {x : E} {y : F}

/-- The normal cone relative to `B`: the elements nonpositive on all displacements
from `x` to points of `C`. Membership of `x` in `C` is not part of this definition. -/
def normalCone (C : Set E) (x : E) : PointedCone ℝ F :=
  PointedCone.dual (-B) ((fun v ↦ v - x) '' C)

/-- The normal-cone inequality. -/
@[simp] theorem mem_normalCone_iff :
    y ∈ normalCone B C x ↔ ∀ v ∈ C, B (v - x) y ≤ 0 := by
  simp [normalCone, PointedCone.mem_dual]

/-- Restricting a constraint enlarges its normal cone. -/
theorem normalCone_antitone (hCD : C ⊆ D) : normalCone B D x ≤ normalCone B C x :=
  PointedCone.dual_anti (image_mono hCD)

/-- Every element is normal to an empty constraint. -/
@[simp] theorem normalCone_empty : normalCone B ∅ x = ⊤ := by
  ext y
  simp

/-- Every element is normal to a singleton at its only point. -/
@[simp] theorem normalCone_singleton : normalCone B {x} x = ⊤ := by
  ext y
  simp

/-- In the unconstrained case, normals are exactly the elements annihilating the pairing. -/
theorem normalCone_univ : (normalCone B univ x : Set F) = {y | ∀ v, B v y = 0} := by
  ext y
  simp only [SetLike.mem_coe, mem_normalCone_iff, mem_ofPred_eq]
  constructor
  · intro hy v
    have hpos := hy (v + x) (mem_univ _)
    have hneg := hy (-v + x) (mem_univ _)
    simp only [add_sub_cancel_right, map_neg, LinearMap.neg_apply] at hpos hneg
    exact le_antisymm hpos (by linarith)
  · intro hy v _
    exact le_of_eq (hy (v - x))

/-- Translating both the constraint and its base point leaves the normals unchanged. -/
theorem normalCone_vadd (a : E) : normalCone B (a +ᵥ C) (a + x) = normalCone B C x := by
  ext y
  simp only [mem_normalCone_iff, ← image_vadd, forall_mem_image, vadd_eq_add,
    add_sub_add_left_eq_sub]

/-- Normals are closed whenever evaluation against each displacement is continuous. -/
theorem isClosed_normalCone [TopologicalSpace F] (hB : ∀ v, Continuous (B v)) :
    IsClosed (normalCone B C x : Set F) := by
  let _ := Module.addCommMonoidToAddCommGroup ℝ (M := F)
  unfold normalCone
  exact PointedCone.isClosed_dual (p := -B) fun v ↦ (hB v).neg

/-- At an admissible point, the subdifferential of the indicator is the normal cone. -/
@[simp] theorem subdifferential_convexIndicator_of_mem (hx : x ∈ C) :
    subdifferential B (convexIndicator C) x = (normalCone B C x : Set F) := by
  classical
  unfold convexIndicator
  ext y
  simpa only [EReal.coe_zero, SetLike.mem_coe, mem_normalCone_iff, zero_add] using
    (mem_subdifferential_ite_iff B (u := fun _ ↦ 0) hx)

/-- Outside the constraint, the indicator has empty subdifferential. -/
@[simp] theorem subdifferential_convexIndicator_of_notMem (hx : x ∉ C) :
    subdifferential B (convexIndicator C) x = ∅ :=
  subdifferential_eq_empty_of_eq_top B (convexIndicator_of_notMem hx)

open Classical in
/-- The indicator subdifferential, including its empty value at inadmissible points. -/
theorem subdifferential_convexIndicator :
    subdifferential B (convexIndicator C) x = if x ∈ C then (normalCone B C x : Set F) else ∅ := by
  by_cases hx : x ∈ C <;> simp [hx]

/-- A constrained minimum is exactly a zero subgradient of the energy plus its indicator.
No convexity, continuity, or constraint qualification is required. -/
theorem zero_mem_subdifferential_add_convexIndicator_iff (f : E → ℝ) (hx : x ∈ C) :
    (0 : F) ∈ subdifferential B (fun v ↦ (f v : EReal) + convexIndicator C v) x ↔
      IsMinOn f C x := by
  classical
  have heq : (fun v ↦ (f v : EReal) + convexIndicator C v) =
      fun v ↦ if v ∈ C then (f v : EReal) else ⊤ := by
    funext v
    by_cases hv : v ∈ C <;> simp [convexIndicator, hv]
  rw [heq, mem_subdifferential_ite_iff B hx, isMinOn_iff]
  simp

/-- The unconditional inclusion in the indicator sum rule: a subgradient plus a normal
is a subgradient of the constrained energy. The reverse inclusion needs qualification. -/
theorem subdifferential_add_normalCone_subset (f : E → ℝ) (hx : x ∈ C) :
    subdifferential B (fun v ↦ (f v : EReal)) x + (normalCone B C x : Set F) ⊆
      subdifferential B (fun v ↦ (f v : EReal) + convexIndicator C v) x := by
  rintro _ ⟨y, hy, z, hz, rfl⟩
  rw [mem_subdifferential_iff]
  simp only [convexIndicator_of_mem hx, add_zero, EReal.coe_ne_bot, EReal.coe_ne_top,
    ne_eq, not_false_eq_true, true_and]
  intro v
  by_cases hv : v ∈ C
  · have hf := (mem_subdifferential_coe_iff B f).1 hy v
    have hn := (mem_normalCone_iff B).1 hz v hv
    simp only [convexIndicator_of_mem hv, add_zero, map_add, ← EReal.coe_add,
      EReal.coe_le_coe_iff]
    linarith
  · simp [convexIndicator_of_notMem hv]

end NormalCone

end TauCeti
