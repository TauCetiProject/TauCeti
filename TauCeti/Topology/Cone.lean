/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Prod
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Function
import Mathlib.Algebra.GroupWithZero.Action.Units

/-!
# Geometric cones and radial extensions

The geometric cone `s.cone` on a subset of a real module consists of its apex
and the rays `(t • x, t)` with `x ∈ s` and `t > 0`. The radial extension `coneMap f`
preserves height and scales the base value by that height. It depends only on
the restriction of `f` to the base, respects composition, and carries maps of
bases and their left inverses to maps of cones and their left inverses.

These constructions provide cone models for extending maps of links across
vertex stars, independently of any PL regularity assumptions.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*,
  Springer (1972), Chapter 1, “Joins and Cones”, pp. 1–2.
-/

public section

noncomputable section

open Set

namespace Set

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The geometric cone on a set, with its apex at height zero and its base at height one.
The cone on the empty set consists of the apex alone. -/
def cone (s : Set E) : Set (E × ℝ) :=
  {p | p = 0 ∨ 0 < p.2 ∧ p.2⁻¹ • p.1 ∈ s}

/-- Cone membership separates the apex from points with a normalized base point. -/
theorem mem_cone {s : Set E} {p : E × ℝ} :
    p ∈ cone s ↔ p = 0 ∨ 0 < p.2 ∧ p.2⁻¹ • p.1 ∈ s := Iff.rfl

@[simp]
theorem zero_mem_cone (s : Set E) : (0 : E × ℝ) ∈ cone s := Or.inl rfl

/-- The empty base contributes only the cone apex. -/
@[simp]
theorem cone_empty : cone (∅ : Set E) = {0} := by
  ext p
  simp [mem_cone]

/-- At positive height, cone membership is membership of the normalized point in the base. -/
@[simp]
theorem smul_mem_cone_iff {s : Set E} (x : E) {t : ℝ} (ht : 0 < t) :
    (t • x, t) ∈ cone s ↔ x ∈ s := by
  simp [mem_cone, ht, ht.ne', smul_smul]

end Set

namespace TauCeti

section Cone

variable {E F G : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F] [AddCommGroup G] [Module ℝ G]

/-- A map of bases extends radially to a height-preserving map of geometric cones. -/
def coneMap (f : E → F) (p : E × ℝ) : F × ℝ :=
  (p.2 • f (p.2⁻¹ • p.1), p.2)

/-- The first component of the radial extension is its scaled base value. -/
@[simp]
theorem coneMap_fst (f : E → F) (p : E × ℝ) :
    (coneMap f p).1 = p.2 • f (p.2⁻¹ • p.1) := (rfl)

/-- The radial extension preserves height. -/
@[simp]
theorem coneMap_snd (f : E → F) (p : E × ℝ) : (coneMap f p).2 = p.2 := (rfl)

@[simp]
theorem coneMap_zero (f : E → F) : coneMap f 0 = 0 := by simp [coneMap]

/-- The radial extension agrees with the base map on each nonzero-height ray. -/
@[simp]
theorem coneMap_smul (f : E → F) (x : E) {t : ℝ} (ht : t ≠ 0) :
    coneMap f (t • x, t) = (t • f x, t) := by
  simp [coneMap, smul_smul, ht]

/-- At height one, radial extension is the original base map. -/
@[simp]
theorem coneMap_one (f : E → F) (x : E) : coneMap f (x, 1) = (f x, 1) := by
  simp [coneMap]

/-- Radial extensions agree on a cone whenever their base maps agree on its base. -/
theorem _root_.Set.EqOn.coneMap {s : Set E} {f g : E → F} (h : EqOn f g s) :
    EqOn (coneMap f) (coneMap g) s.cone := by
  rintro p (rfl | ⟨_, hx⟩)
  · simp
  · simp only [TauCeti.coneMap, h hx]

/-- Radial extension carries a cone to the cone on any set containing the base image. -/
theorem _root_.Set.MapsTo.coneMap {s : Set E} {u : Set F} {f : E → F} (hf : MapsTo f s u) :
    MapsTo (coneMap f) s.cone u.cone := by
  rintro p (rfl | ⟨ht, hx⟩)
  · simp
  · exact Or.inr ⟨ht, by simpa [TauCeti.coneMap, smul_smul, ht.ne'] using hf hx⟩

/-- Radial extension respects composition, including at height zero. -/
theorem coneMap_comp (g : F → G) (f : E → F) :
    coneMap (g ∘ f) = coneMap g ∘ coneMap f := by
  funext p
  by_cases ht : p.2 = 0
  · simp [coneMap, ht]
  · simp [coneMap, smul_smul, ht]

/-- A left inverse on bases extends to a left inverse on their cones. -/
theorem _root_.Set.LeftInvOn.coneMap {s : Set E} {f : E → F} {g : F → E} (h : LeftInvOn g f s) :
    LeftInvOn (coneMap g) (coneMap f) s.cone := by
  rintro p (rfl | ⟨ht, hx⟩)
  · simp
  · simp [TauCeti.coneMap, smul_smul, ht.ne', h hx]

end Cone

end TauCeti
