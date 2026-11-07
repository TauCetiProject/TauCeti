/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Set.Function
import Mathlib.Algebra.GroupWithZero.Action.Units

/-!
# Geometric cones and radial extensions

The geometric cone `s.cone 𝕜` on a subset of a module over a partially ordered division
semiring `𝕜` consists of its apex and the rays `(t • x, t)` with `x ∈ s` and `t > 0`. The radial
extension `coneMap 𝕜 f` preserves height and scales the base value by that height. It depends
only on the restriction of `f` to the base, respects composition, and carries maps of bases and
their left inverses to maps of cones and their left inverses.

These constructions provide cone models for extending maps of links across
vertex stars, independently of any PL regularity assumptions.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*,
  Springer (1972), Chapter 1, “Joins and Cones”, pp. 1–2.
-/

public section

noncomputable section

open Set

variable {𝕜 E F G : Type*} [DivisionSemiring 𝕜]
  [AddCommMonoid E] [Module 𝕜 E] [AddCommMonoid F] [Module 𝕜 F] [AddCommMonoid G] [Module 𝕜 G]

namespace Set

variable [PartialOrder 𝕜]

variable (𝕜) in
/-- The geometric cone on a set, with its apex at height zero and its base at height one.
The cone on the empty set consists of the apex alone. -/
def cone (s : Set E) : Set (E × 𝕜) :=
  {p | p = 0 ∨ 0 < p.2 ∧ p.2⁻¹ • p.1 ∈ s}

/-- Cone membership separates the apex from points with a normalized base point. -/
theorem mem_cone {s : Set E} {p : E × 𝕜} :
    p ∈ s.cone 𝕜 ↔ p = 0 ∨ 0 < p.2 ∧ p.2⁻¹ • p.1 ∈ s := Iff.rfl

/-- The apex lies in every cone. -/
@[simp]
theorem zero_mem_cone (s : Set E) : (0 : E × 𝕜) ∈ s.cone 𝕜 := Or.inl rfl

variable (𝕜) in
/-- The empty base contributes only the cone apex. -/
@[simp]
theorem cone_empty : (∅ : Set E).cone 𝕜 = {0} := by
  ext p
  simp [mem_cone]

/-- At positive height, cone membership is membership of the normalized point in the base. -/
@[simp]
theorem smul_mem_cone_iff {s : Set E} (x : E) {t : 𝕜} (ht : 0 < t) :
    (t • x, t) ∈ s.cone 𝕜 ↔ x ∈ s := by
  simp [mem_cone, ht, ht.ne', smul_smul]

end Set

namespace TauCeti

variable (𝕜) in
/-- A map of bases extends radially to a height-preserving map of geometric cones. -/
def coneMap (f : E → F) (p : E × 𝕜) : F × 𝕜 :=
  (p.2 • f (p.2⁻¹ • p.1), p.2)

/-- The first component of the radial extension is its scaled base value. -/
@[simp]
theorem coneMap_fst (f : E → F) (p : E × 𝕜) :
    (coneMap 𝕜 f p).1 = p.2 • f (p.2⁻¹ • p.1) := (rfl)

/-- The radial extension preserves height. -/
@[simp]
theorem coneMap_snd (f : E → F) (p : E × 𝕜) : (coneMap 𝕜 f p).2 = p.2 := (rfl)

variable (𝕜) in
/-- The radial extension fixes the apex. -/
@[simp]
theorem coneMap_zero (f : E → F) : coneMap 𝕜 f 0 = 0 := by simp [coneMap]

/-- The radial extension agrees with the scaled base map on each ray, including at height
zero. -/
@[simp]
theorem coneMap_smul (f : E → F) (x : E) (t : 𝕜) :
    coneMap 𝕜 f (t • x, t) = (t • f x, t) := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [coneMap]
  · simp [coneMap, smul_smul, ht]

variable (𝕜) in
/-- At height one, radial extension is the original base map. -/
@[simp]
theorem coneMap_one (f : E → F) (x : E) : coneMap 𝕜 f (x, 1) = (f x, 1) := by
  simp [coneMap]

variable (𝕜) in
/-- Radial extension respects composition, including at height zero. -/
theorem coneMap_comp (g : F → G) (f : E → F) :
    coneMap 𝕜 (g ∘ f) = coneMap 𝕜 g ∘ coneMap 𝕜 f := by
  funext p
  rcases eq_or_ne p.2 0 with ht | ht <;> simp [coneMap, smul_smul, ht]

section PartialOrder

variable [PartialOrder 𝕜]

/-- Radial extensions agree on a cone whenever their base maps agree on its base. -/
theorem _root_.Set.EqOn.coneMap {s : Set E} {f g : E → F} (h : EqOn f g s) :
    EqOn (coneMap 𝕜 f) (coneMap 𝕜 g) (s.cone 𝕜) := by
  rintro p (rfl | ⟨_, hx⟩)
  · simp
  · simp only [TauCeti.coneMap, h hx]

/-- Radial extension carries a cone to the cone on any set containing the base image. -/
theorem _root_.Set.MapsTo.coneMap {s : Set E} {u : Set F} {f : E → F} (hf : MapsTo f s u) :
    MapsTo (coneMap 𝕜 f) (s.cone 𝕜) (u.cone 𝕜) := by
  rintro p (rfl | ⟨ht, hx⟩)
  · simp
  · exact Or.inr ⟨ht, by simpa [TauCeti.coneMap, smul_smul, ht.ne'] using hf hx⟩

/-- A left inverse on bases extends to a left inverse on their cones. -/
theorem _root_.Set.LeftInvOn.coneMap {s : Set E} {f : E → F} {g : F → E} (h : LeftInvOn g f s) :
    LeftInvOn (coneMap 𝕜 g) (coneMap 𝕜 f) (s.cone 𝕜) := by
  rintro p (rfl | ⟨ht, hx⟩)
  · simp
  · simp [TauCeti.coneMap, smul_smul, ht.ne', h hx]

end PartialOrder

end TauCeti
