/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Sets.Opens
import Mathlib.Analysis.Convex.PathConnected

/-!
# The exterior of a closed ball

In a real normed space of dimension at least two the complement of a closed ball is path-connected:
it is the image of the product of the unit sphere with the ray `(r, ∞)` of radii exceeding the
ball's under the polar-coordinate map `(u, t) ↦ x + t • u`.

Every unbounded complementary component of a bounded set meets the exterior of any closed ball
containing that set. Connectedness of the exterior therefore forces all such components to
coincide. This uniqueness result and the corresponding filled-hull alternative are proved in
`TauCeti/Analysis/Normed/Module/FilledHull.lean`.

This file also packages the centered exterior `{x : E | R < ‖x‖} = (closedBall 0 R)ᶜ` as an element
`TauCeti.exteriorBall E R : TopologicalSpace.Opens E` together with its basic membership,
complement, monotonicity, nonemptiness, and connectedness lemmas.

## Main definitions

* `TauCeti.exteriorBall`: the open exterior `{x : E | R < ‖x‖}` of the closed ball `closedBall 0 R`
  as a `TopologicalSpace.Opens E`.

## Main results

* `TauCeti.isPathConnected_compl_closedBall` — the exterior of a closed ball is path-connected in
  a real normed space of dimension at least two.
* `TauCeti.nonempty_exteriorBall` — `exteriorBall E R` is nonempty in a nontrivial real normed
  space.
* `TauCeti.isPathConnected_exteriorBall`, `TauCeti.isConnected_exteriorBall` — `exteriorBall E R`
  is path-connected and connected when `1 < Module.rank ℝ E`.

## References

* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Ch. 2.
-/

public section

namespace TauCeti

open Metric Set TopologicalSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The exterior of a closed ball is path-connected** in a real normed space of dimension at
least two. -/
theorem isPathConnected_compl_closedBall (h : 1 < Module.rank ℝ E) (x : E) (r : ℝ) :
    IsPathConnected (closedBall x r)ᶜ := by
  rcases lt_or_ge r 0 with hr | hr
  · simpa [closedBall_eq_empty.mpr hr] using isPathConnected_univ
  have hIoi : IsPathConnected (Ioi r) := (convex_Ioi r).isPathConnected nonempty_Ioi
  convert ((isPathConnected_sphere h 0 zero_le_one).prod hIoi).image
    (f := fun p : E × ℝ => x + p.2 • p.1) (by fun_prop)
  ext w
  simp only [mem_compl_iff, mem_closedBall, dist_eq_norm, not_le, mem_image, mem_prod,
    mem_sphere_zero_iff_norm, mem_Ioi, Prod.exists]
  refine ⟨fun hw => ?_, ?_⟩
  · have hw' : w - x ≠ 0 := norm_pos_iff.mp (hr.trans_lt hw)
    exact ⟨‖w - x‖⁻¹ • (w - x), ‖w - x‖, ⟨by simp [norm_smul, hw'], hw⟩,
      by simp [smul_smul, hw']⟩
  · rintro ⟨u, t, ⟨hu, ht⟩, rfl⟩
    simpa [norm_smul, hu, abs_of_nonneg (hr.trans ht.le)] using ht

/-- The open exterior `{x : E | R < ‖x‖}` of the closed ball of radius `R` about `0`, packaged as
an element of `TopologicalSpace.Opens E`. -/
def exteriorBall (E : Type*) [SeminormedAddCommGroup E] (R : ℝ) : Opens E :=
  ⟨(closedBall 0 R)ᶜ, isClosed_closedBall.isOpen_compl⟩

/-- As a set, `exteriorBall E R` is the complement of the closed ball `closedBall 0 R`. -/
theorem coe_exteriorBall_eq_compl_closedBall {E : Type*} [SeminormedAddCommGroup E] (R : ℝ) :
    (exteriorBall E R : Set E) = (closedBall 0 R)ᶜ :=
  (rfl)

/-- The complement of `exteriorBall E R` is the closed ball `closedBall 0 R`. -/
@[simp]
theorem compl_exteriorBall {E : Type*} [SeminormedAddCommGroup E] (R : ℝ) :
    (exteriorBall E R : Set E)ᶜ = closedBall 0 R :=
  compl_compl _

/-- Membership in `exteriorBall E R` is equivalent to `R < ‖x‖`. -/
@[simp]
theorem mem_exteriorBall {E : Type*} [SeminormedAddCommGroup E] {R : ℝ} {x : E} :
    x ∈ exteriorBall E R ↔ R < ‖x‖ := by
  change x ∈ (closedBall (0 : E) R)ᶜ ↔ R < ‖x‖
  simp

/-- As a set, `exteriorBall E R` is `{x : E | R < ‖x‖}`. -/
theorem coe_exteriorBall {E : Type*} [SeminormedAddCommGroup E] (R : ℝ) :
    (exteriorBall E R : Set E) = {x : E | R < ‖x‖} := by
  ext x
  exact mem_exteriorBall

/-- Increasing the excised radius shrinks the exterior ball. -/
theorem exteriorBall_anti {E : Type*} [SeminormedAddCommGroup E] {R₁ R₂ : ℝ} (h : R₁ ≤ R₂) :
    exteriorBall E R₂ ≤ exteriorBall E R₁ := fun _ hx ↦
  mem_exteriorBall.2 (lt_of_le_of_lt h (mem_exteriorBall.1 hx))

/-- In a nontrivial real normed space, `exteriorBall E R` is nonempty for every `R : ℝ`. -/
theorem nonempty_exteriorBall (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
    (R : ℝ) : (exteriorBall E R : Set E).Nonempty :=
  (NormedSpace.exists_lt_norm ℝ E R).imp fun _ ↦ mem_exteriorBall.2

/-- In a real normed space of dimension at least two, `exteriorBall E R` is path-connected for
every `R : ℝ`. -/
theorem isPathConnected_exteriorBall (h : 1 < Module.rank ℝ E) (R : ℝ) :
    IsPathConnected (exteriorBall E R : Set E) :=
  isPathConnected_compl_closedBall h 0 R

/-- In a real normed space of dimension at least two, `exteriorBall E R` is connected for every
`R : ℝ`. -/
theorem isConnected_exteriorBall (h : 1 < Module.rank ℝ E) (R : ℝ) :
    IsConnected (exteriorBall E R : Set E) :=
  (isPathConnected_exteriorBall h R).isConnected

end TauCeti
