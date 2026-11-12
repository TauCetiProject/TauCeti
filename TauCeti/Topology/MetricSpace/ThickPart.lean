/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.IsometricSMul

/-!
# The thick part of a group action on a metric space

For a group `G` acting on a metric space `X` and a real number `ε`, the `ε`-thick part
`TauCeti.thickPart G ε` is the set of points moved a distance at least `ε` by every nonidentity
element of `G`. Its complement, the thin part, consists of the points moved less than `ε` by some
nonidentity element. For a discrete group of isometries of a hyperbolic manifold this is the
thick-thin decomposition, whose thick part has compact image in the quotient when the quotient
has finite volume.

## Main declarations

* `TauCeti.thickPart G ε`: the points moved at least `ε` by every nonidentity element.
* `TauCeti.isClosed_thickPart`: the thick part of an action by continuous maps is closed.
* `TauCeti.smul_mem_thickPart_iff`: the thick part of an isometric action is invariant.

## References

* Riccardo Benedetti and Carlo Petronio, *Lectures on Hyperbolic Geometry*, Universitext,
  Springer, 1992, Chapter D (the thick-thin decomposition).
-/

public section

open Set

namespace TauCeti

variable (G : Type*) {X : Type*} [Group G] [PseudoMetricSpace X] [MulAction G X]

/-- The **`ε`-thick part** of an action on a metric space: the points moved a distance at least
`ε` by every nonidentity element. For `0 < ε` it excludes every point with nontrivial
stabilizer. -/
def thickPart (ε : ℝ) : Set X :=
  {x | ∀ g : G, g ≠ 1 → ε ≤ dist (g • x) x}

variable {G}

/-- Membership in the thick part, unfolded. -/
@[simp]
theorem mem_thickPart {ε : ℝ} {x : X} :
    x ∈ thickPart G ε ↔ ∀ g : G, g ≠ 1 → ε ≤ dist (g • x) x :=
  Iff.rfl

variable (G) in
/-- The thick part of an action by continuous maps is closed. -/
theorem isClosed_thickPart [ContinuousConstSMul G X] (ε : ℝ) :
    IsClosed (thickPart G ε : Set X) := by
  simp_rw [thickPart, ofPred_forall]
  exact isClosed_iInter fun g ↦ isClosed_iInter fun _ ↦
    isClosed_le continuous_const ((continuous_const_smul g).dist continuous_id)

variable [IsIsometricSMul G X]

/-- The thick part of an isometric action is invariant. -/
theorem smul_mem_thickPart_iff {ε : ℝ} (g : G) {x : X} :
    g • x ∈ thickPart G ε ↔ x ∈ thickPart G ε := by
  suffices h : ∀ (g : G) {x : X}, x ∈ thickPart G ε → g • x ∈ thickPart G ε from
    ⟨fun hx ↦ by simpa using h g⁻¹ hx, h g⟩
  intro g x hx h hh
  have hconj : g⁻¹ * h * g ≠ 1 := by
    rwa [Ne, mul_assoc, inv_mul_eq_one, eq_comm, mul_eq_right]
  calc ε ≤ dist ((g⁻¹ * h * g) • x) x := hx _ hconj
    _ = dist (g • (g⁻¹ * h * g) • x) (g • x) := (dist_smul g _ _).symm
    _ = dist (h • g • x) (g • x) := by simp [mul_smul]

end TauCeti
