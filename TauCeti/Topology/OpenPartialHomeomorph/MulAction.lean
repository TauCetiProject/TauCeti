/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.OpenPartialHomeomorph.Continuity
public import Mathlib.Topology.OpenPartialHomeomorph.IsImage

/-!
# Conjugating a monoid action by an open partial homeomorphism

Let a monoid `G` act on a space `X` and let `χ : X → E` be an open partial homeomorphism, for
instance a chart. In the coordinates of `χ`, an element `g` acts by the conjugated map
`χ ∘ (g • ·) ∘ χ.symm`. This file records that, near a point, conjugation is compatible with
the monoid structure: the identity acts as the identity
(`OpenPartialHomeomorph.conj_one_smul_eventuallyEq`), and a product acts as the composite of the
conjugates (`OpenPartialHomeomorph.conj_mul_smul_eventuallyEq`). These are the local identities
behind the chain-rule computation of the derivative representation at a fixed point.

`OpenPartialHomeomorph.restrInvariant` restricts a chart to the largest invariant open subset
of its source for a finite monoid action.
-/

public section

open Filter Set
open scoped Topology

namespace OpenPartialHomeomorph

variable {G X E : Type*} [Monoid G] [TopologicalSpace X] [TopologicalSpace E] [MulAction G X]
  (χ : OpenPartialHomeomorph X E)

/-- Near a point of the target of `χ`, the conjugate by `χ` of the action of the identity is the
identity. -/
theorem conj_one_smul_eventuallyEq {z : E} (hz : z ∈ χ.target) :
    χ ∘ ((1 : G) • ·) ∘ χ.symm =ᶠ[𝓝 z] id := by
  filter_upwards [χ.eventually_right_inverse hz] with w hw
  simp [hw]

/-- Let `x` be a point of the source of `χ` such that `h • x` also lies in the source. Near `χ x`,
the conjugate by `χ` of the action of `g * h` is the composite of the conjugates of the actions
of `g` and of `h`. -/
theorem conj_mul_smul_eventuallyEq [ContinuousConstSMul G X] {x : X} (hx : x ∈ χ.source) {h : G}
    (hhx : h • x ∈ χ.source) (g : G) :
    χ ∘ ((g * h) • ·) ∘ χ.symm =ᶠ[𝓝 (χ x)] (χ ∘ (g • ·) ∘ χ.symm) ∘ (χ ∘ (h • ·) ∘ χ.symm) := by
  have hcont : ContinuousAt (fun w => h • χ.symm w) (χ x) :=
    (continuous_const_smul h).continuousAt.comp (χ.continuousAt_symm (χ.map_source hx))
  have hmem : ∀ᶠ w in 𝓝 (χ x), h • χ.symm w ∈ χ.source := by
    refine hcont.preimage_mem_nhds ?_
    rw [χ.left_inv hx]
    exact χ.open_source.mem_nhds hhx
  filter_upwards [hmem] with w hw
  simp [χ.left_inv hw, mul_smul]

section InvariantRestriction

variable {Y : Type*} [TopologicalSpace Y]

/-- Restrict a chart to the largest `G`-invariant open subset of its source. -/
noncomputable def restrInvariant (e : OpenPartialHomeomorph X Y) (G : Type*) [Monoid G] [Finite G]
    [MulAction G X] [ContinuousConstSMul G X] : OpenPartialHomeomorph X Y :=
  e.restrOpen (⋂ g : G, (g • ·) ⁻¹' e.source)
    (isOpen_iInter_of_finite fun g => e.open_source.preimage (continuous_const_smul g))

/-- The invariant restriction is the open restriction to the intersection of all translates. -/
theorem restrInvariant_def [Finite G] [ContinuousConstSMul G X] (e : OpenPartialHomeomorph X Y) :
    e.restrInvariant G = e.restrOpen (⋂ g : G, (g • ·) ⁻¹' e.source)
      (isOpen_iInter_of_finite fun g => e.open_source.preimage (continuous_const_smul g)) := (rfl)

/-- Invariant restriction does not change the forward map. -/
@[simp]
theorem coe_restrInvariant [Finite G] [ContinuousConstSMul G X] (e : OpenPartialHomeomorph X Y) :
    ⇑(e.restrInvariant G) = e := (rfl)

/-- Invariant restriction does not change the inverse map. -/
@[simp]
theorem coe_restrInvariant_symm [Finite G] [ContinuousConstSMul G X]
    (e : OpenPartialHomeomorph X Y) : ⇑(e.restrInvariant G).symm = e.symm := (rfl)

/-- A point belongs to the invariant restriction exactly when its whole orbit is in the source. -/
@[simp]
theorem mem_restrInvariant_source_iff [Finite G] [ContinuousConstSMul G X]
    (e : OpenPartialHomeomorph X Y) {x : X} :
    x ∈ (e.restrInvariant G).source ↔ ∀ g : G, g • x ∈ e.source := by
  simp only [restrInvariant, restrOpen_source, mem_inter_iff, mem_iInter, mem_preimage]
  exact ⟨And.right, fun h => ⟨by simpa using h 1, h⟩⟩

/-- The source of an invariant restriction is invariant. -/
theorem smul_mem_restrInvariant_source [Finite G] [ContinuousConstSMul G X]
    (e : OpenPartialHomeomorph X Y) {x : X}
    (hx : x ∈ (e.restrInvariant G).source) (g : G) : g • x ∈ (e.restrInvariant G).source := by
  rw [mem_restrInvariant_source_iff] at hx ⊢
  intro h
  simpa [mul_smul] using hx (h * g)

end InvariantRestriction

end OpenPartialHomeomorph
