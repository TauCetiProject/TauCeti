/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.OpenPartialHomeomorph.Continuity

/-!
# Conjugating a monoid action by an open partial homeomorphism

Let a monoid `G` act on a space `X` and let `χ : X → E` be an open partial homeomorphism, for
instance a chart. In the coordinates of `χ`, an element `g` acts by the conjugated map
`χ ∘ (g • ·) ∘ χ.symm`. This file records that, near a point, conjugation is compatible with
the monoid structure: the identity acts as the identity
(`OpenPartialHomeomorph.conj_one_smul_eventuallyEq`), and a product acts as the composite of the
conjugates (`OpenPartialHomeomorph.conj_mul_smul_eventuallyEq`). These are the local identities
behind the chain-rule computation of the derivative representation at a fixed point.
-/

public section

open Filter
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

end OpenPartialHomeomorph
