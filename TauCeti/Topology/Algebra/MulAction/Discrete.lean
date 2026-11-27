/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.MulAction

/-!
# Scalar actions on discrete spaces

Any scalar action of a discrete space on a discrete space is jointly continuous. This supplies
the continuity hypothesis for discrete coefficient modules without requiring algebraic laws
on the scalar action.

A continuous action on a discrete space also restricts along an injective equivariant map: an
injective map out of a discrete space into a discrete space is inducing. This gives the
continuity of an action on a ring with the discrete topology from its continuity on a discrete
field containing it, such as a fraction field.

## Main results

* `TauCeti.continuousSMul_of_discreteTopology`: scalar actions between discrete spaces are
  continuous.
* `Function.Injective.continuousSMul_of_discreteTopology`: a continuous action on a discrete
  space is continuous on a discrete space mapping injectively and equivariantly into it, and
  `Function.Injective.elim_continuousSMul_discreteTopology` applies results about such discrete
  spaces without putting a topology on the source.
-/

public section

namespace TauCeti

/-- A scalar action between discrete spaces is jointly continuous, since the product of the
scalar space and the acted-on space is discrete. -/
instance (priority := 100) continuousSMul_of_discreteTopology {R M : Type*} [TopologicalSpace R]
    [TopologicalSpace M] [DiscreteTopology R] [DiscreteTopology M] [SMul R M] :
    ContinuousSMul R M :=
  ⟨continuous_of_discreteTopology⟩

end TauCeti

section Injective

variable {G B L : Type*} [SMul G B] [SMul G L] [TopologicalSpace G] [TopologicalSpace L]
  [DiscreteTopology L] [ContinuousSMul G L] {f : B → L}

open Topology in
/-- If `G` acts continuously on a space `L` with the discrete topology, and `f : B → L` is
injective and equivariant, then the action of `G` on `B` is continuous for the discrete topology
on `B`. -/
theorem Function.Injective.continuousSMul_of_discreteTopology [TopologicalSpace B]
    [DiscreteTopology B] (hf : Function.Injective f)
    (hsmul : ∀ (g : G) (b : B), f (g • b) = g • f b) : ContinuousSMul G B :=
  IsInducing.continuousSMul (f := id)
    (isInducing_iff_nhds.mpr fun b ↦ by
      simp [nhds_discrete, Filter.comap_pure, ← Set.image_singleton, hf.preimage_image])
    continuous_id (hsmul _ _)

/-- A statement proved for a continuous action of `G` on `B` with the discrete topology holds as
soon as `B` maps injectively and equivariantly into a space `L` with the discrete topology on which
the action is continuous. This applies results stated for discrete rings, such as Mathlib's
`Algebra.IsInvariant.isIntegral_of_profinite`, to a ring through its fraction field, without
putting a topology on the ring. -/
theorem Function.Injective.elim_continuousSMul_discreteTopology (hf : Function.Injective f)
    (hsmul : ∀ (g : G) (b : B), f (g • b) = g • f b) {p : Prop}
    (h : ∀ [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul G B], p) : p := by
  let _ : TopologicalSpace B := ⊥
  have : DiscreteTopology B := ⟨rfl⟩
  have := hf.continuousSMul_of_discreteTopology hsmul
  exact h

end Injective
