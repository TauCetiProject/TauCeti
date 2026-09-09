/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Quotient
public import TauCeti.GroupTheory.GroupAction.Transitive

/-!
# Topological orbit-stabilizer for transitive actions

For a continuous transitive action on a Hausdorff space `X`, if the quotient by the stabilizer is
compact, then the orbit-stabilizer equivalence is a homeomorphism

`G ⧸ MulAction.stabilizer G b ≃ₜ X`.

Continuity descends from the orbit map `g ↦ g • b` through the quotient topology. The quotient
is compact, so its continuous bijection with the Hausdorff space `X` has continuous inverse.

## Main results

* `TauCeti.continuous_quotientStabilizerEquiv` proves continuity of the algebraic
  orbit-stabilizer equivalence.
* `TauCeti.quotientStabilizerHomeomorph` is its canonical topological upgrade for compact quotient
  and Hausdorff `X`.
* `TauCeti.quotientStabilizerHomeomorph_mk` and
  `TauCeti.quotientStabilizerHomeomorph_smul` record its representative and equivariance laws.
-/

public section

open MulAction

namespace TauCeti

variable (G : Type*) {X : Type*} [Group G] [TopologicalSpace G] [TopologicalSpace X]
  [MulAction G X] [ContinuousSMul G X] [IsPretransitive G X]

/-- The canonical orbit-stabilizer equivalence is continuous for a continuous transitive group
action. -/
@[fun_prop]
theorem continuous_quotientStabilizerEquiv (b : X) :
    Continuous (quotientStabilizerEquiv G b) := by
  apply (QuotientGroup.isQuotientMap_mk (stabilizer G b)).continuous_iff.mpr
  convert continuous_id.smul (continuous_const : Continuous fun _ : G => b) using 1
  funext g
  exact quotientStabilizerEquiv_mk G b g

/-- For a continuous transitive action on a Hausdorff space, a compact quotient by the stabilizer
of a point is canonically homeomorphic to the space. -/
noncomputable def quotientStabilizerHomeomorph (b : X)
    [CompactSpace (G ⧸ (stabilizer G b))] [T2Space X] :
    G ⧸ (stabilizer G b) ≃ₜ X :=
  (continuous_quotientStabilizerEquiv G b).homeoOfEquivCompactToT2

/-- The quotient-stabilizer homeomorphism sends the coset of `g` to `g • b`. -/
@[simp]
theorem quotientStabilizerHomeomorph_mk (b : X)
    [CompactSpace (G ⧸ (stabilizer G b))] [T2Space X] (g : G) :
    quotientStabilizerHomeomorph G b (QuotientGroup.mk g) = g • b :=
  quotientStabilizerEquiv_mk G b g

/-- The quotient-stabilizer homeomorphism is equivariant for the canonical left actions. -/
@[simp]
theorem quotientStabilizerHomeomorph_smul (b : X)
    [CompactSpace (G ⧸ (stabilizer G b))] [T2Space X]
    (g : G) (q : G ⧸ (stabilizer G b)) :
    quotientStabilizerHomeomorph G b (g • q) =
      g • quotientStabilizerHomeomorph G b q :=
  quotientStabilizerEquiv_smul G b g q

end TauCeti
