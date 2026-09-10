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

For a transitive action on a Hausdorff space `X`, if the orbit map at `b` is continuous and the
quotient by the stabilizer is compact, then the orbit-stabilizer equivalence is a homeomorphism

`G ⧸ MulAction.stabilizer G b ≃ₜ X`.

Continuity descends from the orbit map `g ↦ g • b` through the quotient topology. The quotient
is compact, so its continuous bijection with the Hausdorff space `X` has continuous inverse.

## Main results

* `TauCeti.continuous_ofQuotientStabilizer` proves continuity of the orbit map descended to the
  stabilizer quotient, without requiring transitivity.
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
  [MulAction G X]

/-- The orbit map descended to the stabilizer quotient is continuous when the orbit map is. -/
@[fun_prop]
theorem continuous_ofQuotientStabilizer (b : X) (hb : Continuous fun g : G => g • b) :
    Continuous (ofQuotientStabilizer G b) := by
  apply (QuotientGroup.isQuotientMap_mk (stabilizer G b)).continuous_iff.mpr
  convert hb using 1
  funext g
  exact ofQuotientStabilizer_mk G b g

variable [IsPretransitive G X]

/-- The canonical orbit-stabilizer equivalence is continuous when its orbit map is continuous. -/
@[fun_prop]
theorem continuous_quotientStabilizerEquiv (b : X) (hb : Continuous fun g : G => g • b) :
    Continuous (quotientStabilizerEquiv G b) := by
  refine (continuous_ofQuotientStabilizer G b hb).congr fun q => ?_
  induction q using QuotientGroup.induction_on with
  | _ g => rw [ofQuotientStabilizer_mk, quotientStabilizerEquiv_mk]

/-- For a transitive action on a Hausdorff space, if the orbit map at a point is continuous and its
stabilizer quotient is compact, then that quotient is canonically homeomorphic to the space. -/
noncomputable def quotientStabilizerHomeomorph (b : X)
    (hb : Continuous fun g : G => g • b)
    [CompactSpace (G ⧸ (stabilizer G b))] [T2Space X] :
    G ⧸ (stabilizer G b) ≃ₜ X :=
  (continuous_quotientStabilizerEquiv G b hb).homeoOfEquivCompactToT2

/-- The quotient-stabilizer homeomorphism sends the coset of `g` to `g • b`. -/
@[simp]
theorem quotientStabilizerHomeomorph_mk (b : X)
    (hb : Continuous fun g : G => g • b)
    [CompactSpace (G ⧸ (stabilizer G b))] [T2Space X] (g : G) :
    quotientStabilizerHomeomorph G b hb (QuotientGroup.mk g) = g • b := by
  simp only [quotientStabilizerHomeomorph, ← Homeomorph.coe_toEquiv,
    Continuous.toEquiv_homeoOfEquivCompactToT2, quotientStabilizerEquiv_mk]

/-- The quotient-stabilizer homeomorphism is equivariant for the canonical left actions. -/
@[simp]
theorem quotientStabilizerHomeomorph_smul (b : X)
    (hb : Continuous fun g : G => g • b)
    [CompactSpace (G ⧸ (stabilizer G b))] [T2Space X]
    (g : G) (q : G ⧸ (stabilizer G b)) :
    quotientStabilizerHomeomorph G b hb (g • q) =
      g • quotientStabilizerHomeomorph G b hb q := by
  simp only [quotientStabilizerHomeomorph, ← Homeomorph.coe_toEquiv,
    Continuous.toEquiv_homeoOfEquivCompactToT2, quotientStabilizerEquiv_smul]

end TauCeti
