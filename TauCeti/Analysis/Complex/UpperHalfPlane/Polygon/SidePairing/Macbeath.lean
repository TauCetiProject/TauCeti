/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.Neighbours
public import TauCeti.Topology.Algebra.GroupAction.Macbeath.LocallyFinite
import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex.Sides
import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.Tessellation
import TauCeti.Topology.MetricSpace.IsometricSMul

/-!
# Macbeath's presentation of the group of a side-paired polygon

Let `σ` be a side pairing of a convex hyperbolic polygon `P`, and let `Γ ≤ PSL(2, ℝ)` contain the
side-pairing maps, with locally finite translates `γ • P`. These translates cover the upper
half-plane, which is simply connected, and the polygon is closed and path-connected. Macbeath's
theorem for a tile therefore presents `Γ` by the polygon itself: the generators are the elements
`γ` whose translate `γ • P` meets `P`, and the relations are `s * t = u` whenever `P`, `s • P`
and `u • P` have a common point with `u = s * t`. No angle or cycle condition is used.

When moreover distinct translates of the interior of `P` are disjoint, the generators are
exactly the identity, the side-pairing maps, and the inverse partial cycle products at the finite
vertices, and three distinct generating tiles can only meet at a finite vertex, by
`ConvexPolygon.SidePairing.exists_vertex_of_mem_carrier_of_mem_two_smul_carrier`. Reading these
generators as words in the side-pairing maps, and these relations as consequences of the side
and vertex cycle relations, is how Poincaré's polygon theorem obtains the presentation of `Γ`
from the polygon.

## Main results

* `ConvexPolygon.SidePairing.macbeathHom_bijective`: `Γ` is presented by the Macbeath generators
  and relations of the polygon.
* `ConvexPolygon.SidePairing.ker_lift_eq_normalClosure_macbeathRels`: the same statement as an
  equality of subgroups of the free group on the generators.

## References

* A. M. Macbeath, *Groups of homeomorphisms of a simply connected space*, Ann. of Math. (2) 79
  (1964), 473–488.
* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91,
  Springer, 1983, Chapter 9.
-/

public section

open Set UpperHalfPlane
open scoped MatrixGroups Pointwise

namespace TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing

variable {n : ℕ} [NeZero n] {P : ConvexPolygon n} (σ : P.SidePairing) {Γ : Subgroup PSL(2, ℝ)}

/-- The hypotheses of Macbeath's theorem for the polygon: its translates by `Γ` are locally
finite and cover the upper half-plane. -/
private theorem locallyFinite_and_iUnion_eq_univ (hmap : ∀ i, σ.map i ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier) :
    (LocallyFinite fun γ : Γ ↦ γ • P.carrier) ∧ ⋃ γ : Γ, γ • P.carrier = univ := by
  simp only [Set.subtype_smul_set]
  exact ⟨hlf, σ.iUnion_smul_carrier_eq_univ hmap hlf⟩

/-- **Macbeath's presentation of the group of a polygon.** If a subgroup `Γ` contains the
side-pairing maps and its translates of the polygon are locally finite, then `Γ` is presented by
the elements `γ` with `γ • P` meeting `P`, subject to the relations `s * t = u` for every
common point of `P`, `s • P` and `u • P` with `u = s * t`. -/
theorem macbeathHom_bijective (hmap : ∀ i, σ.map i ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier) :
    Function.Bijective (macbeathHom Γ P.carrier) := by
  obtain ⟨hlf', hcover⟩ := σ.locallyFinite_and_iUnion_eq_univ hmap hlf
  exact ⟨macbeathHom_injective_of_locallyFinite P.isClosed_carrier P.isPathConnected_carrier
      hlf' hcover,
    macbeathHom_surjective_of_locallyFinite P.isClosed_carrier hlf' hcover⟩

/-- **Macbeath's presentation of the group of a polygon**, as a description of the relations:
the words in the Macbeath generators of the polygon that evaluate to the identity in `Γ` form the
normal closure of the Macbeath relations. -/
theorem ker_lift_eq_normalClosure_macbeathRels (hmap : ∀ i, σ.map i ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier) :
    (FreeGroup.lift (Subtype.val : macbeathGenerators Γ P.carrier → Γ)).ker =
      Subgroup.normalClosure (macbeathRels Γ P.carrier) := by
  obtain ⟨hlf', hcover⟩ := σ.locallyFinite_and_iUnion_eq_univ hmap hlf
  exact ker_lift_eq_normalClosure_macbeathRels_of_locallyFinite P.isClosed_carrier
    P.isPathConnected_carrier hlf' hcover

end TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing
