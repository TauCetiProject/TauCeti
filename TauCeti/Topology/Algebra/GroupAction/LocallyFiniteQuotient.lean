/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.LocallyFinite

/-!
# Orbit spaces modelled on a closed set with locally finite translates

Let a group act by homeomorphisms on a topological space `X`, and let `F ⊆ X` be closed with
locally finite translates `g • F`. The orbit projection restricted to `F` is then a closed map:
the saturation of a closed subset of `F` is the union of its translates, a locally finite union
of closed sets. If moreover the translates cover `X`, the restricted projection is surjective,
hence a quotient map. The orbit space is therefore homeomorphic to `F` with the points of `F` in
a common orbit identified.

This is the topological input for describing the quotient of the upper half-plane by a Fuchsian
group as a fundamental polygon with its sides glued in pairs.

## Main results

* `TauCeti.isClosedMap_quotientMk_domRestrict_of_locallyFinite_smul`: the orbit projection
  restricted to a closed set with locally finite translates is a closed map.
* `TauCeti.isQuotientMap_quotientMk_domRestrict_of_locallyFinite_smul`: if those translates also
  cover the space, it is a quotient map onto the orbit space.

Both results have additive versions on `AddAction.orbitRel.Quotient`.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91, Springer,
  1983, §9.2 (locally finite fundamental domains and the quotient topology).
-/

public section

open Set Topology
open scoped Pointwise

namespace TauCeti

variable {G X : Type*} [Group G] [MulAction G X] [TopologicalSpace X] [ContinuousConstSMul G X]
  {F : Set X}

/-- **The orbit projection is closed on a closed set with locally finite translates.** If the
translates of a closed set `F` form a locally finite family, the orbit projection restricted to
`F` is a closed map. -/
@[to_additive
/-- **The additive orbit projection is closed on a closed set with locally finite translates.**
If the translates of a closed set `F` form a locally finite family, the additive orbit projection
restricted to `F` is a closed map. -/]
theorem isClosedMap_quotientMk_domRestrict_of_locallyFinite_smul (hF : IsClosed F)
    (hlf : LocallyFinite fun g : G ↦ g • F) :
    IsClosedMap (F.domRestrict (Quotient.mk'' : X → MulAction.orbitRel.Quotient G X)) := by
  intro A hA
  have hA' : IsClosed ((↑) '' A : Set X) := hF.isClosedMap_subtype_val A hA
  rw [domRestrict_eq, image_comp, ← isQuotientMap_quotient_mk'.isClosed_preimage]
  -- The saturation of `A` is a locally finite union of closed translates.
  convert (hlf.subset fun g ↦ smul_set_mono (Subtype.coe_image_subset F A)).isClosed_iUnion
    fun g ↦ hA'.smul g using 1
  -- `Quotient.mk'` and `Quotient.mk''` agree, and `g • U` is the image of `U` under `g • ·`.
  exact MulAction.quotient_preimage_image_eq_union_mul (G := G) _

/-- **A closed set with locally finite covering translates models the orbit space.** If the
translates of a closed set `F` cover `X` and form a locally finite family, the orbit projection
restricted to `F` is a quotient map onto the orbit space. -/
@[to_additive
/-- **A closed set with locally finite covering translates models the additive orbit space.** If
the translates of a closed set `F` cover `X` and form a locally finite family, the additive orbit
projection restricted to `F` is a quotient map onto the orbit space. -/]
theorem isQuotientMap_quotientMk_domRestrict_of_locallyFinite_smul (hF : IsClosed F)
    (hcover : ⋃ g : G, g • F = univ) (hlf : LocallyFinite fun g : G ↦ g • F) :
    IsQuotientMap (F.domRestrict (Quotient.mk'' : X → MulAction.orbitRel.Quotient G X)) := by
  refine (isClosedMap_quotientMk_domRestrict_of_locallyFinite_smul hF hlf).isQuotientMap
    (continuous_quot_mk.comp continuous_subtype_val) ?_
  rintro ⟨x⟩
  obtain ⟨g, y, hy, rfl⟩ := mem_iUnion.mp (hcover ▸ mem_univ x)
  exact ⟨⟨y, hy⟩, (Quotient.sound (MulAction.mem_orbit y g)).symm⟩

end TauCeti
