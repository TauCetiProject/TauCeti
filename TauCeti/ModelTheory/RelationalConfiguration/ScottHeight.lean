/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.BackAndForth
public import TauCeti.ModelTheory.Scott.Height

/-!
# Isomorphism of configurations at the Scott height

On a countable carrier, back-and-forth equivalence at the Scott height of a configuration's
decoded structure decides isomorphism with it. So on a set of configurations whose Scott heights
are at most `β`, isomorphism is back-and-forth equivalence at level `β`. No measurability or
countability of the language is involved.

## Main results

* `TauCeti.RelationalConfiguration.isoSetoid_iff_bfEquivSetoid_of_scottHeight_le`: if `c` has
  Scott height at most `β`, then `d` is isomorphic to `c` exactly when it is equivalent to `c` at
  level `β`.
* `TauCeti.RelationalConfiguration.comap_isoSetoid_eq_bfEquivSetoid_of_scottHeight_le`: on a set
  of Scott height at most `β`, isomorphism is back-and-forth equivalence at level `β`.
* `TauCeti.RelationalConfiguration.iso_inter_eq_bfEquivSetoid_inter_of_scottHeight_le`: the same
  for the pairs of such a set, in the ambient square.
-/

public section

universe u v w

open FirstOrder FirstOrder.Language

namespace TauCeti.RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w} [Countable V]

/-- If the structure decoded from `c` has Scott height at most `β`, then a configuration is
isomorphic to `c` exactly when it is back-and-forth equivalent to `c` at level `β`. -/
theorem isoSetoid_iff_bfEquivSetoid_of_scottHeight_le {β : Ordinal.{w}}
    {c d : RelationalConfiguration L V} (h : @scottHeight L _ V c.toStructure ≤ β) :
    isoSetoid L V c d ↔ bfEquivSetoid L V β c d :=
  ⟨fun hcd => isoSetoid_le_bfEquivSetoid β hcd, fun hcd => isoSetoid_apply.2
    (@nonempty_equiv_of_bfEquiv_of_scottHeight_le L _ V c.toStructure _ V d.toStructure _ β h
      (bfEquivSetoid_apply.1 hcd))⟩

/-- On a set of configurations whose decoded structures have Scott height at most `β`,
isomorphism is back-and-forth equivalence at level `β`. No measurability of the set is needed. -/
theorem comap_isoSetoid_eq_bfEquivSetoid_of_scottHeight_le
    {K : Set (RelationalConfiguration L V)} {β : Ordinal.{w}}
    (hK : ∀ c ∈ K, @scottHeight L _ V c.toStructure ≤ β) :
    (isoSetoid L V).comap (Subtype.val : K → _) =
      (bfEquivSetoid L V β).comap (Subtype.val : K → _) := by
  ext c d
  exact isoSetoid_iff_bfEquivSetoid_of_scottHeight_le (hK c c.property)

/-- On a set `K` of configurations whose decoded structures have Scott height at most `β`, the
isomorphic pairs of `K` are the pairs of `K` that are back-and-forth equivalent at level `β`. -/
theorem iso_inter_eq_bfEquivSetoid_inter_of_scottHeight_le
    {K : Set (RelationalConfiguration L V)} {β : Ordinal.{w}}
    (hK : ∀ c ∈ K, @scottHeight L _ V c.toStructure ≤ β) :
    {p : RelationalConfiguration L V × RelationalConfiguration L V | isoSetoid L V p.1 p.2} ∩
        K ×ˢ K =
      {p | bfEquivSetoid L V β p.1 p.2} ∩ K ×ˢ K := by
  ext p
  exact and_congr_left fun hp => isoSetoid_iff_bfEquivSetoid_of_scottHeight_le (hK _ hp.1)

end TauCeti.RelationalConfiguration
