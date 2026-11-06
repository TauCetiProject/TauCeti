/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Orientation.Cover

/-!
# The tautological orientation over an orientation cover

Pulling a real vector bundle back to its orientation cover gives a canonically oriented
bundle: over `(b, o)`, use the orientation `o`. Its local constancy is precisely the open-sheet
condition in the topology of the orientation cover. No orientation of the original bundle is
required. This supplies, in particular, the orientation of the tautological bundle on finite
oriented Grassmannians.

## References

* J. Milnor and J. Stasheff, *Characteristic Classes*, §9.
-/

public section

open Bundle Filter
open scoped Topology

namespace TauCeti.VectorBundleOrientationCover

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E] {ι : Type*}

/-- Pulling a vector bundle back to its orientation cover canonically orients it, by using
the orientation recorded at each point of the cover. -/
def tautologicalOrientation :
    VectorBundleOrientation F
      ((projection : VectorBundleOrientationCover F E ι → B) *ᵖ E) ι where
  toFun p := p.orientation
  eventually_mapOrientation_eq' p := by
    let e := trivializationAt F E p.proj
    have hp : p.proj ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' p.proj
    have hs : p ∈ sheet e (e.mapOrientation ι hp p.orientation) :=
      mem_sheet_iff.2 ⟨hp, rfl⟩
    filter_upwards [(isOpen_sheet_trivializationAt p.proj
      (e.mapOrientation ι hp p.orientation)).mem_nhds hs] with q hq hq'
    -- The preferred pullback chart is the pullback of the preferred original chart.
    -- `erw` identifies the inherited module instances on the pullback fibre type synonym.
    erw [Trivialization.mapOrientation_pullback, Trivialization.mapOrientation_pullback]
    exact (mem_sheet_iff.1 hq).choose_spec

-- Keep this for explicit rewriting: simplifying the bundled projection's coercion changes
-- the implicit pullback bundle in the left-hand side, so this is not in simp normal form.
/-- The tautological orientation is the orientation recorded by the point of the cover. -/
theorem tautologicalOrientation_apply (p : VectorBundleOrientationCover F E ι) :
    tautologicalOrientation p = p.orientation :=
  (rfl)

end TauCeti.VectorBundleOrientationCover
