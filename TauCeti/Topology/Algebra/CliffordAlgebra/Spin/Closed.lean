/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Compact

/-!
# Closed compact real Spin carrier

The compactness instance for the real Clifford Spin group gives closedness after mapping its carrier
into the Clifford algebra and pulling that closed set back along the units valuation. This is the
ambient closedness statement needed when the Spin group is treated as a closed subgroup of the
Clifford-algebra units.

This carrier is used to view the compact real Spin group as a closed subgroup of the
Clifford-algebra units. The corresponding special-orthogonal carrier is provided separately in
`RealSpecialOrthogonal.lean`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, Section 2.

## Main results

* `TauCeti.CliffordAlgebra.isClosed_range_realCliffordSpinGroupZero_toUnits`: the compact real Spin
  carrier is closed in the Clifford-algebra units.
-/

public section

open Set

namespace TauCeti

namespace CliffordAlgebra

open _root_.CliffordAlgebra

noncomputable section

/-- The compact real Spin carrier is closed in the units of its Clifford algebra. -/
theorem isClosed_range_realCliffordSpinGroupZero_toUnits (n : ℕ) :
    IsClosed (Set.range (spinGroup.toUnits (Q := realCliffordForm n 0))) := by
  let A := CliffordAlgebra (realCliffordForm n 0)
  have hc : IsCompact (Set.univ : Set (realCliffordSpinGroupZero n)) := isCompact_univ
  have himage : IsClosed ((fun x : realCliffordSpinGroupZero n => (x : A)) '' Set.univ) :=
    (hc.image (continuous_subtype_val :
      Continuous ((↑) : realCliffordSpinGroupZero n → A))).isClosed
  have hsu : (fun x : realCliffordSpinGroupZero n => (x : A)) '' Set.univ =
      (realCliffordSpinGroupZero n : Set A) := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, Set.mem_univ _, rfl⟩
  have hs : IsClosed (realCliffordSpinGroupZero n : Set A) := by
    rw [← hsu]
    exact himage
  let f : Aˣ → A := fun u => u
  have hu : IsClosed (f ⁻¹' (realCliffordSpinGroupZero n : Set A)) := by
    simpa only [f] using hs.preimage Units.continuous_val
  have hcoe (x : realCliffordSpinGroupZero n) :
      ((spinGroup.toUnits (Q := realCliffordForm n 0) x : Aˣ) : A) = (x : A) := by
    rfl
  have hset : Set.range (spinGroup.toUnits (Q := realCliffordForm n 0)) =
      f ⁻¹' (realCliffordSpinGroupZero n : Set A) := by
    ext u
    constructor
    · rintro ⟨x, rfl⟩
      change ((spinGroup.toUnits (Q := realCliffordForm n 0) x : Aˣ) : A) ∈
        (realCliffordSpinGroupZero n : Set A)
      rw [hcoe x]
      exact x.2
    · intro hu'
      refine ⟨⟨u, hu'⟩, ?_⟩
      apply Units.ext
      exact hcoe ⟨u, hu'⟩
  rw [hset]
  exact hu

end

end CliffordAlgebra

end TauCeti

end
