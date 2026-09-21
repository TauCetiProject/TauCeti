/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Real.Orbit.Homeomorph

/-!
# The compact Spin orbit map as a quotient map

The orbit map onto the compact real Spin unit level is the composition of the
stabilizer quotient projection with the orbit-stabilizer homeomorphism.  This
quotient-map form is the topological boundary used when descending the local
sphere-bundle data through the stabilizer quotient.
-/

public section

namespace CliffordAlgebra

open TauCeti

noncomputable section

/-- The compact real Spin orbit map induces the stabilizer quotient topology. -/
theorem isQuotientMap_realCliffordSpinOrbitMap (n : ℕ) (hn : 2 ≤ n)
    (x : realCliffordUnitLevel n) :
    Topology.IsQuotientMap (realCliffordSpinOrbitMap n x) := by
  let _ : MulAction.IsPretransitive (realCliffordSpinGroupZero n)
      (realCliffordUnitLevel n) := isPretransitive_realCliffordUnitLevel n hn
  let h := realCliffordSpinOrbitHomeomorph n hn x
  have hcomp :
      (h : _ → _) ∘ QuotientGroup.mk = realCliffordSpinOrbitMap n x := by
    funext s
    rw [realCliffordSpinOrbitMap_apply]
    exact realCliffordSpinOrbitHomeomorph_mk n hn x s
  rw [← hcomp]
  exact h.isQuotientMap.comp (QuotientGroup.isQuotientMap_mk _)

end

end CliffordAlgebra
