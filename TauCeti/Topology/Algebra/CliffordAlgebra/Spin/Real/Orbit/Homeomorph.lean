/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Real.Orbit.Basic
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Compact
import TauCeti.Topology.Algebra.GroupAction.Transitive

/-!
# The compact Spin sphere as a homogeneous quotient

For `n ≥ 2`, the compact real Spin action on its unit quadratic level is transitive and continuous.
This file packages the resulting quotient by a point stabilizer as a homeomorphism with the unit
level. The characteristic representative and equivariance equations are the interface used by
local-section charts and the subsequent sphere-bundle construction.

The construction is a specialization of `TauCeti.quotientStabilizerHomeomorph`; compactness of the
quotient comes from the compact Spin carrier and Hausdorffness from the subtype topology.
-/

public section

namespace CliffordAlgebra

open TauCeti

noncomputable section

private theorem continuous_realCliffordSpinOrbitMap_action (n : ℕ)
    (x : realCliffordUnitLevel n) :
    Continuous (fun s : realCliffordSpinGroupZero n => s • x) := by
  apply (realCliffordSpinOrbitMap n x).continuous.congr
  intro s
  exact realCliffordSpinOrbitMap_apply n x s

/-- The compact Spin orbit identifies the quotient by a unit-level stabilizer with that level. -/
noncomputable def realCliffordSpinOrbitHomeomorph (n : ℕ) (hn : 2 ≤ n)
    (x : realCliffordUnitLevel n) :
    realCliffordSpinGroupZero n ⧸ MulAction.stabilizer (realCliffordSpinGroupZero n) x ≃ₜ
      realCliffordUnitLevel n := by
  let _ : MulAction.IsPretransitive (realCliffordSpinGroupZero n)
      (realCliffordUnitLevel n) := isPretransitive_realCliffordUnitLevel n hn
  exact TauCeti.quotientStabilizerHomeomorph (realCliffordSpinGroupZero n) x
    (continuous_realCliffordSpinOrbitMap_action n x)

/-- The compact Spin orbit homeomorphism evaluates a representative by the Spin action. -/
@[simp]
theorem realCliffordSpinOrbitHomeomorph_mk (n : ℕ) (hn : 2 ≤ n)
    (x : realCliffordUnitLevel n) (s : realCliffordSpinGroupZero n) :
    realCliffordSpinOrbitHomeomorph n hn x (QuotientGroup.mk s) = s • x := by
  let _ : MulAction.IsPretransitive (realCliffordSpinGroupZero n)
      (realCliffordUnitLevel n) := isPretransitive_realCliffordUnitLevel n hn
  simpa only [realCliffordSpinOrbitHomeomorph] using
    TauCeti.quotientStabilizerHomeomorph_mk (realCliffordSpinGroupZero n) x
      (continuous_realCliffordSpinOrbitMap_action n x) s

/-- The compact Spin orbit homeomorphism is equivariant for left multiplication. -/
theorem realCliffordSpinOrbitHomeomorph_smul (n : ℕ) (hn : 2 ≤ n)
    (x : realCliffordUnitLevel n) (s : realCliffordSpinGroupZero n)
    (q : realCliffordSpinGroupZero n ⧸ MulAction.stabilizer (realCliffordSpinGroupZero n) x) :
    realCliffordSpinOrbitHomeomorph n hn x (s • q) =
      s • realCliffordSpinOrbitHomeomorph n hn x q := by
  let _ : MulAction.IsPretransitive (realCliffordSpinGroupZero n)
      (realCliffordUnitLevel n) := isPretransitive_realCliffordUnitLevel n hn
  simpa only [realCliffordSpinOrbitHomeomorph] using
    TauCeti.quotientStabilizerHomeomorph_smul (realCliffordSpinGroupZero n) x
      (continuous_realCliffordSpinOrbitMap_action n x) s q

end

end CliffordAlgebra
