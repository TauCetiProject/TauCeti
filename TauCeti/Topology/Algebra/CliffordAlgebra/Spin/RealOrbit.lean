/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Orbit
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Basic

/-!
# Continuous orbits of compact real Spin groups

For `n ≥ 2` and a chosen basepoint on the unit level, the compact real Spin action gives a
continuous surjection onto that level. This is the sphere-orbit input for proving connectivity of
`Spin(n)`.

The interfaces follow Lawson–Michelsohn, *Spin Geometry* (1989), Chapter I, §2, and use TauCeti's
continuous Spin projection and transitive-action APIs.
-/

public section

namespace CliffordAlgebra

open TauCeti

noncomputable section

/-- The orbit map of the compact real Spin group through a point of its unit level set. -/
noncomputable def realCliffordSpinOrbitMap (n : ℕ) (x : realCliffordUnitLevel n) :
    C(realCliffordSpinGroupZero n, realCliffordUnitLevel n) where
  toFun s := s • x
  continuous_toFun := by
    apply Continuous.subtype_mk ?_ _
    simpa only [SubMulAction.val_smul, realCliffordSpinGroupZero_smul_apply] using
      continuous_spinVectorAction_apply (realCliffordForm n 0) x

/-- The orbit map evaluates to the bundled unit-level Spin translate. -/
@[simp]
theorem realCliffordSpinOrbitMap_apply (n : ℕ) (x : realCliffordUnitLevel n)
    (s : realCliffordSpinGroupZero n) :
    realCliffordSpinOrbitMap n x s = s • x := by
  rfl

/-- The underlying-vector computation of the orbit map. -/
theorem coe_realCliffordSpinOrbitMap_apply (n : ℕ) (x : realCliffordUnitLevel n)
    (s : realCliffordSpinGroupZero n) :
    (realCliffordSpinOrbitMap n x s : Fin n → ℝ) =
      spinVectorAction (realCliffordForm n 0) s x := by
  simp only [realCliffordSpinOrbitMap, ContinuousMap.coe_mk, SubMulAction.val_smul,
    realCliffordSpinGroupZero_smul_apply]

/-- The compact real Spin orbit map is onto the unit level set in dimension at least two. -/
theorem realCliffordSpinOrbitMap_surjective (n : ℕ) (hn : 2 ≤ n)
    (x : realCliffordUnitLevel n) : Function.Surjective (realCliffordSpinOrbitMap n x) := by
  have h := @MulAction.surjective_smul _ _ _
    (realCliffordUnitLevel_isPretransitive n hn) x
  simpa only [realCliffordSpinOrbitMap, ContinuousMap.coe_mk] using h

end

end CliffordAlgebra
