/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.QuadraticForm.Brauer
public import TauCeti.NumberTheory.LocalField.Quaternion.Invariant

/-!
# The Hasse invariant in the local Brauer group

`TauCeti.RegularFormClass.invMap_hasseInvariant_eq_toRatAddCircle_localHasse` computes the local
Brauer invariant of a form's Brauer-valued Hasse invariant from its classical Hasse sign.
It combines `TauCeti.RegularFormClass.quaternionSubgroupSignEquiv_apply_hasseInvariant` with
`TauCeti.BrauerGroup.invMap_brauerGroupEquivBr_eq_toRatAddCircle_sign`.
-/

public section

namespace TauCeti.RegularFormClass

open ClassFieldTheory

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Invertible (2 : K)]

/-- For a regular quadratic form over a nonarchimedean local field with two invertible,
the local Brauer invariant of its Hasse class is `0` or `1/2` in `ℚ/ℤ` according as its
classical Hasse sign is `1` or `-1` (Serre, *A Course in Arithmetic*, Chapter IV, §2,
and *Local Fields*, Chapter XIV, §2). -/
theorem invMap_hasseInvariant_eq_toRatAddCircle_localHasse (q : RegularFormClass K) :
    invMap K (brauerGroupEquivBr K (Additive.ofMul q.hasseInvariant)) =
      ZMod.toRatAddCircle 2 (additiveIntUnitsAddEquiv (Additive.ofMul q.localHasse)) := by
  simpa only [quaternionSubgroupSignEquiv_apply_hasseInvariant] using
    BrauerGroup.invMap_brauerGroupEquivBr_eq_toRatAddCircle_sign
      ⟨q.hasseInvariant, q.hasseInvariant_mem_quaternionSubgroup⟩

end TauCeti.RegularFormClass
