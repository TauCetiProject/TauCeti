/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Quotient
public import TauCeti.Topology.Algebra.Module.Quotient.ConstSMul

/-!
# Continuous descent through Lie ideal quotients

A continuous Lie homomorphism killing an ideal descends continuously to its quotient,
with the topology of the underlying submodule quotient. No continuity of the Lie bracket
or scalar action is required.
-/

public section

namespace TauCeti

/-- The topology of a Lie ideal quotient is the topology of its submodule quotient. -/
instance instTopologicalSpaceLieIdealQuotient {R L : Type*} [CommRing R] [LieRing L]
    [LieAlgebra R L] [TopologicalSpace L] (I : LieIdeal R L) :
    TopologicalSpace (L ⧸ I) :=
  inferInstanceAs (TopologicalSpace (L ⧸ I.toSubmodule))

instance instIsTopologicalAddGroupLieIdealQuotient {R L : Type*} [CommRing R] [LieRing L]
    [LieAlgebra R L] [TopologicalSpace L] [IsTopologicalAddGroup L] (I : LieIdeal R L) :
    IsTopologicalAddGroup (L ⧸ I) :=
  inferInstanceAs (IsTopologicalAddGroup (L ⧸ I.toSubmodule))

instance instContinuousConstSMulLieIdealQuotient {R L : Type*} [CommRing R] [LieRing L]
    [LieAlgebra R L] [TopologicalSpace L] [ContinuousConstSMul R L] (I : LieIdeal R L) :
    ContinuousConstSMul R (L ⧸ I) :=
  inferInstanceAs (ContinuousConstSMul R (L ⧸ I.toSubmodule))

/-- Descent through a Lie ideal quotient preserves continuity. -/
@[fun_prop]
theorem continuous_lieIdeal_liftQ {R L L' : Type*} [CommRing R] [LieRing L]
    [LieAlgebra R L] [LieRing L'] [LieAlgebra R L'] [TopologicalSpace L]
    [TopologicalSpace L'] (I : LieIdeal R L) (f : L →ₗ⁅R⁆ L') (h : I ≤ f.ker)
    (hcont : Continuous f) : Continuous (I.liftQ f h) :=
  I.toSubmodule.isQuotientMap_mkQ.continuous_iff.2 <| by
    simpa only [Function.comp_def, Submodule.mkQ_apply, LieIdeal.liftQ_apply] using hcont

end TauCeti
