/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Basic
public import TauCeti.Topology.Algebra.CliffordAlgebra.Basic

/-!
# Continuity of the even part of a Spin element

A Spin group carries the subtype topology inside its Clifford algebra, which has the module
topology. This file proves that the even part `CliffordAlgebra.spinGroupToEven Q` of a Spin element
depends continuously on it, and deduces a continuity criterion for maps of Spin groups whose
Clifford values are a linear function of the even part. Every linear map out of an even Clifford
subalgebra is continuous (`CliffordAlgebra.continuous_even_linearMap`), so no finiteness or
invertibility assumption is needed.

## Main results

* `CliffordAlgebra.continuous_spinGroupToEven` proves continuity of the even part of a Spin
  element.
* `CliffordAlgebra.continuous_spinGroup_of_coe_eq` proves continuity of a map of Spin groups whose
  Clifford values are a linear function of the even part.
-/

public section

namespace CliffordAlgebra

variable {R V : Type*} [CommRing R] [TopologicalSpace R] [AddCommGroup V] [Module R V]

/-- The even part `spinGroupToEven Q` of a Spin element depends continuously on it, for the subtype
topologies. -/
@[fun_prop]
theorem continuous_spinGroupToEven (Q : QuadraticForm R V) : Continuous (spinGroupToEven Q) :=
  continuous_induced_rng.mpr
    (continuous_subtypeVal.congr fun x ↦ (coe_spinGroupToEven_apply Q x).symm)

/-- A map of Spin groups is continuous if its Clifford values are obtained from the even part by a
linear map of the even subalgebra. -/
theorem continuous_spinGroup_of_coe_eq {W : Type*} [AddCommGroup W] [Module R W]
    {Q : QuadraticForm R V} {P : QuadraticForm R W} {f : spinGroup Q → spinGroup P}
    (φ : even Q →ₗ[R] CliffordAlgebra P)
    (h : ∀ x, (f x : CliffordAlgebra P) = φ (spinGroupToEven Q x)) : Continuous f :=
  continuous_induced_rng.mpr (((continuous_even_linearMap φ).comp
    (continuous_spinGroupToEven Q)).congr fun x ↦ (h x).symm)

end CliffordAlgebra
