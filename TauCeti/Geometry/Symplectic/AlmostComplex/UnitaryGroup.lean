/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.AlmostComplex
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

/-!
# The unitary group of an almost complex structure

The rotations of a quadratic form `Q` commuting with an almost complex structure `J` form a
subgroup `U(V, J)` of the special orthogonal group `SO(Q)`
(`TauCeti.AlmostComplexStructure.unitaryGroup`). For the negative definite form of an orthogonal
complex structure on a four-dimensional inner product space this is the unitary group `U(2)`.

## Main definitions

* `TauCeti.AlmostComplexStructure.unitaryGroup J Q`: the rotations of `SO(Q)` commuting with `J`.

## Main results

* `TauCeti.AlmostComplexStructure.mem_unitaryGroup_iff`: a rotation lies in `U(V, J)` exactly when
  it commutes with `J`.
-/

public section

open Module.End

namespace TauCeti.AlmostComplexStructure

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **The unitary group** `U(V, J)` of an almost complex structure `J`, inside the special
orthogonal group of a quadratic form `Q`: the rotations commuting with `J`. -/
noncomputable def unitaryGroup (J : AlmostComplexStructure V) (Q : QuadraticForm ℝ V) :
    Subgroup (QuadraticMap.specialOrthogonalGroup Q) :=
  (Subgroup.centralizer {J.linearEquiv}).comap (QuadraticMap.specialOrthogonalGroup Q).subtype

/-- A rotation lies in `U(V, J)` exactly when it commutes with `J`. -/
theorem mem_unitaryGroup_iff {J : AlmostComplexStructure V} {Q : QuadraticForm ℝ V}
    {A : QuadraticMap.specialOrthogonalGroup Q} :
    A ∈ J.unitaryGroup Q ↔ ∀ v, (A : V ≃ₗ[ℝ] V) (J v) = J ((A : V ≃ₗ[ℝ] V) v) := by
  simp only [unitaryGroup, Subgroup.mem_comap, Subgroup.coe_subtype,
    Subgroup.mem_centralizer_singleton_iff, LinearEquiv.ext_iff, mul_apply_eq_comp,
    linearEquiv_apply]

end TauCeti.AlmostComplexStructure
