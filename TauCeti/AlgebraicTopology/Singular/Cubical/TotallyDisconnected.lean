/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Connected.TotallyDisconnected
public import TauCeti.AlgebraicTopology.Singular.Cubical.Normalized

/-!
# Normalized cubical chains of a totally disconnected space

A singular `0`-cube is a point, and no `0`-cube is degenerate, so the normalized `0`-chains of any
space are the formal combinations of its points
(`TauCeti.NormalizedCubicalChain.zeroEquiv : C^□_0(X; R) ≃ₗ[R] (X →₀ R)`).

In a totally disconnected space, such as a discrete one, nothing else survives. The image of a
singular cube is connected, hence a point, so every singular cube of positive dimension is constant
and in particular degenerate (`TauCeti.SingularCube.isDegenerate_of_totallyDisconnectedSpace`), and
the normalized chains of positive dimension vanish. This is the situation of the fibre of a
covering map, whose chains form the DG local system of the covering.

## Main definitions

* `TauCeti.NormalizedCubicalChain.zeroEquiv`: the normalized `0`-chains are the finitely supported
  functions on the points.

## Main results

* `TauCeti.SingularCube.isDegenerate_of_totallyDisconnectedSpace`: in a totally disconnected space
  every cube of positive dimension is degenerate.
* `TauCeti.NormalizedCubicalChain.instSubsingletonSuccOfTotallyDisconnectedSpace`: so the
  normalized chains of positive dimension vanish.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter II.
-/

public section

noncomputable section

open unitInterval

namespace TauCeti

variable {X : Type*} [TopologicalSpace X]

namespace SingularCube

/-- **In a totally disconnected space every cube of positive dimension is degenerate**: its image
is connected, hence a single point, so it depends on none of its coordinates. -/
theorem isDegenerate_of_totallyDisconnectedSpace [TotallyDisconnectedSpace X] {n : ℕ}
    (c : SingularCube X (n + 1)) : IsDegenerate c :=
  isDegenerate_iff.2 ⟨0, isDegenerateAt_iff.2 fun _ _ ↦
    (isPreconnected_range c.continuous).subsingleton ⟨_, rfl⟩ ⟨_, rfl⟩⟩

end SingularCube

namespace NormalizedCubicalChain

variable (R : Type*) [Ring R]

/-- **A totally disconnected space has no normalized chains of positive dimension.** -/
instance instSubsingletonSuccOfTotallyDisconnectedSpace [TotallyDisconnectedSpace X] {n : ℕ} :
    Subsingleton (NormalizedCubicalChain X R (n + 1)) :=
  subsingleton_of_forall_eq 0 fun g ↦ by
    induction g using induction_on with
    | zero => rfl
    | add a b ha hb => rw [ha, hb, add_zero]
    | smul r a ha => rw [ha, smul_zero]
    | ofCube c => exact ofCube_eq_zero R (SingularCube.isDegenerate_of_totallyDisconnectedSpace c)

variable (X) in
/-- **The normalized `0`-chains are the formal combinations of points**: no `0`-cube is
degenerate, and a `0`-cube is the constant cube at its value. -/
def zeroEquiv : NormalizedCubicalChain X R 0 ≃ₗ[R] (X →₀ R) :=
  Submodule.quotEquivOfEqBot _ (CubicalChain.degenerate_zero (X := X) (R := R)) ≪≫ₗ
    Finsupp.domLCongr (Homeomorph.continuousMapOfUnique (X := Fin 0 → I) (Y := X)).symm.toEquiv

/-- The class of the `0`-cube at a point is the indicator of that point. -/
@[simp]
theorem zeroEquiv_ofCube_point (x : X) :
    zeroEquiv X R (ofCube X R (SingularCube.point x)) = Finsupp.single x 1 := by
  rw [zeroEquiv, LinearEquiv.trans_apply, ofCube_def, Submodule.quotEquivOfEqBot_apply_mk,
    Finsupp.domLCongr_single, Homeomorph.coe_toEquiv,
    Homeomorph.continuousMapOfUnique_symm_apply, SingularCube.point_apply]

/-- The indicator of a point is the class of the `0`-cube at that point. -/
@[simp]
theorem zeroEquiv_symm_single (x : X) (r : R) :
    (zeroEquiv X R).symm (Finsupp.single x r) = r • ofCube X R (SingularCube.point x) := by
  rw [LinearEquiv.symm_apply_eq, map_smul, zeroEquiv_ofCube_point, Finsupp.smul_single_one]

end NormalizedCubicalChain

end TauCeti
