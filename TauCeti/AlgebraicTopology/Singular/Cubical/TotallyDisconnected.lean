/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Connected.TotallyDisconnected
public import TauCeti.AlgebraicTopology.Singular.Cubical.Normalized

/-!
# Normalized cubical chains of a totally disconnected space

The normalized `0`-chains of any space are the formal combinations of its points
(`TauCeti.NormalizedCubicalChain.zeroEquiv : C^□_0(X; R) ≃ₗ[R] (X →₀ R)`). In a totally
disconnected space, such as a discrete one, nothing else survives. The image of a singular cube is
connected, hence a point, so every singular cube of positive dimension is constant and in
particular degenerate (`TauCeti.SingularCube.isDegenerate_of_totallyDisconnectedSpace`), and
the normalized chains of positive dimension vanish. This is the situation of the fibre of a
covering map, whose chains form the DG local system of the covering.

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

end NormalizedCubicalChain

end TauCeti
