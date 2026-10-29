/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.HomotopyEquiv
public import TauCeti.AlgebraicTopology.SemilocallySimplyConnected.Basic
import TauCeti.AlgebraicTopology.FundamentalGroup.Basic

/-!
# Semilocal simple connectivity is a homotopy invariant

Semilocal simple connectivity pulls back along continuous maps that are injective on fundamental
groups: if `f : C(X, Y)` is injective on `π₁(X, x)` and `U` is a neighbourhood of `f x` whose
loops are null-homotopic in `Y`, then every loop in the neighbourhood `f ⁻¹' U` of `x` maps to a
null-homotopic loop, so is itself null-homotopic. Since the null-homotopy is allowed to leave the
neighbourhood, nothing local about `f` is needed beyond continuity.

A homotopy equivalence is bijective on fundamental groups at every base point
(`ContinuousMap.HomotopyEquiv.fundamentalGroup_map_bijective`), so semilocal simple connectivity
is invariant under homotopy equivalence. This is in contrast with local simple connectivity: the
cone on the Hawaiian earring is contractible, hence semilocally simply connected, but it is not
locally simply connected. Homotopy invariance transfers the standing hypotheses of
covering-space theory from one model of a homotopy type to another, for instance from Milnor's
classifying space to the cellular one.

## Main results

* `SemilocallySimplyConnectedAt.of_injective_fundamentalGroup_map`: semilocal simple
  connectivity at `f x` pulls back to `x` when `f` is injective on `π₁(X, x)`.
* `TauCeti.SemilocallySimplyConnectedSpace.of_injective_fundamentalGroup_map`: the space-level
  form, for a map injective on fundamental groups at every base point.
* `ContinuousMap.HomotopyEquiv.semilocallySimplyConnectedSpace` and
  `ContinuousMap.HomotopyEquiv.semilocallySimplyConnectedSpace_iff`: semilocal simple
  connectivity is a homotopy invariant.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 1.3, where
  semilocal simple connectivity is introduced for the construction of universal covers, with the
  cone on the shrinking wedge of circles as a semilocally simply connected space that is not
  locally simply connected.
-/

public section

open Topology

open scoped ContinuousMap

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **Semilocal simple connectivity pulls back along maps injective on `π₁`.** If `Y` is
semilocally simply connected at `f x` and `f` is injective on `π₁(X, x)`, then `X` is semilocally
simply connected at `x`: the preimage of a witnessing neighbourhood of `f x` witnesses it at `x`. -/
theorem _root_.SemilocallySimplyConnectedAt.of_injective_fundamentalGroup_map (f : C(X, Y))
    {x : X} (hf : Function.Injective (_root_.FundamentalGroup.map f x))
    (h : SemilocallySimplyConnectedAt (f x)) : SemilocallySimplyConnectedAt x := by
  obtain ⟨U, hU, hloop⟩ := semilocallySimplyConnectedAt_def.mp h
  refine semilocallySimplyConnectedAt_def.mpr
    ⟨f ⁻¹' U, f.continuous.continuousAt.preimage_mem_nhds hU, fun γ hγ ↦ ?_⟩
  have hdown := hloop (γ.map f.continuous) <| by
    rintro _ ⟨t, rfl⟩
    exact hγ ⟨t, rfl⟩
  -- The class of `γ` maps to the identity, so it is the identity by injectivity.
  have key : _root_.FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ) = 1 := by
    refine (injective_iff_map_eq_one _).mp hf _ ?_
    rw [FundamentalGroup.map_fromPath, _root_.FundamentalGroup.one_def,
      ← Path.Homotopic.Quotient.mk_refl]
    exact congrArg CategoryTheory.End.of (Quotient.sound hdown)
  rw [_root_.FundamentalGroup.one_def, ← Path.Homotopic.Quotient.mk_refl] at key
  exact Quotient.exact (congrArg CategoryTheory.End.asHom key)

/-- **Semilocal simple connectivity pulls back along maps injective on `π₁`.** A space admitting
a continuous map to a semilocally simply connected space that is injective on fundamental groups
at every base point is semilocally simply connected. -/
theorem SemilocallySimplyConnectedSpace.of_injective_fundamentalGroup_map
    [SemilocallySimplyConnectedSpace Y] (f : C(X, Y))
    (hf : ∀ x, Function.Injective (_root_.FundamentalGroup.map f x)) :
    SemilocallySimplyConnectedSpace X where
  semilocallySimplyConnectedAt x :=
    (SemilocallySimplyConnectedSpace.semilocallySimplyConnectedAt (f x))
      |>.of_injective_fundamentalGroup_map f (hf x)

/-- **Semilocal simple connectivity is a homotopy invariant.** A space homotopy equivalent to a
semilocally simply connected space is semilocally simply connected. -/
theorem _root_.ContinuousMap.HomotopyEquiv.semilocallySimplyConnectedSpace
    [SemilocallySimplyConnectedSpace Y] (e : X ≃ₕ Y) : SemilocallySimplyConnectedSpace X :=
  .of_injective_fundamentalGroup_map e.toFun fun x ↦ (e.fundamentalGroup_map_bijective x).1

/-- Two homotopy equivalent spaces are either both semilocally simply connected or both not. -/
theorem _root_.ContinuousMap.HomotopyEquiv.semilocallySimplyConnectedSpace_iff (e : X ≃ₕ Y) :
    SemilocallySimplyConnectedSpace X ↔ SemilocallySimplyConnectedSpace Y :=
  ⟨fun _ ↦ e.symm.semilocallySimplyConnectedSpace, fun _ ↦ e.semilocallySimplyConnectedSpace⟩

end TauCeti
