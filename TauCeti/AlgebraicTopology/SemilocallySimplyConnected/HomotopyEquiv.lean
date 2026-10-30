/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Equiv
public import TauCeti.AlgebraicTopology.SemilocallySimplyConnected.Basic
import TauCeti.AlgebraicTopology.FundamentalGroup.Basic
import TauCeti.AlgebraicTopology.FundamentalGroup.BasepointChange

/-!
# Semilocal simple connectivity is a homotopy invariant

Semilocal simple connectivity asks that small loops be null-homotopic in the *whole* space, not
in a small neighbourhood. This makes it a homotopy invariant, unlike the local notions of simple
connectivity or contractibility.

More precisely, if `f : X → Y` has a homotopy left inverse `g` (so `g ∘ f` is homotopic to the
identity of `X`) and `Y` is semilocally simply connected, then so is `X`
(`TauCeti.SemilocallySimplyConnectedSpace.of_homotopic_comp`). Given a point `x`, pull back along
`f` a neighbourhood `V` of `f x` whose loops are null-homotopic in `Y`. A loop `γ` at `x` inside
`f⁻¹ V` has a null-homotopic image `f ∘ γ`, so `g ∘ f ∘ γ` is null-homotopic as well. Freely
homotopic maps induce the same map on fundamental groups up to a change of base point
(`ContinuousMap.Homotopy.fundamentalGroupMulEquivOfPath_evalAt_map`), so `γ`, the image of the
loop under the identity, is null-homotopic too.

In particular semilocal simple connectivity is invariant under homotopy equivalence
(`ContinuousMap.HomotopyEquiv.semilocallySimplyConnectedSpace_iff`). This is how the standing
hypotheses of covering-space theory pass from one model of a homotopy type to another, for example
from Milnor's classifying space to the cellular one.

## Main results

* `TauCeti.SemilocallySimplyConnectedSpace.of_homotopic_comp`: a space admitting a map with a
  homotopy left inverse into a semilocally simply connected space is semilocally simply
  connected.
* `ContinuousMap.HomotopyEquiv.semilocallySimplyConnectedSpace`: a space homotopy equivalent to a
  semilocally simply connected space is semilocally simply connected.
* `ContinuousMap.HomotopyEquiv.semilocallySimplyConnectedSpace_iff`: semilocal simple
  connectivity is invariant under homotopy equivalence.
-/

public section

open Topology

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **Semilocal simple connectivity passes to homotopy retracts.** If `f : X → Y` has a homotopy
left inverse `g`, that is, `g ∘ f` is homotopic to the identity of `X`, and `Y` is semilocally
simply connected, then so is `X`. -/
theorem SemilocallySimplyConnectedSpace.of_homotopic_comp [SemilocallySimplyConnectedSpace Y]
    {f : C(X, Y)} {g : C(Y, X)} (h : (g.comp f).Homotopic (ContinuousMap.id X)) :
    SemilocallySimplyConnectedSpace X where
  semilocallySimplyConnectedAt x := by
    obtain ⟨V, hV, hloop⟩ := semilocallySimplyConnectedAt_def.mp
      (SemilocallySimplyConnectedSpace.semilocallySimplyConnectedAt (f x))
    refine semilocallySimplyConnectedAt_def.mpr
      ⟨f ⁻¹' V, f.continuous.continuousAt.preimage_mem_nhds hV, fun γ hγ => ?_⟩
    -- The image of `γ` is a loop in `V`, hence null-homotopic in `Y`.
    set a := FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)
    have hfγ : FundamentalGroup.map f x a = 1 := by
      rw [FundamentalGroup.map_fromPath]
      exact congrArg CategoryTheory.End.of
        ((FundamentalGroupoid.fromPath_eq_iff_homotopic _ _).mpr
          (hloop _ (Set.range_subset_iff.mpr fun t => hγ ⟨t, rfl⟩)))
    -- Up to basepoint change, `(g ∘ f)_*` and `id_*` agree, so the class of `γ` is trivial.
    have key := h.some.fundamentalGroupMulEquivOfPath_evalAt_map x a
    rw [_root_.FundamentalGroup.map_comp, MonoidHom.comp_apply, hfγ, map_one, map_one] at key
    exact (FundamentalGroupoid.fromPath_eq_iff_homotopic _ _).mp
      (congrArg CategoryTheory.End.asHom
        (key.trans (DFunLike.congr_fun (_root_.FundamentalGroup.map_id x) a)).symm)

end TauCeti

namespace ContinuousMap.HomotopyEquiv

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **A space homotopy equivalent to a semilocally simply connected space is semilocally simply
connected.** -/
theorem semilocallySimplyConnectedSpace [TauCeti.SemilocallySimplyConnectedSpace Y]
    (e : X ≃ₕ Y) : TauCeti.SemilocallySimplyConnectedSpace X :=
  .of_homotopic_comp e.left_inv

/-- **Semilocal simple connectivity is invariant under homotopy equivalence.** -/
theorem semilocallySimplyConnectedSpace_iff (e : X ≃ₕ Y) :
    TauCeti.SemilocallySimplyConnectedSpace X ↔ TauCeti.SemilocallySimplyConnectedSpace Y :=
  ⟨fun _ => e.symm.semilocallySimplyConnectedSpace, fun _ => e.semilocallySimplyConnectedSpace⟩

end ContinuousMap.HomotopyEquiv
