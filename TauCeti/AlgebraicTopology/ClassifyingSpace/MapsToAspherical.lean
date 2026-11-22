/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import TauCeti.AlgebraicTopology.EilenbergMacLane.Basic
public import TauCeti.Topology.CWComplex.Classical.CWType
import TauCeti.AlgebraicTopology.ClassifyingSpace.Comparison
import TauCeti.AlgebraicTopology.EilenbergMacLane.WeakHomotopyEquivalence
import TauCeti.AlgebraicTopology.FundamentalGroup.Basic
import TauCeti.AlgebraicTopology.FundamentalGroup.BasepointChange
import TauCeti.AlgebraicTopology.Homotopy.KillHomotopyGroups
import TauCeti.AlgebraicTopology.Homotopy.Whitehead
import TauCeti.Topology.Homotopy.HomotopyGroup.WeakHomotopyEquivalence

/-!
# Maps from a space of CW type into an aspherical space

Let `X` be a path-connected space of CW type with a base point `x`, and `Y` an aspherical space
with base point `y`. Every homomorphism `φ : π₁(X, x) →* π₁(Y, y)` is induced by a continuous map
`f : X → Y` up to a change of base point: there is a path `γ` from `f x` to `y` such that the map
induced by `f`, followed by the change of base point along `γ`, is `φ`
(`TauCeti.IsAspherical.exists_continuousMap_fundamentalGroupMulEquivOfPath_map_eq`). This is the
existence half of Hatcher's Proposition 1B.9 before the base point is moved; `x` is an arbitrary
point, and `X` and `Y` lie in independent universes. When `{x}` has the homotopy extension
property in `X`, a homotopy of `f` with trace `γ` at `x` ends at a map sending `x` to `y` and
inducing `φ` (`ContinuousMap.Homotopy.fundamentalGroupMulEquivOfPath_evalAt_map`), which is the
existence half of Proposition 1B.9 itself.

First `X` is replaced by a homotopy equivalent CW complex, which is Hausdorff. The map then
factors through the cellular classifying space `C` of a presentation of `π₁(X, x)`. Killing the
higher homotopy groups of `X` embeds it into an aspherical space `X'` with the same fundamental
group. The cellular model maps into `X'` by a weak homotopy equivalence `e` inducing that
identification, and into `Y` by a map `g` inducing `φ`; both maps exist because the targets have no
higher homotopy (`TauCeti.exists_mapOfEq_cellularClassifyingSpace`). Since `X` has CW type, the
inclusion of `X` into `X'` lifts through `e` up to homotopy to a map `ℓ : X → C`
(`ContinuousMap.IsWeakHomotopyEquivalence.exists_comp_homotopic`), and `g ∘ ℓ` realizes `φ` up to
the change of base point that corrects the trace of that homotopy
(`ContinuousMap.Homotopy.exists_path_fundamentalGroupMulEquivOfPath_map_comp_eq_mapOfEq`). The
cellular model, `X'` and `Y` are lifted to a common universe with `ULift`; `X` is not lifted.

## Main results

* `TauCeti.IsAspherical.exists_continuousMap_fundamentalGroupMulEquivOfPath_map_eq`: every
  homomorphism from `π₁(X, x)` to the fundamental group of an aspherical space is induced by a map,
  up to a change of base point in the target.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 1.B,
  Proposition 1B.9, and Section 4.1, Proposition 4.22.
-/

public section

open scoped Topology Topology.Homotopy ContinuousMap

open FundamentalGroup

universe u v

namespace TauCeti

/-- The case of `TauCeti.IsAspherical.exists_continuousMap_fundamentalGroupMulEquivOfPath_map_eq`
for a Hausdorff `X` and with `Y` in the universe `max u v`, where the cellular model of `π₁(X, x)`
and the lifted space `X'` live. -/
private theorem IsAspherical.exists_continuousMap_fundamentalGroupMulEquivOfPath_map_eq_max
    {Y : Type (max u v)} [TopologicalSpace Y] {y : Y} (hY : IsAspherical Y y)
    {X : Type u} [TopologicalSpace X] [T2Space X] [CWType X] [PathConnectedSpace X] (x : X)
    (φ : FundamentalGroup X x →* FundamentalGroup Y y) :
    ∃ (f : C(X, Y)) (γ : Path (f x) y),
      ∀ a, fundamentalGroupMulEquivOfPath γ (map f x a) = φ a := by
  -- The aspherical space `X'` containing `X`, lifted to the universe `max u v`.
  let X' := killHomotopyGroups 2 (TopCat.of X) x
  let incl := killHomotopyGroupsIncl 2 (TopCat.of X) x
  let eX : X' ≃ₜ ULift.{v} X' := Homeomorph.ulift.symm
  let ι : C(X, ULift.{v} X') := (eX : C(X', ULift.{v} X')).comp incl.hom
  have hZ : IsAspherical (ULift.{v} X') (ι x) :=
    (eX.isWeakHomotopyEquivalence.isAspherical_iff (incl x)).1
      (isEilenbergMacLaneSpaceOne_killHomotopyGroups (TopCat.of X) x).isAspherical
  -- The inclusion `ι` induces an isomorphism of fundamental groups.
  have hι : Function.Bijective (mapOfEq ι (rfl : ι x = ι x)) := by
    have h := (eX.isWeakHomotopyEquivalence.mapOfEq_bijective (x := incl x) rfl).comp
      (killHomotopyGroupsFundamentalGroupMulEquiv 2 (TopCat.of X) x one_lt_two).bijective
    have hcomp : mapOfEq (eX : C(X', ULift.{v} X')) rfl ∘
        killHomotopyGroupsFundamentalGroupMulEquiv 2 (TopCat.of X) x one_lt_two =
          mapOfEq ι (rfl : ι x = ι x) :=
      funext fun a ↦ by
        rw [Function.comp_apply, killHomotopyGroupsFundamentalGroupMulEquiv_apply]
        exact mapOfEq_mapOfEq_eq_mapOfEq rfl rfl rfl rfl a
    exact hcomp ▸ h
  let ιπ : FundamentalGroup X x ≃* FundamentalGroup (ULift.{v} X') (ι x) :=
    MulEquiv.ofBijective (mapOfEq ι (rfl : ι x = ι x)) hι
  -- The cellular classifying space `C` of a presentation of `π₁(X, x)`, in the universe `max u v`.
  obtain ⟨R, -, -, hC⟩ := exists_isEilenbergMacLaneSpaceOne_cellularClassifyingSpace
    (ULift.{v} (FundamentalGroup X x))
  obtain ⟨ψ₀⟩ := hC.nonempty_fundamentalGroupMulEquiv
  let ψ := ψ₀.trans MulEquiv.ulift
  have := hC.isAspherical.pathConnectedSpace
  have hgt {W : Type (max u v)} [TopologicalSpace W] {w : W} (hW : IsAspherical W w) :
      ∀ k, 2 ≤ k → Subsingleton (π_ k W w) := fun k hk ↦ by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hk
    exact hW.subsingleton_homotopyGroup n
  -- The weak homotopy equivalence `e : C → ULift X'` inducing `ιπ ∘ ψ`, and `g : C → Y`
  -- inducing `φ ∘ ψ`.
  obtain ⟨e, he, heπ⟩ := exists_mapOfEq_cellularClassifyingSpace R (hgt hZ) (ψ.trans ιπ).toMonoidHom
  have heW : e.IsWeakHomotopyEquivalence :=
    (hC.isAspherical.isWeakHomotopyEquivalence_iff hZ he).2 (heπ ▸ (ψ.trans ιπ).bijective)
  obtain ⟨g, hg, hgπ⟩ := exists_mapOfEq_cellularClassifyingSpace R (hgt hY)
    (φ.comp ψ.toMonoidHom)
  -- The lift `ℓ : X → C` of `ι` through `e`; then `g ∘ ℓ` induces `φ ∘ ιπ⁻¹ ∘ ι_* = φ`.
  obtain ⟨ℓ, ⟨H⟩⟩ := heW.exists_comp_homotopic ι
  obtain ⟨γ, hγ⟩ := H.exists_path_fundamentalGroupMulEquivOfPath_map_comp_eq_mapOfEq he hg rfl
    (φ.comp ιπ.symm.toMonoidHom) (MonoidHom.ext fun a ↦ by simp [heπ, hgπ])
  exact ⟨g.comp ℓ, γ, fun a ↦ (hγ a).trans (congrArg φ (ιπ.symm_apply_apply a))⟩

/-- **Homomorphisms into the fundamental group of an aspherical space are induced by maps, up to a
change of base point** (the existence half of Hatcher, Proposition 1B.9, before the base point is
moved). Let `X` be a path-connected space of CW type, such as a path-connected Hausdorff CW
complex, with an arbitrary base point `x`, and let `Y` be aspherical at `y`. For every
homomorphism `φ : π₁(X, x) →* π₁(Y, y)` there are a continuous map `f : X → Y` and a path `γ` from
`f x` to `y` such that the map induced by `f`, followed by the change of base point along `γ`, is
`φ`. The spaces `X` and `Y` lie in independent universes. -/
theorem IsAspherical.exists_continuousMap_fundamentalGroupMulEquivOfPath_map_eq
    {Y : Type v} [TopologicalSpace Y] {y : Y} (hY : IsAspherical Y y)
    {X : Type u} [TopologicalSpace X] [CWType X] [PathConnectedSpace X] (x : X)
    (φ : FundamentalGroup X x →* FundamentalGroup Y y) :
    ∃ (f : C(X, Y)) (γ : Path (f x) y),
      ∀ a, fundamentalGroupMulEquivOfPath γ (map f x a) = φ a := by
  -- Replace `X` by a homotopy equivalent CW complex `D`, which is Hausdorff.
  obtain ⟨Z, _, _, D, _, ⟨e⟩⟩ := (inferInstance : CWType X).exists_homotopyEquiv
  have he := e.isWeakHomotopyEquivalence
  have : PathConnectedSpace D := he.pathConnectedSpace_iff.1 inferInstance
  let eπ : FundamentalGroup X x ≃* FundamentalGroup D (e.toFun x) :=
    MulEquiv.ofBijective (map e.toFun x) (mapOfEq_rfl e.toFun ▸ he.mapOfEq_bijective rfl)
  -- Replace `Y` by `ULift Y`, in the universe `max u v`.
  let eY : Y ≃ₜ ULift.{u} Y := Homeomorph.ulift.symm
  let up : C(Y, ULift.{u} Y) := eY
  let down : C(ULift.{u} Y, Y) := eY.symm
  have hdown : down.comp up = ContinuousMap.id Y := ContinuousMap.ext fun _ ↦ rfl
  obtain ⟨f, γ, hγ⟩ := IsAspherical.exists_continuousMap_fundamentalGroupMulEquivOfPath_map_eq_max
    ((eY.isWeakHomotopyEquivalence.isAspherical_iff y).1 hY) (e.toFun x)
    ((mapOfEq up (rfl : up y = up y)).comp (φ.comp eπ.symm.toMonoidHom))
  refine ⟨down.comp (f.comp e.toFun), γ.map down.continuous, fun a ↦ ?_⟩
  have h := map_fundamentalGroupMulEquivOfPath down γ (map f (e.toFun x) (eπ a))
  rw [hγ, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    eπ.symm_apply_apply, ← mapOfEq_rfl down] at h
  rw [map_comp, map_comp, MonoidHom.comp_apply, MonoidHom.comp_apply]
  exact h.symm.trans (mapOfEq_mapOfEq_of_comp_eq_id down up rfl rfl hdown (φ a))

end TauCeti
