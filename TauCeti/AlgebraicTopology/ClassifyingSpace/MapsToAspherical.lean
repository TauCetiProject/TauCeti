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
import TauCeti.AlgebraicTopology.FundamentalGroup.Homeomorph
import TauCeti.AlgebraicTopology.FundamentalGroup.HomotopyEquiv
import TauCeti.AlgebraicTopology.Homotopy.KillHomotopyGroups
import TauCeti.AlgebraicTopology.Homotopy.Whitehead
import TauCeti.Topology.Homotopy.HomotopyGroup.WeakHomotopyEquivalence

/-!
# Maps from a space of CW type into an aspherical space

Let `X` be a path-connected space of CW type with a base point `x`, and `Y` a space whose higher
homotopy groups at `y` vanish, such as an aspherical space. Every homomorphism
`φ : π₁(X, x) →* π₁(Y, y)` is induced by a continuous map `f : X → Y` up to a change of base point:
there is a path `γ` from `f x` to `y` such that the map induced by `f`, followed by the change of
base point along `γ`, is `φ`
(`exists_continuousMap_fundamentalGroupMulEquivOfPath_map_eq_of_subsingleton_homotopyGroup`).
This is the existence half of Hatcher's Proposition 1B.9 before the base point is moved; `x` is an
arbitrary point, and `X` and `Y` lie in independent universes. When `{x}` has the homotopy
extension property in `X`, a homotopy of `f` with trace `γ` at `x` ends at a map sending `x` to
`y` and inducing `φ` (`ContinuousMap.Homotopy.fundamentalGroupMulEquivOfPath_evalAt_map`), which
is the existence half of Proposition 1B.9 itself.

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

* `exists_continuousMap_fundamentalGroupMulEquivOfPath_map_eq_of_subsingleton_homotopyGroup`: every
  homomorphism from `π₁(X, x)` to the fundamental group of a space with vanishing higher
  homotopy groups is induced by a map, up to a change of base point in the target.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 1.B,
  Proposition 1B.9, and Section 4.1, Proposition 4.22.
-/

public section

open scoped Topology Topology.Homotopy ContinuousMap

open FundamentalGroup

universe u v

namespace TauCeti

/-- The case of
`TauCeti.exists_continuousMap_fundamentalGroupMulEquivOfPath_map_eq_of_subsingleton_homotopyGroup`
for a Hausdorff `X` and with `Y` in the universe `max u v`, where the cellular model of `π₁(X, x)`
and the lifted space `X'` live. -/
private theorem exists_continuousMap_fundamentalGroupMulEquivOfPath_map_eq_max
    {Y : Type (max u v)} [TopologicalSpace Y] {y : Y} (hY : ∀ k, 2 ≤ k → Subsingleton (π_ k Y y))
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
  let ιπ : FundamentalGroup X x ≃* FundamentalGroup (ULift.{v} X') (ι x) :=
    (killHomotopyGroupsFundamentalGroupMulEquiv 2 (TopCat.of X) x one_lt_two).trans
      (homeomorphMulEquiv eX (incl x))
  have hιπ (a : FundamentalGroup X x) : ιπ a = mapOfEq ι (rfl : ι x = ι x) a := by
    rw [MulEquiv.trans_apply, killHomotopyGroupsFundamentalGroupMulEquiv_apply,
      homeomorphMulEquiv_apply]
    exact mapOfEq_mapOfEq_eq_mapOfEq rfl rfl rfl rfl a
  -- The cellular classifying space `C` of a presentation of `π₁(X, x)`, in the universe `max u v`.
  obtain ⟨R, -, -, hC⟩ := exists_isEilenbergMacLaneSpaceOne_cellularClassifyingSpace
    (ULift.{v} (FundamentalGroup X x))
  obtain ⟨ψ₀⟩ := hC.nonempty_fundamentalGroupMulEquiv
  let ψ := ψ₀.trans MulEquiv.ulift
  have := hC.isAspherical.pathConnectedSpace
  -- The weak homotopy equivalence `e : C → ULift X'` inducing `ιπ ∘ ψ`, and `g : C → Y`
  -- inducing `φ ∘ ψ`.
  obtain ⟨e, he, heπ, heW⟩ :=
    exists_isWeakHomotopyEquivalence_mapOfEq_cellularClassifyingSpace R hZ (ψ.trans ιπ)
  obtain ⟨g, hg, hgπ⟩ := exists_mapOfEq_cellularClassifyingSpace R hY (φ.comp ψ.toMonoidHom)
  -- The lift `ℓ : X → C` of `ι` through `e`; then `g ∘ ℓ` induces `φ ∘ ιπ⁻¹ ∘ ι_* = φ`.
  obtain ⟨ℓ, ⟨H⟩⟩ := heW.exists_comp_homotopic ι
  obtain ⟨γ, hγ⟩ := H.exists_path_fundamentalGroupMulEquivOfPath_map_comp_eq_mapOfEq he hg rfl
    (φ.comp ιπ.symm.toMonoidHom) (MonoidHom.ext fun a ↦ by simp [heπ, hgπ])
  exact ⟨g.comp ℓ, γ, fun a ↦ (hγ a).trans (congrArg φ (ιπ.symm_apply_eq.2 (hιπ a).symm))⟩

/-- **Homomorphisms into the fundamental group of a space with vanishing higher homotopy groups
are induced by maps, up to a change of base point** (the existence half of Hatcher, Proposition
1B.9, before the base point is moved). Let `X` be a path-connected space of CW type, such as a
path-connected Hausdorff CW complex, with an arbitrary base point `x`, and let the homotopy groups
`π_k(Y, y)` vanish for `k ≥ 2`, as they do when `Y` is aspherical at `y`. For every
homomorphism `φ : π₁(X, x) →* π₁(Y, y)` there are a continuous map `f : X → Y` and a path `γ` from
`f x` to `y` such that the map induced by `f`, followed by the change of base point along `γ`, is
`φ`. The spaces `X` and `Y` lie in independent universes. -/
theorem exists_continuousMap_fundamentalGroupMulEquivOfPath_map_eq_of_subsingleton_homotopyGroup
    {Y : Type v} [TopologicalSpace Y] {y : Y} (hY : ∀ k, 2 ≤ k → Subsingleton (π_ k Y y))
    {X : Type u} [TopologicalSpace X] [CWType X] [PathConnectedSpace X] (x : X)
    (φ : FundamentalGroup X x →* FundamentalGroup Y y) :
    ∃ (f : C(X, Y)) (γ : Path (f x) y),
      ∀ a, fundamentalGroupMulEquivOfPath γ (map f x a) = φ a := by
  -- Replace `X` by a homotopy equivalent CW complex `D`, which is Hausdorff.
  obtain ⟨Z, _, _, D, _, ⟨e⟩⟩ := (inferInstance : CWType X).exists_homotopyEquiv
  have he := e.isWeakHomotopyEquivalence
  have : PathConnectedSpace D := he.pathConnectedSpace_iff.1 inferInstance
  let eπ : FundamentalGroup X x ≃* FundamentalGroup D (e.toFun x) :=
    MulEquiv.ofBijective (map e.toFun x) (e.fundamentalGroup_map_bijective x)
  -- Replace `Y` by `ULift Y`, in the universe `max u v`.
  let eY : Y ≃ₜ ULift.{u} Y := Homeomorph.ulift.symm
  let down : C(ULift.{u} Y, Y) := eY.symm
  obtain ⟨f, γ, hγ⟩ := exists_continuousMap_fundamentalGroupMulEquivOfPath_map_eq_max
    (fun k hk ↦ (HomotopyGroup.homeomorphEquiv eY y).subsingleton_congr.1 (hY k hk)) (e.toFun x)
    ((homeomorphMulEquiv eY y).toMonoidHom.comp (φ.comp eπ.symm.toMonoidHom))
  refine ⟨down.comp (f.comp e.toFun), γ.map down.continuous, fun a ↦ ?_⟩
  have h := map_fundamentalGroupMulEquivOfPath down γ (map f (e.toFun x) (eπ a))
  simp only [hγ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at h
  rw [← mapOfEq_rfl down] at h
  simp only [map_comp, MonoidHom.comp_apply]
  exact h.symm.trans ((homeomorphMulEquiv_symm_apply eY y _).symm.trans
    ((homeomorphMulEquiv eY y).symm_apply_apply (φ a)))

end TauCeti
