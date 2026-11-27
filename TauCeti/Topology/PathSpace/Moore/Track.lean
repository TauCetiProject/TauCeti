/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Path
public import TauCeti.Topology.PathSpace.Moore.Comparison.Basic
public import TauCeti.Topology.PathSpace.Moore.Truncate

/-!
# Switching between homotopic maps along a Moore path

Let `H` be a homotopy from `θ₀ : B → X` to `θ₁ : B → X`. The **track** of `H` at a point `b`
(`ContinuousMap.Homotopy.mooreTrack`) is the path `t ↦ H (t, b)` from `θ₀ b` to `θ₁ b`, as a
Moore path of length one; it depends continuously on `b`.

A Moore path `γ` in `B` and a time `τ` give the Moore path in `X`

`θ₀ ∘ γ|[0, τ]`, then the track of `H` at `γ τ`, then `θ₁ ∘ γ|[τ, ∞)`

(`TauCeti.MoorePath.mapSplit`): the image of `γ` under `θ₀` up to time `τ` and under `θ₁` from
then on, joined by the track of the homotopy. It runs from `θ₀ (γ 0)` to `θ₁ γ.target` and depends
continuously on the path and the time (`Continuous.moorePath_mapSplit`). At time `0` it is the
track at the source followed by `θ₁ ∘ γ`, and at time `γ.length` it is `θ₀ ∘ γ` followed by the
track at the target.

Since Moore concatenation is strictly associative, splitting a concatenation `α · β` inside one of
its two pieces splits that piece and maps the other one whole:

* `mapSplit (α · β) (α.length + u) = (θ₀ ∘ α) · mapSplit β u`
  (`TauCeti.MoorePath.mapSplit_trans_length_add`);
* `mapSplit (α · β) τ = mapSplit α τ · (θ₁ ∘ β)` for `τ ≤ α.length`
  (`TauCeti.MoorePath.mapSplit_trans_of_le`).

These are the multiplicativity laws that make the paths of trajectories with a marked time,
mapped by `θ₀` before the mark and by `θ₁` after it, compatible with breaking, as in the
continuation cocycles comparing the twisting cocycles built from homotopic collapse maps.

## Main definitions

* `ContinuousMap.Homotopy.mooreTrack`: the track `t ↦ H (t, b)` of a homotopy at a point.
* `ContinuousMap.Homotopy.mooreTrackLoop`: the track at a point which both maps send to `x`, as a
  Moore loop at `x`.
* `TauCeti.MoorePath.mapSplit`: a Moore path mapped by `θ₀` before a time and by `θ₁` after it.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 6.
-/

public section

noncomputable section

open scoped NNReal
open Set

variable {B X : Type*} [TopologicalSpace B] [TopologicalSpace X] {θ₀ θ₁ : C(B, X)}

namespace ContinuousMap.Homotopy

/-- The **track** of a homotopy `H` from `θ₀` to `θ₁` at a point `b`: the path `t ↦ H (t, b)`
from `θ₀ b` to `θ₁ b`, as a Moore path of length one. It depends continuously on `b`. -/
def mooreTrack (H : θ₀.Homotopy θ₁) : C(B, TauCeti.MoorePath X) where
  toFun b := (H.evalAt b).toMoorePath
  continuous_toFun := by
    simp only [Path.toMoorePath_eq_ofUnitPath]
    refine TauCeti.MoorePath.continuous_ofUnitPath.comp <|
      ContinuousMap.continuous_of_continuous_uncurry _ ?_
    simp only [Function.uncurry_def, Path.coe_toContinuousMap, evalAt_apply]
    fun_prop

variable (H : θ₀.Homotopy θ₁) (b : B)

/-- The track of a homotopy at a point is the path `ContinuousMap.Homotopy.evalAt` it traces,
as a Moore path. -/
theorem mooreTrack_eq_toMoorePath : H.mooreTrack b = (H.evalAt b).toMoorePath :=
  (rfl)

@[simp]
theorem mooreTrack_apply (t : ℝ≥0) : H.mooreTrack b t = H (projIcc 0 1 zero_le_one t, b) := by
  rw [mooreTrack_eq_toMoorePath, Path.toMoorePath_eq_ofUnitPath, TauCeti.MoorePath.ofUnitPath_apply,
    Path.coe_toContinuousMap, evalAt_apply]

@[simp]
theorem length_mooreTrack : (H.mooreTrack b).length = 1 := by
  rw [mooreTrack_eq_toMoorePath, Path.length_toMoorePath]

@[simp]
theorem source_mooreTrack : (H.mooreTrack b).source = θ₀ b := by
  rw [mooreTrack_eq_toMoorePath, Path.source_toMoorePath]

@[simp]
theorem target_mooreTrack : (H.mooreTrack b).target = θ₁ b := by
  rw [mooreTrack_eq_toMoorePath, Path.target_toMoorePath]

/-- The **track loop** of a homotopy `H` from `θ₀` to `θ₁` at a point `b` which both maps send to
`x`: the track `t ↦ H (t, b)`, as a Moore loop at `x` of length one. -/
def mooreTrackLoop {b : B} {x : X} (h₀ : θ₀ b = x) (h₁ : θ₁ b = x) : TauCeti.MooreLoopSpace X x :=
  ⟨H.mooreTrack b, by simp [h₀], by simp [h₁]⟩

@[simp]
theorem toMoorePath_mooreTrackLoop {b : B} {x : X} (h₀ : θ₀ b = x) (h₁ : θ₁ b = x) :
    (H.mooreTrackLoop h₀ h₁).toMoorePath = H.mooreTrack b :=
  (rfl)

end ContinuousMap.Homotopy

namespace TauCeti

namespace MoorePath

/-- A Moore path `γ` mapped by `θ₀` up to the time `τ` and by `θ₁` from then on, joined at `γ τ`
by the track of a homotopy `H` from `θ₀` to `θ₁`:
`θ₀ ∘ γ|[0, τ]`, then `t ↦ H (t, γ τ)`, then `θ₁ ∘ γ|[τ, ∞)`. -/
def mapSplit (H : θ₀.Homotopy θ₁) (γ : MoorePath B) (τ : ℝ≥0) : MoorePath X :=
  ((γ.truncate τ).map θ₀).trans ((H.mooreTrack (γ τ)).trans ((γ.drop τ).map θ₁) (by simp))
    (by simp)

variable (H : θ₀.Homotopy θ₁)

theorem mapSplit_def (γ : MoorePath B) (τ : ℝ≥0) :
    γ.mapSplit H τ = ((γ.truncate τ).map θ₀).trans
      ((H.mooreTrack (γ τ)).trans ((γ.drop τ).map θ₁) (by simp)) (by simp) :=
  (rfl)

@[simp]
theorem source_mapSplit (γ : MoorePath B) (τ : ℝ≥0) : (γ.mapSplit H τ).source = θ₀ γ.source := by
  simp [mapSplit]

@[simp]
theorem target_mapSplit (γ : MoorePath B) (τ : ℝ≥0) : (γ.mapSplit H τ).target = θ₁ γ.target := by
  simp [mapSplit]

/-- Splitting a Moore path adds the length one of the track to its length. -/
@[simp]
theorem length_mapSplit (γ : MoorePath B) (τ : ℝ≥0) : (γ.mapSplit H τ).length = γ.length + 1 := by
  simp only [mapSplit, length_trans, length_map, length_truncate, length_drop,
    ContinuousMap.Homotopy.length_mooreTrack]
  rw [add_left_comm, add_comm (min τ γ.length), min_comm τ, tsub_add_min, add_comm]

/-- Split at time `0`, a Moore path is the track at its source followed by its image under `θ₁`. -/
@[simp]
theorem mapSplit_zero (γ : MoorePath B) :
    γ.mapSplit H 0 = (H.mooreTrack γ.source).trans (γ.map θ₁) (by simp) := by
  simp [mapSplit, source_def]

/-- Split at its length, a Moore path is its image under `θ₀` followed by the track at its
target. -/
@[simp]
theorem mapSplit_length (γ : MoorePath B) :
    γ.mapSplit H γ.length = (γ.map θ₀).trans (H.mooreTrack γ.target) (by simp) := by
  simp [mapSplit, target_def]

/-- Splitting a concatenation inside its second piece maps the first piece by `θ₀`. -/
@[simp]
theorem mapSplit_trans_length_add (α β : MoorePath B) (h : α.target = β.source) (u : ℝ≥0) :
    (α.trans β h).mapSplit H (α.length + u) =
      (α.map θ₀).trans (β.mapSplit H u) (by simp [h]) := by
  simp only [mapSplit, truncate_trans_length_add, drop_trans_length_add, trans_apply_length_add,
    map_trans]
  exact trans_assoc ..

/-- Splitting a concatenation inside its first piece maps the second piece by `θ₁`. -/
theorem mapSplit_trans_of_le (α β : MoorePath B) (h : α.target = β.source) {τ : ℝ≥0}
    (hτ : τ ≤ α.length) :
    (α.trans β h).mapSplit H τ = (α.mapSplit H τ).trans (β.map θ₁) (by simp [h]) := by
  simp only [mapSplit, truncate_trans_of_le _ _ _ hτ, drop_trans_of_le _ _ _ hτ,
    trans_apply_of_le _ _ _ hτ, map_trans]
  -- Reassociate `(θ₀ ∘ α|[0, τ]) · ((track · θ₁ ∘ α|[τ, ∞)) · θ₁ ∘ β)` on the right.
  refine Eq.trans ?_ (trans_assoc _ _ _ _ (by simp [h])).symm
  congr 1
  exact (trans_assoc _ _ _ _ (by simp [h])).symm

/-- Splitting is continuous in the path and the time. -/
@[fun_prop]
theorem _root_.Continuous.moorePath_mapSplit {Y : Type*} [TopologicalSpace Y]
    {f : Y → MoorePath B} {g : Y → ℝ≥0} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun y ↦ (f y).mapSplit H (g y) := by
  simp only [mapSplit]
  refine ((continuous_map θ₀).comp (hf.moorePath_truncate hg)).moorePath_trans
    ((H.mooreTrack.continuous.comp (hf.moorePath_eval hg)).moorePath_trans
      ((continuous_map θ₁).comp (hf.moorePath_drop hg)) _) _

end MoorePath

end TauCeti
