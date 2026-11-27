/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Orientation.Cover.Character
public import TauCeti.Topology.VectorBundle.Orientation.Cover.Transport
import TauCeti.Data.SignType.Basic

/-!
# Orientation transport read in trivializations

Let `E → B` be a real vector bundle of rank `card ι`. Transport of orientations along paths
(`TauCeti.VectorBundleOrientationCover.orientationTransport`) is canonical: it chooses no
trivialization. This file computes it in trivializations of the atlas, which is how the
orientation local system of a bundle described by transition functions is determined.

* **Inside one chart transport is constant.** Along a path that stays in the base set of a
  trivialization `e`, transport carries the orientation read as `o` in `e` at the start to the
  orientation read as `o` in `e` at the end
  (`TauCeti.VectorBundleOrientationCover.orientationTransport_mapOrientation_symm`, in
  `TauCeti.Topology.VectorBundle.Orientation.Cover.Transport`).
* **Across two charts transport is the transition.** Let a loop at `b₀` run along a path `γ` from
  `b₀` to `b₁` inside the base set of `e`, then back along a path `γ'` inside the base set of
  `e'`. Read in `e` at `b₀`, transport around it applies the composite `M` of the coordinate
  change from `e` to `e'` at `b₁` and of the coordinate change from `e'` back to `e` at `b₀`
  (`TauCeti.VectorBundleOrientationCover.mapOrientation_orientationTransport_trans`). So the
  orientation character of the loop is the sign of `det M`
  (`TauCeti.VectorBundleOrientationCover.coe_orientationCharacter_fromPath_trans`): transport
  in the orientation local system `o(E)` is the sign of the transition determinant.

For a bundle glued from two charts over the circle with transition the identity on one overlap
arc and `A` on the other, `M` is `A`, so the orientation character of the circle is the sign of
`det A` (`TauCeti.circleClutchingCore`). It is the sign of the determinant of the transition of
the bundle itself, not of a larger bundle containing it: the rank-two transition `diag(1, -1)`
reverses orientations, while `diag(1, -1, -1)` preserves them.

## Main results

* `TauCeti.VectorBundleOrientationCover.mapOrientation_orientationTransport_trans`: transport
  around a loop through two charts applies the composite of the two transitions.
* `TauCeti.VectorBundleOrientationCover.coe_orientationCharacter_fromPath_trans`: the orientation
  character of such a loop is the sign of the determinant of that composite.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §12 (the orientation double cover).
* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §6.2 (orientation local systems of negative normal bundles,
  read through their transition functions).
-/

public section

noncomputable section

open Bundle Module unitInterval

namespace TauCeti.VectorBundleOrientationCover

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {ι : Type*} [Fintype ι] (hι : Fintype.card ι = finrank ℝ F) {b₀ b₁ : B}

variable (e e' : Trivialization F (π F E)) [MemTrivializationAtlas e] [MemTrivializationAtlas e']

/-- **Transport around a loop through two charts.** Let `γ` run from `b₀` to `b₁` inside the
base set of `e` and `γ'` back from `b₁` to `b₀` inside the base set of `e'`. Read in `e` at `b₀`,
transport along `γ` followed by `γ'` applies the coordinate change from `e` to `e'` at `b₁`
followed by the coordinate change from `e'` to `e` at `b₀`. -/
theorem mapOrientation_orientationTransport_trans (γ : Path b₀ b₁) (γ' : Path b₁ b₀)
    (hγ : ∀ t, γ t ∈ e.baseSet) (hγ' : ∀ t, γ' t ∈ e'.baseSet) (hb₀ : b₀ ∈ e.baseSet)
    (o : Orientation ℝ (E b₀) ι) :
    e.mapOrientation ι hb₀ (orientationTransport E hι (γ.trans γ') o) =
      Orientation.map ι ((e.coordChangeL ℝ e' b₁).trans (e'.coordChangeL ℝ e b₀)).toLinearEquiv
        (e.mapOrientation ι hb₀ o) := by
  have hb₁ : b₁ ∈ e.baseSet := γ.target ▸ hγ 1
  have hb₁' : b₁ ∈ e'.baseSet := γ'.source ▸ hγ' 0
  have hb₀' : b₀ ∈ e'.baseSet := γ'.target ▸ hγ' 1
  set ω := e.mapOrientation ι hb₀ o
  have ho : o = (e.mapOrientation ι hb₀).symm ω :=
    ((e.mapOrientation ι hb₀).symm_apply_apply o).symm
  -- Transport along `γ` keeps the reading `ω` in `e`.
  have h₁ : orientationTransport E hι γ o = (e.mapOrientation ι hb₁).symm ω := by
    rw [ho, orientationTransport_mapOrientation_symm hι e γ hγ hb₀ hb₁]
  -- Read in `e'` at `b₁`, this is `ω` moved by the coordinate change from `e` to `e'`.
  set ω' := Orientation.map ι (e.coordChangeL ℝ e' b₁).toLinearEquiv ω
  have h₁' : orientationTransport E hι γ o = (e'.mapOrientation ι hb₁').symm ω' := by
    rw [Equiv.eq_symm_apply, Trivialization.mapOrientation_eq_map_coordChangeL e e' hb₁ hb₁', h₁,
      Equiv.apply_symm_apply]
  -- Transport along `γ'` keeps the reading `ω'` in `e'`; read it back in `e` at `b₀`.
  rw [orientationTransport_trans, Equiv.trans_apply, h₁',
    orientationTransport_mapOrientation_symm hι e' γ' hγ' hb₁' hb₀',
    Trivialization.mapOrientation_eq_map_coordChangeL e' e hb₀' hb₀, Equiv.apply_symm_apply,
    ContinuousLinearEquiv.trans_toLinearEquiv, Orientation.map_trans]

variable [FiniteDimensional ℝ F]

/-- **The orientation character is the sign of the transition determinant.** Let `γ` run from
`b₀` to `b₁` inside the base set of `e` and `γ'` back from `b₁` to `b₀` inside the base set of
`e'`. The orientation character of the loop `γ` followed by `γ'` is the sign of the determinant
of the composite of the coordinate change from `e` to `e'` at `b₁` with the coordinate change
from `e'` to `e` at `b₀`. -/
theorem coe_orientationCharacter_fromPath_trans (γ : Path b₀ b₁) (γ' : Path b₁ b₀)
    (hγ : ∀ t, γ t ∈ e.baseSet) (hγ' : ∀ t, γ' t ∈ e'.baseSet) :
    (orientationCharacter F E hι b₀ (FundamentalGroup.fromPath (.mk (γ.trans γ'))) : ℤ) =
      SignType.sign (LinearMap.det
        (((e.coordChangeL ℝ e' b₁).trans (e'.coordChangeL ℝ e b₀)).toLinearEquiv :
          F →ₗ[ℝ] F)) := by
  set M := ((e.coordChangeL ℝ e' b₁).trans (e'.coordChangeL ℝ e b₀)).toLinearEquiv
  have hb₀ : b₀ ∈ e.baseSet := γ.source ▸ hγ 0
  obtain ⟨p, hp⟩ := surjective_proj (F := F) (E := E) hι b₀
  set o := fiberEquiv F E ι b₀ ⟨p, hp⟩
  -- Read in `e`, transport around the loop is the orientation map of `M`.
  have key (o' : Orientation ℝ (E b₀) ι) :
      orientationTransport E hι (γ.trans γ') o = o' ↔
        Orientation.map ι M (e.mapOrientation ι hb₀ o) = e.mapOrientation ι hb₀ o' := by
    rw [← mapOrientation_orientationTransport_trans hι e e' γ γ' hγ hγ' hb₀,
      (e.mapOrientation ι hb₀).injective.eq_iff]
  refine coe_units_eq_sign_of_eq_one_iff M.isUnit_det'.ne_zero ?_
  rw [orientationCharacter_fromPath_eq_one_iff hι _ o, key, Orientation.map_eq_iff_det_pos _ _ hι]

end TauCeti.VectorBundleOrientationCover
