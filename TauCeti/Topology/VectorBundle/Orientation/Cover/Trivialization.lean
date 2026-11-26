/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Orientation.Cover.Character
public import TauCeti.Topology.VectorBundle.Orientation.Cover.Transport

/-!
# Orientation transport read in trivializations

Let `E → B` be a real vector bundle of rank `card ι`. Transport of orientations along paths
(`TauCeti.VectorBundleOrientationCover.orientationTransport`) is canonical: it chooses no
trivialization. This file computes it in trivializations of the atlas, which is how the
orientation local system of a bundle described by transition functions is determined.

* **Inside one chart transport is constant.** Along a path that stays in the base set of a
  trivialization `e`, transport carries the orientation read as `o` in `e` at the start to the
  orientation read as `o` in `e` at the end
  (`TauCeti.VectorBundleOrientationCover.orientationTransport_mapOrientation_symm`).
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

The orientation character is also characterized through transport along a representing loop
(`orientationCharacter_fromPath_eq_one_iff`, `orientationCharacter_fromPath_eq_neg_one_iff`).

## Main results

* `TauCeti.VectorBundleOrientationCover.orientationTransport_mapOrientation_symm`: transport
  along a path inside one chart is constant in that chart.
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

omit [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  [Fintype ι] in
/-- An orientation read as `o` in a trivialization at a point `b'` equal to `b` is the orientation
of `E b` read as `o` there. -/
private theorem fiberEquiv_mk_mapOrientation_symm (e : Trivialization F (π F E)) [e.IsLinear ℝ]
    {b b' : B} (h : b' = b) (hb : b ∈ e.baseSet) (hb' : b' ∈ e.baseSet) (o : Orientation ℝ F ι) :
    fiberEquiv F E ι b ⟨⟨b', (e.mapOrientation ι hb').symm o⟩, h⟩ =
      (e.mapOrientation ι hb).symm o := by
  subst h
  exact fiberEquiv_mk _

/-- **Transport inside one chart is constant.** Along a path `γ` that stays in the base set of a
trivialization `e` of the atlas, transport carries the orientation of `E b₀` read as `o` in `e` to
the orientation of `E b₁` read as `o` in `e`. -/
theorem orientationTransport_mapOrientation_symm (e : Trivialization F (π F E))
    [MemTrivializationAtlas e] (γ : Path b₀ b₁) (hγ : ∀ t, γ t ∈ e.baseSet)
    (hb₀ : b₀ ∈ e.baseSet) (hb₁ : b₁ ∈ e.baseSet) (o : Orientation ℝ F ι) :
    orientationTransport E hι γ ((e.mapOrientation ι hb₀).symm o) =
      (e.mapOrientation ι hb₁).symm o := by
  -- The orientations read as `o` in `e` along `γ` form a lift of `γ` to the orientation cover.
  let Γ : C(I, VectorBundleOrientationCover F E ι) :=
    ⟨fun t ↦ ⟨γ t, (e.mapOrientation ι (hγ t)).symm o⟩,
      (continuous_mk_mapOrientation_symm hι e o).comp (γ.continuous.subtype_mk hγ)⟩
  have h₀ : fiberEquiv F E ι b₀ ⟨Γ 0, γ.source⟩ = (e.mapOrientation ι hb₀).symm o :=
    fiberEquiv_mk_mapOrientation_symm e γ.source hb₀ (hγ 0) o
  have h₁ : fiberEquiv F E ι b₁ ⟨Γ 1, γ.target⟩ = (e.mapOrientation ι hb₁).symm o :=
    fiberEquiv_mk_mapOrientation_symm e γ.target hb₁ (hγ 1) o
  rw [← h₀, ← h₁]
  exact orientationTransport_eq_of_lift hι γ Γ rfl γ.source γ.target

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

/-- The orientation character of the class of a loop `γ` is `1` exactly when transport along `γ`
returns an orientation `o` of the fibre to itself. -/
theorem orientationCharacter_fromPath_eq_one_iff {b : B} (γ : Path b b)
    (o : Orientation ℝ (E b) ι) :
    orientationCharacter F E hι b (FundamentalGroup.fromPath (.mk γ)) = 1 ↔
      orientationTransport E hι γ o = o := by
  rw [orientationCharacter_eq_one_iff_monodromy_eq hι _ ⟨⟨b, o⟩, rfl⟩,
    orientationTransport_apply, ← (fiberEquiv F E ι b).injective.eq_iff, fiberEquiv_mk]

/-- The orientation character of the class of a loop `γ` is `-1` exactly when transport along `γ`
carries an orientation `o` of the fibre to the opposite orientation. -/
theorem orientationCharacter_fromPath_eq_neg_one_iff {b : B} (γ : Path b b)
    (o : Orientation ℝ (E b) ι) :
    orientationCharacter F E hι b (FundamentalGroup.fromPath (.mk γ)) = -1 ↔
      orientationTransport E hι γ o = -o := by
  rw [orientationCharacter_eq_neg_one_iff hι _ ⟨⟨b, o⟩, rfl⟩, orientationTransport_apply,
    ← fiberEquiv_mk (F := F) (-o), (fiberEquiv F E ι b).injective.eq_iff, Subtype.ext_iff,
    deck_apply]

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
  rcases Int.units_eq_one_or (orientationCharacter F E hι b₀ (FundamentalGroup.fromPath
    (.mk (γ.trans γ')))) with h | h <;> rw [h]
  · rw [orientationCharacter_fromPath_eq_one_iff hι _ o, key,
      Orientation.map_eq_iff_det_pos _ _ hι] at h
    rw [sign_pos h]
    rfl
  · rw [orientationCharacter_fromPath_eq_neg_one_iff hι _ o, key,
      Trivialization.mapOrientation_neg, Orientation.map_eq_neg_iff_det_neg _ _ hι] at h
    rw [sign_neg h]
    rfl

end TauCeti.VectorBundleOrientationCover
