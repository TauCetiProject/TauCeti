/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Flow.ConnectingOrbit
public import TauCeti.Geometry.Manifold.Morse.Boundary.Basic
public import TauCeti.Geometry.Manifold.Morse.Stable.Broken.TrajectorySpace
public import TauCeti.Topology.PathSpace.Moore.Comparison.Basic
import TauCeti.Geometry.Manifold.Morse.Stable.LevelSlice

/-!
# Trajectory records, traced paths and the middle-level slice

The trajectories of an adapted pseudo-gradient appear in two models: as records of broken
trajectories on levels (`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpace`), with their
Moore paths parametrized by the values of `f` (`TauCeti.IsAdaptedPseudoGradient.morseLevelPath`),
and as points of the middle-level slice (`TauCeti.IsAdaptedPseudoGradient.morseTrajectorySlice`),
with the paths they trace (`Flow.connectingPath`). This file compares the two.

* **Moore paths of records trace the trajectories.** The Moore path of the record of a trajectory
  is a reparametrization, by the clamped drop of `f`, of the path traced by the trajectory, so the
  two are homotopic (`IsAdaptedPseudoGradient.homotopic_toPath_morseLevelPath`).
* **Trajectory spaces of index difference one.** Under the Morse–Smale condition, for
  `ind x = ind y + 1` reading off the point of a record on the middle level is a bijection from the
  trajectory space from `x` to `y` onto the middle-level slice
  (`IsAdaptedPseudoGradient.IsMorseSmale.morseBrokenTrajectorySpaceEquivSlice`); its inverse
  records the level points (`TauCeti.IsAdaptedPseudoGradient.levelPoint`) of a trajectory.

## Main definitions

* `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseBrokenTrajectorySpaceEquivSlice`: the
  bijection from a trajectory space of index difference one onto the middle-level slice.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `homotopic_toPath_morseLevelPath`: the Moore path of the record of a trajectory is homotopic to
  the path traced by the trajectory.
* `IsMorseSmale.exists_flow_morseBrokenTrajectorySpaceEquivSlice`: a record of index difference
  one records the trajectory through its point on the middle level.
-/

public section

open Set unitInterval
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {ι : Type*}

namespace IsAdaptedPseudoGradient

variable {hX : IsAdaptedPseudoGradient f X} {p r y : M} {c : ι → ℝ} {w : ι → M}

/-- **The Moore path of the record of a trajectory traces the trajectory.** Let `w` record, on
levels dense between `f r` and `f p`, the trajectory through `y` from the critical point `p` to the
critical point `r ≠ p`. Then its Moore path, read on the unit interval, is homotopic to the path
traced by the trajectory (`Flow.connectingPath`). -/
theorem homotopic_toPath_morseLevelPath (hf : IsMorse 𝓘(ℝ, E) f)
    (hdense : Ioo (f r) (f p) ⊆ closure (range c)) (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0)
    (hr : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f r = 0) (hpr : p ≠ r)
    (hy : y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r)
    (w : hX.morseBrokenTrajectoryRecords p r c) (hw : ∀ i, ∃ t, hX.flow t y = (w : ι → M) i) :
    ((hX.morseLevelPath hf hdense w).toPath.cast (hX.source_morseLevelPath hf hdense w).symm
      (hX.target_morseLevelPath hf hdense w).symm).Homotopic (Flow.connectingPath hy.1 hy.2) := by
  set γ := Flow.connectingPath hy.1 hy.2
  set δ := (hX.morseLevelPath hf hdense w).toPath.cast (hX.source_morseLevelPath hf hdense w).symm
    (hX.target_morseLevelPath hf hdense w).symm
  have hL : 0 < f p - f r :=
    sub_pos.2 (hX.value_lt_of_mem_morseBrokenTrajectoryRecords hpr w.property)
  -- The drop of the value of `f` along `γ`, as a fraction of the total drop.
  let ρ : I → I := fun s ↦ projIcc 0 1 zero_le_one ((f p - f (γ s)) / (f p - f r))
  have hρ : Continuous ρ := continuous_projIcc.comp
    ((continuous_const.sub (hf.contMDiff.continuous.comp γ.continuous)).div_const _)
  have hρ₀ : ρ 0 = 0 := by simp [ρ]
  have hρ₁ : ρ 1 = 1 := by simp [ρ, div_self hL.ne']
  -- Every point of `γ` is an end or a point of the trajectory through `y`.
  have hγ (s : I) : γ s = p ∨ γ s = r ∨ ∃ t, hX.flow t y = γ s := by
    rcases eq_or_ne s 0 with rfl | h0
    · exact Or.inl γ.source
    rcases eq_or_ne s 1 with rfl | h1
    · exact Or.inr (Or.inl γ.target)
    refine Or.inr (Or.inr ⟨_, (Flow.connectingPath_apply_of_mem_Ioo hy.1 hy.2
      ⟨unitInterval.pos_iff_ne_zero.2 h0, unitInterval.lt_one_iff_ne_one.2 h1⟩).symm⟩)
  have hreparam : δ.reparam ρ hρ hρ₀ hρ₁ = γ := by
    ext s
    obtain ⟨_, _, _, -, -, -, -, -, hrec⟩ := hX.mem_morseBrokenTrajectoryRecords.1 w.property
    have hm := hX.morseLevelPoint_eq_of_orbit hf hdense hp hr hpr hy
      (fun i ↦ ⟨(hrec i).1, hw i⟩) (hγ s)
    simp only [Path.coe_reparam, Function.comp_apply, δ, Path.cast_coe, MoorePath.toPath_apply,
      morseLevelPath_apply, length_morseLevelPath, ρ]
    rw [NNReal.coe_mul, Real.coe_toNNReal _ hL.le, coe_toNNReal]
    -- The fraction of the drop is clamped to `[0, 1]`; at either clamp, `γ s` is an end.
    rcases le_or_gt ((f p - f (γ s)) / (f p - f r)) 0 with h₀ | h₀
    · rw [projIcc_of_le_left _ h₀, Subtype.coe_mk, mul_zero, sub_zero,
        hX.morseLevelPoint_of_apply_le le_rfl, ← hm,
        hX.morseLevelPoint_of_apply_le (by linarith [(div_le_iff₀ hL).1 h₀])]
    rcases le_or_gt 1 ((f p - f (γ s)) / (f p - f r)) with h₁ | h₁
    · rw [projIcc_of_right_le _ h₁, Subtype.coe_mk, mul_one, sub_sub_cancel,
        hX.morseLevelPoint_of_le_apply w.property le_rfl, ← hm,
        hX.morseLevelPoint_of_le_apply w.property (by linarith [(one_le_div hL).1 h₁])]
    rw [projIcc_of_mem _ ⟨h₀.le, h₁.le⟩, Subtype.coe_mk, mul_div_cancel₀ _ hL.ne', sub_sub_cancel,
      hm]
  exact ⟨(Path.Homotopy.reparam δ ρ hρ hρ₀ hρ₁).cast rfl hreparam⟩

/-! ### Trajectory spaces of index difference one and the middle-level slice -/

namespace IsMorseSmale

variable (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f) {x y : criticalPoints 𝓘(ℝ, E) f}
  (hdense : Ioo (f y) (f x) ⊆ closure (range c))
  (hind : manifoldMorseIndex 𝓘(ℝ, E) f x = manifoldMorseIndex 𝓘(ℝ, E) f y + 1)

include h hf hdense hind in
/-- In index difference one, the point on the middle level of a trajectory record lies in the
middle-level slice, and the record is the record of the trajectory through it. -/
private theorem morseLevelPoint_mid_spec (w : hX.morseBrokenTrajectorySpace c x y) :
    hX.morseLevelPoint x y ((c ⁻¹' Ioo (f y) (f x)).domRestrict c) w ((f x + f y) / 2) ∈
        hX.morseTrajectorySlice x y ∧
      ∀ i, ∃ t, hX.flow t (hX.morseLevelPoint x y ((c ⁻¹' Ioo (f y) (f x)).domRestrict c) w
        ((f x + f y) / 2)) = w.val i := by
  have hx := mem_criticalPoints_iff_mfderiv_eq_zero.1 x.property
  have hy := mem_criticalPoints_iff_mfderiv_eq_zero.1 y.property
  have hdense' := subset_closure_range_domRestrict_preimage isOpen_Ioo hdense
  obtain ⟨hxy, hwB⟩ := hX.mem_morseBrokenTrajectorySpace.1 w.property
  obtain ⟨z, hz, hwz⟩ := hX.mem_morseTrajectoryRecords.1
    ((h.morseBrokenTrajectorySpace_eq_morseTrajectoryRecords hf hx hy hxy hind.le).subset
      w.property)
  have hlt := hX.value_lt_of_mem_morseBrokenTrajectoryRecords hxy hwB
  obtain ⟨hmem, hlev⟩ := hX.mapsTo_levelPoint hxy (c := (f x + f y) / 2) (by linarith)
    (by linarith) hz
  have hlev : f (hX.levelPoint ((f x + f y) / 2) z) = (f x + f y) / 2 := hlev
  have hm := hX.morseLevelPoint_eq_of_orbit hf hdense' hx hy hxy hz hwz
    (Or.inr (Or.inr ⟨_, (hX.levelPoint_def ((f x + f y) / 2) z).symm⟩))
  rw [hlev] at hm
  rw [hm]
  refine ⟨hX.mem_morseTrajectorySlice.2 ⟨hmem.1, hmem.2, hlev⟩, fun i ↦ ?_⟩
  obtain ⟨s, hs⟩ := (hwz i).2
  exact ⟨s - Flow.levelCrossingTime hX.flow f ((f x + f y) / 2) z, by
    rw [levelPoint_def, ← Flow.map_add, sub_add_cancel, hs]⟩

/-- **The trajectories of index difference one are their points on the middle level.** Under the
Morse–Smale condition, for critical points `x` and `y` with `ind x = ind y + 1` and levels of `c`
dense between `f y` and `f x`, reading off the point on the middle level `(f x + f y) / 2` is a
bijection from the trajectory space from `x` to `y` onto the middle-level slice of trajectories
from `x` to `y` (`TauCeti.IsAdaptedPseudoGradient.morseTrajectorySlice`), on which the Morse
boundary is defined. Its inverse records the level points
(`TauCeti.IsAdaptedPseudoGradient.levelPoint`) of the trajectory through a point of the slice. -/
noncomputable def morseBrokenTrajectorySpaceEquivSlice :
    hX.morseBrokenTrajectorySpace c x y ≃ hX.morseTrajectorySlice x y where
  toFun w := ⟨_, (morseLevelPoint_mid_spec h hf hdense hind w).1⟩
  invFun z := ⟨fun i ↦ hX.levelPoint ((c ⁻¹' Ioo (f y) (f x)).domRestrict c i) z,
    hX.mem_morseBrokenTrajectorySpace.2 ⟨ne_of_manifoldMorseIndex_eq_add_one hind,
      hX.morseTrajectoryRecords_subset_morseBrokenTrajectoryRecords
        (mem_criticalPoints_iff_mfderiv_eq_zero.1 x.property)
        (mem_criticalPoints_iff_mfderiv_eq_zero.1 y.property)
        (ne_of_manifoldMorseIndex_eq_add_one hind) _
        (hX.mem_morseTrajectoryRecords.2
          ⟨z, hX.morseTrajectorySlice_subset x y z.property, fun i ↦
            ⟨(hX.mapsTo_levelPoint (ne_of_manifoldMorseIndex_eq_add_one hind) i.property.1
              i.property.2 (hX.morseTrajectorySlice_subset x y z.property)).2, _,
              (hX.levelPoint_def _ _).symm⟩⟩)⟩⟩
  left_inv w := by
    obtain ⟨hm, hwm⟩ := morseLevelPoint_mid_spec h hf hdense hind w
    obtain ⟨_, _, _, -, -, -, -, -, hrec⟩ :=
      hX.mem_morseBrokenTrajectoryRecords.1 (hX.mem_morseBrokenTrajectorySpace.1 w.property).2
    refine Subtype.ext (funext fun i ↦ ?_)
    -- Both points lie on the orbit of the middle point, on the level `c i`.
    obtain ⟨t, ht⟩ := hwm i
    exact (hX.levelPoint_eq (ne_of_manifoldMorseIndex_eq_add_one hind)
      (hX.morseTrajectorySlice_subset x y hm) (by rw [ht]; exact (hrec i).1)).trans ht
  right_inv z := by
    have hxy := ne_of_manifoldMorseIndex_eq_add_one hind
    have hz := hX.morseTrajectorySlice_subset x y z.property
    refine Subtype.ext ?_
    simp only
    rw [← (hX.mem_morseTrajectorySlice.1 z.property).2.2]
    exact hX.morseLevelPoint_eq_of_orbit hf (subset_closure_range_domRestrict_preimage isOpen_Ioo
      hdense) (mem_criticalPoints_iff_mfderiv_eq_zero.1 x.property)
      (mem_criticalPoints_iff_mfderiv_eq_zero.1 y.property) hxy hz
      (fun i ↦ ⟨(hX.mapsTo_levelPoint hxy i.property.1 i.property.2 hz).2, _,
        (hX.levelPoint_def _ _).symm⟩)
      (Or.inr (Or.inr ⟨0, Flow.map_zero_apply _ _⟩))

/-- The point on the middle level of a trajectory of index difference one. -/
@[simp]
theorem coe_morseBrokenTrajectorySpaceEquivSlice_apply (w : hX.morseBrokenTrajectorySpace c x y) :
    (h.morseBrokenTrajectorySpaceEquivSlice hf hdense hind w : M) =
      hX.morseLevelPoint x y ((c ⁻¹' Ioo (f y) (f x)).domRestrict c) w ((f x + f y) / 2) :=
  (rfl)

/-- The record of a trajectory of index difference one through a point of the middle-level slice
consists of the level points of that point. -/
@[simp]
theorem coe_morseBrokenTrajectorySpaceEquivSlice_symm_apply (z : hX.morseTrajectorySlice x y) :
    ((h.morseBrokenTrajectorySpaceEquivSlice hf hdense hind).symm z : c ⁻¹' Ioo (f y) (f x) → M) =
      fun i ↦ hX.levelPoint ((c ⁻¹' Ioo (f y) (f x)).domRestrict c i) z :=
  (rfl)

/-- A trajectory record of index difference one records the trajectory through its point on the
middle level. -/
theorem exists_flow_morseBrokenTrajectorySpaceEquivSlice (w : hX.morseBrokenTrajectorySpace c x y)
    (i : c ⁻¹' Ioo (f y) (f x)) :
    ∃ t, hX.flow t (h.morseBrokenTrajectorySpaceEquivSlice hf hdense hind w) = w.val i :=
  (morseLevelPoint_mid_spec h hf hdense hind w).2 i

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
