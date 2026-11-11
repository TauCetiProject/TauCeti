/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.OpenPartialHomeomorph.Defs
public import TauCeti.Topology.Homotopy.Extension.Basic
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.UnitInterval
import TauCeti.Analysis.Convex.Topology
import TauCeti.Topology.Homotopy.Extension.NDRPair
import TauCeti.Topology.OpenPartialHomeomorph.Continuity

/-!
# Segments in a chart have the homotopy extension property

Let `e` be an open partial homeomorphism from a Hausdorff space `X` to a proper real normed space
`E`, such as a chart of a manifold modelled on a finite-dimensional space. If the segment
`[x, y]` lies in the target of `e`, its image `e.symm '' [x, y]` in `X` has the homotopy
extension property
(`OpenPartialHomeomorph.hasHomotopyExtensionProperty_symm_image_segment`). Such an image is an
arc in `X`, or a point when `x = y`; the homotopy extension property is what makes collapsing it
to a point a homotopy equivalence (`TauCeti.HasHomotopyExtensionProperty.collapseHomotopyEquiv`).

The proof produces NDR data through `TauCeti.NDRPair.ofHomotopyRel`.

* **The retraction.** A continuous linear form `ℓ` with `ℓ (y - x) = 1`
  (`SeparatingDual.exists_eq_one`) gives the projection
  `z ↦ x + projIcc 0 1 (ℓ (z - x)) • (y - x)` of `E` onto the segment, along the kernel of `ℓ`.
  It fixes the segment and is continuous, unlike the nearest-point projection of a normed space
  which need not be strictly convex.
* **The deformation.** The segment has a thickening `thickening δ [x, y]` inside the target. It is
  convex, so the straight-line homotopy from a point to its projection stays in it; read through
  `e`, this deforms the preimage of the thickening onto the arc, relative to the arc.
* **The control function.** The distance `‖z - p z‖` from a point to its projection vanishes
  exactly on the segment. Rescaled by `2 / δ`, cut off at `1`, and extended by `1` outside the
  source of `e`, it is continuous on `X`: the points of the source where it is below `1` form a
  set whose closure is a compact subset of the source, and `X` is Hausdorff.

## Main results

* `OpenPartialHomeomorph.hasHomotopyExtensionProperty_symm_image_segment`: the image of a segment
  in the target of `e` has the homotopy extension property.

## References

* N. E. Steenrod, *A convenient category of topological spaces*, Michigan Math. J. 14 (1967),
  133–152, Section 6, for NDR pairs.
-/

public section

open Set Metric unitInterval

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The projection of `E` onto the segment `[x, y]` along the kernel of the linear form `ℓ`. When
`ℓ (y - x) = 1` it fixes the segment. -/
private noncomputable def segmentProj (ℓ : StrongDual ℝ E) (x y z : E) : E :=
  x + (projIcc (0 : ℝ) 1 zero_le_one (ℓ (z - x)) : ℝ) • (y - x)

private theorem continuous_segmentProj (ℓ : StrongDual ℝ E) (x y : E) :
    Continuous (segmentProj ℓ x y) := by
  unfold segmentProj
  fun_prop

private theorem segmentProj_mem (ℓ : StrongDual ℝ E) (x y z : E) :
    segmentProj ℓ x y z ∈ segment ℝ x y := by
  rw [segment_eq_image']
  exact mem_image_of_mem _ (projIcc (0 : ℝ) 1 zero_le_one (ℓ (z - x))).2

private theorem segmentProj_eq_self (ℓ : StrongDual ℝ E) {x y z : E}
    (hℓ : y - x ≠ 0 → ℓ (y - x) = 1) (hz : z ∈ segment ℝ x y) : segmentProj ℓ x y z = z := by
  rw [segment_eq_image'] at hz
  obtain ⟨s, hs, rfl⟩ := hz
  by_cases hxy : y - x = 0
  · simp [segmentProj, hxy]
  · simp [segmentProj, hℓ hxy, projIcc_of_mem _ hs]

/-- Every point is within `‖z - p z‖ + ‖y - x‖` of `x`, where `p` is the projection. -/
private theorem norm_sub_le_segmentProj (ℓ : StrongDual ℝ E) (x y z : E) :
    ‖z - x‖ ≤ ‖z - segmentProj ℓ x y z‖ + ‖y - x‖ := by
  have hθ := (projIcc (0 : ℝ) 1 zero_le_one (ℓ (z - x))).2
  have h : ‖segmentProj ℓ x y z - x‖ ≤ ‖y - x‖ := by
    rw [segmentProj, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hθ.1]
    exact mul_le_of_le_one_left (norm_nonneg _) hθ.2
  calc ‖z - x‖ = ‖(z - segmentProj ℓ x y z) + (segmentProj ℓ x y z - x)‖ := by
        rw [sub_add_sub_cancel]
    _ ≤ ‖z - segmentProj ℓ x y z‖ + ‖segmentProj ℓ x y z - x‖ := norm_add_le _ _
    _ ≤ _ := by gcongr

end TauCeti

namespace OpenPartialHomeomorph

open TauCeti

variable {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  (e : OpenPartialHomeomorph X E) {x y : E} {ℓ : StrongDual ℝ E} {δ : ℝ}

/-- The image under `e.symm` of a segment in the target lies in the preimage of every thickening
of the segment inside the target. -/
private theorem symm_image_segment_subset (hδ : 0 < δ) (h : segment ℝ x y ⊆ e.target) :
    e.symm '' segment ℝ x y ⊆ e.source ∩ e ⁻¹' thickening δ (segment ℝ x y) := by
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨e.map_target (h hw), by
    rw [mem_preimage, e.right_inv (h hw)]; exact self_subset_thickening hδ _ hw⟩

/-- **The deformation onto the arc.** Read through `e`, the straight-line homotopy from a point
to its projection onto the segment deforms the preimage of a convex thickening of the segment
inside the target onto the image of the segment, relative to that image. -/
private theorem exists_homotopyRel_segment (hℓ : y - x ≠ 0 → ℓ (y - x) = 1) (hδ : 0 < δ)
    (h : segment ℝ x y ⊆ e.target) (hδt : thickening δ (segment ℝ x y) ⊆ e.target) :
    ∃ r : C(↥(e.source ∩ e ⁻¹' thickening δ (segment ℝ x y)), ↥(e.symm '' segment ℝ x y)),
      Nonempty ((ContinuousMap.id _).HomotopyRel
        ((ContinuousMap.inclusion (e.symm_image_segment_subset hδ h)).comp r)
        {z | ↑z ∈ e.symm '' segment ℝ x y}) := by
  set p := segmentProj ℓ x y
  have hp : Continuous p := continuous_segmentProj ℓ x y
  set U : Set X := e.source ∩ e ⁻¹' thickening δ (segment ℝ x y)
  -- The straight-line path from a point of the thickening to its projection stays in it.
  have hline {z : E} (hz : z ∈ thickening δ (segment ℝ x y)) (t : I) :
      z + (t : ℝ) • (p z - z) ∈ thickening δ (segment ℝ x y) :=
    ((convex_segment x y).thickening δ).add_smul_sub_mem hz
      (self_subset_thickening hδ _ (segmentProj_mem ℓ x y z)) ⟨t.2.1, t.2.2⟩
  have hcontU : Continuous fun z : U => e z :=
    e.continuousOn.comp_continuous continuous_subtype_val fun z => z.2.1
  have hlineU (q : I × U) : e.symm (e q.2 + (q.1 : ℝ) • (p (e q.2) - e q.2)) ∈ U := by
    have hT := hline q.2.2.2 q.1
    exact ⟨e.map_target (hδt hT), by rw [mem_preimage, e.right_inv (hδt hT)]; exact hT⟩
  let r : C(U, e.symm '' segment ℝ x y) :=
    ⟨fun z => ⟨e.symm (p (e z)), mem_image_of_mem _ (segmentProj_mem ℓ x y _)⟩,
      (e.continuousOn_symm.comp_continuous (hp.comp hcontU)
        fun z => h (segmentProj_mem ℓ x y _)).subtype_mk _⟩
  refine ⟨r, ⟨{ toFun := fun q => ⟨e.symm (e q.2 + (q.1 : ℝ) • (p (e q.2) - e q.2)), hlineU q⟩
                continuous_toFun := ?_
                map_zero_left := fun z => Subtype.ext <| by simp [e.left_inv z.2.1]
                map_one_left := fun z => Subtype.ext <| by simp [r]
                prop' := fun t z hz => Subtype.ext <| ?_ }⟩⟩
  · exact (e.continuousOn_symm.comp_continuous ((hcontU.comp continuous_snd).add
      ((continuous_subtype_val.comp continuous_fst).smul
        ((hp.comp (hcontU.comp continuous_snd)).sub (hcontU.comp continuous_snd))))
      fun q => hδt (hline q.2.2.2 q.1)).subtype_mk _
  · obtain ⟨w, hw, hwz⟩ := hz
    have hez : e z = w := by rw [← hwz, e.right_inv (h hw)]
    have hpw : p w = w := segmentProj_eq_self ℓ hℓ hw
    simp [hez, hpw, hwz]

/-- **The control function.** The distance `‖z - p z‖` from a point to its projection onto the
segment, rescaled by `2 / δ`, cut off at `1` and read through `e`, extends by `1` to a continuous
function on `X`. It vanishes exactly on the image of the segment and is less than `1` only on the
preimage of the thickening. -/
private theorem exists_control_segment [T2Space X] [ProperSpace E]
    (hℓ : y - x ≠ 0 → ℓ (y - x) = 1) (hδ : 0 < δ) (h : segment ℝ x y ⊆ e.target)
    (hδt : thickening δ (segment ℝ x y) ⊆ e.target) :
    ∃ f : C(X, I), (∀ z, f z = 0 ↔ z ∈ e.symm '' segment ℝ x y) ∧
      ∀ z, f z < 1 → z ∈ e.source ∩ e ⁻¹' thickening δ (segment ℝ x y) := by
  classical
  set p := segmentProj ℓ x y
  set ρ : E → ℝ := fun z => 2 / δ * ‖z - p z‖
  have hρ : Continuous ρ :=
    continuous_const.mul (continuous_id.sub (continuous_segmentProj ℓ x y)).norm
  -- Where `ρ < 2`, a point is closer than `δ` to the segment.
  have hρlt {z : E} (hz : ρ z < 2) : z ∈ thickening δ (segment ℝ x y) := by
    refine mem_thickening_iff.2 ⟨p z, segmentProj_mem ℓ x y z, ?_⟩
    simp only [ρ] at hz
    rw [div_mul_eq_mul_div, div_lt_iff₀ hδ] at hz
    rw [dist_eq_norm]
    linarith
  -- The points where `ρ ≤ 1` form a compact subset of the target.
  set K : Set E := {z | ρ z ≤ 1}
  have hK : IsCompact K := by
    refine isCompact_of_isClosed_isBounded (isClosed_le hρ continuous_const) ?_
    refine isBounded_closedBall (x := x) (r := δ / 2 + ‖y - x‖) |>.subset fun z hz => ?_
    simp only [K, mem_ofPred_eq, ρ] at hz
    rw [div_mul_eq_mul_div, div_le_iff₀ hδ] at hz
    rw [mem_closedBall, dist_eq_norm]
    linarith [norm_sub_le_segmentProj ℓ x y z]
  have hKt : K ⊆ e.target := fun z hz => hδt (hρlt (lt_of_le_of_lt hz.out one_lt_two))
  have hproj : Continuous (projIcc (0 : ℝ) 1 zero_le_one) := continuous_projIcc
  refine ⟨⟨_, e.continuous_ite_source_of_eq_off_compact (hproj.comp hρ) hK hKt fun z hz =>
    projIcc_eq_one.2 (le_of_lt (not_le.1 hz))⟩, fun z => ?_, fun z hz => ?_⟩
  · rw [e.symm_image_eq_source_inter_preimage h]
    by_cases hzs : z ∈ e.source
    · have hδ' : 0 < 2 / δ := div_pos two_pos hδ
      simp only [ContinuousMap.coe_mk, hzs, ↓reduceIte, Function.comp_apply, projIcc_eq_zero,
        mem_inter_iff, true_and, mem_preimage, ρ]
      have hiff (a : ℝ) : 2 / δ * a ≤ 0 ↔ a ≤ 0 :=
        ⟨fun ha => nonpos_of_mul_nonpos_right ha hδ',
          fun ha => mul_nonpos_of_nonneg_of_nonpos hδ'.le ha⟩
      rw [hiff, norm_le_zero_iff, sub_eq_zero]
      exact ⟨fun hz => hz ▸ segmentProj_mem ℓ x y _, fun hz => (segmentProj_eq_self ℓ hℓ hz).symm⟩
    · simp [hzs]
  · by_cases hzs : z ∈ e.source
    · simp only [ContinuousMap.coe_mk, hzs, ↓reduceIte, Function.comp_apply] at hz
      refine ⟨hzs, hρlt ?_⟩
      by_contra hge
      exact hz.ne (projIcc_eq_one.2 (by linarith [not_lt.1 hge]))
    · simp [hzs] at hz

/-- **A segment in the target of an open partial homeomorphism has the homotopy extension
property.** If `e` is an open partial homeomorphism from a Hausdorff space `X` to a proper real
normed space `E`, and the segment `[x, y]` lies in the target of `e`, then its image
`e.symm '' [x, y]` in `X` has the homotopy extension property. -/
theorem hasHomotopyExtensionProperty_symm_image_segment [T2Space X] [ProperSpace E]
    (h : segment ℝ x y ⊆ e.target) :
    HasHomotopyExtensionProperty (e.symm '' segment ℝ x y) := by
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : StrongDual ℝ E, y - x ≠ 0 → ℓ (y - x) = 1 := by
    by_cases hxy : y - x = 0
    · exact ⟨0, fun h => absurd hxy h⟩
    · obtain ⟨ℓ, hℓ⟩ := SeparatingDual.exists_eq_one (R := ℝ) hxy
      exact ⟨ℓ, fun _ => hℓ⟩
  obtain ⟨δ, hδ, hδt⟩ := (isCompact_segment ℝ x y).exists_thickening_subset_open e.open_target h
  obtain ⟨r, ⟨D⟩⟩ := e.exists_homotopyRel_segment hℓ hδ h hδt
  obtain ⟨f, hf, hfU⟩ := e.exists_control_segment hℓ hδ h hδt
  exact (NDRPair.ofHomotopyRel _ D f hf hfU).hasHomotopyExtensionProperty

end OpenPartialHomeomorph
