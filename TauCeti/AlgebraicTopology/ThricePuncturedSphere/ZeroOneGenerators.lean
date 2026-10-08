/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.PeripheralLoops
public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.PuncturedNeighborhoods
import TauCeti.AlgebraicTopology.FundamentalGroup.BasepointChange
import TauCeti.AlgebraicTopology.FundamentalGroup.PuncturedStarConvex
import TauCeti.AlgebraicTopology.FundamentalGroupoid.Basic
import TauCeti.AlgebraicTopology.UniversalCover.Circle.FundamentalGroup
import TauCeti.Topology.Homotopy.Path

/-!
# The positive local generators at `0` and `1`

The standard punctured neighborhoods of the finite punctures are the punctured discs
`D₀* = {z | ‖z‖ < 1/2}` and `D₁* = {z | ‖z - 1‖ < 1/2}`. Their fundamental groups are infinite
cyclic, and this file names a positive generator of each and identifies it with the peripheral
element of the thrice-punctured sphere at the same puncture:

* `δZero` is the counterclockwise circle of radius `1/4` about `0`, based at `1/4`, and
  `δOne` is the counterclockwise circle of radius `1/4` about `1`, based at `3/4`;
* each generates the fundamental group of its punctured disc (`zpowers_δZero`, `zpowers_δOne`);
* included into `ℂ ∖ {0, 1}` and transported to the basepoint `1/2` along the real segments
  `αZero` and `αOne`, they are exactly `periph0` and `periph1`
  (`transport_δZero_eq_periph0`, `transport_δOne_eq_periph1`).

The peripheral loops `γ0` and `γ1` themselves run on the boundary circles of `D₀*` and `D₁*`, so
they cannot serve as local loops. The comparison goes through the larger punctured discs of
radius `1` about each puncture, which avoid the other puncture and contain both the peripheral
loop and the local one. The direction from the puncture is injective on their fundamental
groups, and both loops wind once around the puncture, so they are conjugate along the segment
(`Circle.homotopic_trans_of_degree_map_eq`).

This identifies the local monodromy used to fill a cover at `0` and at `1` with the first two
permutations of its triple, including their orientation. The puncture at infinity is treated in
`TauCeti.AlgebraicTopology.ThricePuncturedSphere.InfinityGenerator`.

## References

* A. Hatcher, *Algebraic Topology*, Theorem 1.7 and Proposition 1.18.
* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, London Mathematical Society Student Texts 79, Cambridge University Press, 2012,
  §1.2.7, for the punctured discs about the branch values.
-/

public section

noncomputable section

open Set Metric Complex Real

namespace TauCeti
namespace ThricePuncturedSphere

/-! ### The direction from a finite puncture -/

section Direction

variable {S : Set ThricePuncturedSphere} {c : ℂ} {R : ℝ}

/-- A punctured disc of radius at most `1` about `0` or `1` avoids both punctures. -/
private theorem ball_diff_subset_range (hc : c = 0 ∨ c = 1) (hR : R ≤ 1) :
    ball c R \ {c} ⊆ range ((↑) : ThricePuncturedSphere → ℂ) := by
  rintro w ⟨hw, hwc⟩
  rw [mem_singleton_iff] at hwc
  rw [mem_ball, dist_eq_norm] at hw
  refine ⟨⟨w, ?_, ?_⟩, rfl⟩ <;> rintro rfl <;> rcases hc with rfl | rfl
  -- Either `w` is the centre itself, or it is the other puncture, at distance `1 ≥ R`.
  all_goals first | exact hwc rfl | (norm_num at hw; linarith)

/-- A subset of `ℂ ∖ {0, 1}` that is a punctured disc of `ℂ`, read in `ℂ`. -/
private def ballHomeomorph (hS : ∀ z : ThricePuncturedSphere, z ∈ S ↔ (z : ℂ) ∈ ball c R \ {c})
    (hsub : ball c R \ {c} ⊆ range ((↑) : ThricePuncturedSphere → ℂ)) :
    S ≃ₜ ↥(ball c R \ {c}) :=
  (Homeomorph.setCongr (Set.ext hS)).trans
    (Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange hsub)

/-- The direction `(z - c) / ‖z - c‖` from the puncture `c`. -/
private def direction (hS : ∀ z : ThricePuncturedSphere, z ∈ S ↔ (z : ℂ) ∈ ball c R \ {c})
    (hsub : ball c R \ {c} ⊆ range ((↑) : ThricePuncturedSphere → ℂ)) : C(S, Circle) :=
  (c.directionFrom (ball c R)).comp ⟨ballHomeomorph hS hsub, (ballHomeomorph hS hsub).continuous⟩

private theorem coe_direction
    (hS : ∀ z : ThricePuncturedSphere, z ∈ S ↔ (z : ℂ) ∈ ball c R \ {c})
    (hsub : ball c R \ {c} ⊆ range ((↑) : ThricePuncturedSphere → ℂ)) (z : S) :
    (direction hS hsub z : ℂ) =
      (((z : ThricePuncturedSphere) : ℂ) - c) / ‖((z : ThricePuncturedSphere) : ℂ) - c‖ := by
  have h : (ballHomeomorph hS hsub z : ℂ) = (z : ThricePuncturedSphere) :=
    Topology.IsEmbedding.homeomorphOfSubsetRange_apply_coe Topology.IsEmbedding.subtypeVal hsub _
  simp [direction, h]

/-- The direction from the puncture induces a bijection on fundamental groups. -/
private theorem map_direction_bijective (hR : 0 < R)
    (hS : ∀ z : ThricePuncturedSphere, z ∈ S ↔ (z : ℂ) ∈ ball c R \ {c})
    (hsub : ball c R \ {c} ⊆ range ((↑) : ThricePuncturedSphere → ℂ)) (z : S) :
    Function.Bijective (FundamentalGroup.map (direction hS hsub) z) := by
  have hstar := (convex_ball c R).starConvex (mem_ball_self hR)
  have h := hstar.fundamentalGroup_map_directionFrom_bijective (r := R / 2) (by positivity)
    (sphere_subset_ball (by linarith)) (ballHomeomorph hS hsub z)
  have hcomp : ⇑(FundamentalGroup.map (direction hS hsub) z) =
      FundamentalGroup.map (c.directionFrom (ball c R)) (ballHomeomorph hS hsub z) ∘
        FundamentalGroup.map (⟨ballHomeomorph hS hsub, (ballHomeomorph hS hsub).continuous⟩ :
          C(S, ↥(ball c R \ {c}))) z :=
    funext fun γ => FundamentalGroupoid.map_comp_map _ _ γ
  rw [hcomp]
  have hhome : ⇑(FundamentalGroup.homeomorphMulEquiv (ballHomeomorph hS hsub) z) =
      ⇑(FundamentalGroup.map (⟨ballHomeomorph hS hsub, (ballHomeomorph hS hsub).continuous⟩ :
          C(S, ↥(ball c R \ {c}))) z) := by
    funext γ
    simp
  exact h.comp (hhome ▸ (FundamentalGroup.homeomorphMulEquiv (ballHomeomorph hS hsub) z).bijective)

/-- A loop running once counterclockwise around a circle about the puncture has direction of
degree one. -/
private theorem degree_map_direction
    (hS : ∀ z : ThricePuncturedSphere, z ∈ S ↔ (z : ℂ) ∈ ball c R \ {c})
    (hsub : ball c R \ {c} ⊆ range ((↑) : ThricePuncturedSphere → ℂ)) {x : S} (γ : Path x x)
    {r φ : ℝ} (hr : 0 < r)
    (hγ : ∀ t : unitInterval,
      ((γ t : ThricePuncturedSphere) : ℂ) = c + r * exp ((φ + 2 * π * t : ℝ) * I)) :
    Circle.degree (γ.map (direction hS hsub).continuous) = 1 := by
  refine Circle.degree_eq_of_sub_eq _ (θ := fun t => φ + 2 * π * t) (by fun_prop) (fun t => ?_)
    (by simp)
  apply Subtype.ext
  rw [Circle.coe_exp, Path.map_coe, Function.comp_apply, coe_direction, hγ t, add_sub_cancel_left,
    norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_real, Real.norm_of_nonneg hr.le,
    mul_div_cancel_left₀ _ (ofReal_ne_zero.mpr hr.ne')]

end Direction

/-! ### The puncture `0` -/

/-- The point `1/4` of the punctured neighborhood of `0`. -/
def zeroBasePt : puncturedNeighborhoodZero :=
  ⟨⟨1 / 4, by norm_num, by norm_num⟩, by rw [mem_puncturedNeighborhoodZero]; norm_num⟩

@[simp]
theorem coe_zeroBasePt : ((zeroBasePt : ThricePuncturedSphere) : ℂ) = 1 / 4 :=
  (rfl)

/-- The counterclockwise circle `t ↦ (1/4)·exp(2πit)` of radius `1/4` about `0`, based at `1/4`,
as a loop in the punctured neighborhood of `0`. -/
def δZero : Path zeroBasePt zeroBasePt where
  toFun t := ⟨⟨circleMap 0 (1 / 4) (2 * π * t), by
      have hnorm : ‖circleMap 0 (1 / 4) (2 * π * t)‖ = 1 / 4 := by simp [norm_circleMap_zero]
      constructor <;> rintro h <;> rw [h] at hnorm <;> norm_num at hnorm⟩, by
    rw [mem_puncturedNeighborhoodZero]
    simp only [norm_circleMap_zero]
    norm_num⟩
  continuous_toFun := by fun_prop
  source' := Subtype.ext (Subtype.ext (by simp [circleMap, zeroBasePt]))
  target' := Subtype.ext (Subtype.ext (by simp [circleMap, zeroBasePt]))

@[simp]
theorem coe_δZero (t : unitInterval) :
    ((δZero t : ThricePuncturedSphere) : ℂ) = circleMap 0 (1 / 4) (2 * π * t) :=
  (rfl)

/-- The real segment `t ↦ 1/2 - t/4` from the basepoint `1/2` to `1/4`. -/
def αZero : Path basePt (zeroBasePt : ThricePuncturedSphere) where
  toFun t := ⟨((1 / 2 - t / 4 : ℝ) : ℂ), by
      rw [Ne, ofReal_eq_zero]
      linarith [t.2.2], by
      rw [Ne, ← ofReal_one, ofReal_inj]
      linarith [t.2.1]⟩
  continuous_toFun := by fun_prop
  source' := Subtype.ext (by simp [coe_basePt])
  target' := Subtype.ext (by norm_num [zeroBasePt])

@[simp]
theorem coe_αZero (t : unitInterval) : (αZero t : ℂ) = ((1 / 2 - t / 4 : ℝ) : ℂ) :=
  (rfl)

private theorem mem_puncturedNeighborhoodZero_iff_mem_ball (z : ThricePuncturedSphere) :
    z ∈ puncturedNeighborhoodZero ↔ (z : ℂ) ∈ ball (0 : ℂ) (1 / 2) \ {0} := by
  simp [mem_puncturedNeighborhoodZero, z.ne_zero]

/-- The standard punctured neighborhood of `0` is path connected. -/
theorem isPathConnected_puncturedNeighborhoodZero : IsPathConnected puncturedNeighborhoodZero := by
  have := pathConnectedSpace_ball_diff_singleton (0 : ℂ) (R := 1 / 2) (by norm_num)
  exact isPathConnected_iff_pathConnectedSpace.2 (ballHomeomorph
    mem_puncturedNeighborhoodZero_iff_mem_ball
    (ball_diff_subset_range (.inl rfl) (by norm_num))).symm.pathConnectedSpace

/-- The counterclockwise circle `δZero` generates the fundamental group of the punctured
neighborhood of `0`. -/
@[simp]
theorem zpowers_δZero : Subgroup.zpowers (FundamentalGroup.fromPath (.mk δZero)) = ⊤ :=
  Circle.zpowers_fromPath_eq_top_of_degree_map_eq_one
    (map_direction_bijective (by norm_num) mem_puncturedNeighborhoodZero_iff_mem_ball
      (ball_diff_subset_range (.inl rfl) (by norm_num)) zeroBasePt).injective
    (degree_map_direction _ _ δZero (r := 1 / 4) (φ := 0) (by norm_num) fun t => by
      simp [circleMap])

/-- Include the local generator at `0` and transport it along `αZero.symm`: the result is
`periph0`. -/
theorem transport_δZero_eq_periph0 :
    (FundamentalGroup.fundamentalGroupMulEquivOfPath αZero).symm
      (FundamentalGroup.map
        (⟨Subtype.val, continuous_subtype_val⟩ : C(puncturedNeighborhoodZero, _)) zeroBasePt
        (FundamentalGroup.fromPath (.mk δZero))) = periph0 := by
  -- Compare `γ0` with the conjugated local loop inside the punctured unit disc about `0`.
  let S : Set ThricePuncturedSphere := {z | (z : ℂ) ∈ ball (0 : ℂ) 1 \ {0}}
  have hmem {z : ThricePuncturedSphere} (hz : ‖(z : ℂ)‖ < 1) : z ∈ S :=
    ⟨mem_ball_zero_iff.mpr hz, z.ne_zero⟩
  have hb : basePt ∈ S := hmem (by norm_num [coe_basePt])
  have hy : (zeroBasePt : ThricePuncturedSphere) ∈ S := hmem (by norm_num)
  have hγ (t : unitInterval) : γ0 t ∈ S := hmem (by rw [norm_coe_γ0]; norm_num)
  have hδ (t : unitInterval) : δZero.map continuous_subtype_val t ∈ S :=
    hmem (by simp [norm_circleMap_zero]; norm_num)
  have hα (t : unitInterval) : αZero t ∈ S := hmem (by
    rw [coe_αZero, norm_real, Real.norm_of_nonneg (by linarith [t.2.2])]
    linarith [t.2.1])
  have hsub := ball_diff_subset_range (c := 0) (R := 1) (.inl rfl) le_rfl
  have h := (Circle.homotopic_trans_of_degree_map_eq
    (map_direction_bijective (S := S) one_pos (fun _ => Iff.rfl) hsub ⟨basePt, hb⟩).injective
    (γ := γ0.codRestrict (x := ⟨basePt, hb⟩) (y := ⟨basePt, hb⟩) hγ)
    (δ := (δZero.map continuous_subtype_val).codRestrict (x := ⟨_, hy⟩) (y := ⟨_, hy⟩) hδ)
    (by
      rw [degree_map_direction _ _ _ (r := 1 / 2) (φ := 0) (by norm_num) fun t => by
          simp [coe_γ0, circleMap],
        degree_map_direction _ _ _ (r := 1 / 4) (φ := 0) (by norm_num) fun t => by
          simp [circleMap]])
    (αZero.codRestrict (x := ⟨basePt, hb⟩) (y := ⟨_, hy⟩) hα)).map
    ⟨Subtype.val, continuous_subtype_val⟩
  simp only [Path.map_trans, ← Path.map_symm, Path.map_codRestrict] at h
  rw [FundamentalGroup.map_apply, ← Path.Homotopic.Quotient.mk_map,
    FundamentalGroup.fundamentalGroupMulEquivOfPath_symm_apply, periph0_def,
    ← Path.Homotopic.Quotient.mk_symm, ← Path.Homotopic.Quotient.mk_trans,
    ← Path.Homotopic.Quotient.mk_trans]
  exact Quotient.sound h.symm

/-! ### The puncture `1` -/

/-- The point `3/4` of the punctured neighborhood of `1`. -/
def oneBasePt : puncturedNeighborhoodOne :=
  ⟨⟨3 / 4, by norm_num, by norm_num⟩, by rw [mem_puncturedNeighborhoodOne]; norm_num⟩

@[simp]
theorem coe_oneBasePt : ((oneBasePt : ThricePuncturedSphere) : ℂ) = 3 / 4 :=
  (rfl)

/-- The counterclockwise circle `t ↦ 1 - (1/4)·exp(2πit)` of radius `1/4` about `1`, based at
`3/4`, as a loop in the punctured neighborhood of `1`. -/
def δOne : Path oneBasePt oneBasePt where
  toFun t := ⟨⟨circleMap 1 (-(1 / 4)) (2 * π * t), by
      have hnorm : ‖circleMap 1 (-(1 / 4)) (2 * π * t) - 1‖ = 1 / 4 := by
        simp [circleMap_sub_center, norm_circleMap_zero]
      constructor <;> rintro h <;> rw [h] at hnorm <;> norm_num at hnorm⟩, by
    rw [mem_puncturedNeighborhoodOne, circleMap_sub_center, norm_circleMap_zero]
    norm_num⟩
  continuous_toFun := by fun_prop
  source' := Subtype.ext (Subtype.ext (by norm_num [circleMap, oneBasePt]))
  target' := Subtype.ext (Subtype.ext (by norm_num [circleMap, oneBasePt]))

@[simp]
theorem coe_δOne (t : unitInterval) :
    ((δOne t : ThricePuncturedSphere) : ℂ) = circleMap 1 (-(1 / 4)) (2 * π * t) :=
  (rfl)

/-- The real segment `t ↦ 1/2 + t/4` from the basepoint `1/2` to `3/4`. -/
def αOne : Path basePt (oneBasePt : ThricePuncturedSphere) where
  toFun t := ⟨((1 / 2 + t / 4 : ℝ) : ℂ), by
      rw [Ne, ofReal_eq_zero]
      linarith [t.2.1], by
      rw [Ne, ← ofReal_one, ofReal_inj]
      linarith [t.2.2]⟩
  continuous_toFun := by fun_prop
  source' := Subtype.ext (by simp [coe_basePt])
  target' := Subtype.ext (by norm_num [oneBasePt])

@[simp]
theorem coe_αOne (t : unitInterval) : (αOne t : ℂ) = ((1 / 2 + t / 4 : ℝ) : ℂ) :=
  (rfl)

private theorem mem_puncturedNeighborhoodOne_iff_mem_ball (z : ThricePuncturedSphere) :
    z ∈ puncturedNeighborhoodOne ↔ (z : ℂ) ∈ ball (1 : ℂ) (1 / 2) \ {1} := by
  simp [mem_puncturedNeighborhoodOne, dist_eq_norm, z.ne_one]

/-- The standard punctured neighborhood of `1` is path connected. -/
theorem isPathConnected_puncturedNeighborhoodOne : IsPathConnected puncturedNeighborhoodOne := by
  have := pathConnectedSpace_ball_diff_singleton (1 : ℂ) (R := 1 / 2) (by norm_num)
  exact isPathConnected_iff_pathConnectedSpace.2 (ballHomeomorph
    mem_puncturedNeighborhoodOne_iff_mem_ball
    (ball_diff_subset_range (.inr rfl) (by norm_num))).symm.pathConnectedSpace

/-- The counterclockwise circle `δOne` generates the fundamental group of the punctured
neighborhood of `1`. -/
@[simp]
theorem zpowers_δOne : Subgroup.zpowers (FundamentalGroup.fromPath (.mk δOne)) = ⊤ :=
  Circle.zpowers_fromPath_eq_top_of_degree_map_eq_one
    (map_direction_bijective (by norm_num) mem_puncturedNeighborhoodOne_iff_mem_ball
      (ball_diff_subset_range (.inr rfl) (by norm_num)) oneBasePt).injective
    (degree_map_direction _ _ δOne (r := 1 / 4) (φ := π) (by norm_num) fun t => by
      rw [coe_δOne, circleMap_neg_radius, circleMap, add_comm (2 * π * (t : ℝ)) π])

/-- Include the local generator at `1` and transport it along `αOne.symm`: the result is
`periph1`. -/
theorem transport_δOne_eq_periph1 :
    (FundamentalGroup.fundamentalGroupMulEquivOfPath αOne).symm
      (FundamentalGroup.map
        (⟨Subtype.val, continuous_subtype_val⟩ : C(puncturedNeighborhoodOne, _)) oneBasePt
        (FundamentalGroup.fromPath (.mk δOne))) = periph1 := by
  -- Compare `γ1` with the conjugated local loop inside the punctured unit disc about `1`.
  let S : Set ThricePuncturedSphere := {z | (z : ℂ) ∈ ball (1 : ℂ) 1 \ {1}}
  have hmem {z : ThricePuncturedSphere} (hz : ‖(z : ℂ) - 1‖ < 1) : z ∈ S :=
    ⟨by rwa [mem_ball, dist_eq_norm], z.ne_one⟩
  have hb : basePt ∈ S := hmem (by norm_num [coe_basePt])
  have hy : (oneBasePt : ThricePuncturedSphere) ∈ S := hmem (by norm_num)
  have hγ (t : unitInterval) : γ1 t ∈ S := hmem (by rw [norm_coe_γ1_sub_one]; norm_num)
  have hδ (t : unitInterval) : δOne.map continuous_subtype_val t ∈ S :=
    hmem (by simp [circleMap_sub_center, norm_circleMap_zero]; norm_num)
  have hα (t : unitInterval) : αOne t ∈ S := hmem (by
    rw [coe_αOne, ← ofReal_one, ← ofReal_sub, norm_real, Real.norm_of_nonpos (by linarith [t.2.2])]
    linarith [t.2.1])
  have hsub := ball_diff_subset_range (c := 1) (R := 1) (.inr rfl) le_rfl
  have h := (Circle.homotopic_trans_of_degree_map_eq
    (map_direction_bijective (S := S) one_pos (fun _ => Iff.rfl) hsub ⟨basePt, hb⟩).injective
    (γ := γ1.codRestrict (x := ⟨basePt, hb⟩) (y := ⟨basePt, hb⟩) hγ)
    (δ := (δOne.map continuous_subtype_val).codRestrict (x := ⟨_, hy⟩) (y := ⟨_, hy⟩) hδ)
    (by
      rw [degree_map_direction _ _ _ (r := 1 / 2) (φ := π) (by norm_num) fun t => by
          rw [Path.codRestrict_coe, coe_γ1, circleMap_neg_radius, circleMap,
            add_comm (2 * π * (t : ℝ)) π],
        degree_map_direction _ _ _ (r := 1 / 4) (φ := π) (by norm_num) fun t => by
          rw [Path.codRestrict_coe, Path.map_coe, Function.comp_apply, coe_δOne,
            circleMap_neg_radius, circleMap, add_comm (2 * π * (t : ℝ)) π]])
    (αOne.codRestrict (x := ⟨basePt, hb⟩) (y := ⟨_, hy⟩) hα)).map
    ⟨Subtype.val, continuous_subtype_val⟩
  simp only [Path.map_trans, ← Path.map_symm, Path.map_codRestrict] at h
  rw [FundamentalGroup.map_apply, ← Path.Homotopic.Quotient.mk_map,
    FundamentalGroup.fundamentalGroupMulEquivOfPath_symm_apply, periph1_def,
    ← Path.Homotopic.Quotient.mk_symm, ← Path.Homotopic.Quotient.mk_trans,
    ← Path.Homotopic.Quotient.mk_trans]
  exact Quotient.sound h.symm

end ThricePuncturedSphere
end TauCeti
