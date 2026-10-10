/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.PuncturedStarConvex
public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.PeripheralLoops
public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.PuncturedNeighborhoods
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
import TauCeti.GroupTheory.SpecificGroups.Cyclic.Basic
import TauCeti.AlgebraicTopology.FundamentalGroupoid.Basic
import TauCeti.Topology.Homotopy.Path

/-!
# Local peripheral generators at the finite punctures

The counterclockwise circles of radius `1/4` about `0` and `1` generate the fundamental groups
of their standard punctured neighborhoods. Including them into the thrice-punctured sphere
and transporting along radial segments gives `periph0` and `periph1`, respectively. Their
transported conjugacy classes are therefore independent of the connecting path.

These identifications allow the local monodromy of a cover at the finite punctures to be read
from the first two permutations of its monodromy triple. The smaller circles are necessary:
the globally based loops have radius `1/2` and lie on, not inside, the neighborhood boundaries.

The local computation uses `StarConvex.fundamentalGroup_map_directionFrom_bijective` and
`Circle.fundamentalGroupMulEquiv_fromPath`. Radial deformation compares the small circle with
the globally based loop; the second puncture is transported by the holomorphic map `z ↦ 1 - z`.

## References

* A. Hatcher, *Algebraic Topology*, Theorem 1.7 and Proposition 1.18.
* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, §2.7, for peripheral monodromy.
-/

public section

noncomputable section

open Set Metric Complex

namespace TauCeti
namespace ThricePuncturedSphere

private def zeroBallHomeomorph : puncturedNeighborhoodZero ≃ₜ
    ↥(ball (0 : ℂ) (1 / 2) \ {0}) :=
  puncturedNeighborhoodZeroHomeomorphPuncturedDiscOneHalf.trans
    (Homeomorph.setCongr (by
      ext w
      simp only [mem_puncturedDiscOneHalf, mem_sdiff, mem_ball, dist_zero_right,
        mem_singleton_iff, norm_pos_iff]
      tauto))

/-- The standard punctured neighborhood of `0` is path connected. -/
theorem isPathConnected_puncturedNeighborhoodZero : IsPathConnected puncturedNeighborhoodZero := by
  have := pathConnectedSpace_ball_diff_singleton (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)
  exact isPathConnected_iff_pathConnectedSpace.2 zeroBallHomeomorph.symm.pathConnectedSpace

/-- The standard punctured neighborhood of `1` is path connected. -/
theorem isPathConnected_puncturedNeighborhoodOne : IsPathConnected puncturedNeighborhoodOne := by
  have := isPathConnected_iff_pathConnectedSpace.1 isPathConnected_puncturedNeighborhoodZero
  exact isPathConnected_iff_pathConnectedSpace.2
    puncturedNeighborhoodOneHomeomorphZero.symm.pathConnectedSpace

/-- The direction of the affine coordinate at the puncture `0`. -/
def directionAtZero : C(puncturedNeighborhoodZero, Circle) :=
  ((0 : ℂ).directionFrom (ball 0 (1 / 2))).comp
    ⟨zeroBallHomeomorph, zeroBallHomeomorph.continuous⟩

/-- The direction at `0` is the normalization of `z`. -/
@[simp]
theorem coe_directionAtZero (z : puncturedNeighborhoodZero) :
    (directionAtZero z : ℂ) = ((z : ThricePuncturedSphere) : ℂ) /
      ‖((z : ThricePuncturedSphere) : ℂ)‖ := by
  simp [directionAtZero, zeroBallHomeomorph, Homeomorph.setCongr]

private theorem map_zeroDirection_bijective (z : puncturedNeighborhoodZero) :
    Function.Bijective (FundamentalGroup.map directionAtZero z) := by
  have hstar := (convex_ball (0 : ℂ) (1 / 2)).starConvex (mem_ball_self (by norm_num))
  have h := hstar.fundamentalGroup_map_directionFrom_bijective (r := 1 / 4) (by norm_num)
    (sphere_subset_ball (by norm_num)) (zeroBallHomeomorph z)
  have hcomp : ⇑(FundamentalGroup.map directionAtZero z) =
      FundamentalGroup.map ((0 : ℂ).directionFrom (ball 0 (1 / 2))) (zeroBallHomeomorph z) ∘
        FundamentalGroup.map
          (⟨zeroBallHomeomorph, zeroBallHomeomorph.continuous⟩ :
            C(puncturedNeighborhoodZero, _)) z := by
    dsimp only [directionAtZero]
    exact funext fun γ => FundamentalGroupoid.map_comp_map _ _ γ
  rw [hcomp]
  have hhome : ⇑(FundamentalGroup.homeomorphMulEquiv zeroBallHomeomorph z) =
      ⇑(FundamentalGroup.map
        (⟨zeroBallHomeomorph, zeroBallHomeomorph.continuous⟩ :
          C(puncturedNeighborhoodZero, _)) z) := by
    funext γ
    simp
  exact h.comp (hhome ▸ (FundamentalGroup.homeomorphMulEquiv zeroBallHomeomorph z).bijective)

/-- Winding number about `0` identifies the local fundamental group with `ℤ`. -/
def zeroFundamentalGroupMulEquivInt (z : puncturedNeighborhoodZero) :
    FundamentalGroup puncturedNeighborhoodZero z ≃* Multiplicative ℤ :=
  (MulEquiv.ofBijective (FundamentalGroup.map directionAtZero z)
    (map_zeroDirection_bijective z)).trans (Circle.fundamentalGroupMulEquiv _)

/-- The winding number is the degree of the normalized affine coordinate of a loop. -/
theorem zeroFundamentalGroupMulEquivInt_fromPath {z : puncturedNeighborhoodZero}
    (γ : Path z z) :
    zeroFundamentalGroupMulEquivInt z (FundamentalGroup.fromPath (.mk γ)) =
      Multiplicative.ofAdd (Circle.degree (γ.map directionAtZero.continuous)) := by
  simp only [zeroFundamentalGroupMulEquivInt, MulEquiv.trans_apply,
    MulEquiv.ofBijective_apply, FundamentalGroup.map_apply,
    ← Path.Homotopic.Quotient.mk_map, Circle.fundamentalGroupMulEquiv_fromPath]

/-- The point `1/4` inside the standard neighborhood of `0`. -/
def zeroBasePt : puncturedNeighborhoodZero :=
  ⟨⟨1 / 4, by norm_num⟩, by norm_num⟩

@[simp]
theorem coe_zeroBasePt : ((zeroBasePt : ThricePuncturedSphere) : ℂ) = 1 / 4 := (rfl)

/-- The counterclockwise circle of radius `1/4` about `0`, inside its local neighborhood. -/
def δZero : Path zeroBasePt zeroBasePt where
  toFun t := ⟨⟨circleMap 0 (1 / 4) (2 * Real.pi * t), by
    have hnorm : ‖circleMap 0 (1 / 4) (2 * Real.pi * t)‖ = 1 / 4 := by
      simp [norm_circleMap_zero]
    constructor <;> rintro h <;> rw [h] at hnorm <;> norm_num at hnorm⟩,
    by norm_num [norm_circleMap_zero]⟩
  continuous_toFun := by fun_prop
  source' := by ext; simp [zeroBasePt, circleMap]
  target' := by ext; simp [zeroBasePt, circleMap]

@[simp]
theorem coe_δZero (t : unitInterval) :
    (((δZero t : puncturedNeighborhoodZero) : ThricePuncturedSphere) : ℂ) =
      circleMap 0 (1 / 4) (2 * Real.pi * t) := (rfl)

private theorem zeroDirection_δZero (t : unitInterval) :
    directionAtZero (δZero t) = Circle.exp (2 * Real.pi * t) := by
  apply Subtype.ext
  rw [coe_directionAtZero, coe_δZero]
  rw [norm_circleMap_zero]
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
  simp only [circleMap_zero, Circle.coe_exp]
  push_cast
  ring

/-- The local circle has positive winding number one. -/
@[simp]
theorem zeroFundamentalGroupMulEquivInt_δZero :
    zeroFundamentalGroupMulEquivInt zeroBasePt (FundamentalGroup.fromPath (.mk δZero)) =
      Multiplicative.ofAdd 1 := by
  rw [zeroFundamentalGroupMulEquivInt_fromPath]
  congr 1
  exact Circle.degree_eq_of_sub_eq _ (θ := fun t => 2 * Real.pi * t)
    (by fun_prop) (fun t => (zeroDirection_δZero t).symm) (by simp)

/-- The counterclockwise small circle generates the local fundamental group at `0`. -/
@[simp]
theorem zpowers_δZero : Subgroup.zpowers (FundamentalGroup.fromPath (.mk δZero)) = ⊤ :=
  (zeroFundamentalGroupMulEquivInt zeroBasePt).zpowers_eq_top_of_apply_eq_ofAdd_one
    zeroFundamentalGroupMulEquivInt_δZero

private def radiusCircle (r : ℝ) (hr : 0 < r) (hr1 : r < 1) : C(Circle, ThricePuncturedSphere) :=
  ⟨fun z => ⟨r * (z : ℂ), by
    have hn : ‖(r : ℂ) * (z : ℂ)‖ = r := by simp [hr.le]
    constructor <;> rintro h <;> rw [h] at hn
    · norm_num at hn; linarith
    · norm_num at hn; linarith⟩, by fun_prop⟩

private def shrinkCircle : (radiusCircle (1 / 2) (by norm_num) (by norm_num)).Homotopy
    (radiusCircle (1 / 4) (by norm_num) (by norm_num)) where
  toFun p := radiusCircle (1 / 2 - (p.1 : ℝ) / 4)
    (by linarith [p.1.2.2]) (by linarith [p.1.2.1]) p.2
  continuous_toFun := by
    dsimp only [radiusCircle, ContinuousMap.coe_mk]
    fun_prop
  map_zero_left z := by ext; simp [radiusCircle]
  map_one_left z := by ext; norm_num [radiusCircle]

private theorem coe_shrinkCircle (t : unitInterval) (z : Circle) :
    (shrinkCircle (t, z) : ℂ) = (1 / 2 - (t : ℝ) / 4 : ℝ) * (z : ℂ) := (rfl)

/-- The radial segment from the global basepoint `1/2` to the local basepoint `1/4`. -/
def αZero : Path basePt (zeroBasePt : ThricePuncturedSphere) :=
  (shrinkCircle.evalAt 1).cast (by ext; simp [radiusCircle, coe_basePt])
    (by ext; simp [radiusCircle])

@[simp]
theorem coe_αZero (t : unitInterval) : (αZero t : ℂ) = 1 / 2 - (t : ℝ) / 4 := by
  rw [αZero, Path.cast_coe, ContinuousMap.Homotopy.evalAt_apply]
  rw [coe_shrinkCircle]
  simp

private theorem γ0_trans_αZero_homotopic :
    (γ0.trans αZero).Homotopic
      (αZero.trans (δZero.map continuous_subtype_val)) := by
  have h := Path.Homotopic.map_trans_evalAt shrinkCircle Circle.expLoop
  have h0 : radiusCircle (1 / 2) (by norm_num) (by norm_num) 1 = basePt := by
    ext; simp [radiusCircle, coe_basePt]
  have h1 : radiusCircle (1 / 4) (by norm_num) (by norm_num) 1 =
      (zeroBasePt : ThricePuncturedSphere) := by ext; simp [radiusCircle]
  convert h.pathCast h0.symm h1.symm using 1 <;> ext t <;>
    simp only [Path.cast_coe, Path.trans_apply, Path.map_coe,
      ContinuousMap.Homotopy.evalAt_apply, Function.comp_apply] <;>
    split_ifs
  · simp [radiusCircle, circleMap_zero, Circle.coe_exp]
  · rw [αZero, Path.cast_coe, ContinuousMap.Homotopy.evalAt_apply]
  · rw [αZero, Path.cast_coe, ContinuousMap.Homotopy.evalAt_apply]
  · simp [radiusCircle, circleMap_zero, Circle.coe_exp]

/-- Include the local generator at `0` and transport back along the radial segment:
the result is exactly `periph0`. -/
theorem transport_δZero_eq_periph0 :
    (FundamentalGroup.fundamentalGroupMulEquivOfPath αZero).symm
      (FundamentalGroup.map
        (⟨Subtype.val, continuous_subtype_val⟩ : C(puncturedNeighborhoodZero, _)) zeroBasePt
        (FundamentalGroup.fromPath (.mk δZero))) = periph0 := by
  rw [FundamentalGroup.map_apply, ← Path.Homotopic.Quotient.mk_map,
    periph0_def]
  exact fundamentalGroupMulEquivOfPath_symm_fromPath_of_homotopic γ0_trans_αZero_homotopic

/-- The point `3/4` inside the standard neighborhood of `1`. -/
def oneBasePt : puncturedNeighborhoodOne :=
  puncturedNeighborhoodOneHomeomorphZero.symm zeroBasePt

/-- The local basepoint at `1` is the image of the local basepoint at `0` under `z ↦ 1 - z`. -/
theorem oneBasePt_def :
    oneBasePt = puncturedNeighborhoodOneHomeomorphZero.symm zeroBasePt := (rfl)

@[simp]
theorem coe_oneBasePt : ((oneBasePt : ThricePuncturedSphere) : ℂ) = 3 / 4 := by
  rw [oneBasePt_def, coe_puncturedNeighborhoodOneHomeomorphZero_symm_apply, coe_mob01,
    coe_zeroBasePt]
  norm_num

/-- The counterclockwise small circle about `1`, obtained from `δZero` by `z ↦ 1 - z`. -/
def δOne : Path oneBasePt oneBasePt :=
  (δZero.map puncturedNeighborhoodOneHomeomorphZero.symm.continuous).cast
    oneBasePt_def oneBasePt_def

@[simp]
theorem coe_δOne (t : unitInterval) :
    (((δOne t : puncturedNeighborhoodOne) : ThricePuncturedSphere) : ℂ) =
      1 - circleMap 0 (1 / 4) (2 * Real.pi * t) := by
  simp only [δOne, Path.cast_coe, Path.map_coe, Function.comp_apply]
  rw [coe_puncturedNeighborhoodOneHomeomorphZero_symm_apply, coe_mob01, coe_δZero]

/-- Winding number in the coordinate `1 - z` identifies the local group at `1` with `ℤ`.
This holomorphic coordinate has the same orientation as `z - 1`. -/
def oneFundamentalGroupMulEquivInt (z : puncturedNeighborhoodOne) :
    FundamentalGroup puncturedNeighborhoodOne z ≃* Multiplicative ℤ :=
  (FundamentalGroup.homeomorphMulEquiv puncturedNeighborhoodOneHomeomorphZero z).trans
    (zeroFundamentalGroupMulEquivInt (puncturedNeighborhoodOneHomeomorphZero z))

/-- Winding number at `1` is the degree after applying the coordinate `1 - z` and normalizing. -/
theorem oneFundamentalGroupMulEquivInt_fromPath {z : puncturedNeighborhoodOne}
    (γ : Path z z) :
    oneFundamentalGroupMulEquivInt z (FundamentalGroup.fromPath (.mk γ)) =
      Multiplicative.ofAdd (Circle.degree
        ((γ.map puncturedNeighborhoodOneHomeomorphZero.continuous).map
          directionAtZero.continuous)) := by
  simp only [oneFundamentalGroupMulEquivInt, MulEquiv.trans_apply,
    FundamentalGroup.homeomorphMulEquiv_apply, FundamentalGroup.mapOfEq_apply,
    ← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast,
    Path.cast_rfl_rfl, zeroFundamentalGroupMulEquivInt_fromPath]

/-- The local circle at `1` has positive winding number one. -/
@[simp]
theorem oneFundamentalGroupMulEquivInt_δOne :
    oneFundamentalGroupMulEquivInt oneBasePt (FundamentalGroup.fromPath (.mk δOne)) =
      Multiplicative.ofAdd 1 := by
  rw [oneFundamentalGroupMulEquivInt_fromPath]
  congr 1
  apply Circle.degree_eq_of_sub_eq _ (θ := fun t => 2 * Real.pi * t) (by fun_prop) ?_ (by simp)
  intro t
  simp only [δOne, Path.cast_coe, Path.map_coe, Function.comp_apply,
    Homeomorph.apply_symm_apply]
  exact (zeroDirection_δZero t).symm

/-- The counterclockwise small circle generates the local fundamental group at `1`. -/
@[simp]
theorem zpowers_δOne : Subgroup.zpowers (FundamentalGroup.fromPath (.mk δOne)) = ⊤ :=
  (oneFundamentalGroupMulEquivInt oneBasePt).zpowers_eq_top_of_apply_eq_ofAdd_one
    oneFundamentalGroupMulEquivInt_δOne

/-- The radial segment from the global basepoint `1/2` to the local basepoint `3/4`. -/
def αOne : Path basePt (oneBasePt : ThricePuncturedSphere) :=
  (αZero.map mob01.continuous).cast mob01_basePt.symm
    ((congrArg Subtype.val oneBasePt_def).trans
      (coe_puncturedNeighborhoodOneHomeomorphZero_symm_apply zeroBasePt))

@[simp]
theorem coe_αOne (t : unitInterval) : (αOne t : ℂ) = 1 / 2 + (t : ℝ) / 4 := by
  rw [αOne, Path.cast_coe, Path.map_coe, Function.comp_apply, coe_mob01, coe_αZero]
  ring

private theorem γ1_trans_αOne_homotopic :
    (γ1.trans αOne).Homotopic
      (αOne.trans (δOne.map continuous_subtype_val)) := by
  have h := (γ0_trans_αZero_homotopic.map (⟨mob01, mob01.continuous⟩ : C(_, _))).pathCast
    mob01_basePt.symm ((congrArg Subtype.val oneBasePt_def).trans
      (coe_puncturedNeighborhoodOneHomeomorphZero_symm_apply zeroBasePt))
  convert h using 1 <;> ext t <;>
    simp only [Path.cast_coe, Path.map_coe, Path.trans_apply, Function.comp_apply] <;>
    split_ifs
  · simp
  · rw [αOne, Path.cast_coe, Path.map_coe, Function.comp_apply]
    rfl
  · rw [αOne, Path.cast_coe, Path.map_coe, Function.comp_apply]
    rfl
  · simp only [δOne, Path.cast_coe, Path.map_coe, Function.comp_apply]
    exact congrArg Subtype.val
      (coe_puncturedNeighborhoodOneHomeomorphZero_symm_apply (δZero _))

/-- Include the local generator at `1` and transport back along the radial segment:
the result is exactly `periph1`. -/
theorem transport_δOne_eq_periph1 :
    (FundamentalGroup.fundamentalGroupMulEquivOfPath αOne).symm
      (FundamentalGroup.map
        (⟨Subtype.val, continuous_subtype_val⟩ : C(puncturedNeighborhoodOne, _)) oneBasePt
        (FundamentalGroup.fromPath (.mk δOne))) = periph1 := by
  rw [FundamentalGroup.map_apply, ← Path.Homotopic.Quotient.mk_map,
    periph1_def]
  exact fundamentalGroupMulEquivOfPath_symm_fromPath_of_homotopic γ1_trans_αOne_homotopic

/-- Transport along any connecting path gives the peripheral conjugacy class at `0`. -/
theorem conjClassesEquivOfPath_δZero {x : ThricePuncturedSphere}
    (γ : Path (zeroBasePt : ThricePuncturedSphere) x) :
    FundamentalGroup.conjClassesEquivOfPath γ
      (ConjClasses.mk (FundamentalGroup.map
        (⟨Subtype.val, continuous_subtype_val⟩ : C(puncturedNeighborhoodZero, _)) zeroBasePt
        (FundamentalGroup.fromPath (.mk δZero)))) = periph0Class x := by
  have h := congrArg ConjClasses.mk
    ((MulEquiv.symm_apply_eq _).mp transport_δZero_eq_periph0)
  rw [← FundamentalGroup.conjClassesEquivOfPath_mk] at h
  rw [h, conjClassesEquivOfPath_mk_periph0, conjClassesEquivOfPath_periph0Class]

/-- Transport along any connecting path gives the peripheral conjugacy class at `1`. -/
theorem conjClassesEquivOfPath_δOne {x : ThricePuncturedSphere}
    (γ : Path (oneBasePt : ThricePuncturedSphere) x) :
    FundamentalGroup.conjClassesEquivOfPath γ
      (ConjClasses.mk (FundamentalGroup.map
        (⟨Subtype.val, continuous_subtype_val⟩ : C(puncturedNeighborhoodOne, _)) oneBasePt
        (FundamentalGroup.fromPath (.mk δOne)))) = periph1Class x := by
  have h := congrArg ConjClasses.mk
    ((MulEquiv.symm_apply_eq _).mp transport_δOne_eq_periph1)
  rw [← FundamentalGroup.conjClassesEquivOfPath_mk] at h
  rw [h, conjClassesEquivOfPath_mk_periph1, conjClassesEquivOfPath_periph1Class]

end ThricePuncturedSphere
end TauCeti
