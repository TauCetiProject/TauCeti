/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.PuncturedStarConvex
public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.LoopAtInfinity
public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.PuncturedNeighborhoods
import TauCeti.AlgebraicTopology.FundamentalGroup.BasepointChange
import TauCeti.AlgebraicTopology.FundamentalGroupoid.Basic
import TauCeti.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# The positive local generator at infinity

The standard punctured neighborhood of infinity is `D∞* = {z | 2 < ‖z‖}`. Its coordinate
`w = 1/z` identifies it with the punctured disc of radius `1/2`, so it is path connected
(`isPathConnected_puncturedNeighborhoodInf`). Taking the direction of `w` and then the degree of a
circle loop identifies its fundamental group with `ℤ`.

The clockwise large-circle loop `δ.symm`, restricted to `D∞*`, has degree `+1` in this
coordinate. It therefore generates the local fundamental group. Under inclusion into the
thrice-punctured sphere and transport to the global basepoint along `αPlus.symm`, it is exactly
`periphInf`. Transport along any other path has the same conjugacy class. This identifies the
local monodromy used to fill a cover at infinity with the third permutation of its triple,
including its orientation.

The computation reuses `StarConvex.fundamentalGroup_map_directionFrom_bijective`,
`Circle.fundamentalGroupMulEquiv_fromPath`, and the large-circle identity
`periphInf_eq_fromPath`.

## References

* A. Hatcher, *Algebraic Topology*, Theorem 1.7 and Proposition 1.18.
* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, pp. 125–126, for the peripheral loops around the three punctures.
-/

public section

noncomputable section

open Set Metric Complex

namespace TauCeti
namespace ThricePuncturedSphere

private def infBallHomeomorph : puncturedNeighborhoodInf ≃ₜ
    ↥(ball (0 : ℂ) (1 / 2) \ {0}) :=
  puncturedNeighborhoodInfHomeomorphPuncturedDiscOneHalf.trans
    (Homeomorph.setCongr (by
      ext w
      simp only [mem_puncturedDiscOneHalf, mem_sdiff, mem_ball, dist_zero_right,
        mem_singleton_iff, norm_pos_iff]
      tauto))

/-- The direction of the local coordinate `w = 1/z` at infinity. -/
def directionAtInf : C(puncturedNeighborhoodInf, Circle) :=
  ((0 : ℂ).directionFrom (ball 0 (1 / 2))).comp
    (⟨infBallHomeomorph, infBallHomeomorph.continuous⟩ :
      C(puncturedNeighborhoodInf, ↥(ball (0 : ℂ) (1 / 2) \ {0})))

/-- The local direction at infinity is the normalization of `1/z`. -/
@[simp]
theorem coe_directionAtInf (z : puncturedNeighborhoodInf) :
    (directionAtInf z : ℂ) = (1 / (z : ThricePuncturedSphere)) /
      ‖1 / ((z : ThricePuncturedSphere) : ℂ)‖ := by
  simp [directionAtInf, infBallHomeomorph, Homeomorph.setCongr]

/-- The local direction induces a bijection on fundamental groups at every local basepoint. -/
theorem map_directionAtInf_bijective (z : puncturedNeighborhoodInf) :
    Function.Bijective (FundamentalGroup.map directionAtInf z) := by
  have hstar := (convex_ball (0 : ℂ) (1 / 2)).starConvex (mem_ball_self (by norm_num))
  have h := hstar.fundamentalGroup_map_directionFrom_bijective (r := 1 / 4) (by norm_num)
    (sphere_subset_ball (by norm_num)) (infBallHomeomorph z)
  have hcomp : ⇑(FundamentalGroup.map directionAtInf z) =
      FundamentalGroup.map ((0 : ℂ).directionFrom (ball 0 (1 / 2))) (infBallHomeomorph z) ∘
        (FundamentalGroup.map (⟨infBallHomeomorph, infBallHomeomorph.continuous⟩ :
          C(puncturedNeighborhoodInf, ↥(ball (0 : ℂ) (1 / 2) \ {0}))) z) := by
    dsimp only [directionAtInf]
    exact funext fun γ => FundamentalGroupoid.map_comp_map _ _ γ
  rw [hcomp]
  have hhome : ⇑(FundamentalGroup.homeomorphMulEquiv infBallHomeomorph z) =
      ⇑(FundamentalGroup.map
        (⟨infBallHomeomorph, infBallHomeomorph.continuous⟩ :
          C(puncturedNeighborhoodInf, ↥(ball (0 : ℂ) (1 / 2) \ {0}))) z) := by
    funext γ
    simp
  exact h.comp (hhome ▸ (FundamentalGroup.homeomorphMulEquiv infBallHomeomorph z).bijective)

/-- Winding number in the coordinate `w = 1/z` identifies `π₁(D∞*, z)` with `ℤ`. -/
def infFundamentalGroupMulEquivInt (z : puncturedNeighborhoodInf) :
    FundamentalGroup puncturedNeighborhoodInf z ≃* Multiplicative ℤ :=
  (MulEquiv.ofBijective (FundamentalGroup.map directionAtInf z)
    (map_directionAtInf_bijective z)).trans (Circle.fundamentalGroupMulEquiv _)

/-- The local winding number of a loop is the degree of its direction in the infinity chart. -/
theorem infFundamentalGroupMulEquivInt_fromPath {z : puncturedNeighborhoodInf} (γ : Path z z) :
    infFundamentalGroupMulEquivInt z (FundamentalGroup.fromPath (.mk γ)) =
      Multiplicative.ofAdd (Circle.degree (γ.map directionAtInf.continuous)) := by
  simp only [infFundamentalGroupMulEquivInt, MulEquiv.trans_apply,
    MulEquiv.ofBijective_apply, FundamentalGroup.map_apply,
    ← Path.Homotopic.Quotient.mk_map, Circle.fundamentalGroupMulEquiv_fromPath]

/-- The standard punctured neighborhood of infinity is path connected: in the coordinate `w = 1/z`
it is a punctured disc, which is homotopy equivalent to a circle. -/
theorem isPathConnected_puncturedNeighborhoodInf : IsPathConnected puncturedNeighborhoodInf := by
  have : PathConnectedSpace (sphere (0 : ℂ) (1 / 4)) := by
    refine isPathConnected_iff_pathConnectedSpace.1 (isPathConnected_sphere ?_ 0 (by norm_num))
    rw [Complex.rank_real_complex]
    exact Nat.one_lt_ofNat
  have hstar := (convex_ball (0 : ℂ) (1 / 2)).starConvex (mem_ball_self (by norm_num))
  have := (hstar.sphereHomotopyEquiv (r := 1 / 4) (by norm_num)
    (sphere_subset_ball (by norm_num))).pathConnectedSpace
  exact isPathConnected_iff_pathConnectedSpace.2 infBallHomeomorph.symm.pathConnectedSpace

/-- The point `pPlus` lies in the standard punctured neighborhood of infinity. -/
theorem pPlus_mem_puncturedNeighborhoodInf : pPlus ∈ puncturedNeighborhoodInf := by
  have h := norm_coe_δ 0
  rw [δ.source] at h
  rw [mem_puncturedNeighborhoodInf, h]
  norm_num

/-- The basepoint `pPlus` viewed inside the local neighborhood of infinity. -/
abbrev infBasePt : puncturedNeighborhoodInf := ⟨pPlus, pPlus_mem_puncturedNeighborhoodInf⟩

@[simp]
theorem coe_infBasePt : (infBasePt : ThricePuncturedSphere) = pPlus := (rfl)

/-- The clockwise circle `δ.symm`, as a loop in the punctured neighborhood of infinity. -/
def δInf : Path infBasePt infBasePt :=
  δ.symm.codRestrict (x := infBasePt) (y := infBasePt) fun t => by
    simpa only [mem_puncturedNeighborhoodInf, Path.symm_apply, Function.comp_apply, norm_coe_δ]
      using (by norm_num : (2 : ℝ) < 3)

/-- Inclusion of the local loop into the thrice-punctured sphere is the clockwise large circle. -/
@[simp]
theorem map_val_δInf : δInf.map continuous_subtype_val = δ.symm :=
  Path.map_codRestrict _ _

/-- The local loop has the same affine values as the clockwise large circle. -/
@[simp]
theorem coe_δInf (t : unitInterval) :
    (((δInf t : puncturedNeighborhoodInf) : ThricePuncturedSphere) : ℂ) =
      circleMap 0 3 (Real.arccos (1 / 6) + 2 * Real.pi * (1 - (t : ℝ))) := by
  rw [δInf, Path.codRestrict_coe, Path.symm_apply, Function.comp_apply, coe_δ]
  rfl

/-- In the coordinate at infinity, the direction of `δInf` has angle
`-arccos(1/6) + 2πt`, increasing by one full turn. -/
@[simp]
theorem directionAtInf_δInf (t : unitInterval) :
    directionAtInf (δInf t) = Circle.exp (-Real.arccos (1 / 6) + 2 * Real.pi * t) := by
  apply Subtype.ext
  have hn : ‖(((δInf t : puncturedNeighborhoodInf) : ThricePuncturedSphere) : ℂ)‖ = 3 := by
    simp [norm_circleMap_zero]
  rw [coe_directionAtInf, norm_div, norm_one, hn]
  rw [coe_δInf, circleMap_zero, Circle.coe_exp]
  have he : Complex.exp (↑(Real.arccos (1 / 6) + 2 * Real.pi * (1 - (t : ℝ))) * I) =
      Complex.exp (↑(Real.arccos (1 / 6) - 2 * Real.pi * t) * I) := by
    have hangle : Real.arccos (1 / 6) + 2 * Real.pi * (1 - (t : ℝ)) =
        Real.arccos (1 / 6) - 2 * Real.pi * t + 2 * Real.pi := by ring
    rw [hangle, ofReal_add, add_mul, Complex.exp_add]
    simp
  rw [he]
  have hneg : -Real.arccos (1 / 6) + 2 * Real.pi * (t : ℝ) =
      -(Real.arccos (1 / 6) - 2 * Real.pi * t) := by ring
  rw [hneg, ofReal_neg, neg_mul, Complex.exp_neg]
  push_cast
  field_simp

/-- The clockwise affine circle is the positive generator in the infinity chart. -/
@[simp]
theorem infFundamentalGroupMulEquivInt_δInf :
    infFundamentalGroupMulEquivInt infBasePt (FundamentalGroup.fromPath (.mk δInf)) =
      Multiplicative.ofAdd 1 := by
  rw [infFundamentalGroupMulEquivInt_fromPath]
  congr 1
  exact Circle.degree_eq_of_sub_eq _ (θ := fun t => -Real.arccos (1 / 6) + 2 * Real.pi * t)
    (by fun_prop) (fun t => (directionAtInf_δInf t).symm) (by simp)

/-- The local fundamental group at infinity is generated by the clockwise large circle. -/
@[simp]
theorem zpowers_δInf :
    Subgroup.zpowers (FundamentalGroup.fromPath (.mk δInf)) = ⊤ :=
  (infFundamentalGroupMulEquivInt infBasePt).zpowers_eq_top_of_apply_eq_ofAdd_one
    infFundamentalGroupMulEquivInt_δInf

/-- Include the local generator and transport along `αPlus.symm`: the result is `periphInf`. -/
theorem transport_δInf_eq_periphInf :
    (FundamentalGroup.fundamentalGroupMulEquivOfPath αPlus).symm
      (FundamentalGroup.map
        (⟨Subtype.val, continuous_subtype_val⟩ : C(puncturedNeighborhoodInf, _)) infBasePt
        (FundamentalGroup.fromPath (.mk δInf))) = periphInf := by
  rw [FundamentalGroup.map_apply, ← Path.Homotopic.Quotient.mk_map, map_val_δInf,
    FundamentalGroup.fundamentalGroupMulEquivOfPath_symm_apply, periphInf_eq_fromPath]
  -- The imported identity uses generic quotient notation, whereas the transport API uses
  -- `Path.Homotopic.Quotient.mk`; both denote the same homotopy class.
  exact (Path.Homotopic.Quotient.trans_assoc (.mk αPlus) (.mk δ.symm) (.mk αPlus.symm)).symm

/-- Transporting the included positive local generator along any path gives the peripheral
conjugacy class at infinity. Thus the class is independent of the transporting path. -/
theorem conjClassesEquivOfPath_δInf {x : ThricePuncturedSphere} (γ : Path pPlus x) :
    FundamentalGroup.conjClassesEquivOfPath γ
      (ConjClasses.mk (FundamentalGroup.map
        (⟨Subtype.val, continuous_subtype_val⟩ : C(puncturedNeighborhoodInf, _)) infBasePt
        (FundamentalGroup.fromPath (.mk δInf)))) = periphInfClass x := by
  have h := congrArg ConjClasses.mk
    ((MulEquiv.symm_apply_eq _).mp transport_δInf_eq_periphInf)
  rw [← FundamentalGroup.conjClassesEquivOfPath_mk] at h
  rw [h, conjClassesEquivOfPath_mk_periphInf,
    conjClassesEquivOfPath_periphInfClass]

end ThricePuncturedSphere
end TauCeti
