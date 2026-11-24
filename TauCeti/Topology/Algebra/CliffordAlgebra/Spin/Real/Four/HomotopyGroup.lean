/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.HomotopyGroup
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Real.Four.Basic
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Real.Stabilization
public import TauCeti.Topology.Homotopy.HomotopyGroup.Product

import TauCeti.Topology.Homotopy.HomotopyGroup.TopologicalMonoid

/-!
# Higher homotopy groups and factor-pinning of compact `Spin(4)` and `SO(4)`

Using `TauCeti.realSpinFourCalibratedHomeomorphQuaternionSphereProd`, positive-dimensional homotopy
groups of compact `Spin(4)` and higher homotopy groups (`k ≥ 2`) of `SO(4)` split into two copies of
`πₖ(S³, 1)`: `πₖ(Spin(4), 1) ≃* πₖ(S³, 1) × πₖ(S³, 1)` (`k ≥ 1`),
`πₖ(SO(4), 1) ≃* πₖ(S³, 1) × πₖ(S³, 1)` (`k ≥ 2`), `Spin(4)` is `2`-connected, and `π₂(SO(4)) = 0`.
First-coordinate stabilization (`Spin(3) → Spin(4)` and `SO(3) → SO(4)`) induces the diagonal map
via `HomotopyGroup.map_conj_apply`, while conjugation by first-coordinate reflection
(`TauCeti.realCliffordCoordReflection 0`) swaps the two `πₖ(S³, 1)` factors (`Prod.swap`).

## Main definitions and results

* `CliffordAlgebra.realSpinFourCalibratedHomotopyGroupMulEquivSphereProd`,
  `CliffordAlgebra.realSpecialOrthogonalFourCalibratedHomotopyGroupMulEquivSphereProd`, and
  `TauCeti.specialOrthogonalGroupFourCalibratedHomotopyGroupMulEquivSphereProd`: sphere-product
  homotopy decompositions of `Spin(4)` and `SO(4)`.
* `CliffordAlgebra.subsingleton_homotopyGroup_realSpin_four`,
  `CliffordAlgebra.subsingleton_homotopyGroup_realSpecialOrthogonal_four`, and
  `TauCeti.subsingleton_homotopyGroup_specialOrthogonalGroup_four`: `2`-connectedness of `Spin(4)`
  and `π₂(SO(4)) = 0`.
* `CliffordAlgebra.realSpinFourCalibratedHomotopyGroupMulEquivSphereProd_firstInclusion` and
  `CliffordAlgebra.realSpinFourCalibratedHomotopyGroupMulEquivSphereProd_firstReflection` (with
  `SO(4)` counterparts): diagonal stabilization and factor-swapping reflection on homotopy groups.

## References

* A. Hatcher, *Algebraic Topology* (2002), Proposition 4.1 and Section 4.2.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, Theorem 3.7 and §4.
-/

public section

open Metric
open scoped Quaternion Topology.Homotopy

namespace CliffordAlgebra

open TauCeti

noncomputable section

section Nonempty

variable {N : Type*} [DecidableEq N] [Nonempty N]

/-- **`πₖ(Spin(4)) ≅ πₖ(S³) × πₖ(S³)` for `k ≥ 1` in the calibrated model.** -/
def realSpinFourCalibratedHomotopyGroupMulEquivSphereProd :
    HomotopyGroup N (realCliffordSpinGroupZero 4) 1 ≃*
      HomotopyGroup N (sphere (0 : ℍ[ℝ]) 1) 1 × HomotopyGroup N (sphere (0 : ℍ[ℝ]) 1) 1 :=
  (HomotopyGroup.homeomorphMulEquivOfEq realSpinFourCalibratedHomeomorphQuaternionSphereProd
    realSpinFourCalibratedHomeomorphQuaternionSphereProd_one).trans
    (HomotopyGroup.prodMulEquiv 1 1)

/-- Forward evaluation of `realSpinFourCalibratedHomotopyGroupMulEquivSphereProd`. -/
theorem realSpinFourCalibratedHomotopyGroupMulEquivSphereProd_apply
    (a : HomotopyGroup N (realCliffordSpinGroupZero 4) 1) :
    realSpinFourCalibratedHomotopyGroupMulEquivSphereProd a =
      HomotopyGroup.prodMulEquiv 1 1
        (HomotopyGroup.map ⟨realSpinFourCalibratedHomeomorphQuaternionSphereProd,
          realSpinFourCalibratedHomeomorphQuaternionSphereProd.continuous⟩
          realSpinFourCalibratedHomeomorphQuaternionSphereProd_one a) := by
  rw [realSpinFourCalibratedHomotopyGroupMulEquivSphereProd, MulEquiv.trans_apply,
    HomotopyGroup.homeomorphMulEquivOfEq_apply]

/-- Inverse evaluation of `realSpinFourCalibratedHomotopyGroupMulEquivSphereProd`. -/
theorem realSpinFourCalibratedHomotopyGroupMulEquivSphereProd_symm_apply
    (ab : HomotopyGroup N (sphere (0 : ℍ[ℝ]) 1) 1 × HomotopyGroup N (sphere (0 : ℍ[ℝ]) 1) 1) :
    realSpinFourCalibratedHomotopyGroupMulEquivSphereProd.symm ab =
      HomotopyGroup.map ⟨realSpinFourCalibratedHomeomorphQuaternionSphereProd.symm,
        realSpinFourCalibratedHomeomorphQuaternionSphereProd.symm.continuous⟩
        realSpinFourCalibratedHomeomorphQuaternionSphereProd_symm_one
        (HomotopyGroup.prod ab.1 ab.2) := by
  rw [realSpinFourCalibratedHomotopyGroupMulEquivSphereProd, MulEquiv.symm_trans_apply,
    HomotopyGroup.prodMulEquiv_symm_apply, HomotopyGroup.homeomorphMulEquivOfEq_symm_apply]

private theorem fst_realSpinFourCalibratedHomotopyGroupMulEquivSphereProd_apply
    (x : HomotopyGroup N (realCliffordSpinGroupZero 4) 1) :
    (realSpinFourCalibratedHomotopyGroupMulEquivSphereProd x).1 =
      HomotopyGroup.map ((ContinuousMap.fst : C(_, _)).comp
        ⟨realSpinFourCalibratedHomeomorphQuaternionSphereProd,
          realSpinFourCalibratedHomeomorphQuaternionSphereProd.continuous⟩) (by simp) x := by
  simp only [realSpinFourCalibratedHomotopyGroupMulEquivSphereProd_apply,
    HomotopyGroup.prodMulEquiv_apply, HomotopyGroup.prodEquiv_apply, HomotopyGroup.map_comp_apply]
  rfl

private theorem snd_realSpinFourCalibratedHomotopyGroupMulEquivSphereProd_apply
    (x : HomotopyGroup N (realCliffordSpinGroupZero 4) 1) :
    (realSpinFourCalibratedHomotopyGroupMulEquivSphereProd x).2 =
      HomotopyGroup.map ((ContinuousMap.snd : C(_, _)).comp
        ⟨realSpinFourCalibratedHomeomorphQuaternionSphereProd,
          realSpinFourCalibratedHomeomorphQuaternionSphereProd.continuous⟩) (by simp) x := by
  simp only [realSpinFourCalibratedHomotopyGroupMulEquivSphereProd_apply,
    HomotopyGroup.prodMulEquiv_apply, HomotopyGroup.prodEquiv_apply, HomotopyGroup.map_comp_apply]
  rfl

/-- **First-coordinate stabilization `Spin(3) → Spin(4)` induces the diagonal map on homotopy
groups** in the calibrated sphere-product model. -/
@[simp] theorem realSpinFourCalibratedHomotopyGroupMulEquivSphereProd_firstInclusion
    (a : HomotopyGroup N (realCliffordSpinGroupZero 3) 1) :
    realSpinFourCalibratedHomotopyGroupMulEquivSphereProd
        (HomotopyGroup.map (realCliffordSpinFirstInclusionContinuousMonoidHom 3 :
          C(realCliffordSpinGroupZero 3, realCliffordSpinGroupZero 4))
          (map_one (realCliffordSpinFirstInclusionContinuousMonoidHom 3)) a) =
      (realSpinThreeHomotopyGroupMulEquivSphere a,
        realSpinThreeHomotopyGroupMulEquivSphere a) := by
  let f₁ : C(realCliffordSpinGroupZero 3, unitary ℍ[ℝ]) :=
    realSpinThreeContinuousMulEquivQuaternionUnitary
  let f₂ : C(unitary ℍ[ℝ], unitary ℍ[ℝ]) :=
    ⟨MulAut.conj realSpinThreeToFourCalibrationUnitary,
      IsTopologicalGroup.continuous_conj realSpinThreeToFourCalibrationUnitary⟩
  let f₃ : C(unitary ℍ[ℝ], sphere (0 : ℍ[ℝ]) 1) :=
    ⟨Quaternion.unitaryHomeomorphSphere, Quaternion.unitaryHomeomorphSphere.continuous⟩
  have hf₁ : f₁ 1 = 1 := map_one realSpinThreeContinuousMulEquivQuaternionUnitary
  have hf₂ : f₂ 1 = 1 := (MulAut.conj realSpinThreeToFourCalibrationUnitary).map_one
  have hf₂q (q) : f₂ q = MulAut.conj realSpinThreeToFourCalibrationUnitary q := rfl
  have hf₃ : f₃ 1 = 1 := Quaternion.unitaryHomeomorphSphere_one
  have hf₃f₁ : f₃.comp f₁ = ⟨realSpinThreeHomeomorphQuaternionSphere,
      realSpinThreeHomeomorphQuaternionSphere.continuous⟩ :=
    ContinuousMap.ext fun s ↦ Subtype.ext (by simp [f₃, f₁])
  have hdiag : HomotopyGroup.map ((f₃.comp f₂).comp f₁) (by simp [hf₁, hf₂, hf₃]) a =
      realSpinThreeHomotopyGroupMulEquivSphere a := by
    rw [← HomotopyGroup.map_comp_apply (f₃.comp f₂) (by simp [hf₂, hf₃]) f₁ hf₁,
      ← HomotopyGroup.map_comp_apply f₃ hf₃ f₂ hf₂, HomotopyGroup.map_conj_apply,
      HomotopyGroup.map_comp_apply, realSpinThreeHomotopyGroupMulEquivSphere_apply]
    exact HomotopyGroup.map_congr hf₃f₁ _ _ a
  apply Prod.ext
  · rw [fst_realSpinFourCalibratedHomotopyGroupMulEquivSphereProd_apply,
      HomotopyGroup.map_comp_apply, ← hdiag]
    exact HomotopyGroup.map_congr (ContinuousMap.ext fun s ↦ Subtype.ext (by simp [f₁, f₃, hf₂q]))
      _ _ a
  · rw [snd_realSpinFourCalibratedHomotopyGroupMulEquivSphereProd_apply,
      HomotopyGroup.map_comp_apply, ← hdiag]
    exact HomotopyGroup.map_congr (ContinuousMap.ext fun s ↦ Subtype.ext (by simp [f₁, f₃, hf₂q]))
      _ _ a

/-- **First-coordinate reflection swaps the two `πₖ(S³)` factors of `πₖ(Spin(4))`.** -/
@[simp] theorem realSpinFourCalibratedHomotopyGroupMulEquivSphereProd_firstReflection
    (a : HomotopyGroup N (realCliffordSpinGroupZero 4) 1) :
    realSpinFourCalibratedHomotopyGroupMulEquivSphereProd
        (HomotopyGroup.map ((realCliffordCoordReflection (0 : Fin 4)).spinGroupContinuousMulEquiv :
          C(realCliffordSpinGroupZero 4, realCliffordSpinGroupZero 4))
          (map_one (realCliffordCoordReflection (0 : Fin 4)).spinGroupContinuousMulEquiv) a) =
      Prod.swap (realSpinFourCalibratedHomotopyGroupMulEquivSphereProd a) := by
  apply Prod.ext
  · rw [Prod.fst_swap, fst_realSpinFourCalibratedHomotopyGroupMulEquivSphereProd_apply,
      snd_realSpinFourCalibratedHomotopyGroupMulEquivSphereProd_apply, HomotopyGroup.map_comp_apply]
    exact HomotopyGroup.map_congr (ContinuousMap.ext fun s ↦ Subtype.ext (by simp)) _ _ a
  · rw [Prod.snd_swap, snd_realSpinFourCalibratedHomotopyGroupMulEquivSphereProd_apply,
      fst_realSpinFourCalibratedHomotopyGroupMulEquivSphereProd_apply, HomotopyGroup.map_comp_apply]
    exact HomotopyGroup.map_congr (ContinuousMap.ext fun s ↦ Subtype.ext (by simp)) _ _ a

end Nonempty

/-- **Compact `Spin(4)` is `2`-connected at every basepoint**: `πₖ(Spin(4), g) = 0` for `k < 3`. -/
theorem subsingleton_homotopyGroup_realSpin_four {N : Type*} (hN : Nat.card N < 3)
    (g : realCliffordSpinGroupZero 4) :
    Subsingleton (HomotopyGroup N (realCliffordSpinGroupZero 4) g) := by
  have : Subsingleton (HomotopyGroup N (sphere (0 : ℍ[ℝ]) 1) 1) :=
    subsingleton_homotopyGroup_sphere_quaternion hN 1
  have : Subsingleton (HomotopyGroup N (sphere (0 : ℍ[ℝ]) 1 × sphere (0 : ℍ[ℝ]) 1) (1, 1)) :=
    (HomotopyGroup.prodEquiv (N := N) (1 : sphere (0 : ℍ[ℝ]) 1) 1).subsingleton
  have : Subsingleton (HomotopyGroup N (realCliffordSpinGroupZero 4) 1) :=
    (HomotopyGroup.homeomorphEquivOfEq realSpinFourCalibratedHomeomorphQuaternionSphereProd
      realSpinFourCalibratedHomeomorphQuaternionSphereProd_one).subsingleton
  exact (HomotopyGroup.homeomorphEquivOfEq (Homeomorph.mulLeft g) (mul_one g)).symm.subsingleton

section Nontrivial

variable {N : Type*} [DecidableEq N] [Nontrivial N]

/-- **`πₖ(SO(4)) ≅ πₖ(S³) × πₖ(S³)` for `k ≥ 2` in the calibrated model.** -/
def realSpecialOrthogonalFourCalibratedHomotopyGroupMulEquivSphereProd :
    HomotopyGroup N (QuadraticMap.specialOrthogonalGroup (realCliffordForm 4 0)) 1 ≃*
      HomotopyGroup N (sphere (0 : ℍ[ℝ]) 1) 1 × HomotopyGroup N (sphere (0 : ℍ[ℝ]) 1) 1 :=
  (realCliffordSpinProjectionZeroHomotopyGroupMulEquiv 4).symm.trans
    realSpinFourCalibratedHomotopyGroupMulEquivSphereProd

/-- Forward evaluation of `realSpecialOrthogonalFourCalibratedHomotopyGroupMulEquivSphereProd`. -/
theorem realSpecialOrthogonalFourCalibratedHomotopyGroupMulEquivSphereProd_apply
    (b : HomotopyGroup N (QuadraticMap.specialOrthogonalGroup (realCliffordForm 4 0)) 1) :
    realSpecialOrthogonalFourCalibratedHomotopyGroupMulEquivSphereProd b =
      realSpinFourCalibratedHomotopyGroupMulEquivSphereProd
        ((realCliffordSpinProjectionZeroHomotopyGroupMulEquiv 4).symm b) := by
  rw [realSpecialOrthogonalFourCalibratedHomotopyGroupMulEquivSphereProd, MulEquiv.trans_apply]

/-- Compatibility across `Spin(4) → SO(4)`. -/
@[simp] theorem realSpecialOrthogonalFourCalibratedHomotopyGroupMulEquivSphereProd_spinProjection
    (a : HomotopyGroup N (realCliffordSpinGroupZero 4) 1) :
    realSpecialOrthogonalFourCalibratedHomotopyGroupMulEquivSphereProd
        (HomotopyGroup.map (realCliffordSpinProjectionZero 4 : C(_, _))
          (map_one (realCliffordSpinProjectionZero 4)) a) =
      realSpinFourCalibratedHomotopyGroupMulEquivSphereProd a := by
  simp [realSpecialOrthogonalFourCalibratedHomotopyGroupMulEquivSphereProd,
    ← realCliffordSpinProjectionZeroHomotopyGroupMulEquiv_apply]

/-- Inverse of `realSpecialOrthogonalFourCalibratedHomotopyGroupMulEquivSphereProd`. -/
theorem realSpecialOrthogonalFourCalibratedHomotopyGroupMulEquivSphereProd_symm_apply
    (ab : HomotopyGroup N (sphere (0 : ℍ[ℝ]) 1) 1 × HomotopyGroup N (sphere (0 : ℍ[ℝ]) 1) 1) :
    realSpecialOrthogonalFourCalibratedHomotopyGroupMulEquivSphereProd.symm ab =
      HomotopyGroup.map (realCliffordSpinProjectionZero 4 : C(_, _))
        (map_one (realCliffordSpinProjectionZero 4))
        (realSpinFourCalibratedHomotopyGroupMulEquivSphereProd.symm ab) := by
  rw [realSpecialOrthogonalFourCalibratedHomotopyGroupMulEquivSphereProd,
    MulEquiv.symm_trans_apply, MulEquiv.symm_symm,
    realCliffordSpinProjectionZeroHomotopyGroupMulEquiv_apply]

/-- **First-coordinate stabilization `SO(3) → SO(4)` is diagonal on `πₖ` (`k ≥ 2`).** -/
@[simp] theorem realSpecialOrthogonalFourCalibratedHomotopyGroupMulEquivSphereProd_firstInclusion
    (b : HomotopyGroup N (QuadraticMap.specialOrthogonalGroup (realCliffordForm 3 0)) 1) :
    realSpecialOrthogonalFourCalibratedHomotopyGroupMulEquivSphereProd
        (HomotopyGroup.map
          (realCliffordSpecialOrthogonalFirstInclusionContinuousMonoidHom 3 : C(_, _))
          (map_one (realCliffordSpecialOrthogonalFirstInclusionContinuousMonoidHom 3)) b) =
      (realSpecialOrthogonalThreeHomotopyGroupMulEquivSphere b,
        realSpecialOrthogonalThreeHomotopyGroupMulEquivSphere b) := by
  obtain ⟨a, rfl⟩ := (realCliffordSpinProjectionZeroHomotopyGroupMulEquiv 3).surjective b
  rw [realCliffordSpinProjectionZeroHomotopyGroupMulEquiv_apply,
    realSpecialOrthogonalThreeHomotopyGroupMulEquivSphere_spinProjection,
    HomotopyGroup.map_map_of_comm (realCliffordSpinProjectionZero 4 : C(_, _))
      (map_one (realCliffordSpinProjectionZero 4))
      (realCliffordSpinFirstInclusionContinuousMonoidHom 3 :
        C(realCliffordSpinGroupZero 3, realCliffordSpinGroupZero 4))
      (map_one (realCliffordSpinFirstInclusionContinuousMonoidHom 3)) (fun s ↦ by simp),
    realSpecialOrthogonalFourCalibratedHomotopyGroupMulEquivSphereProd_spinProjection,
    realSpinFourCalibratedHomotopyGroupMulEquivSphereProd_firstInclusion]

/-- **First-coordinate reflection swaps the two `πₖ(S³)` factors of `πₖ(SO(4))` (`k ≥ 2`).** -/
@[simp] theorem realSpecialOrthogonalFourCalibratedHomotopyGroupMulEquivSphereProd_firstReflection
    (b : HomotopyGroup N (QuadraticMap.specialOrthogonalGroup (realCliffordForm 4 0)) 1) :
    realSpecialOrthogonalFourCalibratedHomotopyGroupMulEquivSphereProd
        (HomotopyGroup.map
          (realCliffordCoordReflectionSpecialOrthogonalContinuousMulEquiv (0 : Fin 4) : C(_, _))
          (map_one (realCliffordCoordReflectionSpecialOrthogonalContinuousMulEquiv (0 : Fin 4)))
          b) =
      Prod.swap (realSpecialOrthogonalFourCalibratedHomotopyGroupMulEquivSphereProd b) := by
  obtain ⟨a, rfl⟩ := (realCliffordSpinProjectionZeroHomotopyGroupMulEquiv 4).surjective b
  rw [realCliffordSpinProjectionZeroHomotopyGroupMulEquiv_apply,
    realSpecialOrthogonalFourCalibratedHomotopyGroupMulEquivSphereProd_spinProjection,
    HomotopyGroup.map_map_of_comm (realCliffordSpinProjectionZero 4 : C(_, _))
      (map_one (realCliffordSpinProjectionZero 4))
      ((realCliffordCoordReflection (0 : Fin 4)).spinGroupContinuousMulEquiv :
        C(realCliffordSpinGroupZero 4, realCliffordSpinGroupZero 4))
      (map_one (realCliffordCoordReflection (0 : Fin 4)).spinGroupContinuousMulEquiv)
      (fun s ↦ by simp),
    realSpecialOrthogonalFourCalibratedHomotopyGroupMulEquivSphereProd_spinProjection,
    realSpinFourCalibratedHomotopyGroupMulEquivSphereProd_firstReflection]

end Nontrivial

/-- **`π₂(SO(4)) = 0` at every basepoint.** -/
theorem subsingleton_homotopyGroup_realSpecialOrthogonal_four {N : Type*} (hN : Nat.card N = 2)
    (g : QuadraticMap.specialOrthogonalGroup (realCliffordForm 4 0)) :
    Subsingleton
      (HomotopyGroup N (QuadraticMap.specialOrthogonalGroup (realCliffordForm 4 0)) g) := by
  classical
  have : Finite N := Nat.finite_of_card_ne_zero (by omega)
  have : Nontrivial N := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have : Subsingleton (HomotopyGroup N (realCliffordSpinGroupZero 4) 1) :=
    subsingleton_homotopyGroup_realSpin_four (by omega) 1
  have : Subsingleton
      (HomotopyGroup N (QuadraticMap.specialOrthogonalGroup (realCliffordForm 4 0)) 1) :=
    (realCliffordSpinProjectionZeroHomotopyGroupMulEquiv 4).symm.toEquiv.subsingleton
  exact (HomotopyGroup.homeomorphEquivOfEq (Homeomorph.mulLeft g) (mul_one g)).symm.subsingleton

end

end CliffordAlgebra

namespace TauCeti

noncomputable section

section Nontrivial

variable {N : Type*} [DecidableEq N] [Nontrivial N]

/-- **`πₖ(SO(4)) ≅ πₖ(S³) × πₖ(S³)` for `k ≥ 2`, for the matrix group.** -/
def specialOrthogonalGroupFourCalibratedHomotopyGroupMulEquivSphereProd :
    HomotopyGroup N (Matrix.specialOrthogonalGroup (Fin 4) ℝ) 1 ≃*
      HomotopyGroup N (sphere (0 : ℍ[ℝ]) 1) 1 × HomotopyGroup N (sphere (0 : ℍ[ℝ]) 1) 1 :=
  (HomotopyGroup.homeomorphMulEquivOfEq
    (QuadraticMap.matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm 4).toHomeomorph
    (map_one (QuadraticMap.matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm 4))).trans
    CliffordAlgebra.realSpecialOrthogonalFourCalibratedHomotopyGroupMulEquivSphereProd

/-- Forward evaluation of `specialOrthogonalGroupFourCalibratedHomotopyGroupMulEquivSphereProd`. -/
theorem specialOrthogonalGroupFourCalibratedHomotopyGroupMulEquivSphereProd_apply
    (a : HomotopyGroup N (Matrix.specialOrthogonalGroup (Fin 4) ℝ) 1) :
    specialOrthogonalGroupFourCalibratedHomotopyGroupMulEquivSphereProd a =
      CliffordAlgebra.realSpecialOrthogonalFourCalibratedHomotopyGroupMulEquivSphereProd
        (HomotopyGroup.map
          (QuadraticMap.matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm 4 : C(_, _))
          (map_one (QuadraticMap.matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm 4))
          a) := by
  rw [specialOrthogonalGroupFourCalibratedHomotopyGroupMulEquivSphereProd, MulEquiv.trans_apply,
    HomotopyGroup.homeomorphMulEquivOfEq_apply]
  congr 1

/-- Inverse of `specialOrthogonalGroupFourCalibratedHomotopyGroupMulEquivSphereProd`. -/
theorem specialOrthogonalGroupFourCalibratedHomotopyGroupMulEquivSphereProd_symm_apply
    (ab : HomotopyGroup N (sphere (0 : ℍ[ℝ]) 1) 1 × HomotopyGroup N (sphere (0 : ℍ[ℝ]) 1) 1) :
    specialOrthogonalGroupFourCalibratedHomotopyGroupMulEquivSphereProd.symm ab =
      HomotopyGroup.map
        ((QuadraticMap.matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm 4).symm : C(_, _))
        (map_one (QuadraticMap.matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm 4).symm)
        (CliffordAlgebra.realSpecialOrthogonalFourCalibratedHomotopyGroupMulEquivSphereProd.symm
          ab) := by
  rw [specialOrthogonalGroupFourCalibratedHomotopyGroupMulEquivSphereProd,
    MulEquiv.symm_trans_apply, HomotopyGroup.homeomorphMulEquivOfEq_symm_apply]
  exact HomotopyGroup.map_congr (ContinuousMap.ext fun _ ↦ rfl) _ _ _

end Nontrivial

/-- **`π₂(SO(4)) = 0` for the matrix group.** -/
theorem subsingleton_homotopyGroup_specialOrthogonalGroup_four {N : Type*} (hN : Nat.card N = 2)
    (g : Matrix.specialOrthogonalGroup (Fin 4) ℝ) :
    Subsingleton (HomotopyGroup N (Matrix.specialOrthogonalGroup (Fin 4) ℝ) g) :=
  have := CliffordAlgebra.subsingleton_homotopyGroup_realSpecialOrthogonal_four hN
    (QuadraticMap.matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm 4 g)
  (HomotopyGroup.homeomorphEquivOfEq
    (QuadraticMap.matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm 4).toHomeomorph
    rfl).subsingleton

end

end TauCeti
end
