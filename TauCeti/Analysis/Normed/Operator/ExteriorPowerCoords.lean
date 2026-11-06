/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.ExteriorPower.Coordinates
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Instances.Matrix

/-!
# Exterior powers of coordinate operators

For a continuous linear operator `g` between coordinate spaces over a normed field,
`g.exteriorPowerCoords j` is its `j`th exterior power read in the coordinates
`exteriorPower.piEquiv`, that is, the `j`th compound matrix of `g`, as a continuous linear
operator between the coordinate spaces of dimensions `m.choose j` and `n.choose j`. The
construction preserves identities and composition, and it depends continuously on the
operator (`ContinuousLinearMap.continuous_exteriorPowerCoords`), since its
matrix entries are minors of the matrix of `g`. It can therefore be applied to continuous families
of transition matrices.

In degrees zero and one the compound matrices are identified explicitly, through the continuous
coordinate equivalences `exteriorPower.piZeroContinuousEquiv` with the coordinate line and
`exteriorPower.piOneContinuousEquiv` with the original coordinate space.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {l m n : ℕ}

/-- The `j`th exterior power of an operator between coordinate spaces, read in the coordinates
`exteriorPower.piEquiv`: the `j`th compound matrix of the operator. -/
noncomputable def exteriorPowerCoords (j : ℕ) (g : (Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜)) :
    (Fin (m.choose j) → 𝕜) →L[𝕜] (Fin (n.choose j) → 𝕜) :=
  ⟨(g : (Fin m → 𝕜) →ₗ[𝕜] (Fin n → 𝕜)).exteriorPowerCoords j, LinearMap.continuous_on_pi _⟩

@[simp] theorem coe_exteriorPowerCoords (j : ℕ) (g : (Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜)) :
    (g.exteriorPowerCoords j : (Fin (m.choose j) → 𝕜) →ₗ[𝕜] (Fin (n.choose j) → 𝕜)) =
      (g : (Fin m → 𝕜) →ₗ[𝕜] (Fin n → 𝕜)).exteriorPowerCoords j := (rfl)

@[simp] theorem exteriorPowerCoords_apply (j : ℕ) (g : (Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜))
    (v : Fin (m.choose j) → 𝕜) :
    g.exteriorPowerCoords j v = (g : (Fin m → 𝕜) →ₗ[𝕜] (Fin n → 𝕜)).exteriorPowerCoords j v :=
  (rfl)

@[simp] theorem exteriorPowerCoords_id (j m : ℕ) :
    (ContinuousLinearMap.id 𝕜 (Fin m → 𝕜)).exteriorPowerCoords j =
      ContinuousLinearMap.id 𝕜 (Fin (m.choose j) → 𝕜) :=
  coe_injective (LinearMap.exteriorPowerCoords_id j m)

@[simp] theorem exteriorPowerCoords_comp (j : ℕ) (g : (Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜))
    (f : (Fin l → 𝕜) →L[𝕜] (Fin m → 𝕜)) :
    (g.comp f).exteriorPowerCoords j = (g.exteriorPowerCoords j).comp (f.exteriorPowerCoords j) :=
  coe_injective (LinearMap.exteriorPowerCoords_comp j (g : (Fin m → 𝕜) →ₗ[𝕜] (Fin n → 𝕜))
    (f : (Fin l → 𝕜) →ₗ[𝕜] (Fin m → 𝕜)))

/-- The compound matrix depends continuously on the operator. -/
theorem continuous_exteriorPowerCoords (j m n : ℕ) :
    Continuous (exteriorPowerCoords j : ((Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜)) → _) := by
  -- Expand in the standard basis: the compound matrix is a sum of rank-one operators whose
  -- columns are vectors of minors.
  have h : (exteriorPowerCoords j : ((Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜)) → _) = fun g ↦
      ∑ t, smulRightL 𝕜 _ _ (proj t : (Fin (m.choose j) → 𝕜) →L[𝕜] 𝕜)
        (g.exteriorPowerCoords j (Pi.single t 1)) := by
    funext g
    refine ContinuousLinearMap.ext fun v ↦ ?_
    conv_lhs => rw [pi_eq_sum_univ' v]
    simp only [map_sum, map_smul, sum_apply, smulRightL_apply_apply, smulRight_apply, proj_apply]
  rw [h]
  refine continuous_finsetSum _ fun t _ ↦ (smulRightL 𝕜 _ _
    (proj t : (Fin (m.choose j) → 𝕜) →L[𝕜] 𝕜)).continuous.comp' (continuous_pi fun s ↦ ?_)
  simp_rw [exteriorPowerCoords_apply, LinearMap.exteriorPowerCoords_single_apply, coe_coe]
  refine Continuous.matrix_det (continuous_matrix fun i k ↦ ?_)
  simp only [Matrix.of_apply]
  exact (continuous_apply _).comp
    (continuous_eval_const (F := (Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜)) (Pi.single _ 1))

end ContinuousLinearMap

namespace exteriorPower

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] {m n : ℕ}

/-- `exteriorPower.piZeroEquiv` as a continuous linear equivalence. -/
noncomputable def piZeroContinuousEquiv (m : ℕ) : (Fin (m.choose 0) → 𝕜) ≃L[𝕜] (Fin 1 → 𝕜) :=
  { toLinearEquiv := piZeroEquiv m
    continuous_toFun := (piZeroEquiv m).toLinearMap.continuous_on_pi
    continuous_invFun := (piZeroEquiv m).symm.toLinearMap.continuous_on_pi }

@[simp] theorem coe_piZeroContinuousEquiv (m : ℕ) :
    (piZeroContinuousEquiv 𝕜 m : (Fin (m.choose 0) → 𝕜) ≃ₗ[𝕜] (Fin 1 → 𝕜)) = piZeroEquiv m :=
  (rfl)

variable {𝕜} in
/-- In degree zero, every compound matrix is the identity of the coordinate line. -/
theorem piZeroContinuousEquiv_comp_exteriorPowerCoords (g : (Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜)) :
    (piZeroContinuousEquiv 𝕜 n : (Fin (n.choose 0) → 𝕜) →L[𝕜] (Fin 1 → 𝕜)).comp
      (g.exteriorPowerCoords 0) = piZeroContinuousEquiv 𝕜 m := by
  ext v : 1
  exact piZeroEquiv_exteriorPowerCoords (g : (Fin m → 𝕜) →ₗ[𝕜] (Fin n → 𝕜)) v

/-- `exteriorPower.piOneEquiv` as a continuous linear equivalence. -/
noncomputable def piOneContinuousEquiv (m : ℕ) : (Fin (m.choose 1) → 𝕜) ≃L[𝕜] (Fin m → 𝕜) :=
  { toLinearEquiv := piOneEquiv m
    continuous_toFun := (piOneEquiv m).toLinearMap.continuous_on_pi
    continuous_invFun := (piOneEquiv m).symm.toLinearMap.continuous_on_pi }

@[simp] theorem coe_piOneContinuousEquiv (m : ℕ) :
    (piOneContinuousEquiv 𝕜 m : (Fin (m.choose 1) → 𝕜) ≃ₗ[𝕜] (Fin m → 𝕜)) = piOneEquiv m :=
  (rfl)

variable {𝕜} in
/-- In degree one, the compound matrix of `g` is `g`, read in
`exteriorPower.piOneContinuousEquiv`. -/
theorem piOneContinuousEquiv_comp_exteriorPowerCoords (g : (Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜)) :
    (piOneContinuousEquiv 𝕜 n : (Fin (n.choose 1) → 𝕜) →L[𝕜] (Fin n → 𝕜)).comp
      (g.exteriorPowerCoords 1) =
      g.comp (piOneContinuousEquiv 𝕜 m : (Fin (m.choose 1) → 𝕜) →L[𝕜] (Fin m → 𝕜)) := by
  ext v : 1
  exact piOneEquiv_exteriorPowerCoords (g : (Fin m → 𝕜) →ₗ[𝕜] (Fin n → 𝕜)) v

end exteriorPower
