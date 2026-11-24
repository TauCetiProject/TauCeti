/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.SpecialOrthogonal
public import TauCeti.Analysis.Matrix.EuclideanLin
public import TauCeti.Topology.Algebra.OrthogonalGroup

/-!
# Real special orthogonal matrices as Euclidean operators

Over `ℝ`, the topological group isomorphism `TauCeti.matrixUnitaryContinuousMulEquivEuclidean`
induced by `Matrix.toEuclideanCLM` restricts to determinant-one subgroups, identifying the matrix
special orthogonal group `Matrix.specialOrthogonalGroup ι ℝ` with the operator-norm special
orthogonal group `TauCeti.specialOrthogonalGroup (EuclideanSpace ℝ ι)`.

## Main definitions

* `TauCeti.matrixSpecialOrthogonalContinuousMulEquivEuclidean`: topological group isomorphism
  between real special orthogonal matrices and
  `TauCeti.specialOrthogonalGroup (EuclideanSpace ℝ ι)`.
* `TauCeti.sphereRotationUnitary`: the rotation `TauCeti.sphereRotation b y` as an orthogonal
  operator of `ℝᴺ`, taking `b` to `y` (`TauCeti.sphereRotationUnitary_apply_of_ne`) and depending
  continuously on `y` away from `-b` (`TauCeti.continuousOn_sphereRotationUnitary`).
-/

public section

noncomputable section

namespace TauCeti

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable (ι) in
/-- Real special orthogonal `ι × ι` matrices and the special orthogonal operator group of
`EuclideanSpace ℝ ι` are isomorphic as topological groups via `Matrix.toEuclideanCLM`. -/
def matrixSpecialOrthogonalContinuousMulEquivEuclidean :
    Matrix.specialOrthogonalGroup ι ℝ ≃ₜ* specialOrthogonalGroup (EuclideanSpace ℝ ι) where
  toFun A :=
    ⟨matrixUnitaryContinuousMulEquivEuclidean ι ℝ ⟨A.val, A.property.1⟩,
      mem_specialOrthogonalGroup_iff.2 <| by
        rw [coe_matrixUnitaryContinuousMulEquivEuclidean, Matrix.det_toEuclideanCLM]
        exact A.property.2⟩
  invFun g :=
    ⟨((matrixUnitaryContinuousMulEquivEuclidean ι ℝ).symm g.val).val,
      ((matrixUnitaryContinuousMulEquivEuclidean ι ℝ).symm g.val).property,
      MonoidHom.mem_mker.2 <| by
        have hg : (g.val : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι).det = 1 :=
          mem_specialOrthogonalGroup_iff.1 g.property
        simpa [coe_matrixUnitaryContinuousMulEquivEuclidean_symm,
          ← Matrix.det_toEuclideanCLM (ι := ι) (𝕜 := ℝ)] using hg⟩
  left_inv A := Subtype.ext <| by
    simpa only [coe_matrixUnitaryContinuousMulEquivEuclidean,
      coe_matrixUnitaryContinuousMulEquivEuclidean_symm] using
      StarAlgEquiv.symm_apply_apply (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) A.val
  right_inv g := Subtype.ext <| Subtype.ext <| by
    simpa only [coe_matrixUnitaryContinuousMulEquivEuclidean,
      coe_matrixUnitaryContinuousMulEquivEuclidean_symm] using
      StarAlgEquiv.apply_symm_apply (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) g.val.val
  map_mul' A B := Subtype.ext <| Subtype.ext <| by
    simp only [Submonoid.coe_mul, Subgroup.coe_mul,
      coe_matrixUnitaryContinuousMulEquivEuclidean]
    exact map_mul (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) A.val B.val
  continuous_toFun :=
    ((matrixUnitaryContinuousMulEquivEuclidean ι ℝ).continuous.comp
      (continuous_subtypeVal.subtype_mk fun A ↦ A.property.1)).subtype_mk _
  continuous_invFun :=
    (continuous_subtypeVal.comp
      ((matrixUnitaryContinuousMulEquivEuclidean ι ℝ).symm.continuous.comp
        continuous_subtypeVal)).subtype_mk _

/-- The underlying continuous linear map of `matrixSpecialOrthogonalContinuousMulEquivEuclidean` is
`Matrix.toEuclideanCLM`. -/
@[simp]
theorem coe_matrixSpecialOrthogonalContinuousMulEquivEuclidean
    (A : Matrix.specialOrthogonalGroup ι ℝ) :
    ((matrixSpecialOrthogonalContinuousMulEquivEuclidean ι A :
        unitary (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)) :
      EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) =
      Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (A : Matrix ι ι ℝ) :=
  coe_matrixUnitaryContinuousMulEquivEuclidean ⟨A.val, A.property.1⟩

/-- The underlying matrix of `(matrixSpecialOrthogonalContinuousMulEquivEuclidean ι).symm` is given
by `Matrix.toEuclideanCLM.symm`. -/
@[simp]
theorem coe_matrixSpecialOrthogonalContinuousMulEquivEuclidean_symm
    (g : specialOrthogonalGroup (EuclideanSpace ℝ ι)) :
    (((matrixSpecialOrthogonalContinuousMulEquivEuclidean ι).symm g :
        Matrix.specialOrthogonalGroup ι ℝ) : Matrix ι ι ℝ) =
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)).symm
        ((g : unitary (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)) :
          EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) :=
  coe_matrixUnitaryContinuousMulEquivEuclidean_symm g.val

/-! ### Rotations taking one unit vector to another -/

section Rotation

open Metric

variable {N : ℕ}

/-- The rotation `sphereRotation b y` of `ℝᴺ` taking the unit vector `b` to the unit vector
`y ≠ -b`, as an orthogonal operator. -/
noncomputable def sphereRotationUnitary (b y : sphere (0 : EuclideanSpace ℝ (Fin N)) 1) :
    unitary (EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) :=
  (matrixSpecialOrthogonalContinuousMulEquivEuclidean (Fin N) (sphereRotation b y) :
    unitary (EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)))

/-- `sphereRotationUnitary b y` is the image of the special orthogonal matrix
`sphereRotation b y`, so it lies in `TauCeti.specialOrthogonalGroup`. -/
theorem sphereRotationUnitary_def (b y : sphere (0 : EuclideanSpace ℝ (Fin N)) 1) :
    sphereRotationUnitary b y =
      (matrixSpecialOrthogonalContinuousMulEquivEuclidean (Fin N) (sphereRotation b y) :
        unitary (EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))) :=
  (rfl)

/-- The underlying continuous linear map of `sphereRotationUnitary b y` is the matrix
`sphereRotation b y` acting through `Matrix.toEuclideanCLM`. -/
@[simp]
theorem coe_sphereRotationUnitary (b y : sphere (0 : EuclideanSpace ℝ (Fin N)) 1) :
    (sphereRotationUnitary b y : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) =
      Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ)
        (sphereRotation b y : Matrix (Fin N) (Fin N) ℝ) := by
  rw [sphereRotationUnitary_def, coe_matrixSpecialOrthogonalContinuousMulEquivEuclidean]

/-- The operator `sphereRotationUnitary b y` takes `b` to `y` when `y ≠ -b`. -/
theorem sphereRotationUnitary_apply_of_ne {b y : sphere (0 : EuclideanSpace ℝ (Fin N)) 1}
    (h : y ≠ -b) :
    (sphereRotationUnitary b y : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) b =
      y := by
  rw [coe_sphereRotationUnitary,
    ← WithLp.toLp_ofLp (p := 2) (b : EuclideanSpace ℝ (Fin N)), Matrix.toEuclideanCLM_toLp,
    sphereRotation_mulVec h, WithLp.toLp_ofLp]

/-- The operator `sphereRotationUnitary b y` depends continuously on `y` away from `-b`. -/
theorem continuousOn_sphereRotationUnitary (b : sphere (0 : EuclideanSpace ℝ (Fin N)) 1) :
    ContinuousOn (sphereRotationUnitary b) {-b}ᶜ :=
  continuous_subtypeVal.comp_continuousOn
    ((matrixSpecialOrthogonalContinuousMulEquivEuclidean (Fin N)).continuous.comp_continuousOn
      (continuousOn_sphereRotation b))

end Rotation

end TauCeti
