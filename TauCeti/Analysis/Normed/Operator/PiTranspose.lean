/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Transposes of continuous linear maps between coordinate spaces

For finite index types `ι` and `κ`, the coordinate space `ι → 𝕜` is identified with its
continuous dual by Mathlib's `ContinuousLinearEquiv.piRing`, under which `w : ι → 𝕜` is the
functional `v ↦ ∑ i, v i • w i`. Reading precomposition with `T : (ι → 𝕜) →L[𝕜] (κ → 𝕜)`
through these identifications gives the transpose `T.piTranspose : (κ → 𝕜) →L[𝕜] (ι → 𝕜)`.

Since precomposition is itself a continuous bilinear operation, transposition is a continuous
linear map `ContinuousLinearMap.piTransposeL` of operator spaces; in particular a continuous
family of matrices has a continuous family of transposes. The defining adjunction for the
standard pairing is `ContinuousLinearMap.sum_mul_piTranspose`, the matrix of the transpose is
the transposed matrix (`ContinuousLinearMap.toMatrix'_piTranspose`), and transposition is an
involution reversing composition.

These are the coordinate transition maps of a dual vector bundle presented by finite-matrix
charts.
-/

public section

open Matrix

namespace ContinuousLinearMap

variable {𝕜 ι κ μ : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ]

variable (𝕜 ι κ) in
/-- Transposition of continuous linear maps between coordinate spaces, as a continuous linear
map. It is precomposition on continuous duals, read through `ContinuousLinearEquiv.piRing`. -/
noncomputable def piTransposeL : ((ι → 𝕜) →L[𝕜] (κ → 𝕜)) →L[𝕜] ((κ → 𝕜) →L[𝕜] (ι → 𝕜)) :=
  ((ContinuousLinearEquiv.piRing (𝕜 := 𝕜) (E := 𝕜) κ).arrowCongr
    (ContinuousLinearEquiv.piRing (𝕜 := 𝕜) (E := 𝕜) ι)).toContinuousLinearMap.comp
      (compL 𝕜 (ι → 𝕜) (κ → 𝕜) 𝕜).flip

/-- The transpose of a continuous linear map between coordinate spaces, with respect to the
standard pairings `∑ i, v i * w i`. -/
noncomputable def piTranspose (T : (ι → 𝕜) →L[𝕜] (κ → 𝕜)) : (κ → 𝕜) →L[𝕜] (ι → 𝕜) :=
  piTransposeL 𝕜 ι κ T

@[simp] theorem piTransposeL_apply (T : (ι → 𝕜) →L[𝕜] (κ → 𝕜)) :
    piTransposeL 𝕜 ι κ T = T.piTranspose := (rfl)

/-- A continuous family of maps between coordinate spaces has a continuous family of
transposes. -/
theorem _root_.Continuous.piTranspose {X : Type*} [TopologicalSpace X]
    {T : X → (ι → 𝕜) →L[𝕜] (κ → 𝕜)} (hT : Continuous T) :
    Continuous fun x => (T x).piTranspose :=
  (piTransposeL 𝕜 ι κ).continuous.comp hT

/-- A family of maps between coordinate spaces that is continuous on a set has transposes
continuous on that set. -/
theorem _root_.ContinuousOn.piTranspose {X : Type*} [TopologicalSpace X]
    {T : X → (ι → 𝕜) →L[𝕜] (κ → 𝕜)} {s : Set X} (hT : ContinuousOn T s) :
    ContinuousOn (fun x => (T x).piTranspose) s :=
  (piTransposeL 𝕜 ι κ).continuous.comp_continuousOn hT

/-- Read as a functional, the transpose of `T` applied to `w` is the functional `w`
precomposed with `T`. -/
theorem piRing_symm_piTranspose (T : (ι → 𝕜) →L[𝕜] (κ → 𝕜)) (w : κ → 𝕜) :
    (ContinuousLinearEquiv.piRing (𝕜 := 𝕜) (E := 𝕜) ι).symm (T.piTranspose w) =
      ((ContinuousLinearEquiv.piRing (𝕜 := 𝕜) (E := 𝕜) κ).symm w).comp T := by
  simp [piTranspose, piTransposeL]

/-- The transpose is adjoint to `T` for the standard pairings of coordinate spaces. -/
theorem sum_mul_piTranspose (T : (ι → 𝕜) →L[𝕜] (κ → 𝕜)) (v : ι → 𝕜) (w : κ → 𝕜) :
    ∑ i, v i * T.piTranspose w i = ∑ j, T v j * w j := by
  simpa using congrArg (fun f : (ι → 𝕜) →L[𝕜] 𝕜 => f v) (piRing_symm_piTranspose T w)

/-- The coordinates of the transpose: its `i`-th entry pairs `w` with the `i`-th column of
`T`. -/
theorem piTranspose_apply (T : (ι → 𝕜) →L[𝕜] (κ → 𝕜)) (w : κ → 𝕜) (i : ι) :
    T.piTranspose w i = ∑ j, T (Pi.single i 1) j * w j := by
  simpa [Pi.single_apply] using sum_mul_piTranspose T (Pi.single i 1) w

/-- A transposed map is determined by its pairings with all coordinate vectors. -/
theorem eq_piTranspose_iff (T : (ι → 𝕜) →L[𝕜] (κ → 𝕜)) (S : (κ → 𝕜) →L[𝕜] (ι → 𝕜)) :
    S = T.piTranspose ↔ ∀ v w, ∑ i, v i * S w i = ∑ j, T v j * w j := by
  refine ⟨fun h v w => h ▸ sum_mul_piTranspose T v w, fun h => ?_⟩
  ext w i
  simpa [Pi.single_apply, piTranspose_apply] using h (Pi.single i 1) w

/-- The matrix of the transpose is the transpose of the matrix. -/
@[simp] theorem toMatrix'_piTranspose (T : (ι → 𝕜) →L[𝕜] (κ → 𝕜)) :
    LinearMap.toMatrix' (T.piTranspose : (κ → 𝕜) →ₗ[𝕜] (ι → 𝕜)) =
      (LinearMap.toMatrix' (T : (ι → 𝕜) →ₗ[𝕜] (κ → 𝕜)))ᵀ := by
  ext i j
  simp [LinearMap.toMatrix'_apply, piTranspose_apply, Pi.single_apply]

@[simp] theorem piTranspose_id :
    (ContinuousLinearMap.id 𝕜 (ι → 𝕜)).piTranspose = ContinuousLinearMap.id 𝕜 (ι → 𝕜) :=
  ((eq_piTranspose_iff _ _).2 fun v w => by simp).symm

/-- Transposition reverses composition. -/
@[simp] theorem piTranspose_comp (S : (κ → 𝕜) →L[𝕜] (μ → 𝕜)) (T : (ι → 𝕜) →L[𝕜] (κ → 𝕜)) :
    (S.comp T).piTranspose = T.piTranspose.comp S.piTranspose :=
  ((eq_piTranspose_iff _ _).2 fun v w => by
    simp only [comp_apply, sum_mul_piTranspose]).symm

/-- Transposition is an involution. -/
@[simp] theorem piTranspose_piTranspose (T : (ι → 𝕜) →L[𝕜] (κ → 𝕜)) :
    T.piTranspose.piTranspose = T :=
  ((eq_piTranspose_iff _ _).2 fun v w => by
    simp only [sum_mul_piTranspose, mul_comm]).symm

theorem piTranspose_injective :
    Function.Injective (piTranspose : ((ι → 𝕜) →L[𝕜] (κ → 𝕜)) → _) :=
  Function.LeftInverse.injective piTranspose_piTranspose

@[simp] theorem piTranspose_inj {S T : (ι → 𝕜) →L[𝕜] (κ → 𝕜)} :
    S.piTranspose = T.piTranspose ↔ S = T :=
  piTranspose_injective.eq_iff

@[simp] theorem piTranspose_zero :
    (0 : (ι → 𝕜) →L[𝕜] (κ → 𝕜)).piTranspose = 0 :=
  map_zero (piTransposeL 𝕜 ι κ)

@[simp] theorem piTranspose_add (S T : (ι → 𝕜) →L[𝕜] (κ → 𝕜)) :
    (S + T).piTranspose = S.piTranspose + T.piTranspose :=
  map_add (piTransposeL 𝕜 ι κ) S T

@[simp] theorem piTranspose_neg (T : (ι → 𝕜) →L[𝕜] (κ → 𝕜)) :
    (-T).piTranspose = -T.piTranspose :=
  map_neg (piTransposeL 𝕜 ι κ) T

@[simp] theorem piTranspose_smul (c : 𝕜) (T : (ι → 𝕜) →L[𝕜] (κ → 𝕜)) :
    (c • T).piTranspose = c • T.piTranspose :=
  map_smul (piTransposeL 𝕜 ι κ) c T

end ContinuousLinearMap
