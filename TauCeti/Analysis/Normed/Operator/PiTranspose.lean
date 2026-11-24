/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Kronecker
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
the transposed matrix (`ContinuousLinearMap.toMatrix'_piTranspose`), so transposition preserves
determinants (`ContinuousLinearMap.det_piTranspose`), and transposition is an involution
reversing composition.

These are the coordinate transition maps of a dual vector bundle presented by finite-matrix
charts.

On `Fin`-indexed Kronecker coordinates, `ContinuousLinearMap.piTranspose_kronecker_eq_homCoordConj`
identifies `S.piTranspose.kronecker R` with operator conjugation
`ContinuousLinearMap.homCoordConj S R`.

Given a coordinate equivalence `e : F ≃L[𝕜] (ι → 𝕜)`, `ContinuousLinearEquiv.dualCoords e`
identifies the continuous dual `F →L[𝕜] 𝕜` with `ι → 𝕜`. Changing dual coordinates from `e₁` to `e₂`
is `ContinuousLinearMap.piTranspose` of the primal coordinate change
(`ContinuousLinearEquiv.dualCoords_symm_trans_dualCoords`), and for two bases `b₁`, `b₂` of `F` its
determinant is `b₁.det b₂` (`Module.Basis.det_dualCoords_equivFunL_symm_trans`).
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

/-- Transposition preserves the determinant of an endomorphism of a coordinate space. -/
@[simp] theorem det_piTranspose (T : (ι → 𝕜) →L[𝕜] (ι → 𝕜)) :
    T.piTranspose.det = T.det := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.det, ← LinearMap.det_toMatrix',
    ← LinearMap.det_toMatrix', toMatrix'_piTranspose, Matrix.det_transpose]

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

section Kronecker

variable {m m' n n' : ℕ}

/-- On `Fin (_ * _) → 𝕜`, `S.piTranspose.kronecker R` equals operator conjugation
`homCoordConj S R`. -/
theorem piTranspose_kronecker_eq_homCoordConj (S : (Fin m' → 𝕜) →L[𝕜] (Fin m → 𝕜))
    (R : (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜)) :
    S.piTranspose.kronecker R = homCoordConj S R := by
  refine ContinuousLinearMap.ext fun v ↦ funext fun k' ↦ ?_
  obtain ⟨⟨i', j'⟩, rfl⟩ := finProdFinEquiv.surjective k'
  rw [kronecker_apply, homCoordConj_apply, piTranspose_apply]
  have hv : (fun j : Fin n ↦ ∑ i : Fin m, S (Pi.single i' 1) i * v (finProdFinEquiv (i, j))) =
      ∑ i : Fin m, S (Pi.single i' 1) i • fun j : Fin n ↦ v (finProdFinEquiv (i, j)) := by
    ext j; simp [Finset.sum_apply, smul_eq_mul]
  rw [hv, map_sum]
  simp [Finset.sum_apply, smul_eq_mul]

end Kronecker

end ContinuousLinearMap

namespace ContinuousLinearEquiv

section DualCoords

variable {𝕜 F ι κ : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The dual coordinate equivalence on `F →L[𝕜] 𝕜` associated to `e : F ≃L[𝕜] (ι → 𝕜)`,
sending `p` to `i ↦ p (e.symm (Pi.single i 1))`. -/
noncomputable def dualCoords (e : F ≃L[𝕜] (ι → 𝕜)) : (F →L[𝕜] 𝕜) ≃L[𝕜] (ι → 𝕜) :=
  (e.arrowCongr (.refl 𝕜 𝕜)).trans (ContinuousLinearEquiv.piRing (𝕜 := 𝕜) (E := 𝕜) ι)

@[simp] theorem dualCoords_apply (e : F ≃L[𝕜] (ι → 𝕜)) (p : F →L[𝕜] 𝕜) (i : ι) :
    e.dualCoords p i = p (e.symm (Pi.single i 1)) := by simp [dualCoords]

@[simp] theorem dualCoords_symm_apply (e : F ≃L[𝕜] (ι → 𝕜)) (w : ι → 𝕜) (v : F) :
    e.dualCoords.symm w v = ∑ i, e v i * w i := by simp [dualCoords]

/-- Pairing a coordinate vector `v` against `e.dualCoords p` evaluates `p` on `e.symm v`. -/
theorem sum_mul_dualCoords_apply (e : F ≃L[𝕜] (ι → 𝕜)) (p : F →L[𝕜] 𝕜) (v : ι → 𝕜) :
    ∑ i, v i * e.dualCoords p i = p (e.symm v) := by
  have hv : (∑ i, v i • Pi.single i (1 : 𝕜)) = v := by ext j; simp [Pi.single_apply]
  calc ∑ i, v i * e.dualCoords p i
      = p (e.symm (∑ i, v i • Pi.single i 1)) := by
        simp [dualCoords_apply, ← smul_eq_mul, map_sum, _root_.map_smul]
    _ = p (e.symm v) := by rw [hv]

/-- Changing dual coordinates from `e₁` to `e₂` is the transpose of changing primal coordinates from
`e₂` to `e₁`. -/
theorem dualCoords_symm_trans_dualCoords (e₁ : F ≃L[𝕜] (ι → 𝕜)) (e₂ : F ≃L[𝕜] (κ → 𝕜)) :
    ((e₁.dualCoords.symm.trans e₂.dualCoords : (ι → 𝕜) →L[𝕜] (κ → 𝕜))) =
      (e₂.symm.trans e₁ : (κ → 𝕜) →L[𝕜] (ι → 𝕜)).piTranspose := by
  refine (_root_.ContinuousLinearMap.eq_piTranspose_iff _ _).2 fun v w ↦ ?_
  exact (e₂.sum_mul_dualCoords_apply (e₁.dualCoords.symm w) v).trans
    (e₁.dualCoords_symm_apply w (e₂.symm v))

end DualCoords

end ContinuousLinearEquiv

namespace Module.Basis

section DualCoords

variable {𝕜 F ι : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] [T2Space F]
  [Fintype ι] [DecidableEq ι]

/-- In `b.equivFunL.dualCoords`, the `i`th coordinate of `p : F →L[𝕜] 𝕜` is `p (b i)`. -/
theorem dualCoords_equivFunL_apply (b : Module.Basis ι 𝕜 F) (p : F →L[𝕜] 𝕜) (i : ι) :
    b.equivFunL.dualCoords p i = p (b i) :=
  (b.equivFunL.dualCoords_apply p i).trans (congrArg p (b.equivFunL.injective (by simp)))

/-- Reconstructing a functional from its dual coordinates `w` pairs `v : F` with `w` against
`b.equivFun v`. -/
theorem dualCoords_equivFunL_symm_apply (b : Module.Basis ι 𝕜 F) (w : ι → 𝕜) (v : F) :
    b.equivFunL.dualCoords.symm w v = ∑ i, b.equivFun v i * w i :=
  b.equivFunL.dualCoords_symm_apply w v

/-- Changing dual coordinates from `b₁` to `b₂` has determinant `b₁.det b₂`. -/
theorem det_dualCoords_equivFunL_symm_trans (b₁ b₂ : Module.Basis ι 𝕜 F) :
    ((b₁.equivFunL.dualCoords.symm.trans
      b₂.equivFunL.dualCoords).toContinuousLinearMap).det = b₁.det b₂ := by
  rw [ContinuousLinearEquiv.dualCoords_symm_trans_dualCoords, ContinuousLinearMap.det_piTranspose]
  have hconj : ((b₂.equivFunL.symm.trans b₁.equivFunL : (ι → 𝕜) →L[𝕜] (ι → 𝕜)) :
      (ι → 𝕜) →ₗ[𝕜] (ι → 𝕜)) =
      b₁.equivFun.toLinearMap ∘ₗ (b₁.equiv b₂ (Equiv.refl ι)).toLinearMap ∘ₗ
        b₁.equivFun.symm.toLinearMap :=
    LinearMap.ext fun v ↦ by simp [Module.Basis.equivFun_symm_apply, map_sum, map_smul]
  rw [ContinuousLinearMap.det, hconj, LinearMap.det_conj _ b₁.equivFun, b₂.det_basis b₁]

end DualCoords

end Module.Basis

