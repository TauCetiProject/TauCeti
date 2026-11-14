/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Analysis.Normed.Operator.Kronecker
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

On `Fin`-indexed Kronecker coordinates, `piTranspose` commutes with `kronecker`, identifies
`S.piTranspose.kronecker R` with `homCoordConj S R`, and makes `kroneckerCoev` and `kroneckerEv`
dinatural with respect to `piTranspose`.

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

section Kronecker

variable {m m' n n' : ℕ}

/-- Transposing a Kronecker product transposes each factor. -/
@[simp] theorem piTranspose_kronecker (f : (Fin m → 𝕜) →L[𝕜] (Fin m' → 𝕜))
    (g : (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜)) :
    (f.kronecker g).piTranspose = f.piTranspose.kronecker g.piTranspose := by
  refine (ContinuousLinearEquiv.finProdCLM 𝕜 (m' * n') (m * n)).symm.injective ?_
  ext k
  obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective k
  obtain ⟨⟨i', j'⟩, rfl⟩ := finProdFinEquiv.surjective a
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective b
  rw [ContinuousLinearEquiv.finProdCLM_symm_apply, ContinuousLinearEquiv.finProdCLM_symm_apply,
    kronecker_single, piTranspose_apply, piTranspose_apply, piTranspose_apply]
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte]
  exact kronecker_single f g i j i' j'

/-- On `Fin (_ * _) → 𝕜`, `S.piTranspose.kronecker R` equals operator conjugation `homCoordConj S R`
via `ContinuousLinearEquiv.finProdCLM`. -/
theorem piTranspose_kronecker_eq_homCoordConj (S : (Fin m' → 𝕜) →L[𝕜] (Fin m → 𝕜))
    (R : (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜)) :
    S.piTranspose.kronecker R = homCoordConj S R := by
  refine ContinuousLinearMap.ext fun v ↦ (ContinuousLinearEquiv.finProdCLM 𝕜 m' n').injective <|
    ContinuousLinearMap.ext fun u' ↦ funext fun j' ↦ ?_
  rw [finProdCLM_homCoordConj, comp_apply, comp_apply, ContinuousLinearEquiv.finProdCLM_apply]
  simp only [kronecker_apply]
  rw [sum_mul_piTranspose]
  have hlin : ContinuousLinearEquiv.finProdCLM 𝕜 m n v (S u') =
      ∑ i : Fin m, S u' i • fun j ↦ v (finProdFinEquiv (i, j)) := by
    ext j; simp [ContinuousLinearEquiv.finProdCLM_apply, Finset.sum_apply, smul_eq_mul]
  rw [hlin, map_sum]
  simp [Finset.sum_apply, smul_eq_mul]

/-- Coevaluation is dinatural with respect to `piTranspose`: acting on the left factor by `f`
agrees with acting on the right factor by `f.piTranspose`. -/
theorem kronecker_comp_kroneckerCoev (f : (Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜)) :
    (f.kronecker (ContinuousLinearMap.id 𝕜 (Fin m → 𝕜))).comp (kroneckerCoev 𝕜 m) =
      ((ContinuousLinearMap.id 𝕜 (Fin n → 𝕜)).kronecker f.piTranspose).comp
        (kroneckerCoev 𝕜 n) := by
  refine ContinuousLinearMap.ext fun c ↦ funext fun k ↦ ?_
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
  simp only [comp_apply, kronecker_apply, id_apply, kroneckerCoev_apply]
  have h₁ : (fun i' : Fin m ↦ if i' = j then c 0 else 0) = c 0 • Pi.single j 1 := by
    ext i'; simp [Pi.single_apply, eq_comm]
  have h₂ : (fun j' : Fin n ↦ if i = j' then c 0 else 0) = c 0 • Pi.single i 1 := by
    ext j'; simp [Pi.single_apply, eq_comm]
  rw [h₁, h₂, f.map_smul, f.piTranspose.map_smul, Pi.smul_apply, Pi.smul_apply, piTranspose_apply]
  simp [Pi.single_apply]

/-- When `T.comp S = id`, `T ⊗ S.piTranspose` carries `kroneckerCoev 𝕜 m` to `kroneckerCoev 𝕜 n`. -/
theorem kronecker_piTranspose_comp_kroneckerCoev {T : (Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜)}
    {S : (Fin n → 𝕜) →L[𝕜] (Fin m → 𝕜)} (hTS : T.comp S = ContinuousLinearMap.id 𝕜 _) :
    (T.kronecker S.piTranspose).comp (kroneckerCoev 𝕜 m) = kroneckerCoev 𝕜 n := by
  have h : T.kronecker S.piTranspose =
      (T.kronecker (ContinuousLinearMap.id 𝕜 (Fin n → 𝕜))).comp
        ((ContinuousLinearMap.id 𝕜 (Fin m → 𝕜)).kronecker S.piTranspose) := by
    rw [kronecker_comp_kronecker, comp_id, id_comp]
  rw [h, comp_assoc, ← kronecker_comp_kroneckerCoev S, ← comp_assoc,
    kronecker_comp_kronecker, hTS, id_comp, id_kronecker_id, id_comp]

/-- Evaluation is dinatural with respect to `piTranspose`: acting on the left factor by
`f.piTranspose` agrees with acting on the right factor by `f`. -/
theorem kroneckerEv_comp_kronecker (f : (Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜)) :
    (kroneckerEv 𝕜 m).comp (f.piTranspose.kronecker (ContinuousLinearMap.id 𝕜 (Fin m → 𝕜))) =
      (kroneckerEv 𝕜 n).comp ((ContinuousLinearMap.id 𝕜 (Fin n → 𝕜)).kronecker f) := by
  refine ContinuousLinearMap.ext fun v ↦ funext fun z ↦ ?_
  simp only [comp_apply, kroneckerEv_apply, kronecker_apply, id_apply]
  have lhs_eq : ∑ i : Fin m, f.piTranspose (fun i' ↦ v (finProdFinEquiv (i', i))) i =
      ∑ i : Fin m, ∑ j : Fin n, f (Pi.single i 1) j * v (finProdFinEquiv (j, i)) :=
    Finset.sum_congr rfl fun i _ ↦ piTranspose_apply f _ i
  rw [lhs_eq, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hrow : (fun i : Fin m ↦ v (finProdFinEquiv (j, i))) =
      ∑ i : Fin m, v (finProdFinEquiv (j, i)) • Pi.single i 1 := by
    ext i; simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hrow, map_sum]
  simp [Finset.sum_apply, smul_eq_mul, mul_comm]

/-- When `S.comp T = id`, `S.piTranspose ⊗ T` intertwines `kroneckerEv 𝕜 n` with
`kroneckerEv 𝕜 m`. -/
theorem kroneckerEv_comp_piTranspose_kronecker {S : (Fin n → 𝕜) →L[𝕜] (Fin m → 𝕜)}
    {T : (Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜)} (hST : S.comp T = ContinuousLinearMap.id 𝕜 _) :
    (kroneckerEv 𝕜 n).comp (S.piTranspose.kronecker T) = kroneckerEv 𝕜 m := by
  have h : S.piTranspose.kronecker T =
      (S.piTranspose.kronecker (ContinuousLinearMap.id 𝕜 (Fin n → 𝕜))).comp
        ((ContinuousLinearMap.id 𝕜 (Fin m → 𝕜)).kronecker T) := by
    rw [kronecker_comp_kronecker, comp_id, id_comp]
  rw [h, ← comp_assoc, kroneckerEv_comp_kronecker S, comp_assoc,
    kronecker_comp_kronecker, id_comp, hST, id_kronecker_id, comp_id]

end Kronecker

end ContinuousLinearMap
