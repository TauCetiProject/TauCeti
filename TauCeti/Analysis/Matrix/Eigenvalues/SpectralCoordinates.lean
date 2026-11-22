/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Matrix.Spectrum
public import TauCeti.Analysis.Matrix.Exponential.SkewAdjoint
public import TauCeti.Analysis.Matrix.SelfAdjoint
import Mathlib.Analysis.Calculus.FDeriv.Star
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import TauCeti.Analysis.Matrix.Spectrum

/-!
# Local spectral coordinates for self-adjoint matrices

The spectral parametrization takes a real diagonal and conjugates it by a unitary frame.
Near a fixed frame, the exponential `TauCeti.expStrictUpper` of a skew-adjoint matrix with
vanishing diagonal parametrizes the transverse directions. In strict upper-triangular
coordinates the differential in each such direction multiplies by the corresponding eigenvalue
gap. This gives the local Vandermonde Jacobian in both the real and complex cases.

The fixed-frame chart `TauCeti.spectralMatrix` takes values in the self-adjoint subspace. Every
self-adjoint matrix with simple spectrum is the center of an open chart of this form, and in
the decreasing chamber its diagonal coordinate is the ordered eigenvalue vector.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*,
  Cambridge University Press (2010), proof of Theorem 2.5.2 and §4.1.
-/

public section

noncomputable section

open scoped Matrix TauCeti.SelfAdjointMatrix

namespace TauCeti

open Matrix

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

/-- The diagonal embedding of real eigenvalue coordinates as a continuous real linear map. -/
private def diagonalRealL : (Fin n → ℝ) →L[ℝ] Matrix (Fin n) (Fin n) 𝕜 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun d ↦ diagonal fun i ↦ (d i : 𝕜)
      map_add' := fun d e ↦ by simp [diagonal_add]
      map_smul' := fun c d ↦ by
        ext i j
        by_cases h : i = j <;> simp [h, Algebra.smul_def] }

private theorem diagonalRealL_apply (d : Fin n → ℝ) :
    diagonalRealL d = (diagonal fun i ↦ (d i : 𝕜)) := (rfl)

/-- The spectral parametrization in matrix coordinates based at the identity frame.
The first input is the diagonal and the second gives the transverse unitary directions. -/
def spectralCoordinates (x : SelfAdjointCoordinates n 𝕜) : SelfAdjointCoordinates n 𝕜 :=
  selfAdjointCoordinatesLinearMap
    (Unitary.conjStarAlgAut ℝ _ (expStrictUpper x.2) (diagonalRealL x.1))

/-- The parametrization reads the matrix coordinates of the unitary conjugate of the diagonal. -/
theorem spectralCoordinates_apply (x : SelfAdjointCoordinates n 𝕜) :
    spectralCoordinates x =
      selfAdjointCoordinatesLinearMap
        ((expStrictUpper x.2 : Matrix (Fin n) (Fin n) 𝕜) *
          diagonal (fun i ↦ (x.1 i : 𝕜)) *
          star (expStrictUpper x.2 : Matrix (Fin n) (Fin n) 𝕜)) := by
  rw [spectralCoordinates, Unitary.conjStarAlgAut_apply, diagonalRealL_apply]

/-- At zero angles the parametrization returns the original coordinates. -/
@[simp] theorem spectralCoordinates_zero (d : Fin n → ℝ) :
    spectralCoordinates (d, (0 : StrictUpperFin n → 𝕜)) = (d, 0) := by
  apply Prod.ext
  · funext i
    simp [spectralCoordinates_apply]
  · funext ij
    simp [spectralCoordinates_apply, diagonal_apply_ne _ (Fin.ne_of_val_ne ij.property.ne)]

/-- On each strict upper coordinate the gap operator multiplies by the column eigenvalue
minus the row eigenvalue. It fixes the real diagonal coordinates. -/
def spectralGapMap (d : Fin n → ℝ) :
    SelfAdjointCoordinates n 𝕜 →L[ℝ] SelfAdjointCoordinates n 𝕜 :=
  (ContinuousLinearMap.id ℝ _).prodMap
    (ContinuousLinearMap.pi fun ij : StrictUpperFin n ↦
      (d ij.val.2 - d ij.val.1) • ContinuousLinearMap.proj (R := ℝ) ij)

/-- The gap operator on the diagonal component. -/
@[simp] theorem spectralGapMap_fst (d : Fin n → ℝ) (v : SelfAdjointCoordinates n 𝕜) :
    (spectralGapMap d v).1 = v.1 := (rfl)

/-- The gap operator on a strict upper component. -/
@[simp] theorem spectralGapMap_snd (d : Fin n → ℝ) (v : SelfAdjointCoordinates n 𝕜)
    (ij : StrictUpperFin n) :
    (spectralGapMap d v).2 ij = (d ij.val.2 - d ij.val.1) • v.2 ij := (rfl)

/-- Each strict upper entry contributes one eigenvalue gap for each real scalar dimension. -/
theorem det_spectralGapMap (d : Fin n → ℝ) :
    (spectralGapMap (𝕜 := 𝕜) d).det =
      ∏ ij : StrictUpperFin n, (d ij.val.2 - d ij.val.1) ^ Module.finrank ℝ 𝕜 := by
  let f (ij : StrictUpperFin n) : 𝕜 →ₗ[ℝ] 𝕜 := (d ij.val.2 - d ij.val.1) • LinearMap.id
  have heq : (spectralGapMap (𝕜 := 𝕜) d).toLinearMap =
      LinearMap.id.prodMap (LinearMap.pi fun ij ↦ (f ij).comp (LinearMap.proj ij)) := by
    ext v <;> rfl
  rw [ContinuousLinearMap.det, heq, LinearMap.det_prodMap, LinearMap.det_id, one_mul,
    LinearMap.det_pi]
  simp [f, LinearMap.det_smul]

private theorem diagonalRealL_isHermitian (d : Fin n → ℝ) :
    (diagonalRealL (𝕜 := 𝕜) d).IsHermitian := by
  rw [diagonalRealL_apply]
  exact isHermitian_diagonal_of_self_adjoint _ (by ext i; simp)

/-- The relative unitary frame based at a given angle. -/
private def relativeFrame (a b : StrictUpperFin n → 𝕜) : unitaryGroup (Fin n) 𝕜 :=
  star (expStrictUpper a) * expStrictUpper b

@[simp] private theorem relativeFrame_self (a : StrictUpperFin n → 𝕜) : relativeFrame a a = 1 := by
  simp [relativeFrame]

private theorem coe_relativeFrame (a b : StrictUpperFin n → 𝕜) :
    (relativeFrame a b : Matrix (Fin n) (Fin n) 𝕜) =
      star (expStrictUpper a : Matrix (Fin n) (Fin n) 𝕜) *
        (expStrictUpper b : Matrix (Fin n) (Fin n) 𝕜) := (rfl)

private theorem expStrictUpper_mul_relativeFrame (a b : StrictUpperFin n → 𝕜) :
    expStrictUpper a * relativeFrame a b = expStrictUpper b := by
  simp [relativeFrame, ← mul_assoc]

/-- The differential of the angular coordinates in the moving unitary frame.
The differential is taken at the base angle, where the relative frame is the identity. -/
def spectralAngularFDeriv (a : StrictUpperFin n → 𝕜) :
    (StrictUpperFin n → 𝕜) →L[ℝ] (StrictUpperFin n → 𝕜) :=
  fderiv ℝ (fun b ↦ (selfAdjointCoordinatesLinearMap
    (star (expStrictUpper a : Matrix (Fin n) (Fin n) 𝕜) *
      (expStrictUpper b : Matrix (Fin n) (Fin n) 𝕜))).2) a

/-- The angular differential is the derivative of the strict upper entries of the unitary
frame relative to the frame at the base angle. -/
theorem spectralAngularFDeriv_def (a : StrictUpperFin n → 𝕜) :
    spectralAngularFDeriv a =
      fderiv ℝ (fun b ↦ (selfAdjointCoordinatesLinearMap
        (star (expStrictUpper a : Matrix (Fin n) (Fin n) 𝕜) *
          (expStrictUpper b : Matrix (Fin n) (Fin n) 𝕜))).2) a := (rfl)

section Differentiation

open scoped Matrix.Norms.L2Operator

attribute [local instance] Matrix.l2OpNormedAlgebraReal

private theorem contDiff_relativeFrame (a : StrictUpperFin n → 𝕜) {k : WithTop ℕ∞} :
    ContDiff ℝ k (fun b ↦ (relativeFrame a b : Matrix (Fin n) (Fin n) 𝕜)) := by
  simp only [coe_relativeFrame]
  exact contDiff_const.mul contDiff_expStrictUpper

/-- At zero angle, the angular differential is the identity. -/
@[simp] theorem spectralAngularFDeriv_zero :
    spectralAngularFDeriv (0 : StrictUpperFin n → 𝕜) = ContinuousLinearMap.id ℝ _ := by
  let read := (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (StrictUpperFin n → 𝕜)).comp
    selfAdjointCoordinatesLinearMap
  have h := read.hasFDerivAt.comp (0 : StrictUpperFin n → 𝕜) hasFDerivAt_expStrictUpper_zero
  have hr : read.comp skewAdjointOfStrictUpper = ContinuousLinearMap.id ℝ _ := by
    ext v ij
    simp [read, Fin.lt_def.mpr ij.property]
  simpa only [spectralAngularFDeriv_def, expStrictUpper_zero, OneMemClass.coe_one,
    star_one, Matrix.one_mul, Function.comp_def, read, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_snd'] using h.fderiv.trans hr

private theorem star_fderiv_relativeFrame (a v : StrictUpperFin n → 𝕜) :
    star (fderiv ℝ (fun b ↦ (relativeFrame a b : Matrix (Fin n) (Fin n) 𝕜)) a v) =
      -(fderiv ℝ (fun b ↦ (relativeFrame a b : Matrix (Fin n) (Fin n) 𝕜)) a v) := by
  let F (b : StrictUpperFin n → 𝕜) := (relativeFrame a b : Matrix (Fin n) (Fin n) 𝕜)
  let L := fderiv ℝ F a
  have hF : HasFDerivAt F L a :=
    ((contDiff_relativeFrame a (k := 1)).differentiable one_ne_zero a).hasFDerivAt
  have hu : (fun b ↦ F b * star (F b)) = fun _ ↦ (1 : Matrix (Fin n) (Fin n) 𝕜) :=
    funext fun b ↦ Unitary.coe_mul_star_self (relativeFrame a b)
  have he := hF.fun_mul' hF.star
  rw [hu] at he
  have hv := DFunLike.congr_fun (he.unique (hasFDerivAt_const _ _)) v
  have h1 : F a = 1 := by simp [F]
  simpa [L, F, h1, eq_neg_iff_add_eq_zero, add_comm] using hv

/-- Differentiate the conjugation in the frame in which the base matrix is diagonal. -/
private theorem hasFDerivAt_spectralCoordinates_relative (x : SelfAdjointCoordinates n 𝕜) :
    HasFDerivAt
      (fun y : SelfAdjointCoordinates n 𝕜 ↦ selfAdjointCoordinatesLinearMap
        (Unitary.conjStarAlgAut ℝ _ (relativeFrame x.2 y.2) (diagonalRealL y.1)))
      ((spectralGapMap x.1).comp
        ((ContinuousLinearMap.id ℝ _).prodMap (spectralAngularFDeriv x.2))) x := by
  let F (b : StrictUpperFin n → 𝕜) := (relativeFrame x.2 b : Matrix (Fin n) (Fin n) 𝕜)
  let L := fderiv ℝ F x.2
  have hF : HasFDerivAt F L x.2 :=
    ((contDiff_relativeFrame x.2 (k := 1)).differentiable one_ne_zero x.2).hasFDerivAt
  have h1 : F x.2 = 1 := by simp [F]
  have hFF := hF.comp x (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (StrictUpperFin n → 𝕜)).hasFDerivAt
  have hd := (diagonalRealL (𝕜 := 𝕜)).hasFDerivAt.comp x
    (ContinuousLinearMap.fst ℝ (Fin n → ℝ) (StrictUpperFin n → 𝕜)).hasFDerivAt
  have h := selfAdjointCoordinatesLinearMap.hasFDerivAt.comp x ((hFF.fun_mul' hd).fun_mul' hFF.star)
  have hread (v : StrictUpperFin n → 𝕜) (ij : StrictUpperFin n) :
      spectralAngularFDeriv x.2 v ij = L v ij.val.1 ij.val.2 := by
    let read := (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (StrictUpperFin n → 𝕜)).comp
      selfAdjointCoordinatesLinearMap
    have he : spectralAngularFDeriv x.2 = read.comp L :=
      (read.hasFDerivAt.comp x.2 hF).fderiv
    rw [he, ContinuousLinearMap.comp_apply]
    exact selfAdjointCoordinatesLinearMap_snd _ ij
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ ?_)).congr_fderiv ?_
  · rw [Unitary.conjStarAlgAut_apply]
    rfl
  · apply ContinuousLinearMap.ext
    intro v
    have hs (i j : Fin n) : star (L v.2 j i) = -(L v.2 i j) := by
      simpa only [Matrix.star_apply, Matrix.neg_apply] using
        congrFun₂ (star_fderiv_relativeFrame x.2 v.2) i j
    simp only [ContinuousLinearMap.comp_apply, Function.comp_apply,
      ContinuousLinearMap.coe_prodMap',
      ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst', add_apply, smul_apply,
      h1, star_one, Matrix.one_mul, diagonalRealL_apply]
    apply Prod.ext <;> funext i
    · simp [mul_diagonal, diagonal_mul, hs, mul_comm]
    · simp [hread, mul_diagonal, diagonal_mul,
        diagonal_apply_ne _ (Fin.ne_of_val_ne i.property.ne), hs, Algebra.smul_def]
      ring

/-- The spectral parametrization is smooth in the diagonal and angular variables. -/
theorem contDiff_spectralCoordinates {k : WithTop ℕ∞} :
    ContDiff ℝ k (spectralCoordinates (n := n) (𝕜 := 𝕜)) := by
  have hparam : spectralCoordinates (n := n) (𝕜 := 𝕜) = fun x ↦
      selfAdjointCoordinatesLinearMap ((expStrictUpper x.2 : Matrix (Fin n) (Fin n) 𝕜) *
        diagonalRealL x.1 * star (expStrictUpper x.2 : Matrix (Fin n) (Fin n) 𝕜)) := by
    funext x
    rw [spectralCoordinates_apply, diagonalRealL_apply]
  rw [hparam]
  have h := (contDiff_expStrictUpper (n := n) (𝕜 := 𝕜) (k := k)).comp
    (contDiff_snd : ContDiff ℝ k (Prod.snd : SelfAdjointCoordinates n 𝕜 → _))
  let S := (starL' ℝ : Matrix (Fin n) (Fin n) 𝕜 ≃L[ℝ] _).toContinuousLinearMap
  have hstar := S.contDiff.comp h
  exact (selfAdjointCoordinatesLinearMap (n := n) (𝕜 := 𝕜)).contDiff.comp
    ((h.mul ((diagonalRealL (n := n) (𝕜 := 𝕜)).contDiff.comp contDiff_fst)).mul hstar)

/-- In the moving frame, the differential is the angular differential followed by the
gap operator, with the diagonal component fixed. -/
theorem hasFDerivAt_spectralCoordinates (x : SelfAdjointCoordinates n 𝕜) :
    HasFDerivAt spectralCoordinates
      ((unitaryConjCoordinates (expStrictUpper x.2)).toContinuousLinearMap.comp
        ((spectralGapMap x.1).comp
          ((ContinuousLinearMap.id ℝ _).prodMap (spectralAngularFDeriv x.2)))) x := by
  have h := (unitaryConjCoordinates (expStrictUpper x.2)).toContinuousLinearMap.hasFDerivAt.comp x
    (hasFDerivAt_spectralCoordinates_relative x)
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ ?_)
  let A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) 𝕜) :=
    ⟨Unitary.conjStarAlgAut ℝ _ (relativeFrame x.2 y.2) (diagonalRealL y.1),
      (diagonalRealL_isHermitian (𝕜 := 𝕜) y.1).isSelfAdjoint.conjugate
        (relativeFrame x.2 y.2)⟩
  simp only [Function.comp_apply, ContinuousLinearEquiv.coe_coe]
  rw [unitaryConjCoordinates_apply_selfAdjointCoordinatesLinearMap (A := A)]
  simp only [A, ← Unitary.conjStarAlgAut_mul_apply, expStrictUpper_mul_relativeFrame,
    spectralCoordinates]

end Differentiation

/-- The absolute Jacobian factors as the angular Jacobian times the Vandermonde in the
diagonal, raised to the real dimension of the scalar field. -/
theorem abs_det_fderiv_spectralCoordinates (x : SelfAdjointCoordinates n 𝕜) :
    |(fderiv ℝ spectralCoordinates x).det| =
      |(spectralAngularFDeriv x.2).det| *
        ∏ ij : StrictUpperFin n, |x.1 ij.val.2 - x.1 ij.val.1| ^ Module.finrank ℝ 𝕜 := by
  rw [(hasFDerivAt_spectralCoordinates x).fderiv]
  have h : ((ContinuousLinearMap.id ℝ (Fin n → ℝ)).prodMap
        (spectralAngularFDeriv x.2)).det = (spectralAngularFDeriv x.2).det :=
    (LinearMap.det_prodMap LinearMap.id (spectralAngularFDeriv x.2).toLinearMap).trans
      (by rw [LinearMap.det_id, one_mul])
  rw [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp,
    ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp, abs_mul, abs_mul]
  rw [abs_det_unitaryConjCoordinates, one_mul]
  -- Return to the continuous-linear-map determinants after applying multiplicativity.
  change |(spectralGapMap (𝕜 := 𝕜) x.1).det| *
    |((ContinuousLinearMap.id ℝ (Fin n → ℝ)).prodMap (spectralAngularFDeriv x.2)).det| = _
  rw [h, det_spectralGapMap, Finset.abs_prod]
  simp only [abs_pow, mul_comm]

/-- At a diagonal with distinct entries, spectral coordinates give a local chart
centered at zero angle, in any fixed unitary frame. -/
theorem exists_spectralCoordinates_openPartialHomeomorph (d : Fin n → ℝ)
    (hd : Function.Injective d) (U : unitaryGroup (Fin n) 𝕜) :
    ∃ e : OpenPartialHomeomorph (SelfAdjointCoordinates n 𝕜) (SelfAdjointCoordinates n 𝕜),
      (e : _ → _) = unitaryConjCoordinates U ∘ spectralCoordinates ∧
      (d, (0 : StrictUpperFin n → 𝕜)) ∈ e.source := by
  let x : SelfAdjointCoordinates n 𝕜 := (d, 0)
  let L := fderiv ℝ spectralCoordinates x
  have hL : L.det ≠ 0 := by
    rw [← abs_ne_zero]
    rw [abs_det_fderiv_spectralCoordinates]
    simp only [x, spectralAngularFDeriv_zero]
    have hid : (ContinuousLinearMap.id ℝ (StrictUpperFin n → 𝕜)).det = 1 := LinearMap.det_id
    rw [hid, abs_one, one_mul]
    refine Finset.prod_ne_zero_iff.mpr fun ij _ ↦ ?_
    have hne := hd.ne (Fin.ne_of_val_ne ij.property.ne).symm
    exact pow_ne_zero _ (abs_ne_zero.mpr (sub_ne_zero.mpr hne))
  let L' := (LinearMap.equivOfIsUnitDet (isUnit_iff_ne_zero.mpr hL)).toContinuousLinearEquiv
  have hL' : L'.toContinuousLinearMap = L := by
    apply ContinuousLinearMap.ext
    exact LinearMap.equivOfIsUnitDet_apply _
  have hF := hasFDerivAt_spectralCoordinates x
  have hF' : HasFDerivAt spectralCoordinates L'.toContinuousLinearMap x := by
    rw [hL']
    exact hF.differentiableAt.hasFDerivAt
  have h := (contDiff_spectralCoordinates (k := 1)).contDiffAt.hasStrictFDerivAt hF' one_ne_zero
  refine ⟨(h.toOpenPartialHomeomorph _).transHomeomorph (unitaryConjCoordinates U).toHomeomorph,
    ?_, h.mem_toOpenPartialHomeomorph_source⟩
  exact congrArg (fun f ↦ unitaryConjCoordinates U ∘ f) h.toOpenPartialHomeomorph_coe

/-- Conjugate the real diagonal of the first component by the fixed frame and the
transverse unitary exponential of the second component. -/
def spectralMatrix (U : unitaryGroup (Fin n) 𝕜) (x : SelfAdjointCoordinates n 𝕜) :
    selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) 𝕜) :=
  selfAdjointCoordinates.symm (unitaryConjCoordinates U (spectralCoordinates x))

/-- In self-adjoint coordinates the fixed-frame chart is the unitary coordinate change of the
spectral parametrization. -/
@[simp] theorem selfAdjointCoordinates_spectralMatrix (U : unitaryGroup (Fin n) 𝕜)
    (x : SelfAdjointCoordinates n 𝕜) :
    selfAdjointCoordinates (spectralMatrix U x) =
      unitaryConjCoordinates U (spectralCoordinates x) :=
  selfAdjointCoordinates.apply_symm_apply _

/-- Ambient matrix formula for spectral coordinates in a fixed unitary frame. -/
theorem coe_spectralMatrix (U : unitaryGroup (Fin n) 𝕜) (x : SelfAdjointCoordinates n 𝕜) :
    (spectralMatrix U x : Matrix (Fin n) (Fin n) 𝕜) =
      Unitary.conjStarAlgAut ℝ _ (U * expStrictUpper x.2) (diagonal fun i ↦ (x.1 i : 𝕜)) := by
  let D := diagonal fun i : Fin n ↦ (x.1 i : 𝕜)
  have hD : IsSelfAdjoint D :=
    (isHermitian_diagonal_of_self_adjoint _ (by ext i; simp)).isSelfAdjoint
  let B : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) 𝕜) :=
    ⟨Unitary.conjStarAlgAut ℝ _ (expStrictUpper x.2) D, hD.conjugate (expStrictUpper x.2)⟩
  have hB : spectralCoordinates x = selfAdjointCoordinatesLinearMap B.val := by
    rw [spectralCoordinates_apply]
    rfl
  have hC : selfAdjointCoordinates ((UnitaryGroup.selfAdjointConj U) B) =
      selfAdjointCoordinatesLinearMap (Unitary.conjStarAlgAut ℝ _ U B.val) := by
    rw [selfAdjointCoordinates_apply, UnitaryGroup.coe_selfAdjointConj_apply]
    rfl
  rw [spectralMatrix, hB, unitaryConjCoordinates_apply_selfAdjointCoordinatesLinearMap, ← hC,
    ContinuousLinearEquiv.symm_apply_apply, UnitaryGroup.coe_selfAdjointConj_apply]
  exact (Unitary.conjStarAlgAut_mul_apply U (expStrictUpper x.2) D).symm

/-- In the decreasing chamber the diagonal coordinate is the ordered eigenvalue vector. -/
theorem eigenvalues₀_spectralMatrix (U : unitaryGroup (Fin n) 𝕜) (x : SelfAdjointCoordinates n 𝕜)
    (hd : Antitone x.1) :
    (selfAdjoint.isHermitian_coe (spectralMatrix U x)).eigenvalues₀ =
      x.1 ∘ Fin.cast (Fintype.card_fin n) := by
  let hA := selfAdjoint.isHermitian_coe (spectralMatrix U x)
  have hB : (Unitary.conjStarAlgAut ℝ _ (U * expStrictUpper x.2)
      (diagonal fun i ↦ (x.1 i : 𝕜))).IsHermitian := coe_spectralMatrix U x ▸ hA
  rw [← List.ofFn_inj, ← hA.sort_roots_charpoly_eq_eigenvalues₀, coe_spectralMatrix,
    hB.sort_roots_charpoly_eq_eigenvalues₀,
    eigenvalues₀_conjStarAlgAut_diagonal (U * expStrictUpper x.2) hd hB]

/-- Every simple self-adjoint matrix is the center of a local spectral chart. -/
theorem exists_spectralMatrix_openPartialHomeomorph
    (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) 𝕜))
    (hs : Function.Injective (selfAdjoint.isHermitian_coe A).eigenvalues) :
    ∃ (U : unitaryGroup (Fin n) 𝕜) (d : Fin n → ℝ)
      (e : OpenPartialHomeomorph (SelfAdjointCoordinates n 𝕜)
        (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) 𝕜))),
      (e : _ → _) = spectralMatrix U ∧ (d, 0) ∈ e.source ∧ e (d, 0) = A := by
  let hA := selfAdjoint.isHermitian_coe A
  obtain ⟨e, he, hsource⟩ := exists_spectralCoordinates_openPartialHomeomorph hA.eigenvalues hs
    hA.eigenvectorUnitary
  let e' := e.transHomeomorph selfAdjointCoordinates.symm.toHomeomorph
  have he' : (e' : _ → _) = spectralMatrix hA.eigenvectorUnitary := by
    funext x
    exact congrArg selfAdjointCoordinates.symm (congrFun he x)
  refine ⟨hA.eigenvectorUnitary, hA.eigenvalues, e', he', hsource, ?_⟩
  apply Subtype.ext
  rw [he', coe_spectralMatrix, expStrictUpper_zero, mul_one]
  exact hA.spectral_theorem.symm

end TauCeti
