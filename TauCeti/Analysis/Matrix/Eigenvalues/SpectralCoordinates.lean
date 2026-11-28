/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import TauCeti.Analysis.Matrix.Eigenvalues.Basic
public import Mathlib.LinearAlgebra.Vandermonde
public import TauCeti.Analysis.Matrix.Exponential.SkewAdjoint
public import TauCeti.Analysis.Matrix.SelfAdjoint
import TauCeti.Analysis.Calculus.FDeriv.Unitary
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import TauCeti.LinearAlgebra.Vandermonde
import TauCeti.Topology.Order.FiniteFamily
import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Basic
import TauCeti.Topology.Algebra.Module.Determinant

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

/-- The spectral parametrization in matrix coordinates based at the identity frame.
The first input is the diagonal and the second gives the transverse unitary directions. -/
def spectralCoordinates (x : SelfAdjointCoordinates n 𝕜) : SelfAdjointCoordinates n 𝕜 :=
  selfAdjointCoordinatesLinearMap
    (Unitary.conjStarAlgAut ℝ _ (expStrictUpper x.2) (selfAdjointDiagonal (𝕜 := 𝕜) x.1))

/-- The parametrization reads the matrix coordinates of the unitary conjugate of the diagonal. -/
theorem spectralCoordinates_apply (x : SelfAdjointCoordinates n 𝕜) :
    spectralCoordinates x =
      selfAdjointCoordinatesLinearMap
        ((expStrictUpper x.2 : Matrix (Fin n) (Fin n) 𝕜) *
          diagonal (fun i ↦ (x.1 i : 𝕜)) *
          star (expStrictUpper x.2 : Matrix (Fin n) (Fin n) 𝕜)) := by
  rw [spectralCoordinates, Unitary.conjStarAlgAut_apply, coe_selfAdjointDiagonal]

/-- At zero angles the parametrization returns the original coordinates. -/
@[simp] theorem spectralCoordinates_zero (d : Fin n → ℝ) :
    spectralCoordinates (d, (0 : FinStrictUpper n → 𝕜)) = (d, 0) := by
  apply Prod.ext
  · funext i
    simp [spectralCoordinates_apply]
  · funext ij
    simp [spectralCoordinates_apply, diagonal_apply_ne _ ij.property.ne]

/-- On each strict upper coordinate the gap operator multiplies by the column eigenvalue
minus the row eigenvalue. It fixes the real diagonal coordinates. -/
def spectralGapMap (d : Fin n → ℝ) :
    SelfAdjointCoordinates n 𝕜 →L[ℝ] SelfAdjointCoordinates n 𝕜 :=
  (ContinuousLinearMap.id ℝ _).prodMap
    (ContinuousLinearMap.pi fun ij : FinStrictUpper n ↦
      (d ij.val.2 - d ij.val.1) • ContinuousLinearMap.proj (R := ℝ) ij)

/-- The gap operator on the diagonal component. -/
@[simp] theorem spectralGapMap_fst (d : Fin n → ℝ) (v : SelfAdjointCoordinates n 𝕜) :
    (spectralGapMap d v).1 = v.1 := (rfl)

/-- The gap operator on a strict upper component. -/
@[simp] theorem spectralGapMap_snd (d : Fin n → ℝ) (v : SelfAdjointCoordinates n 𝕜)
    (ij : FinStrictUpper n) :
    (spectralGapMap d v).2 ij = (d ij.val.2 - d ij.val.1) • v.2 ij := (rfl)

/-- Each strict upper entry contributes one eigenvalue gap for each real scalar dimension. -/
theorem det_spectralGapMap (d : Fin n → ℝ) :
    (spectralGapMap (𝕜 := 𝕜) d).det =
      ∏ ij : FinStrictUpper n, (d ij.val.2 - d ij.val.1) ^ Module.finrank ℝ 𝕜 := by
  -- Each strict upper block is a scalar multiple of the identity on `𝕜`.
  have hf : (fun ij : FinStrictUpper n ↦
      (d ij.val.2 - d ij.val.1) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ ↦ 𝕜) ij) =
      fun ij ↦ ((d ij.val.2 - d ij.val.1) • ContinuousLinearMap.id ℝ 𝕜).comp
        (ContinuousLinearMap.proj ij) := by
    simp only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.id_comp]
  rw [spectralGapMap, ContinuousLinearMap.det_prodMap, ContinuousLinearMap.det_id, one_mul, hf,
    ContinuousLinearMap.det_pi]
  simp only [ContinuousLinearMap.det_smul, ContinuousLinearMap.det_id, mul_one]

section Differentiation

open scoped Matrix.Norms.L2Operator

attribute [local instance] Matrix.l2OpNormedAlgebraReal

/-- Differentiate the conjugation in the frame in which the base matrix is diagonal. -/
private theorem hasFDerivAt_spectralCoordinates_relative (x : SelfAdjointCoordinates n 𝕜) :
    HasFDerivAt
      (fun y : SelfAdjointCoordinates n 𝕜 ↦ selfAdjointCoordinatesLinearMap
        (Unitary.conjStarAlgAut ℝ _ (relativeFrame x.2 y.2) (selfAdjointDiagonal (𝕜 := 𝕜) y.1)))
      ((spectralGapMap x.1).comp
        ((ContinuousLinearMap.id ℝ _).prodMap (spectralAngularFDeriv x.2))) x := by
  let F (b : FinStrictUpper n → 𝕜) := (relativeFrame x.2 b : Matrix (Fin n) (Fin n) 𝕜)
  let L := fderiv ℝ F x.2
  have hF : HasFDerivAt F L x.2 :=
    ((contDiff_relativeFrame x.2 (k := 1)).differentiable one_ne_zero x.2).hasFDerivAt
  have hFF := hF.comp x (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (FinStrictUpper n → 𝕜)).hasFDerivAt
  have hd := ((selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) 𝕜)).subtypeL.comp
    selfAdjointDiagonal).hasFDerivAt.comp x
    (ContinuousLinearMap.fst ℝ (Fin n → ℝ) (FinStrictUpper n → 𝕜)).hasFDerivAt
  have hD := hFF.unitary_conj_of_eq_one hd
    (.of_forall fun y ↦ (relativeFrame x.2 y.2).property) (by simp [F])
  have h := selfAdjointCoordinatesLinearMap.hasFDerivAt.comp x hD
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ ?_)).congr_fderiv ?_
  · simp only [Unitary.conjStarAlgAut_apply, Function.comp_apply, F,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', Submodule.subtypeL_apply]
  · apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.comp_apply, Function.comp_apply,
      ContinuousLinearMap.coe_prodMap', ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.coe_fst', add_apply,
      sub_apply, ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply',
      Submodule.subtypeL_apply, coe_selfAdjointDiagonal]
    apply Prod.ext <;> funext i
    · simp [mul_diagonal, diagonal_mul, mul_comm]
    · simp [spectralAngularFDeriv_apply, mul_diagonal, diagonal_mul,
        diagonal_apply_ne _ i.property.ne, Algebra.smul_def]
      ring

/-- The spectral parametrization is smooth in the diagonal and angular variables. -/
theorem contDiff_spectralCoordinates {k : WithTop ℕ∞} :
    ContDiff ℝ k (spectralCoordinates (n := n) (𝕜 := 𝕜)) := by
  let D := (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) 𝕜)).subtypeL.comp
    (selfAdjointDiagonal (n := n) (𝕜 := 𝕜))
  have h := Matrix.UnitaryGroup.contDiff_conjStarAlgAut_expStrictUpper
    (1 : unitaryGroup (Fin n) 𝕜)
    (D.contDiff.comp contDiff_fst)
    (contDiff_snd : ContDiff ℝ k (Prod.snd : SelfAdjointCoordinates n 𝕜 → _))
  convert (selfAdjointCoordinatesLinearMap (n := n) (𝕜 := 𝕜)).contDiff.comp h using 1
  funext x
  simp only [Function.comp_apply, one_mul, D, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply, spectralCoordinates]

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
  -- Both sides are coordinates of unitary conjugates of the same self-adjoint diagonal.
  simp only [Function.comp_apply, ContinuousLinearEquiv.coe_coe]
  rw [unitaryConjCoordinates_selfAdjointCoordinatesLinearMap_conjStarAlgAut,
    expStrictUpper_mul_relativeFrame, spectralCoordinates]

end Differentiation

/-- The absolute Jacobian factors as the angular Jacobian times the Vandermonde in the
diagonal, raised to the real dimension of the scalar field. -/
theorem abs_det_fderiv_spectralCoordinates (x : SelfAdjointCoordinates n 𝕜) :
    |(fderiv ℝ spectralCoordinates x).det| =
      |(spectralAngularFDeriv x.2).det| *
        |(vandermonde x.1).det| ^ Module.finrank ℝ 𝕜 := by
  rw [abs_det_vandermonde_pow_eq_prod]
  rw [(hasFDerivAt_spectralCoordinates x).fderiv]
  simp only [ContinuousLinearMap.det_comp, ContinuousLinearMap.det_prodMap,
    ContinuousLinearMap.det_id, det_spectralGapMap, abs_mul, abs_det_unitaryConjCoordinates,
    Finset.abs_prod, abs_pow, one_mul, mul_comm]

/-- The absolute determinant of the angular differential is continuous in the base angle. -/
theorem continuous_abs_det_spectralAngularFDeriv :
    Continuous fun a : FinStrictUpper n → 𝕜 ↦ |(spectralAngularFDeriv a).det| := by
  -- At a fixed simple diagonal, the full Jacobian differs by a nonzero constant factor.
  let d₀ (i : Fin n) : ℝ := (i : ℕ)
  let g : ℝ := |(vandermonde d₀).det| ^ Module.finrank ℝ 𝕜
  have hg : g ≠ 0 :=
    pow_ne_zero _ (abs_ne_zero.mpr (det_vandermonde_ne_zero_iff.mpr
      (Nat.cast_injective.comp Fin.val_injective)))
  have h : (fun a : FinStrictUpper n → 𝕜 ↦ |(spectralAngularFDeriv a).det|) =
      fun a ↦ |(fderiv ℝ spectralCoordinates (d₀, a)).det| / g := by
    funext a
    rw [abs_det_fderiv_spectralCoordinates, mul_div_cancel_right₀ _ hg]
  rw [h]
  exact ((ContinuousLinearMap.continuous_det.comp
    ((contDiff_spectralCoordinates (k := 1)).continuous_fderiv one_ne_zero)).comp
      (continuous_const.prodMk continuous_id)).abs.div_const _

/-- At a diagonal with distinct entries, spectral coordinates give a local chart
centered at zero angle, in any fixed unitary frame. -/
theorem exists_spectralCoordinates_openPartialHomeomorph (d : Fin n → ℝ)
    (hd : Function.Injective d) (U : unitaryGroup (Fin n) 𝕜) :
    ∃ e : OpenPartialHomeomorph (SelfAdjointCoordinates n 𝕜) (SelfAdjointCoordinates n 𝕜),
      (e : _ → _) = unitaryConjCoordinates U ∘ spectralCoordinates ∧
      (d, (0 : FinStrictUpper n → 𝕜)) ∈ e.source := by
  let x : SelfAdjointCoordinates n 𝕜 := (d, 0)
  let L := fderiv ℝ spectralCoordinates x
  have hL : L.det ≠ 0 := by
    rw [← abs_ne_zero]
    rw [abs_det_fderiv_spectralCoordinates]
    simp only [x, spectralAngularFDeriv_zero, ContinuousLinearMap.det_id, abs_one, one_mul]
    exact pow_ne_zero _ (abs_ne_zero.mpr (det_vandermonde_ne_zero_iff.mpr hd))
  have hF' : HasFDerivAt spectralCoordinates
      (L.toContinuousLinearEquivOfDetNeZero hL : _ →L[ℝ] _) x := by
    rw [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
    exact (hasFDerivAt_spectralCoordinates x).differentiableAt.hasFDerivAt
  have h := (contDiff_spectralCoordinates (k := 1)).contDiffAt.hasStrictFDerivAt hF' one_ne_zero
  refine ⟨(h.toOpenPartialHomeomorph _).transHomeomorph (unitaryConjCoordinates U).toHomeomorph,
    ?_, h.mem_toOpenPartialHomeomorph_source⟩
  rw [OpenPartialHomeomorph.transHomeomorph_apply, ContinuousLinearEquiv.coe_toHomeomorph,
    h.toOpenPartialHomeomorph_coe]

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

/-- For any fixed frame the spectral chart is smooth in the diagonal and angular variables. -/
theorem contDiff_spectralMatrix {k : WithTop ℕ∞} (U : unitaryGroup (Fin n) 𝕜) :
    ContDiff ℝ k (spectralMatrix U) :=
  selfAdjointCoordinates.symm.toContinuousLinearMap.contDiff.comp
    ((unitaryConjCoordinates U).toContinuousLinearMap.contDiff.comp contDiff_spectralCoordinates)

/-- The fixed-frame chart conjugates the self-adjoint diagonal by the product of the fixed frame
and the transverse unitary exponential. -/
theorem spectralMatrix_eq_selfAdjointConj (U : unitaryGroup (Fin n) 𝕜)
    (x : SelfAdjointCoordinates n 𝕜) :
    spectralMatrix U x =
      UnitaryGroup.selfAdjointConj (U * expStrictUpper x.2) (selfAdjointDiagonal x.1) := by
  rw [spectralMatrix, spectralCoordinates,
    unitaryConjCoordinates_selfAdjointCoordinatesLinearMap_conjStarAlgAut,
    ← selfAdjointCoordinates_selfAdjointConj, ContinuousLinearEquiv.symm_apply_apply]

/-- At zero angles the spectral chart conjugates the diagonal by the fixed frame. -/
@[simp] theorem spectralMatrix_zero (U : unitaryGroup (Fin n) 𝕜) (d : Fin n → ℝ) :
    spectralMatrix U (d, 0) = UnitaryGroup.selfAdjointConj U (selfAdjointDiagonal d) := by
  rw [spectralMatrix_eq_selfAdjointConj, expStrictUpper_zero, mul_one]

/-- Ambient matrix formula for spectral coordinates in a fixed unitary frame. -/
theorem coe_spectralMatrix (U : unitaryGroup (Fin n) 𝕜) (x : SelfAdjointCoordinates n 𝕜) :
    (spectralMatrix U x : Matrix (Fin n) (Fin n) 𝕜) =
      Unitary.conjStarAlgAut ℝ _ (U * expStrictUpper x.2) (diagonal fun i ↦ (x.1 i : 𝕜)) := by
  rw [spectralMatrix_eq_selfAdjointConj, UnitaryGroup.coe_selfAdjointConj_apply,
    coe_selfAdjointDiagonal, Unitary.conjStarAlgAut_apply, star_eq_conjTranspose]

/-- In the decreasing chamber the diagonal coordinate is the ordered eigenvalue vector. -/
@[simp] theorem orderedEigenvalues_spectralMatrix (U : unitaryGroup (Fin n) 𝕜)
    (x : SelfAdjointCoordinates n 𝕜) (hd : Antitone x.1) :
    selfAdjoint.orderedEigenvalues (spectralMatrix U x) = x.1 := by
  rw [spectralMatrix_eq_selfAdjointConj, selfAdjoint.orderedEigenvalues_selfAdjointConj]
  exact selfAdjoint.orderedEigenvalues_selfAdjointDiagonal hd

/-- At a distinct real diagonal, the fixed-frame spectral matrix map is a local chart
containing the zero-angle parameter. -/
theorem exists_spectralMatrix_openPartialHomeomorph_at_diagonal (d : Fin n → ℝ)
    (hd : Function.Injective d) (U : unitaryGroup (Fin n) 𝕜) :
    ∃ e : OpenPartialHomeomorph (SelfAdjointCoordinates n 𝕜)
        (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) 𝕜)),
      (e : _ → _) = spectralMatrix U ∧ (d, 0) ∈ e.source := by
  obtain ⟨e, he, hsource⟩ := exists_spectralCoordinates_openPartialHomeomorph d hd U
  refine ⟨e.transHomeomorph selfAdjointCoordinates.symm.toHomeomorph, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.transHomeomorph_apply, ContinuousLinearEquiv.coe_toHomeomorph, he]
    rfl
  · simpa only [OpenPartialHomeomorph.transHomeomorph_source] using hsource

/-- Every simple self-adjoint matrix is the center of a local spectral chart. -/
theorem exists_spectralMatrix_openPartialHomeomorph
    (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) 𝕜))
    (hs : Function.Injective (selfAdjoint.isHermitian_coe A).eigenvalues) :
    ∃ (U : unitaryGroup (Fin n) 𝕜) (d : Fin n → ℝ)
      (e : OpenPartialHomeomorph (SelfAdjointCoordinates n 𝕜)
        (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) 𝕜))),
      (e : _ → _) = spectralMatrix U ∧ (d, 0) ∈ e.source ∧ e (d, 0) = A := by
  let hA := selfAdjoint.isHermitian_coe A
  obtain ⟨e, he, hsource⟩ := exists_spectralMatrix_openPartialHomeomorph_at_diagonal
    hA.eigenvalues hs hA.eigenvectorUnitary
  refine ⟨hA.eigenvectorUnitary, hA.eigenvalues, e, he, hsource, ?_⟩
  apply Subtype.ext
  rw [he, coe_spectralMatrix, expStrictUpper_zero, mul_one]
  exact hA.spectral_theorem.symm

section DecreasingChamber

open Filter Set Matrix.UnitaryGroup
open scoped Topology

local notation "chamber" => Set.ofPred (fun d : Fin n → ℝ ↦ StrictAnti d)
local notation "Frames" => unitaryGroup (Fin n) 𝕜
local notation "Angles" => FinStrictUpper n → 𝕜

/-- Injectivity on the angular slice of any diagonal extends to the same set of
angles over the whole decreasing chamber. -/
theorem injOn_spectralMatrix_one {d₀ : Fin n → ℝ}
    {B : Set Angles} (hB : InjOn (spectralMatrix (1 : Frames)) ({d₀} ×ˢ B)) :
    InjOn (spectralMatrix (1 : Frames)) (chamber ×ˢ B) := by
  rintro ⟨d, a⟩ ⟨hd, ha⟩ ⟨e, b⟩ ⟨he, hb⟩ h
  have hde : d = e := by
    have hh := congrArg selfAdjoint.orderedEigenvalues h
    rwa [orderedEigenvalues_spectralMatrix 1 (d, a) (StrictAnti.antitone hd),
      orderedEigenvalues_spectralMatrix 1 (e, b) (StrictAnti.antitone he)] at hh
  subst e
  simp only [spectralMatrix_eq_selfAdjointConj, one_mul,
    selfAdjointConj_diagonal_eq_iff (StrictAnti.injective hd)] at h
  have h' : spectralMatrix (1 : Frames) (d₀, a) = spectralMatrix 1 (d₀, b) := by
    simp only [spectralMatrix_eq_selfAdjointConj, one_mul]
    apply (selfAdjointConj (star (expStrictUpper b))).injective
    simp only [← selfAdjointConj_mul_apply, Unitary.star_mul_self, selfAdjointConj_one,
      LinearIsometryEquiv.coe_refl, id_eq]
    apply Subtype.ext
    simpa only [coe_selfAdjointConj_apply, coe_selfAdjointDiagonal, Unitary.conjStarAlgAut_apply,
      star_eq_conjTranspose, Function.comp_def] using
      conjStarAlgAut_diagonal_eq_of_isDiag (fun i ↦ (d₀ i : 𝕜)) _ h
  have ha₀ : (d₀, a) ∈ {d₀} ×ˢ B := ⟨mem_singleton _, ha⟩
  have hb₀ : (d₀, b) ∈ {d₀} ×ˢ B := ⟨mem_singleton _, hb⟩
  have hab : a = b := congrArg Prod.snd (hB ha₀ hb₀ h')
  exact Prod.ext rfl hab

/-- The frames whose conjugate lies in an identity-frame spectral patch are independent of the
choice of strictly decreasing diagonal. -/
theorem conj_diagonal_mem_spectralPatch_iff {d d₀ : Fin n → ℝ}
    (hd : StrictAnti d) (hd₀ : StrictAnti d₀) {B : Set Angles} (U : Frames) :
    selfAdjointConj U (selfAdjointDiagonal d) ∈ spectralMatrix 1 '' (chamber ×ˢ B) ↔
      selfAdjointConj U (selfAdjointDiagonal d₀) ∈ spectralMatrix 1 '' (chamber ×ˢ B) := by
  suffices ∀ e : Fin n → ℝ, StrictAnti e →
      (selfAdjointConj U (selfAdjointDiagonal e) ∈ spectralMatrix 1 '' (chamber ×ˢ B) ↔
        ∃ a ∈ B, Matrix.IsDiag ((star (expStrictUpper a) * U : Frames) :
          Matrix (Fin n) (Fin n) 𝕜)) by
    exact (this d hd).trans (this d₀ hd₀).symm
  intro e he
  constructor
  · rintro ⟨⟨b, a⟩, ⟨hb, ha⟩, h⟩
    have hbe : b = e := by
      have hh := congrArg selfAdjoint.orderedEigenvalues (h.trans (spectralMatrix_zero U e).symm)
      rwa [orderedEigenvalues_spectralMatrix 1 (b, a) (StrictAnti.antitone hb),
        orderedEigenvalues_spectralMatrix U (e, 0) he.antitone] at hh
    subst b
    have h' := h.symm
    simp only [spectralMatrix_eq_selfAdjointConj, one_mul,
      selfAdjointConj_diagonal_eq_iff he.injective] at h'
    exact ⟨a, ha, h'⟩
  · rintro ⟨a, ha, h⟩
    refine ⟨(e, a), ⟨he, ha⟩, ?_⟩
    symm
    simpa only [spectralMatrix_eq_selfAdjointConj, one_mul,
      selfAdjointConj_diagonal_eq_iff he.injective] using h

/-- Around zero angle, a simple diagonal has an injective angular ball whose patch over the
decreasing chamber contains the diagonal in its interior. -/
theorem exists_spectralMatrix_angularBall (d₀ : Fin n → ℝ) (hd₀ : StrictAnti d₀) :
    ∃ r > 0, InjOn (spectralMatrix (1 : Frames)) ({d₀} ×ˢ Metric.ball (0 : Angles) r) ∧
      (selfAdjointDiagonal (𝕜 := 𝕜) d₀) ∈
        interior (spectralMatrix 1 '' (chamber ×ˢ Metric.ball (0 : Angles) r)) := by
  obtain ⟨E, hE, hsource⟩ := exists_spectralMatrix_openPartialHomeomorph_at_diagonal
    d₀ hd₀.injective (1 : Frames)
  have hnhds : E.source ∩ (chamber ×ˢ (univ : Set Angles)) ∈ 𝓝 (d₀, 0) := by
    exact inter_mem (E.open_source.mem_nhds hsource)
      ((isOpen_setOf_strictAnti.prod isOpen_univ).mem_nhds ⟨hd₀, mem_univ _⟩)
  obtain ⟨s, hs, t, ht, hst⟩ := mem_nhds_prod_iff.mp hnhds
  obtain ⟨r, hr, hrt⟩ := Metric.mem_nhds_iff.mp ht
  obtain ⟨u, hus, huo, hdu⟩ := mem_nhds_iff.mp hs
  have hsub : u ×ˢ Metric.ball (0 : Angles) r ⊆ E.source :=
    subset_trans (prod_mono hus hrt) (hst.trans inter_subset_left)
  have huC : u ⊆ chamber := by
    intro d hd
    have hmem : (d, (0 : Angles)) ∈ s ×ˢ t := ⟨hus hd, mem_of_mem_nhds ht⟩
    exact (hst hmem).2.1
  refine ⟨r, hr, ?_, ?_⟩
  · rw [← hE]
    exact E.injOn.mono ((prod_mono (singleton_subset_iff.2 hdu) subset_rfl).trans hsub)
  · have hcenter : spectralMatrix (1 : Frames) (d₀, 0) = selfAdjointDiagonal d₀ := by
      simp only [spectralMatrix_zero, selfAdjointConj_one, LinearIsometryEquiv.coe_refl, id_eq]
    rw [← hcenter, ← hE]
    refine mem_interior_iff_mem_nhds.mpr (mem_of_superset
      ((E.isOpen_image_of_subset_source (huo.prod Metric.isOpen_ball) hsub).mem_nhds
        (mem_image_of_mem _ ⟨hdu, Metric.mem_ball_self hr⟩)) ?_)
    exact image_mono (prod_mono huC subset_rfl)

end DecreasingChamber

end TauCeti
