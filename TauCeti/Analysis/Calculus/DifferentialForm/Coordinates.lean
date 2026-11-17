/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import TauCeti.Analysis.Calculus.DifferentialForm.Basic
import TauCeti.LinearAlgebra.Determinant.Basic
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Coordinate volume forms, coordinate minor forms, and signed coordinate evaluations

Evaluating an `n`-form on the tuples obtained by omitting one of `n + 1` vectors gives its
signed coordinate coefficients (`ContinuousAlternatingMap.signedRemoveNth`). Summing the
directional derivatives of these coefficients recovers the actual exterior derivative. The
within-set identity is shared by the full-space and half-space Stokes proofs.

This file also defines the foundational real coordinate volume `m`-form
`TauCeti.coordVolumeForm` on `Fin m → ℝ` and the coordinate `n`-minor forms
`TauCeti.coordMinorForm` on `Fin (n + 1) → ℝ` (`dx₀ ∧ ⋯ ∧ dx̂ᵢ ∧ ⋯ ∧ dxₙ`), together with the
top-degree decomposition (`ContinuousAlternatingMap.eq_coordVolumeForm_smulRight`), determinant
pullback law (`TauCeti.coordVolumeForm_compContinuousLinearMap`), standard-basis evaluations, and
row-zero Laplace expansion (`TauCeti.sum_signed_mul_coordMinorForm`).
-/

public section

noncomputable section

namespace ContinuousAlternatingMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : ℕ}

/-- Signed evaluations on the tuples obtained by removing one vector, as a continuous linear
map on alternating forms. In a coordinate basis these are the vector-field coefficients used
in the divergence expression of the exterior derivative. -/
def signedRemoveNth (v : Fin (n + 1) → E) :
    (E [⋀^Fin n]→L[𝕜] F) →L[𝕜] (Fin (n + 1) → F) :=
  ContinuousLinearMap.pi fun i ↦ (-1 : 𝕜) ^ i.val • apply 𝕜 E F (i.removeNth v)

@[simp]
theorem signedRemoveNth_apply (v : Fin (n + 1) → E) (ω : E [⋀^Fin n]→L[𝕜] F)
    (i : Fin (n + 1)) : signedRemoveNth v ω i = (-1 : 𝕜) ^ i.val • ω (i.removeNth v) :=
  by simp [signedRemoveNth, ContinuousAlternatingMap.apply_apply]

/-- The sum of the directional derivatives of signed omission coefficients is the exterior
derivative on the original tuple. Only differentiability within the given set is required. -/
theorem _root_.DifferentiableWithinAt.sum_fderivWithin_signedRemoveNth {ω : E → E [⋀^Fin n]→L[𝕜] F}
    {s : Set E} {x : E} (hω : DifferentiableWithinAt 𝕜 ω s x)
    (hs : UniqueDiffWithinAt 𝕜 s x) (v : Fin (n + 1) → E) :
    (∑ i : Fin (n + 1), fderivWithin 𝕜 (signedRemoveNth v ∘ ω) s x (v i) i) =
      extDerivWithin ω s x v := by
  have hd := ((signedRemoveNth (𝕜 := 𝕜) (F := F) v).hasFDerivAt.comp_hasFDerivWithinAt x
    hω.hasFDerivWithinAt).fderivWithin hs
  rw [hd, extDerivWithin, alternatizeUncurryFin_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp [ContinuousLinearMap.comp_apply, signedRemoveNth_apply, ← Int.cast_smul_eq_zsmul 𝕜]

end ContinuousAlternatingMap

namespace TauCeti

section VolumeAndMinor

/-- The standard determinant volume `m`-form on `Fin m → ℝ`, sending an `m`-tuple of vectors to
the determinant of the `m × m` matrix having those vectors as rows. -/
def coordVolumeForm {m : ℕ} : (Fin m → ℝ) [⋀^Fin m]→L[ℝ] ℝ :=
  AlternatingMap.toContinuousAlternatingMap Matrix.detRowAlternating

/-- Evaluating `coordVolumeForm` on an `m`-tuple of vectors gives the determinant of the matrix
having those vectors as rows. -/
theorem coordVolumeForm_apply {m : ℕ} (v : Fin m → Fin m → ℝ) :
    coordVolumeForm v = (Matrix.of v).det := by
  rw [coordVolumeForm, AlternatingMap.coe_toContinuousAlternatingMap, ← Pi.basisFun_det,
    Pi.basisFun_det_apply]

/-- The underlying alternating map of `coordVolumeForm` is the determinant form of the standard
coordinate basis `Pi.basisFun ℝ (Fin m)`. -/
theorem toAlternatingMap_coordVolumeForm {m : ℕ} :
    (coordVolumeForm (m := m)).toAlternatingMap = (Pi.basisFun ℝ (Fin m)).det := by
  rw [← AlternatingMap.toContinuousAlternatingMap_symm_apply, coordVolumeForm,
    LinearEquiv.symm_apply_apply, Pi.basisFun_det]

/-- `coordVolumeForm` evaluates to `1` on the standard coordinate basis. -/
@[simp]
theorem coordVolumeForm_single {m : ℕ} :
    coordVolumeForm (fun i : Fin m ↦ Pi.single i (1 : ℝ)) = 1 := by
  have hb : (fun i : Fin m ↦ Pi.single i (1 : ℝ)) = Pi.basisFun ℝ (Fin m) :=
    funext fun i ↦ (Pi.basisFun_apply ℝ (Fin m) i).symm
  rw [hb, ← ContinuousAlternatingMap.coe_toAlternatingMap, toAlternatingMap_coordVolumeForm,
    Module.Basis.det_self]

/-- Every continuous alternating `m`-form on `Fin m → ℝ` into a real normed space `E` equals
`coordVolumeForm` tensored with its value on the standard basis. -/
theorem _root_.ContinuousAlternatingMap.eq_coordVolumeForm_smulRight {m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (η : (Fin m → ℝ) [⋀^Fin m]→L[ℝ] E) :
    η = coordVolumeForm.smulRight (η (fun i ↦ Pi.single i 1)) := by
  refine ContinuousAlternatingMap.toAlternatingMap_injective ?_
  have hb : (Pi.basisFun ℝ (Fin m) : Fin m → Fin m → ℝ) = fun i ↦ Pi.single i 1 :=
    funext (Pi.basisFun_apply ℝ (Fin m))
  have h := η.toAlternatingMap.eq_basis_det_smulRight (Pi.basisFun ℝ (Fin m))
  have hsmul :
      ((coordVolumeForm (m := m)).smulRight (η fun i ↦ Pi.single i 1)).toAlternatingMap =
        (coordVolumeForm (m := m)).toAlternatingMap.smulRight (η fun i ↦ Pi.single i 1) := by
    ext v
    simp
  rw [hsmul, toAlternatingMap_coordVolumeForm]
  rwa [hb, ContinuousAlternatingMap.coe_toAlternatingMap] at h

/-- Pulling `coordVolumeForm` back along a continuous linear endomorphism multiplies it by the
signed determinant. -/
theorem coordVolumeForm_compContinuousLinearMap {m : ℕ}
    (L : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ)) :
    coordVolumeForm.compContinuousLinearMap L =
      LinearMap.det L.toLinearMap • coordVolumeForm := by
  refine ContinuousAlternatingMap.toAlternatingMap_injective ?_
  have hcomp :
      ((coordVolumeForm (m := m)).compContinuousLinearMap L).toAlternatingMap =
        (coordVolumeForm (m := m)).toAlternatingMap.compLinearMap L.toLinearMap := by
    ext v
    simp [Function.comp_def]
  rw [hcomp, ContinuousAlternatingMap.toAlternatingMap_smul]
  exact coordVolumeForm.toAlternatingMap.compLinearMap_eq_det_smul
    (Pi.basisFun ℝ (Fin m)) L.toLinearMap

/-- The real `n`-form on `Fin (n + 1) → ℝ` omitting coordinate `i`: the determinant of the `n × n`
matrix of remaining coordinates of `n` vectors, i.e., `dx₀ ∧ ⋯ ∧ dx̂ᵢ ∧ ⋯ ∧ dxₙ`. -/
def coordMinorForm {n : ℕ} (i : Fin (n + 1)) : (Fin (n + 1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ :=
  AlternatingMap.toContinuousAlternatingMap
    (Matrix.detRowAlternating.compLinearMap (LinearMap.funLeft ℝ ℝ i.succAbove))

/-- Evaluating `coordMinorForm i` on an `n`-tuple of vectors gives the determinant of the `n × n`
matrix obtained by omitting column `i`. -/
theorem coordMinorForm_apply {n : ℕ} (i : Fin (n + 1)) (v : Fin n → Fin (n + 1) → ℝ) :
    coordMinorForm i v = (Matrix.of fun r c ↦ v r (i.succAbove c)).det := by
  rw [coordMinorForm, AlternatingMap.coe_toContinuousAlternatingMap,
    AlternatingMap.compLinearMap_apply, ← Pi.basisFun_det, Pi.basisFun_det_apply]
  rfl

/-- Laplace expansion along row zero expresses the `(n + 1) × (n + 1)` determinant with top row `w`
and remaining rows `v` as the alternating pairing of `w` with `coordMinorForm`. -/
theorem sum_signed_mul_coordMinorForm {n : ℕ} (w : Fin (n + 1) → ℝ)
    (v : Fin n → Fin (n + 1) → ℝ) :
    ∑ i : Fin (n + 1), (-1 : ℝ) ^ (i : ℕ) * w i * coordMinorForm i v =
      (Matrix.of (Fin.cons w v)).det := by
  rw [Matrix.det_succ_row_zero]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [coordMinorForm_apply]
  rfl

/-- `coordMinorForm i` evaluates to `1` on the standard basis omitting `i` and to `0` when a
different basis vector is omitted. -/
@[simp]
theorem coordMinorForm_succAbove_single {n : ℕ} (i j : Fin (n + 1)) :
    coordMinorForm i (fun r ↦ Pi.single (j.succAbove r) 1) = if i = j then 1 else 0 := by
  rw [coordMinorForm_apply]
  split_ifs with h
  · subst h
    have h1 : (Matrix.of fun r c : Fin n ↦
        (Pi.single (i.succAbove r) (1 : ℝ) : Fin (n + 1) → ℝ) (i.succAbove c)) = 1 := by
      ext r c
      simp [Pi.single_apply, (Fin.succAbove_right_injective (p := i)).eq_iff, Matrix.one_apply,
        eq_comm]
    rw [h1, Matrix.det_one]
  · obtain ⟨c, hc⟩ := Fin.exists_succAbove_eq (Ne.symm h)
    exact Matrix.det_eq_zero_of_column_eq_zero c fun r ↦ by simp [hc]

/-- `coordMinorForm i` evaluated on `j.removeNth` of the standard basis equals `1` if `i = j` and
`0` otherwise. -/
@[simp]
theorem coordMinorForm_removeNth_single {n : ℕ} (i j : Fin (n + 1)) :
    coordMinorForm i (j.removeNth fun k : Fin (n + 1) ↦ (Pi.single k 1 : Fin (n + 1) → ℝ)) =
      if i = j then 1 else 0 :=
  coordMinorForm_succAbove_single i j

end VolumeAndMinor

end TauCeti
