/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import TauCeti.Analysis.Calculus.DifferentialForm.Basic
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Coordinate minor forms and signed coordinate evaluations

Evaluating an `n`-form on the tuples obtained by omitting one of `n + 1` vectors gives its
signed coordinate coefficients (`ContinuousAlternatingMap.signedRemoveNth`). Summing the
directional derivatives of these coefficients recovers the actual exterior derivative. The
within-set identity is shared by the full-space and half-space Stokes proofs.

This file also defines the real coordinate `n`-minor forms `TauCeti.coordMinorForm` on
`Fin (n + 1) → ℝ` (`dx₀ ∧ ⋯ ∧ dx̂ᵢ ∧ ⋯ ∧ dxₙ`), together with standard-basis omission evaluation
(`TauCeti.coordMinorForm_removeNth_single`) and row-zero Laplace expansion
(`TauCeti.sum_signed_mul_coordMinorForm`).
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

section MinorForm

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

/-- `coordMinorForm i` evaluated on `j.removeNth` of the standard basis equals `1` if `i = j` and
`0` otherwise. -/
@[simp]
theorem coordMinorForm_removeNth_single {n : ℕ} (i j : Fin (n + 1)) :
    coordMinorForm i (j.removeNth fun k : Fin (n + 1) ↦ (Pi.single k 1 : Fin (n + 1) → ℝ)) =
      if i = j then 1 else 0 := by
  rw [coordMinorForm_apply]
  simp only [Fin.removeNth_apply]
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

end MinorForm

end TauCeti
