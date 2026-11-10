/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# Boundary flux on boxes

`boxBoundarySum` is the front-minus-back face sum in Mathlib's Bochner divergence theorem.
The face parametrizations insert the omitted coordinate, in increasing coordinate order.
The codomain may be any real normed space, so quaternion-valued fluxes need no separate
integration theory.

`boxBoundarySum_eq_zero_of_hasFDerivAt` gives vanishing boundary flux for a continuous field
with pointwise derivatives and zero divergence in the open box. No continuity of the
derivatives is required. Degenerate boxes are included.
-/

public section

open MeasureTheory Set

namespace TauCeti

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The oriented boundary flux of a family of fields on a box: the integral on each front
face minus the integral on the corresponding back face. -/
noncomputable def boxBoundarySum (a b : Fin (n + 1) → ℝ)
    (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E) : E :=
  ∑ i, ((∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F i (i.insertNth (b i) x)) -
    ∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F i (i.insertNth (a i) x))

/-- The defining front-minus-back expansion of the boundary flux. -/
theorem boxBoundarySum_def (a b : Fin (n + 1) → ℝ)
    (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E) :
    boxBoundarySum a b F =
      ∑ i, ((∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F i (i.insertNth (b i) x)) -
        ∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F i (i.insertNth (a i) x)) := (rfl)

/-- On the unit cube, the boundary flux is the sum of front-minus-back integrals over
unit cubes of one lower dimension. -/
theorem boxBoundarySum_zero_one (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E) :
    boxBoundarySum 0 1 F =
      ∑ i, ((∫ x in Icc (0 : Fin n → ℝ) 1, F i (i.insertNth 1 x)) -
        ∫ x in Icc (0 : Fin n → ℝ) 1, F i (i.insertNth 0 x)) := by
  simp only [boxBoundarySum_def, Function.comp_def, Pi.zero_def, Pi.one_def]

@[simp]
theorem boxBoundarySum_zero (a b : Fin (n + 1) → ℝ) :
    boxBoundarySum a b (fun _ _ ↦ (0 : E)) = 0 := by
  simp [boxBoundarySum_def]

/-- A continuous field with pointwise derivatives of zero divergence in the open box has
zero boundary flux. Continuity of the derivatives is not assumed. -/
theorem boxBoundarySum_eq_zero_of_hasFDerivAt {a b : Fin (n + 1) → ℝ} (hab : a ≤ b)
    {F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E}
    {D : Fin (n + 1) → (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] E}
    (hc : ∀ i, ContinuousOn (F i) (Icc a b))
    (hd : ∀ x ∈ pi univ (fun i ↦ Ioo (a i) (b i)), ∀ i, HasFDerivAt (F i) (D i x) x)
    (hzero : ∀ x ∈ pi univ (fun i ↦ Ioo (a i) (b i)), ∑ i, D i x (Pi.single i 1) = 0) :
    boxBoundarySum a b F = 0 := by
  have hae : (fun x ↦ ∑ i, D i x (Pi.single i 1)) =ᵐ[volume.restrict (Icc a b)] 0 := by
    rw [volume_pi, ← Measure.restrict_congr_set Measure.univ_pi_Ioo_ae_eq_Icc]
    exact (ae_restrict_mem (isOpen_set_pi finite_univ fun _ _ ↦ isOpen_Ioo).measurableSet).mono
      fun x hx ↦ hzero x hx
  have hi : IntegrableOn (fun x ↦ ∑ i, D i x (Pi.single i 1)) (Icc a b) :=
    (integrable_zero _ E _).congr hae.symm
  have h := integral_divergence_of_hasFDerivAt_off_countable' a b hab F D ∅ countable_empty hc
    (fun x hx ↦ hd x hx.1) hi
  rw [integral_congr_ae hae] at h
  simpa only [Pi.zero_apply, integral_zero, boxBoundarySum_def] using h.symm

end TauCeti
