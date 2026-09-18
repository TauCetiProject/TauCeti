/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Integrability of a random symmetric matrix

A symmetric matrix is determined by its entries above the diagonal, and reading them off is a
continuous linear equivalence with a finite product of copies of `ℝ`. A random symmetric matrix is
therefore Bochner integrable exactly when each of its entries is, which is how the moments of a
symmetric-matrix law are computed entry by entry.
-/

public section

open MeasureTheory

namespace TauCeti

variable {p : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {f : Ω → selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)}

/-- **A random symmetric matrix is integrable exactly when all of its entries are.** -/
theorem integrable_iff_integrable_coe_apply :
    Integrable f μ ↔ ∀ i j, Integrable (fun ω => (f ω : Matrix (Fin p) (Fin p) ℝ) i j) μ := by
  constructor
  · intro h i j
    have hcoords : Integrable (fun ω => symmetricCoordinates p (f ω)) μ :=
      (symmetricCoordinates p).toContinuousLinearMap.integrable_comp h
    rcases le_total i j with hle | hle
    · simpa only [symmetricCoordinates_apply] using hcoords.eval (⟨(i, j), hle⟩ : upperTriangle p)
    · have h' := hcoords.eval (⟨(j, i), hle⟩ : upperTriangle p)
      simp only [symmetricCoordinates_apply] at h'
      simpa only [selfAdjoint.coe_apply_comm] using h'
  · intro h
    have hcoords : Integrable (fun ω => symmetricCoordinates p (f ω)) μ := by
      rw [← memLp_one_iff_integrable]
      refine MemLp.of_eval fun ij => ?_
      simpa only [symmetricCoordinates_apply] using memLp_one_iff_integrable.2 (h ij.1.1 ij.1.2)
    have hcomp : ((symmetricCoordinates p).symm.toContinuousLinearMap ∘
        fun ω => symmetricCoordinates p (f ω)) = f := by
      funext ω
      simp
    rw [← hcomp]
    exact (symmetricCoordinates p).symm.toContinuousLinearMap.integrable_comp hcoords

end TauCeti
