/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

import TauCeti.MeasureTheory.Constructions.Pi

/-!
# Lebesgue measure under matrix vectorization

Column-stacking vectorization preserves product Lebesgue measure, also when either index type
is empty. Thus a density on Euclidean vector coordinates transfers to a matrix density without
a Jacobian factor. The proof regroups product coordinates with `TauCeti.measurePreserving_piCurry`
and uses Mathlib's `PiLp.volume_preserving_toLp` for the Euclidean volume normalization.
-/

public section

noncomputable section

open MeasureTheory

namespace Matrix

/-- Matrices inherit the product measure of their entries. -/
instance instMeasureSpace {m n α : Type*} [Fintype m] [Fintype n] [MeasureSpace α] :
    MeasureSpace (Matrix m n α) where
  volume := (volume : Measure (m → n → α)).map (Matrix.ofMeasurableEquiv m n α)

/-- Reading an array of entries as a matrix preserves product volume. -/
theorem volume_preserving_ofMeasurableEquiv (m n α : Type*) [Fintype m] [Fintype n]
    [MeasureSpace α] : MeasurePreserving (Matrix.ofMeasurableEquiv m n α) volume volume :=
  ⟨(Matrix.ofMeasurableEquiv m n α).measurable, rfl⟩

/-- Product matrix volume is sigma-finite whenever entry volume is. -/
instance instSigmaFiniteVolume {m n α : Type*} [Fintype m] [Fintype n] [MeasureSpace α]
    [SigmaFinite (volume : Measure α)] : SigmaFinite (volume : Measure (Matrix m n α)) := by
  rw [← (volume_preserving_ofMeasurableEquiv m n α).map_eq]
  exact (Matrix.ofMeasurableEquiv m n α).sigmaFinite_map

end Matrix

namespace TauCeti

/-- Column-stacking vectorization carries product Lebesgue measure on real matrices to Euclidean
volume on the vectorized coordinates. -/
theorem volume_preserving_matrixVecMeasurableEquiv {m n : Type*} [Fintype m] [Fintype n] :
    MeasurePreserving (matrixVecMeasurableEquiv (m := m) (n := n) (α := ℝ) 2) volume volume := by
  let e : n × m ≃ (Σ _ : m, n) :=
    (Equiv.prodComm n m).trans (Equiv.sigmaEquivProd m n).symm
  have hc := (measurePreserving_piCurry (fun _ : m => fun _ : n => (volume : Measure ℝ))).symm
    (MeasurableEquiv.piCurry _)
  have hr := (measurePreserving_piCongrLeft (fun _ : (Σ _ : m, n) => (volume : Measure ℝ)) e).symm
    (MeasurableEquiv.piCongrLeft _ e)
  have hp := PiLp.volume_preserving_toLp (n × m)
  rw [volume_pi] at hp
  have h := hp.comp (hr.comp hc)
  have ho := (Matrix.volume_preserving_ofMeasurableEquiv m n ℝ).symm
    (Matrix.ofMeasurableEquiv m n ℝ)
  simp only [volume_pi] at ho
  refine (h.comp ho).congr (MeasurableEquiv.measurable _) (ae_of_all _ fun X => ?_)
  rw [matrixVecMeasurableEquiv_apply]
  ext ⟨j, i⟩
  simp [e, MeasurableEquiv.piCongrLeft]
  rfl

end TauCeti
