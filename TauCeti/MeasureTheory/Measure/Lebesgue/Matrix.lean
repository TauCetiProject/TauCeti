/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.MeasurableSpace
public import TauCeti.LinearAlgebra.Matrix.Triangular.Coordinates
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

import TauCeti.MeasureTheory.Constructions.Pi

/-!
# Lebesgue measure under matrix vectorization

Matrices over a measure space inherit the product measure on their entries via
`Matrix.ofMeasurableEquiv`. This measure is sigma-finite whenever the entry measure is.

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
  simp only [MeasurableEquiv.piCongrLeft, Equiv.trans_apply, Equiv.prodComm_apply,
    MeasurableEquiv.symm_mk, MeasurableEquiv.coe_mk, Function.comp_apply,
    Matrix.ofMeasurableEquiv_symm_apply, Equiv.piCongrLeft_symm_apply, Prod.swap_prod_mk,
    Equiv.sigmaEquivProd_symm_apply, MeasurableEquiv.piCurry_symm_apply, Sigma.uncurry,
    Matrix.of_symm_apply, Matrix.vec, e]

end TauCeti

namespace TauCeti

variable {n : ℕ} {R : Type*}

/-- Assemble a matrix from its upper triangular and strict lower entries as a measurable
equivalence. -/
def schurMatrixMeasurableEquiv [MeasurableSpace R] :
    SchurCoordinates n R ≃ᵐ Matrix (Fin n) (Fin n) R :=
  ((Matrix.ofMeasurableEquiv (Fin n) (Fin n) R).symm.trans <|
    (MeasurableEquiv.curry (Fin n) (Fin n) R).symm.trans <|
      (MeasurableEquiv.piEquivPiSubtypeProd (fun _ ↦ R)
        (fun ij : Fin n × Fin n ↦ ij.1 ≤ ij.2)).trans <|
        (MeasurableEquiv.refl _).prodCongr
          (MeasurableEquiv.piCongrLeft (fun _ ↦ R) (schurLowerIndexEquiv n)).symm).symm

/-- Reading the entries with the measurable equivalence agrees with the linear split. -/
private theorem schurMatrixMeasurableEquiv_symm_apply [Semiring R] [MeasurableSpace R]
    (A : Matrix (Fin n) (Fin n) R) :
    schurMatrixMeasurableEquiv.symm A = schurMatrixEquiv.symm A := by
  apply Prod.ext <;> funext ij
  · -- Curry and split read the entry indexed by the same upper position.
    exact (Matrix.schurMatrixEquiv_symm_fst A ij).symm
  · rw [Matrix.schurMatrixEquiv_symm_snd]
    let e := MeasurableEquiv.piCongrLeft (fun _ ↦ R) (schurLowerIndexEquiv n)
    let f : {ij : Fin n × Fin n // ¬ij.1 ≤ ij.2} → R := fun k ↦ A k.val.1 k.val.2
    -- The lower projection alone applies the index permutation to the flattened entries.
    change e.symm f ij = _
    have h : e (e.symm f) (schurLowerIndexEquiv n ij) = e.symm f ij :=
      MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ ↦ R)
        (schurLowerIndexEquiv n) (e.symm f) ij
    rw [MeasurableEquiv.apply_symm_apply] at h
    simpa only [f, schurLowerIndexEquiv_apply_val] using h.symm

/-- The measurable and linear assembly maps agree pointwise. -/
theorem schurMatrixMeasurableEquiv_apply [Semiring R] [MeasurableSpace R]
    (x : SchurCoordinates n R) :
    schurMatrixMeasurableEquiv x = schurMatrixEquiv x := by
  apply schurMatrixMeasurableEquiv.symm.injective
  rw [MeasurableEquiv.symm_apply_apply, schurMatrixMeasurableEquiv_symm_apply,
    LinearEquiv.symm_apply_apply]

/-- Assembling a matrix from its upper and strict lower entries preserves product volume. -/
theorem measurePreserving_schurMatrixMeasurableEquiv [MeasureSpace R]
    [SigmaFinite (volume : Measure R)] :
    MeasurePreserving (schurMatrixMeasurableEquiv (n := n) (R := R)) volume volume := by
  let p (ij : Fin n × Fin n) := ij.1 ≤ ij.2
  have hread := (Matrix.volume_preserving_ofMeasurableEquiv (Fin n) (Fin n) R).symm
    (Matrix.ofMeasurableEquiv (Fin n) (Fin n) R)
  have hflat := (measurePreserving_curry
    (fun _ _ : Fin n ↦ (volume : Measure R))).symm (MeasurableEquiv.curry (Fin n) (Fin n) R)
  have hsplit := volume_preserving_piEquivPiSubtypeProd (fun _ : Fin n × Fin n ↦ R) p
  have hswap := (volume_measurePreserving_piCongrLeft (fun _ : {ij // ¬p ij} ↦ R)
    (schurLowerIndexEquiv n)).symm (MeasurableEquiv.piCongrLeft _ (schurLowerIndexEquiv n))
  exact (((MeasurePreserving.id (volume : Measure ({ij // p ij} → R))).prod hswap).comp
    (hsplit.comp (hflat.comp hread))).symm schurMatrixMeasurableEquiv.symm

/-- Linear assembly of a matrix from its upper and strict lower entries preserves product volume. -/
theorem measurePreserving_schurMatrixEquiv [Semiring R] [MeasureSpace R]
    [SigmaFinite (volume : Measure R)] :
    MeasurePreserving (schurMatrixEquiv (n := n) (R := R)) volume volume := by
  have h : (⇑(schurMatrixMeasurableEquiv (n := n) (R := R))) = schurMatrixEquiv :=
    funext schurMatrixMeasurableEquiv_apply
  rw [← h]
  exact measurePreserving_schurMatrixMeasurableEquiv

end TauCeti
