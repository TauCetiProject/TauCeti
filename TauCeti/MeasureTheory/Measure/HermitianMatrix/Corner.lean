/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.HermitianMatrix.Lebesgue
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Splitting off the last row and column of a Hermitian matrix

A complex Hermitian matrix `T` of size `k + 1` is determined by its upper left block of size `k`,
a Hermitian matrix, by its last column above the diagonal, a vector in `ℂ ^ k`, and by its real
corner entry. `TauCeti.hermitianCornerEquiv k` is this splitting, as a measurable equivalence
from the Hermitian matrices of size `k + 1` to the product of the Hermitian matrices of size
`k`, `Fin k → ℂ` and `ℝ`. It carries `TauCeti.hermitianLebesgue (k + 1)` to the product of
`TauCeti.hermitianLebesgue k` and Lebesgue measure
(`TauCeti.measurePreserving_hermitianCornerEquiv`), since in the coordinates of
`TauCeti.hermitianCoordinates` it only regroups coordinates.

## Main declarations

* `TauCeti.hermitianCornerEquiv`, with `TauCeti.coe_hermitianCornerEquiv_fst`,
  `TauCeti.hermitianCornerEquiv_snd_fst`, `TauCeti.hermitianCornerEquiv_snd_snd`.
* `TauCeti.measurePreserving_hermitianCornerEquiv`, `TauCeti.continuous_hermitianCornerEquiv`.
-/

public section

noncomputable section

open MeasureTheory Matrix

namespace TauCeti

variable (k : ℕ)

/-- The index set of the real coordinates of a Hermitian matrix of size `k + 1`, sorted into those
of the upper left block, those of the real and imaginary parts of the last column above the
diagonal, and the corner. -/
def hermitianCornerIndex :
    (Fin k × Fin k) ⊕ ((Fin k ⊕ Fin k) ⊕ Unit) ≃ Fin (k + 1) × Fin (k + 1) :=
  Equiv.ofBijective
    (fun
      | .inl ij => (ij.1.castSucc, ij.2.castSucc)
      | .inr (.inl (.inl a)) => (a.castSucc, Fin.last k)
      | .inr (.inl (.inr a)) => (Fin.last k, a.castSucc)
      | .inr (.inr _) => (Fin.last k, Fin.last k))
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨by
      rintro (⟨i, j⟩ | (a | a) | ⟨⟩) (⟨i', j'⟩ | (a' | a') | ⟨⟩) h <;>
        simp_all [Prod.ext_iff, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm],
      by simp; ring⟩)

/-- The real coordinates of a Hermitian matrix of size `k + 1`, in the convention of
`TauCeti.hermitianCoordinates`, regrouped into the coordinates of the upper left block, the last
column above the diagonal as a complex vector, and the corner. -/
def cornerCoordinates :
    (Fin (k + 1) × Fin (k + 1) → ℝ) ≃ᵐ (Fin k × Fin k → ℝ) × (Fin k → ℂ) × ℝ :=
  (MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) (hermitianCornerIndex k)).symm.trans <|
    (MeasurableEquiv.sumPiEquivProdPi fun _ ↦ ℝ).trans <|
      MeasurableEquiv.prodCongr (.refl _) <|
        (MeasurableEquiv.sumPiEquivProdPi fun _ ↦ ℝ).trans <|
          MeasurableEquiv.prodCongr
            ((MeasurableEquiv.sumPiEquivProdPi fun _ ↦ ℝ).trans <|
              (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin k)).symm.trans <|
                MeasurableEquiv.piCongrRight fun _ ↦ Complex.measurableEquivRealProd.symm)
            (MeasurableEquiv.funUnique Unit ℝ)

/-- Regrouping the coordinates preserves Lebesgue measure. -/
theorem measurePreserving_cornerCoordinates : MeasurePreserving (cornerCoordinates k) := by
  have h_complex : MeasurePreserving
      (MeasurableEquiv.piCongrRight fun _ : Fin k ↦ Complex.measurableEquivRealProd.symm) :=
    volume_preserving_pi fun _ ↦ Complex.volume_preserving_equiv_real_prod.symm _
  have h_col := ((volume_measurePreserving_sumPiEquivProdPi fun _ : Fin k ⊕ Fin k ↦ ℝ).trans
    ((volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin k)).symm _)).trans h_complex
  exact ((volume_measurePreserving_piCongrLeft (fun _ ↦ ℝ) (hermitianCornerIndex k)).symm _).trans
    ((volume_measurePreserving_sumPiEquivProdPi _).trans <| (MeasurePreserving.id _).prod <|
      (volume_measurePreserving_sumPiEquivProdPi _).trans <|
        h_col.prod (volume_preserving_funUnique Unit ℝ))

variable {k} in
/-- `cornerCoordinates` reads the coordinates of the block, of the last column above the
diagonal and of the corner. -/
theorem cornerCoordinates_apply (x : Fin (k + 1) × Fin (k + 1) → ℝ) :
    cornerCoordinates k x = (fun ij ↦ x (ij.1.castSucc, ij.2.castSucc),
      fun a ↦ ⟨x (a.castSucc, Fin.last k), x (Fin.last k, a.castSucc)⟩,
      x (Fin.last k, Fin.last k)) :=
  (rfl)

/-- Regrouping the coordinates is continuous. -/
theorem continuous_cornerCoordinates : Continuous (cornerCoordinates k) := by
  have h (x y : ℝ) : (⟨x, y⟩ : ℂ) = Complex.equivRealProdCLM.symm (x, y) := (rfl)
  simp only [funext cornerCoordinates_apply, h]
  fun_prop

/-- The splitting of a Hermitian matrix of size `k + 1` into its upper left block of size `k`,
its last column above the diagonal and its real corner entry. -/
def hermitianCornerEquiv :
    selfAdjoint.submodule ℝ (Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) ≃ᵐ
      selfAdjoint.submodule ℝ (Matrix (Fin k) (Fin k) ℂ) × (Fin k → ℂ) × ℝ :=
  (hermitianCoordinatesMeasurableEquiv (k + 1)).trans <| (cornerCoordinates k).trans <|
    .prodCongr (hermitianCoordinatesMeasurableEquiv k).symm (.refl _)

variable {k}

/-- `hermitianCornerEquiv` in terms of `hermitianCoordinates` and `cornerCoordinates`. -/
theorem hermitianCornerEquiv_apply
    (T : selfAdjoint.submodule ℝ (Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)) :
    hermitianCornerEquiv k T = Prod.map (hermitianCoordinates k).symm id
      (cornerCoordinates k (hermitianCoordinates (k + 1) T)) := by
  simp [hermitianCornerEquiv, MeasurableEquiv.prodCongr]

/-- The first component of `hermitianCornerEquiv k T` is the upper left block of `T`. -/
theorem coe_hermitianCornerEquiv_fst
    (T : selfAdjoint.submodule ℝ (Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)) :
    ((hermitianCornerEquiv k T).1 : Matrix (Fin k) (Fin k) ℂ) =
      (T : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ).submatrix Fin.castSucc Fin.castSucc := by
  ext i j
  simp only [hermitianCornerEquiv_apply, cornerCoordinates_apply, Prod.map_fst, submatrix_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · have h' : i.castSucc < j.castSucc := Fin.castSucc_lt_castSucc_iff.2 h
    simp [h, h', h'.le, Complex.ext_iff]
  · simp [Complex.ext_iff]
  · have h' : j.castSucc < i.castSucc := Fin.castSucc_lt_castSucc_iff.2 h
    rw [← selfAdjoint.conj_coe_apply T]
    simp [h, h', h'.le, Complex.ext_iff]

/-- The second component of `hermitianCornerEquiv k T` is the last column of `T` above the
diagonal. -/
theorem hermitianCornerEquiv_snd_fst
    (T : selfAdjoint.submodule ℝ (Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)) :
    (hermitianCornerEquiv k T).2.1 =
      fun a ↦ (T : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) a.castSucc (Fin.last k) := by
  funext a
  simp [hermitianCornerEquiv_apply, cornerCoordinates_apply, (Fin.castSucc_lt_last a).le]

/-- The third component of `hermitianCornerEquiv k T` is the corner entry of `T`. -/
theorem hermitianCornerEquiv_snd_snd
    (T : selfAdjoint.submodule ℝ (Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)) :
    (hermitianCornerEquiv k T).2.2 =
      ((T : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (Fin.last k) (Fin.last k)).re := by
  simp [hermitianCornerEquiv_apply, cornerCoordinates_apply]

variable (k)

/-- Splitting off the last row and column is continuous. -/
theorem continuous_hermitianCornerEquiv : Continuous (hermitianCornerEquiv k) := by
  rw [funext hermitianCornerEquiv_apply]
  exact ((hermitianCoordinates k).symm.continuous.prodMap continuous_id).comp <|
    (continuous_cornerCoordinates k).comp (hermitianCoordinates (k + 1)).continuous

/-- Splitting off the last row and column carries `hermitianLebesgue (k + 1)` to the product of
`hermitianLebesgue k` and Lebesgue measure on `(Fin k → ℂ) × ℝ`. -/
theorem measurePreserving_hermitianCornerEquiv :
    MeasurePreserving (hermitianCornerEquiv k) (hermitianLebesgue (k + 1))
      ((hermitianLebesgue k).prod volume) := by
  rw [funext hermitianCornerEquiv_apply]
  exact ((measurePreserving_hermitianCoordinates_symm k).prod (.id _)).comp <|
    (measurePreserving_cornerCoordinates k).comp (measurePreserving_hermitianCoordinates (k + 1))

end TauCeti
