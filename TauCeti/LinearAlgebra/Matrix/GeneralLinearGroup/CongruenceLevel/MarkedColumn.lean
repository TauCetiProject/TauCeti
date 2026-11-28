/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
import TauCeti.LinearAlgebra.Matrix.Divisibility

/-!
# Changing the marked lattice in a congruence level

If a matrix fixes a marked column modulo `τ`, dilating the corresponding coordinate by `τ`
conjugates it to another integral matrix, now fixing the marked row modulo `τ`. This calculation
is used for the local invariance of the theta-lift operator `Up`; see
`New.IsSplitLevel.exists_inclGL_eq_conj_diagNInv` in `New/UpperBound/Objects/LiftLawsModuloN.lean`
of lsernau/grh-lean at `72fead1`.
-/

public section

open Matrix TauCeti

namespace Matrix.GeneralLinearGroup

/-- If `a` fixes the marked column modulo a principal congruence ideal `(τ)`, then conjugation
by the diagonal matrix with entry `τ` at that coordinate lifts to an integral invertible matrix
whose marked row is the standard row modulo `(τ)`. The scaling element must be a
nonzerodivisor in the integral ring and a unit in the ambient algebra. -/
theorem exists_map_eq_diagGL_mul_mul_inv_of_col_eq
    {A F R ι : Type*} [CommRing A] [CommRing F] [CommRing R] [Algebra A F]
    [Fintype ι] [DecidableEq ι] (a : GL ι A) (red : A →+* R) (l : ι) {τ : A} (u : Fˣ)
    (hu : algebraMap A F τ = u) (hτ : IsRegular τ)
    (hker : ∀ x, red x = 0 ↔ τ ∣ x)
    (ha : (map red a : Matrix ι ι R).col l = Pi.single l 1) :
    ∃ b : GL ι A, (map red b : Matrix ι ι R).row l = Pi.single l 1 ∧
      map (algebraMap A F) b = diagGL (fun i ↦ if i = l then u else 1) *
        map (algebraMap A F) a * (diagGL (fun i ↦ if i = l then u else 1))⁻¹ := by
  let d : ι → A := fun i ↦ if i = l then τ else 1
  obtain ⟨C, hC⟩ := (Matrix.exists_diagonal_mul_eq_mul_diagonal_iff (a := d)
    (v := (a : Matrix ι ι A)ᵀ)).mpr fun i j ↦ by
      by_cases hi : i = l
      · subst i
        by_cases hj : j = l
        · simp [hj, d, dvd_mul_left]
        · have hz : red (a j l) = 0 := by simpa [hj] using congrFun ha j
          simpa only [d, ite_true, transpose_apply] using ((hker _).mp hz).mul_right (d j)
      · simp [d, hi]
  have hB : Cᵀ * diagonal d = diagonal d * (a : Matrix ι ι A) := by
    simpa [transpose_mul] using congrArg Matrix.transpose hC
  have hdet : (Cᵀ).det = (a : Matrix ι ι A).det := by
    have h := congrArg Matrix.det hB
    simp only [det_mul, det_diagonal, d, Fintype.prod_ite_eq'] at h
    exact hτ.right (h.trans (mul_comm _ _))
  let U : GL ι F := diagGL (fun i ↦ if i = l then u else 1)
  have hU : (diagonal d).map (algebraMap A F) = (U : Matrix ι ι F) := by
    rw [diagonal_map (map_zero _), diagGL_coe]
    congr 1
    funext i
    by_cases hi : i = l <;> simp [d, hi, hu]
  have hmap (e : GL ι A) : (e : Matrix ι ι A).map (algebraMap A F) =
      (map (algebraMap A F) e : Matrix ι ι F) := by
    ext i j
    simp
  have heq : Cᵀ.map (algebraMap A F) = (U * map (algebraMap A F) a * U⁻¹).val := by
    have h := congrArg (fun M : Matrix ι ι A ↦ M.map (algebraMap A F)) hB
    simp only [Matrix.map_mul, hU, hmap] at h
    simpa only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, coe_mul] using
      congrArg (· * (U⁻¹ : GL ι F).val) h
  have hd : IsUnit (Cᵀ).det := hdet ▸ a.isUnit.map (Matrix.detMonoidHom : Matrix ι ι A →* A)
  let b := mk'' Cᵀ hd
  have hb : (b : Matrix ι ι A) = Cᵀ := by simp [b]
  have hbmap : map (algebraMap A F) b = U * map (algebraMap A F) a * U⁻¹ :=
    Units.ext ((hmap b).symm.trans (by rw [hb, heq]))
  refine ⟨b, ?_, hbmap⟩
  funext j
  simp only [row, GeneralLinearGroup.map_apply, hb]
  have h : Cᵀ l j * d j = τ * a l j := by
    simpa [d] using congrFun (congrFun hB l) j
  by_cases hj : j = l
  · subst j
    have h' : Cᵀ l l * τ = τ * a l l := by simpa [d] using h
    rw [hτ.right (h'.trans (mul_comm _ _))]
    exact congrFun ha l
  · have hzero : red τ = 0 := (hker _).mpr dvd_rfl
    have hc : Cᵀ l j = τ * a l j := by simpa [d, hj] using h
    rw [hc, map_mul, hzero, zero_mul]
    simp [hj]

end Matrix.GeneralLinearGroup
