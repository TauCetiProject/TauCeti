/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Tactic.FinCases
import TauCeti.Algebra.QuadraticAlgebra.Ideal
import TauCeti.LinearAlgebra.Basis.ExtendedIdeal
import TauCeti.LinearAlgebra.Matrix.ToLin

/-!
# Coordinates, extended ideals and quadratic-algebra determinants

The native basis `(1, ω)` of `QuadraticAlgebra ℤ (-1) 0` identifies the two coordinates without
identifying their multiplication with coordinatewise multiplication. These examples compute a
coefficient matrix and its quotient reduction, distinguish extended ideals from `(1 + ω)`, and
show why taking a determinant does not commute with splitting coordinates.
Two rational quadratic-algebra matrices use the relation `ω² = 2`: their determinants are
zero and one, with the latter having actual basis coordinates `(1, 0)`.
-/

open QuadraticAlgebra Matrix

namespace TauCeti.ExtendedIdealExamples

/-- The images `1 + 2ω`, `3ω` give column coordinates `[[1, 0], [2, 3]]`. -/
example :
    let φ := (Pi.basisFun ℤ (Fin 2)).constr ℤ
      ![(⟨1, 2⟩ : QuadraticAlgebra ℤ (-1) 0), ⟨0, 3⟩]
    LinearMap.toMatrix (Pi.basisFun ℤ (Fin 2)) (basis (-1) 0) φ = !![1, 0; 2, 3] := by
  intro φ
  ext i j
  fin_cases i <;> fin_cases j <;> simp [φ, LinearMap.toMatrix_apply]

/-- Applying the matrix to `(x, y)` gives the coordinates of `φ (x, y)`. -/
example (x y : ℤ) :
    let φ := (Pi.basisFun ℤ (Fin 2)).constr ℤ
      ![(⟨1, 2⟩ : QuadraticAlgebra ℤ (-1) 0), ⟨0, 3⟩]
    (basis (-1) 0).repr (φ ![x, y]) = ![x, 2 * x + 3 * y] := by
  intro φ
  have h := LinearMap.toMatrix_mulVec_eq_repr (Pi.basisFun ℤ (Fin 2))
    (basis (-1) 0) φ ![x, y]
  have hM : LinearMap.toMatrix (Pi.basisFun ℤ (Fin 2)) (basis (-1) 0) φ =
      !![1, 0; 2, 3] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [φ, LinearMap.toMatrix_apply]
  rw [hM] at h
  rw [← (Pi.basisFun ℤ (Fin 2)).equivFun_symm_apply, Pi.basisFun_equivFun] at h
  ext i
  fin_cases i
  · simpa [mulVec, dotProduct, Fin.sum_univ_two] using congrFun h.symm 0
  · simpa [mulVec, dotProduct, Fin.sum_univ_two] using congrFun h.symm 1

/-- Extended-ideal membership is equivalent to both rows taking values in `(2)`. -/
example (x y : ℤ) :
    let φ := (Pi.basisFun ℤ (Fin 2)).constr ℤ
      ![(⟨1, 2⟩ : QuadraticAlgebra ℤ (-1) 0), ⟨0, 3⟩]
    φ ![x, y] ∈ (Ideal.span ({2} : Set ℤ)).map (algebraMap ℤ _) ↔
      2 ∣ x ∧ 2 ∣ 2 * x + 3 * y := by
  intro φ
  have h := LinearMap.apply_sum_smul_mem_map_algebraMap_iff (Pi.basisFun ℤ (Fin 2))
    (basis (-1) 0) φ (Ideal.span ({2} : Set ℤ)) ![x, y]
  rw [← (Pi.basisFun ℤ (Fin 2)).equivFun_symm_apply, Pi.basisFun_equivFun] at h
  simpa [φ, Fin.forall_fin_two, mulVec, dotProduct, Fin.sum_univ_two,
    LinearMap.toMatrix_apply, Ideal.mem_span_singleton] using h

/-- In the quotient basis the reduced map has identity matrix modulo `2`. -/
example :
    let J := Ideal.span ({2} : Set ℤ)
    let q := Ideal.Quotient.mk (J.map (algebraMap ℤ (QuadraticAlgebra ℤ (-1) 0)))
    let φ' := (Pi.basisFun (ℤ ⧸ J) (Fin 2)).constr (ℤ ⧸ J) ![q ⟨1, 2⟩, q ⟨0, 3⟩]
    LinearMap.toMatrix (Pi.basisFun (ℤ ⧸ J) (Fin 2)) ((basis (-1) 0).quotient J) φ' =
      !![1, 0; 0, 1] := by
  intro J q φ'
  let φ := (Pi.basisFun ℤ (Fin 2)).constr ℤ
    ![(⟨1, 2⟩ : QuadraticAlgebra ℤ (-1) 0), ⟨0, 3⟩]
  have h := LinearMap.toMatrix_quotient (Pi.basisFun ℤ (Fin 2))
    (Pi.basisFun (ℤ ⧸ J) (Fin 2)) (basis (-1) 0) φ φ'
      (by intro j; fin_cases j <;> simp [φ, φ', q])
  have h2 : (2 : ℤ ⧸ J) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have h3 : (3 : ℤ ⧸ J) = 1 :=
    Ideal.Quotient.eq.mpr (by norm_num [J, Ideal.mem_span_singleton])
  rw [h]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [φ, LinearMap.toMatrix_apply, h2, h3]

/-- The class of `1 + ω` still has two coordinates in the quotient basis. -/
example :
    let J := Ideal.span ({2} : Set ℤ)
    let q := Ideal.Quotient.mk (J.map (algebraMap ℤ (QuadraticAlgebra ℤ (-1) 0)))
    ⇑(((basis (-1) 0).quotient J).repr (q ⟨1, 1⟩)) = ![1, 1] := by
  intro J q
  ext i
  dsimp only [q]
  rw [Module.Basis.quotient_repr_mk]
  fin_cases i <;> simp

/-- The quotient by the extended ideal `(2)` has the nonzero square-zero element `1 + ω`.
It is not the residue field at `(1 + ω)`. -/
example :
    let J := Ideal.span ({2} : Set ℤ)
    let z : QuadraticAlgebra ℤ (-1) 0 ⧸ J.map (algebraMap ℤ _) :=
      Ideal.Quotient.mk _ ⟨1, 1⟩
    z ≠ 0 ∧ z ^ 2 = 0 ∧
      ¬IsField (QuadraticAlgebra ℤ (-1) 0 ⧸
        J.map (algebraMap ℤ (QuadraticAlgebra ℤ (-1) 0))) := by
  intro J z
  have hz : z ≠ 0 := by
    dsimp only [z]
    rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem, mem_map_algebraMap_iff]
    norm_num [J, Ideal.mem_span_singleton]
  have hz2 : z ^ 2 = 0 := by
    dsimp only [z]
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, mem_map_algebraMap_iff]
    norm_num [pow_two, J, Ideal.mem_span_singleton]
  refine ⟨hz, hz2, fun hf ↦ ?_⟩
  let := hf.toField
  exact hz ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hz2)

/-- Identifying `ℤ / (2)` with `ZMod 2`, the quotient by the extended ideal is free of rank
two on the classes of `1, ω`. No residue-field quotient replaces this carrier. -/
example :
    let J := Ideal.span ({2} : Set ℤ)
    let e := Int.quotientSpanNatEquivZMod 2
    let _ := Module.compHom
      (QuadraticAlgebra ℤ (-1) 0 ⧸ J.map (algebraMap ℤ (QuadraticAlgebra ℤ (-1) 0)))
      e.symm.toRingHom
    ∃ b : Module.Basis (Fin 2) (ZMod 2)
        (QuadraticAlgebra ℤ (-1) 0 ⧸ J.map (algebraMap ℤ (QuadraticAlgebra ℤ (-1) 0))),
      (∀ i, b i = Ideal.Quotient.mk _ (basis (-1) 0 i)) ∧
        Module.finrank (ZMod 2)
          (QuadraticAlgebra ℤ (-1) 0 ⧸ J.map (algebraMap ℤ (QuadraticAlgebra ℤ (-1) 0))) = 2 := by
  intro J e inst
  let b := ((basis (-1) 0).quotient J).mapCoeffs e
    (by
      intro c x
      -- The left scalar acts through `e.symm`; expose that action to use the inverse law.
      change e.symm (e c) • x = c • x
      rw [e.symm_apply_apply])
  refine ⟨b, ?_, ?_⟩
  · intro i
    simp only [b, Module.Basis.mapCoeffs_apply, Module.Basis.quotient_apply]
  · simpa using Module.finrank_eq_card_basis b

/-- For the base ring and basis `1`, extension and the coordinate criterion are identities. -/
example (R : Type*) [CommRing R] (J : Ideal R) (x : R) :
    J.map (algebraMap R R) = J ∧
      (x ∈ J.map (algebraMap R R) ↔ (Module.Basis.singleton (Fin 1) R).repr x 0 ∈ J) := by
  simp

/-- Both coordinates of `2 + 2ω` are in `(2)`; neither coordinate of `1 + ω` is in `(2)`. -/
example :
    (⟨2, 2⟩ : QuadraticAlgebra ℤ (-1) 0) ∈
        (Ideal.span ({2} : Set ℤ)).map (algebraMap ℤ _) ∧
      (⟨1, 1⟩ : QuadraticAlgebra ℤ (-1) 0) ∉
        (Ideal.span ({2} : Set ℤ)).map (algebraMap ℤ _) ∧
      (1 : ℤ) ∉ Ideal.span ({2} : Set ℤ) := by
  simp only [mem_map_algebraMap_iff]
  norm_num [Ideal.mem_span_singleton]

/-- The Gaussian ideal `(1 + ω)` is not extended from any integer ideal. Its generator would
force `1 ∈ J`, while its norm `2` prevents it from generating the unit ideal. -/
example : ¬∃ J : Ideal ℤ, J.map (algebraMap ℤ (QuadraticAlgebra ℤ (-1) 0)) =
    Ideal.span {(⟨1, 1⟩ : QuadraticAlgebra ℤ (-1) 0)} := by
  rintro ⟨J, hJ⟩
  have hz : (⟨1, 1⟩ : QuadraticAlgebra ℤ (-1) 0) ∈ J.map (algebraMap ℤ _) := by
    rw [hJ]
    exact Ideal.subset_span (Set.mem_singleton _)
  have h1 : (1 : ℤ) ∈ J := (mem_map_algebraMap_iff.mp hz).1
  have he : (1 : QuadraticAlgebra ℤ (-1) 0) ∈ J.map (algebraMap ℤ _) := by
    simpa using Ideal.mem_map_of_mem (algebraMap ℤ (QuadraticAlgebra ℤ (-1) 0)) h1
  rw [hJ, Ideal.mem_span_singleton] at he
  have hu := isUnit_of_dvd_one he
  norm_num [isUnit_iff_norm_isUnit, norm_def, Int.isUnit_iff] at hu

/-- Coordinates do not preserve determinants: `det diag(ω, ω) = -1`, while the two
coordinate matrices have determinants `0` and `1`. -/
example :
    let M := diagonal (fun _ : Fin 2 ↦ (ω : QuadraticAlgebra ℤ (-1) 0))
    ⇑((basis (-1) 0).repr M.det) = ![-1, 0] ∧
      (M.map (fun z ↦ (basis (-1) 0).repr z 0)).det = 0 ∧
      (M.map (fun z ↦ (basis (-1) 0).repr z 1)).det = 1 := by
  intro M
  norm_num [M, det_fin_two, diagonal]

/-- The relation `ω² = 2` makes this rational quadratic-algebra determinant zero. -/
example : (!![1, ω; ω, 2] : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra ℚ 2 0)).det = 0 := by
  norm_num [det_fin_two, omega_mul_omega_eq_mk]

/-- Changing the bottom-right entry to three gives determinant one and coordinates `(1, 0)`. -/
example :
    let M : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra ℚ 2 0) := !![1, ω; ω, 3]
    M.det = 1 ∧ ⇑((basis (2 : ℚ) 0).repr M.det) = ![1, 0] := by
  intro M
  norm_num [M, det_fin_two, omega_mul_omega_eq_mk]

end TauCeti.ExtendedIdealExamples
