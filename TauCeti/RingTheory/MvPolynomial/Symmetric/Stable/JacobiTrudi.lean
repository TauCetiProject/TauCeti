/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Symmetric.Elementary
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Stable.Omega
import TauCeti.Combinatorics.Enumerative.Partition.Conjugate
import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.DualJacobiTrudi

/-!
# The Jacobi--Trudi identities in the symmetric functions and `ω(s_λ) = s_(λᵗ)`

In the ring `Λ_R` of symmetric functions, the Schur function of a partition `λ` is given by the two
Jacobi--Trudi determinants

`s_λ = det (h_(λᵢ - i + j))_(0 ≤ i, j < r) = det (e_(λᵗᵢ - i + j))_(0 ≤ i, j < r')`,

for every `r` at least the number of parts of `λ` and every `r'` at least its largest part, with
`λᵗ` the conjugate partition. The indices are integers, and `h_m = e_m = 0` for `m < 0`; these are
`TauCeti.SymmetricFunction.hsymmInt` and `TauCeti.SymmetricFunction.esymmInt`. Both identities
follow from their versions in finitely many variables, since a symmetric function is determined
by its specializations to the alphabets `Fin d`.

The involution `ω` exchanges `h_m` and `e_m`, so it carries the first determinant for `λ` to the
second determinant for `λᵗ`, whose row lengths are the column lengths of `λ`. Hence
`ω(s_λ) = s_(λᵗ)`.

## Main definitions

* `TauCeti.SymmetricFunction.hsymmInt R m`: the complete homogeneous symmetric function `h_m` for
  `m ≥ 0`, and `0` for `m < 0`.
* `TauCeti.SymmetricFunction.esymmInt R m`: the elementary symmetric function `e_m` for `m ≥ 0`,
  and `0` for `m < 0`.

## Main results

* `TauCeti.SymmetricFunction.of_stableSchur_eq_det_hsymmInt`: **the Jacobi--Trudi identity**
  `s_λ = det (h_(λᵢ - i + j))` in `Λ_R`.
* `TauCeti.SymmetricFunction.of_stableSchur_eq_det_esymmInt`: **the dual Jacobi--Trudi identity**
  `s_λ = det (e_(λᵗᵢ - i + j))` in `Λ_R`.
* `TauCeti.SymmetricFunction.omega_hsymmInt`, `TauCeti.SymmetricFunction.omega_esymmInt`:
  `ω(h_m) = e_m` and `ω(e_m) = h_m` in every integer degree.
* `TauCeti.SymmetricFunction.omega_of_stableSchur`: **`ω(s_λ) = s_(λᵗ)`**.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  (3.4), (3.5) and (3.8).
-/

public section

namespace TauCeti

open MvPolynomial DirectSum

namespace SymmetricFunction

section CommSemiring

variable (R : Type*) [CommSemiring R]

/-- The **complete homogeneous symmetric function of integer degree** `m`: `h_m` for `m ≥ 0` and
`0` for `m < 0`. This is the indexing of the Jacobi--Trudi determinant
`TauCeti.SymmetricFunction.of_stableSchur_eq_det_hsymmInt`. -/
noncomputable def hsymmInt (m : ℤ) : SymmetricFunction R :=
  if 0 ≤ m then DirectSum.of _ m.toNat (stableHsymm R m.toNat) else 0

/-- The **elementary symmetric function of integer degree** `m`: `e_m` for `m ≥ 0` and `0` for
`m < 0`. This is the indexing of the dual Jacobi--Trudi determinant
`TauCeti.SymmetricFunction.of_stableSchur_eq_det_esymmInt`. -/
noncomputable def esymmInt (m : ℤ) : SymmetricFunction R :=
  if 0 ≤ m then DirectSum.of _ m.toNat (stableEsymm R m.toNat) else 0

variable {R}

/-- In a nonnegative degree, `TauCeti.SymmetricFunction.hsymmInt` is `h_m`. -/
@[simp]
theorem hsymmInt_of_nonneg {m : ℤ} (hm : 0 ≤ m) :
    hsymmInt R m = DirectSum.of _ m.toNat (stableHsymm R m.toNat) := by
  simp [hsymmInt, hm]

/-- In a natural-number degree, `TauCeti.SymmetricFunction.hsymmInt` is `h_n`. -/
theorem hsymmInt_natCast (n : ℕ) :
    hsymmInt R n = DirectSum.of _ n (stableHsymm R n) := by
  simp

/-- In a negative degree, `TauCeti.SymmetricFunction.hsymmInt` vanishes. -/
@[simp]
theorem hsymmInt_of_neg {m : ℤ} (hm : m < 0) : hsymmInt R m = 0 := by
  simp [hsymmInt, not_le.mpr hm]

/-- `h_0 = 1`. -/
theorem hsymmInt_zero : hsymmInt R 0 = 1 := by
  simp

/-- In a nonnegative degree, `TauCeti.SymmetricFunction.esymmInt` is `e_m`. -/
@[simp]
theorem esymmInt_of_nonneg {m : ℤ} (hm : 0 ≤ m) :
    esymmInt R m = DirectSum.of _ m.toNat (stableEsymm R m.toNat) := by
  simp [esymmInt, hm]

/-- In a natural-number degree, `TauCeti.SymmetricFunction.esymmInt` is `e_n`. -/
theorem esymmInt_natCast (n : ℕ) :
    esymmInt R n = DirectSum.of _ n (stableEsymm R n) := by
  simp

/-- In a negative degree, `TauCeti.SymmetricFunction.esymmInt` vanishes. -/
@[simp]
theorem esymmInt_of_neg {m : ℤ} (hm : m < 0) : esymmInt R m = 0 := by
  simp [esymmInt, not_le.mpr hm]

/-- `e_0 = 1`. -/
theorem esymmInt_zero : esymmInt R 0 = 1 := by
  simp

/-- In `d` variables, `TauCeti.SymmetricFunction.hsymmInt` specializes to `TauCeti.hsymmInt`. -/
@[simp]
theorem specialization_hsymmInt (d : ℕ) (m : ℤ) :
    specialization R d (hsymmInt R m) = TauCeti.hsymmInt (Fin d) R m := by
  rcases le_or_gt 0 m with hm | hm
  · simp [hsymmInt, hm]
  · simp [hm]

/-- In `d` variables, `TauCeti.SymmetricFunction.esymmInt` specializes to `TauCeti.esymmInt`. -/
@[simp]
theorem specialization_esymmInt (d : ℕ) (m : ℤ) :
    specialization R d (esymmInt R m) = TauCeti.esymmInt (Fin d) R m := by
  rcases le_or_gt 0 m with hm | hm
  · simp [esymmInt, hm]
  · simp [hm]

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] {n : ℕ}

/-- **`ω(h_m) = e_m`** in every integer degree. -/
@[simp]
theorem omega_hsymmInt (m : ℤ) : omega R (hsymmInt R m) = esymmInt R m := by
  unfold hsymmInt esymmInt
  split_ifs <;> simp

/-- **`ω(e_m) = h_m`** in every integer degree. -/
@[simp]
theorem omega_esymmInt (m : ℤ) : omega R (esymmInt R m) = hsymmInt R m := by
  rw [← omega_hsymmInt, omega_omega]

/-- **The Jacobi--Trudi identity** in the symmetric functions: the Schur function of a partition
`μ` is `det (h_(μᵢ - i + j))_(0 ≤ i, j < r)` for every `r` at least the number of parts of `μ`,
where `μᵢ` is the `i`-th largest part (`0` past the last part) and `h_m = 0` for `m < 0`. -/
theorem of_stableSchur_eq_det_hsymmInt (μ : n.Partition) {r : ℕ} (hr : μ.parts.card ≤ r) :
    DirectSum.of _ n (stableSchur R μ) =
      (Matrix.of fun i j : Fin r =>
        hsymmInt R (((YoungDiagram.ofPartition μ).rowLen i : ℤ) - (i : ℕ) + (j : ℕ))).det :=
  ext_specialization fun d => by
    rw [specialization_of, coe_stableSymmetricProj_stableSchur, schurPoly_eq_det_hsymmInt μ hr,
      AlgHom.map_det]
    congr 1
    ext i j : 1
    simp

/-- **The dual Jacobi--Trudi identity** in the symmetric functions: the Schur function of a
partition `μ` is `det (e_(μᵗᵢ - i + j))_(0 ≤ i, j < r)` for every `r` at least the largest part of
`μ`, where `μᵗᵢ` is the length of the `i`-th column of the Young diagram of `μ` and `e_m = 0` for
`m < 0`. -/
theorem of_stableSchur_eq_det_esymmInt (μ : n.Partition) {r : ℕ}
    (hr : (YoungDiagram.ofPartition μ).rowLen 0 ≤ r) :
    DirectSum.of _ n (stableSchur R μ) =
      (Matrix.of fun i j : Fin r =>
        esymmInt R (((YoungDiagram.ofPartition μ).colLen i : ℤ) - (i : ℕ) + (j : ℕ))).det :=
  ext_specialization fun d => by
    rw [specialization_of, coe_stableSymmetricProj_stableSchur,
      Nat.Partition.schurPoly_eq_det_esymmInt μ hr, AlgHom.map_det]
    congr 1
    ext i j : 1
    simp

/-- **`ω(s_μ) = s_(μᵗ)`**: the involution `ω` sends the Schur function of a partition to the Schur
function of the conjugate partition. -/
@[simp]
theorem omega_of_stableSchur (μ : n.Partition) :
    omega R (DirectSum.of _ n (stableSchur R μ)) =
      DirectSum.of _ n (stableSchur R μ.conjugate) := by
  -- `ω` turns the Jacobi--Trudi determinant of `μ`, of size the number of parts of `μ`, into the
  -- dual Jacobi--Trudi determinant of `μᵗ`, whose column lengths are the row lengths of `μ` and
  -- whose largest part is the number of parts of `μ`.
  have hr : (YoungDiagram.ofPartition μ.conjugate).rowLen 0 ≤ μ.parts.card := by
    rw [YoungDiagram.ofPartition_conjugate, YoungDiagram.rowLen_transpose,
      YoungDiagram.colLen_zero_ofPartition]
  rw [of_stableSchur_eq_det_hsymmInt μ le_rfl, of_stableSchur_eq_det_esymmInt μ.conjugate hr,
    ← AlgEquiv.coe_toAlgHom, AlgHom.map_det]
  congr 1
  ext i j : 1
  simp [YoungDiagram.ofPartition_conjugate, YoungDiagram.colLen_transpose]

end CommRing

end SymmetricFunction

end TauCeti
