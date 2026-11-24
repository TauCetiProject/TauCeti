/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import TauCeti.Algebra.Quaternion.NormForm
import Mathlib.Tactic.LinearCombination

/-!
# Rotations of `R³` by quaternion conjugation

Identify `R³` with the pure Hamilton quaternions over a commutative ring `R` by
`v ↦ v₀ i + v₁ j + v₂ k`. Conjugation `v ↦ q * v * star q` by a quaternion `q` preserves the pure
quaternions, so it is a linear map of `R³`; its matrix is `Quaternion.rotationMatrix q`, whose
entries are the classical quadratic expressions in the coordinates of `q`
(`Quaternion.mul_mk_zero_mul_star`). This matrix is multiplicative in `q`, sends `star q` to the
transpose, satisfies `R(q)ᵀ R(q) = N(q)² · 1` and has determinant `N(q)³`, where `N` is the reduced
norm `Quaternion.normSq`. So a unit quaternion gives a rotation, and conjugation is a group
homomorphism `Quaternion.unitaryToSpecialOrthogonalGroup` from the unit quaternions to `SO(3, R)`.

When `R` is a domain in which `2 ≠ 0`, conjugation by `q` is the identity only for `q = ±1`
(`Quaternion.rotationMatrix_eq_one_iff`), so two unit quaternions give the same rotation exactly
when they agree up to sign (`Quaternion.unitaryToSpecialOrthogonalGroup_eq_iff`). Over `ℝ` the
homomorphism is also onto, which identifies `SO(3)` with the unit quaternions modulo `±1`; that is
`TauCeti.RealProjectiveSpace.homeomorphSpecialOrthogonalGroup`.

## Main definitions

* `Quaternion.rotationMatrix q`: the matrix of `v ↦ q * v * star q` on the pure quaternions.
* `Quaternion.unitaryToSpecialOrthogonalGroup`: the homomorphism from the unit quaternions to
  `SO(3, R)`.

## Main results

* `Quaternion.mul_mk_zero_mul_star` and `Quaternion.rotationMatrix_eq_iff`: `rotationMatrix q` is
  the unique matrix intertwined with conjugation by `q`.
* `Quaternion.rotationMatrix_mul`, `Quaternion.rotationMatrix_star`: multiplicativity, and
  conjugation goes to the transpose.
* `Quaternion.transpose_rotationMatrix_mul_self`, `Quaternion.det_rotationMatrix`: the Gram matrix
  and the determinant.
* `Quaternion.rotationMatrix_eq_one_iff`, `Quaternion.unitaryToSpecialOrthogonalGroup_eq_one_iff`:
  the kernel is `{1, -1}`.
* `Quaternion.unitaryToSpecialOrthogonalGroup_eq_iff`: two unit quaternions give the same rotation
  exactly when they agree up to sign.

## References

* J. H. Conway and D. A. Smith, *On Quaternions and Octonions*, A K Peters, 2003, Chapter 3.
* J. Stillwell, *Naive Lie Theory*, Undergraduate Texts in Mathematics, Springer, 2008, §1.5.
-/

public section

open Matrix
open scoped Quaternion

namespace Quaternion

variable {R : Type*} [CommRing R]

/-- The matrix of conjugation `v ↦ q * v * star q` by a quaternion `q` on the pure quaternions
`v₀ i + v₁ j + v₂ k`, read in the coordinates `(v₀, v₁, v₂)`
(`Quaternion.mul_mk_zero_mul_star`). For a unit quaternion it is a rotation
(`Quaternion.rotationMatrix_mem_specialOrthogonalGroup`). -/
def rotationMatrix (q : ℍ[R]) : Matrix (Fin 3) (Fin 3) R :=
  !![q.re ^ 2 + q.imI ^ 2 - q.imJ ^ 2 - q.imK ^ 2, 2 * (q.imI * q.imJ - q.re * q.imK),
      2 * (q.imI * q.imK + q.re * q.imJ);
    2 * (q.imI * q.imJ + q.re * q.imK), q.re ^ 2 - q.imI ^ 2 + q.imJ ^ 2 - q.imK ^ 2,
      2 * (q.imJ * q.imK - q.re * q.imI);
    2 * (q.imI * q.imK - q.re * q.imJ), 2 * (q.imJ * q.imK + q.re * q.imI),
      q.re ^ 2 - q.imI ^ 2 - q.imJ ^ 2 + q.imK ^ 2]

/-- The entries of `rotationMatrix q`. -/
theorem rotationMatrix_def (q : ℍ[R]) :
    rotationMatrix q =
      !![q.re ^ 2 + q.imI ^ 2 - q.imJ ^ 2 - q.imK ^ 2, 2 * (q.imI * q.imJ - q.re * q.imK),
          2 * (q.imI * q.imK + q.re * q.imJ);
        2 * (q.imI * q.imJ + q.re * q.imK), q.re ^ 2 - q.imI ^ 2 + q.imJ ^ 2 - q.imK ^ 2,
          2 * (q.imJ * q.imK - q.re * q.imI);
        2 * (q.imI * q.imK - q.re * q.imJ), 2 * (q.imJ * q.imK + q.re * q.imI),
          q.re ^ 2 - q.imI ^ 2 - q.imJ ^ 2 + q.imK ^ 2] :=
  (rfl)

/-- **Conjugation by a quaternion acts on the pure quaternions by `rotationMatrix`**: for
`v = v₀ i + v₁ j + v₂ k`, the quaternion `q * v * star q` is pure, with coordinates
`rotationMatrix q *ᵥ v`. -/
theorem mul_mk_zero_mul_star (q : ℍ[R]) (v : Fin 3 → R) :
    q * ⟨0, v 0, v 1, v 2⟩ * star q =
      ⟨0, (rotationMatrix q *ᵥ v) 0, (rotationMatrix q *ᵥ v) 1, (rotationMatrix q *ᵥ v) 2⟩ := by
  ext <;> simp [rotationMatrix, mulVec, dotProduct, Fin.sum_univ_three] <;> ring

/-- `rotationMatrix q` is the only matrix intertwined with conjugation by `q` on the pure
quaternions. -/
theorem rotationMatrix_eq_iff {q : ℍ[R]} {A : Matrix (Fin 3) (Fin 3) R} :
    rotationMatrix q = A ↔
      ∀ v : Fin 3 → R,
        q * ⟨0, v 0, v 1, v 2⟩ * star q = ⟨0, (A *ᵥ v) 0, (A *ᵥ v) 1, (A *ᵥ v) 2⟩ := by
  refine ⟨fun h v ↦ h ▸ mul_mk_zero_mul_star q v, fun h ↦ ext_iff_mulVec.mpr fun v ↦ ?_⟩
  have hv := (mul_mk_zero_mul_star q v).symm.trans (h v)
  simp only [QuaternionAlgebra.mk.injEq, true_and] at hv
  ext i
  fin_cases i
  exacts [hv.1, hv.2.1, hv.2.2]

/-- Conjugation by `1` is the identity. -/
@[simp]
theorem rotationMatrix_one : rotationMatrix (1 : ℍ[R]) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotationMatrix]

/-- Conjugation by `-q` is conjugation by `q`. -/
@[simp]
theorem rotationMatrix_neg (q : ℍ[R]) : rotationMatrix (-q) = rotationMatrix q := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotationMatrix]

/-- **Conjugation is multiplicative**: conjugating by `p * q` is conjugating by `q`, then by
`p`. -/
@[simp]
theorem rotationMatrix_mul (p q : ℍ[R]) :
    rotationMatrix (p * q) = rotationMatrix p * rotationMatrix q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotationMatrix, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

/-- Conjugation by `star q` has the transposed matrix of conjugation by `q`. -/
@[simp]
theorem rotationMatrix_star (q : ℍ[R]) : rotationMatrix (star q) = (rotationMatrix q)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotationMatrix] <;> ring

/-- The Gram matrix of the columns of `rotationMatrix q` is `N(q)² · 1`, where `N(q) = q * star q`
is the reduced norm. -/
theorem transpose_rotationMatrix_mul_self (q : ℍ[R]) :
    (rotationMatrix q)ᵀ * rotationMatrix q = normSq q ^ 2 • (1 : Matrix (Fin 3) (Fin 3) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotationMatrix, Matrix.mul_apply, Fin.sum_univ_three, normSq_def'] <;> ring

/-- The determinant of `rotationMatrix q` is `N(q)³`, where `N(q) = q * star q` is the reduced
norm. -/
@[simp]
theorem det_rotationMatrix (q : ℍ[R]) : (rotationMatrix q).det = normSq q ^ 3 := by
  rw [det_fin_three]
  simp [rotationMatrix, normSq_def']
  ring

section SpecialOrthogonal

attribute [local instance] starRingOfComm

/-- **Conjugation by a unit quaternion is a rotation.** -/
theorem rotationMatrix_mem_specialOrthogonalGroup {q : ℍ[R]} (hq : q ∈ unitary ℍ[R]) :
    rotationMatrix q ∈ specialOrthogonalGroup (Fin 3) R := by
  rw [mem_unitary_iff_normSq_eq_one] at hq
  rw [mem_specialOrthogonalGroup_iff, mem_orthogonalGroup_iff', transpose_rotationMatrix_mul_self,
    det_rotationMatrix, hq]
  simp

/-- **The unit quaternions act on `R³` by rotations**: the homomorphism sending a unit quaternion
`q` to the matrix of `v ↦ q * v * star q`. -/
def unitaryToSpecialOrthogonalGroup : unitary ℍ[R] →* specialOrthogonalGroup (Fin 3) R where
  toFun q := ⟨rotationMatrix q, rotationMatrix_mem_specialOrthogonalGroup q.property⟩
  map_one' := Subtype.ext rotationMatrix_one
  map_mul' p q := Subtype.ext <| by
    simp only [Submonoid.coe_mul, rotationMatrix_mul]

/-- The rotation attached to a unit quaternion `q` is `rotationMatrix q`. -/
@[simp]
theorem coe_unitaryToSpecialOrthogonalGroup_apply (q : unitary ℍ[R]) :
    (unitaryToSpecialOrthogonalGroup q : Matrix (Fin 3) (Fin 3) R) = rotationMatrix (q : ℍ[R]) :=
  (rfl)

end SpecialOrthogonal

section Kernel

variable [IsDomain R] [NeZero (2 : R)]

/-- **The kernel of conjugation is `{1, -1}`**: over a domain in which `2 ≠ 0`, conjugation by a
quaternion `q` is the identity of `R³` exactly when `q = 1` or `q = -1`. -/
theorem rotationMatrix_eq_one_iff {q : ℍ[R]} : rotationMatrix q = 1 ↔ q = 1 ∨ q = -1 := by
  refine ⟨fun h ↦ ?_, by rintro (rfl | rfl) <;> simp⟩
  have h2 : (2 : R) ≠ 0 := two_ne_zero
  have cancel (x : R) (hx : 2 * (2 * x) = 0) : x = 0 := by simpa [h2] using hx
  have e (i j : Fin 3) : rotationMatrix q i j = (1 : Matrix (Fin 3) (Fin 3) R) i j :=
    congrFun₂ h i j
  have h00 : q.re ^ 2 + q.imI ^ 2 - q.imJ ^ 2 - q.imK ^ 2 = 1 := by
    simpa [rotationMatrix] using e 0 0
  have h11 : q.re ^ 2 - q.imI ^ 2 + q.imJ ^ 2 - q.imK ^ 2 = 1 := by
    simpa [rotationMatrix] using e 1 1
  have h22 : q.re ^ 2 - q.imI ^ 2 - q.imJ ^ 2 + q.imK ^ 2 = 1 := by
    simpa [rotationMatrix] using e 2 2
  have h01 : 2 * (q.imI * q.imJ - q.re * q.imK) = 0 := by simpa [rotationMatrix] using e 0 1
  have h10 : 2 * (q.imI * q.imJ + q.re * q.imK) = 0 := by simpa [rotationMatrix] using e 1 0
  have h02 : 2 * (q.imI * q.imK + q.re * q.imJ) = 0 := by simpa [rotationMatrix] using e 0 2
  have h20 : 2 * (q.imI * q.imK - q.re * q.imJ) = 0 := by simpa [rotationMatrix] using e 2 0
  have h12 : 2 * (q.imJ * q.imK - q.re * q.imI) = 0 := by simpa [rotationMatrix] using e 1 2
  have h21 : 2 * (q.imJ * q.imK + q.re * q.imI) = 0 := by simpa [rotationMatrix] using e 2 1
  -- The off-diagonal entries make the products of the real part with each imaginary part, and
  -- of two of the imaginary parts, vanish.
  have hIJ : q.imI * q.imJ = 0 := cancel _ (by linear_combination h01 + h10)
  have hI : q.re * q.imI = 0 := cancel _ (by linear_combination h21 - h12)
  have hJ : q.re * q.imJ = 0 := cancel _ (by linear_combination h02 - h20)
  have hK : q.re * q.imK = 0 := cancel _ (by linear_combination h10 - h01)
  -- If the real part vanished, two of the diagonal entries would force `2 = 0`.
  have hre : q.re ≠ 0 := by
    intro h0
    rcases mul_eq_zero.mp hIJ with hi | hj
    · exact h2 (by linear_combination -(h11 + h22) + 2 * q.re * h0 - 2 * q.imI * hi)
    · exact h2 (by linear_combination -(h00 + h22) + 2 * q.re * h0 - 2 * q.imJ * hj)
  have hi : q.imI = 0 := (mul_eq_zero.mp hI).resolve_left hre
  have hj : q.imJ = 0 := (mul_eq_zero.mp hJ).resolve_left hre
  have hk : q.imK = 0 := (mul_eq_zero.mp hK).resolve_left hre
  have hsq : (q.re - 1) * (q.re + 1) = 0 := by
    linear_combination h00 - q.imI * hi + q.imJ * hj + q.imK * hk
  rcases mul_eq_zero.mp hsq with h1 | h1
  · have hr : q.re = 1 := by linear_combination h1
    left
    ext <;> simp [hr, hi, hj, hk]
  · have hr : q.re = -1 := by linear_combination h1
    right
    ext <;> simp [hr, hi, hj, hk]

attribute [local instance] starRingOfComm

/-- **The kernel of the action of the unit quaternions on `R³` is `{1, -1}`.** -/
theorem unitaryToSpecialOrthogonalGroup_eq_one_iff {q : unitary ℍ[R]} :
    unitaryToSpecialOrthogonalGroup q = 1 ↔ q = 1 ∨ q = -1 := by
  simp only [Subtype.ext_iff, coe_unitaryToSpecialOrthogonalGroup_apply, OneMemClass.coe_one,
    Unitary.coe_neg, rotationMatrix_eq_one_iff]

/-- **Two unit quaternions give the same rotation exactly when they agree up to sign.** -/
theorem unitaryToSpecialOrthogonalGroup_eq_iff {p q : unitary ℍ[R]} :
    unitaryToSpecialOrthogonalGroup p = unitaryToSpecialOrthogonalGroup q ↔ p = q ∨ p = -q := by
  rw [← div_eq_one, ← map_div, unitaryToSpecialOrthogonalGroup_eq_one_iff, div_eq_one,
    div_eq_iff_eq_mul, neg_one_mul]

end Kernel

end Quaternion
