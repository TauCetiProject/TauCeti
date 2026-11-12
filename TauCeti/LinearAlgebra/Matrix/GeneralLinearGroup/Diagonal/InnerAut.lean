/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.InnerAut
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
import Mathlib.Data.Set.Finite.Basic

/-!
# Diagonal conjugations of matrix algebras

Over an infinite field, a matrix whose inner automorphism commutes with every diagonal
conjugation is diagonal. In particular, passing from invertible matrices to their inner
algebra automorphisms introduces no extra elements in the centralizer of the diagonal torus.
This supplies the pointwise centralizer calculation for the projective general linear group.

The proof tests diagonals with just one exceptional entry `t`, chosen with `t² ≠ 1`.
Commuting conjugations give a scalar commutation relation; a nonzero off-diagonal entry
would force an entire row to vanish. The argument works in every characteristic.

## References

* J. E. Humphreys, *Linear Algebraic Groups* (1975), §16.1.
-/

public section

open Matrix TauCeti

namespace Matrix.GeneralLinearGroup

variable {ι K : Type*} [Fintype ι] [DecidableEq ι]

/-- Dividing each diagonal entry by the last one preserves conjugation and makes the
last diagonal entry equal to one. -/
theorem innerAut_diagGL_normalize (r : ℕ) {A : Type*} [CommSemiring A]
    (d : Fin (r + 1) → Aˣ) :
    innerAut (diagGL d) =
      innerAut
        (diagGL (Fin.lastCases 1 (fun i ↦ d i.castSucc / d (Fin.last r)))) := by
  have hd : (d / fun _ ↦ d (Fin.last r)) =
      Fin.lastCases 1 (fun i ↦ d i.castSucc / d (Fin.last r)) := by
    funext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp
  simpa only [map_div, diagGL_const, innerAut_scalar, div_one]
    using congrArg (fun d ↦ innerAut (diagGL d)) hd

variable [Field K] [Infinite K]

/-- Over an infinite field, a matrix centralizing all diagonal conjugations up to scalars
is diagonal. Equivalently, the inverse image of the centralizer of the projective diagonal
torus is the ordinary diagonal torus. -/
theorem isDiag_of_commute_innerAut_diagGL (g : GL ι K)
    (hg : ∀ d : ι → Kˣ, Commute (innerAut g) (innerAut (diagGL d))) :
    (g : Matrix ι ι K).IsDiag := by
  classical
  obtain ⟨t, ht⟩ := (Set.toFinite ({0, 1, -1} : Set K)).exists_notMem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ht
  have ht0 : t ≠ 0 := ht.1
  have ht1 : t ≠ 1 := ht.2.1
  have htsq : t * t ≠ 1 := by
    rw [← sq, sq_ne_one_iff]
    exact ht.2
  intro i j hij
  by_contra hentry
  let d : ι → Kˣ := Function.update 1 j (Units.mk0 t ht0)
  let D := diagGL d
  have hcent : g * D * (D * g)⁻¹ ∈ Subgroup.center (GL ι K) := by
    apply (innerAut_eq_one_iff _).mp
    simp only [map_mul, map_inv, mul_inv_eq_one]
    exact (hg d).eq
  -- Commuting inner automorphisms give a scalar commutation relation.
  obtain ⟨c, hc⟩ := mem_center_iff_val_mem_range_scalar.mp hcent
  have heq : (g : Matrix ι ι K) * (D : Matrix ι ι K) =
      Matrix.scalar ι c * ((D : Matrix ι ι K) * (g : Matrix ι ι K)) := by
    have h := congrArg (fun a : GL ι K ↦ (a : Matrix ι ι K))
      (inv_mul_cancel_right (g * D) (D * g))
    rw [Units.val_mul, ← hc, Units.val_mul, Units.val_mul] at h
    exact h.symm
  have hentries (a b : ι) : g a b * (d b : K) = c * ((d a : K) * g a b) := by
    have h := congrArg (fun M : Matrix ι ι K ↦ M a b) heq
    simpa only [D, diagGL_coe, Matrix.mul_diagonal, Matrix.diagonal_mul,
      Matrix.scalar_apply, Matrix.diagonal_mul] using h
  have hct : c = t := by
    have h := hentries i j
    simp only [d, Function.update_self, Function.update_of_ne hij,
      Pi.one_apply, Units.val_one, Units.val_mk0, one_mul] at h
    exact (mul_right_cancel₀ hentry (by simpa [mul_comm] using h)).symm
  -- A nonzero off-diagonal entry would force an entire row to vanish.
  have hrow (a : ι) : g j a = 0 := by
    have h := hentries j a
    rw [hct] at h
    simp only [d, Function.update_self, Units.val_mk0] at h
    have hcoef : (d a : K) ≠ t * t := by
      by_cases ha : a = j
      · subst a
        simp only [d, Function.update_self, Units.val_mk0]
        intro h
        exact ht1 ((mul_left_cancel₀ ht0 (by simpa using h)).symm)
      · simpa only [d, Function.update_of_ne ha, Pi.one_apply, Units.val_one] using htsq.symm
    have hmul : (d a : K) * g j a = (t * t) * g j a := by
      simpa [mul_comm, mul_assoc] using h
    exact (mul_eq_mul_right_iff.mp hmul).resolve_left hcoef
  have h := congrArg (fun M : Matrix ι ι K ↦ M j j) g.val_inv
  simp [Matrix.mul_apply, hrow] at h

end Matrix.GeneralLinearGroup
