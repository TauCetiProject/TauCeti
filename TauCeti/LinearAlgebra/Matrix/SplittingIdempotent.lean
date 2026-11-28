/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Tactic.LinearCombination

/-!
# Splitting idempotents of matrices with reducible separable characteristic polynomial

A separable, reducible non-unit polynomial P over a field F factors into coprime non-units
P = A * B with u * A + v * B = 1, giving an idempotent p = u * A modulo P with neither p
nor 1 - p coprime to P. Evaluating p at a matrix M : Matrix n n F whose characteristic
polynomial is P yields a nontrivial idempotent eval M p by Cayley–Hamilton.

## Main results
* Polynomial.exists_idempotent_mod_not_isCoprime: a separable, reducible non-unit polynomial over
  a field admits an idempotent p modulo P with neither p nor 1 - p coprime to P.
* Matrix.exists_isIdempotentElem_aeval_ne_zero_ne_one: a matrix over a field whose characteristic
  polynomial is separable and reducible admits a polynomial p such that eval M p is a
  nontrivial idempotent.

## Provenance
Adapted from grh-lean (https://github.com/lsernau/grh-lean at commit
72fead102f663d5c7a407964a13dc0cf9d977207, Apache 2.0, Copyright 2026 Anthropic, PBC), file
src/Lib/Shimura/TraceFormula/MarkedDefiniteSums.lean (exists_idempotent_mod,
splittingIdempotent_ne_zero_and_ne_one), generalized from GL n F to arbitrary Matrix n n F.
-/

public section

open Polynomial

namespace Polynomial

/-- A separable polynomial P over a field that is neither irreducible nor a unit admits a
polynomial p with P ∣ p * p - p, ¬IsCoprime P p, and ¬IsCoprime P (1 - p). -/
theorem exists_idempotent_mod_not_isCoprime {F : Type*} [Field F] {P : F[X]}
    (hsep : P.Separable) (hred : ¬Irreducible P) (hunit : ¬IsUnit P) :
    ∃ p : F[X], P ∣ p * p - p ∧ ¬IsCoprime P p ∧ ¬IsCoprime P (1 - p) := by
  obtain ⟨A, B, hA, hB, rfl⟩ := (irreducible_or_factor hunit).resolve_left hred
  obtain ⟨u, v, huv⟩ := hsep.isCoprime
  refine ⟨u * A, ⟨-u * v, by linear_combination u * A * huv⟩, fun h ↦ ?_, fun h ↦ ?_⟩
  · exact hA (isCoprime_self.1 h.of_mul_left_left.of_mul_right_right)
  · rw [← huv, add_sub_cancel_left] at h
    exact hB (isCoprime_self.1 h.of_mul_left_right.of_mul_right_right)

end Polynomial
namespace Matrix

/-- If eval M p is a unit, then p is coprime to M.charpoly. -/
private theorem isCoprime_charpoly_of_isUnit_aeval {F n : Type*} [Field F] [Fintype n]
    [DecidableEq n] {M : Matrix n n F} {p : F[X]} (h : IsUnit (aeval M p)) :
    IsCoprime M.charpoly p := by
  classical
  set d := EuclideanDomain.gcd M.charpoly p
  by_contra hcop
  have hd_unit : ¬IsUnit d := fun ⟨u, hu⟩ ↦ hcop ⟨↑u⁻¹ * EuclideanDomain.gcdA M.charpoly p,
    ↑u⁻¹ * EuclideanDomain.gcdB M.charpoly p, by
      linear_combination -↑u⁻¹ * EuclideanDomain.gcd_eq_gcd_ab M.charpoly p - ↑u⁻¹ * hu +
        u.inv_mul⟩
  let f := algebraMap F (AlgebraicClosure F)
  let M' := M.map f
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root (d.map f)
    (by rw [degree_map]; exact fun h0 ↦ hd_unit (isUnit_iff_degree_eq_zero.2 h0))
  have hα_char : M'.charpoly.IsRoot α := by
    rw [Matrix.charpoly_map]
    exact hα.dvd (map_dvd (mapRingHom f) (EuclideanDomain.gcd_dvd_left M.charpoly p))
  obtain ⟨x, hx0, hMx⟩ := Matrix.exists_mulVec_eq_zero_iff.2
    (show (scalar n α - M').det = 0 by rw [← Matrix.eval_charpoly, hα_char])
  have heig : M' *ᵥ x = α • x := by
    simpa [sub_mulVec, scalar_apply, mulVec_diagonal, sub_eq_zero, eq_comm] using hMx
  have haeval : ∀ q : (AlgebraicClosure F)[X], aeval M' q *ᵥ x = eval α q • x := fun q ↦ by
    induction q using Polynomial.induction_on' with
    | add q₁ q₂ h₁ h₂ => simp [map_add, add_mulVec, add_smul, h₁, h₂]
    | monomial k c =>
      have hpow : ∀ m : ℕ, M' ^ m *ᵥ x = α ^ m • x := fun m ↦ by
        induction m with
        | zero => simp
        | succ m hm => rw [pow_succ', ← mulVec_mulVec, hm, mulVec_smul, heig, smul_smul, pow_succ]
      simp [aeval_monomial, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, hpow, smul_smul]
  have hpα : (p.map f).IsRoot α :=
    hα.dvd (map_dvd (mapRingHom f) (EuclideanDomain.gcd_dvd_right M.charpoly p))
  have h0 : aeval M' (p.map f) *ᵥ x = 0 := by rw [haeval, hpα, zero_smul]
  have hmap : aeval M' (p.map f) = (aeval M p).map f := by
    rw [aeval_def, eval₂_map, aeval_def]
    have hcomp : (algebraMap (AlgebraicClosure F) (Matrix n n (AlgebraicClosure F))).comp f =
        f.mapMatrix.comp (algebraMap F (Matrix n n F)) := by
      ext r i j; by_cases hij : i = j <;> simp [Algebra.algebraMap_eq_smul_one, hij]
    exact hcomp ▸ (Polynomial.hom_eval₂ p (algebraMap F (Matrix n n F)) f.mapMatrix M).symm
  obtain ⟨u, hu⟩ := h.map f.mapMatrix
  rw [RingHom.mapMatrix_apply, ← hmap] at hu
  exact hx0 (by simpa [mulVec_mulVec, ← hu] using congrArg (u⁻¹.val *ᵥ ·) h0)

/-- If the characteristic polynomial of a matrix M : Matrix n n F on a nonempty finite index type
is separable and not irreducible, then there is a polynomial p : F[X] such that eval M p is a
nontrivial idempotent (IsIdempotentElem (aeval M p), eval M p ≠ 0, and eval M p ≠ 1). -/
theorem exists_isIdempotentElem_aeval_ne_zero_ne_one {F n : Type*} [Field F] [Fintype n]
    [DecidableEq n] [Nonempty n] {M : Matrix n n F}
    (hsep : M.charpoly.Separable) (hred : ¬Irreducible M.charpoly) :
    ∃ p : F[X], IsIdempotentElem (aeval M p) ∧ aeval M p ≠ 0 ∧ aeval M p ≠ 1 := by
  have hunit : ¬IsUnit M.charpoly :=
    not_isUnit_of_natDegree_pos _ (by simp [Fintype.card_pos])
  obtain ⟨p, hdvd, hself, honesub⟩ :=
    Polynomial.exists_idempotent_mod_not_isCoprime hsep hred hunit
  refine ⟨p, ?_, fun h0 ↦ honesub ?_, fun h1 ↦ hself ?_⟩
  · have h := aeval_dvd M hdvd
    rwa [aeval_self_charpoly, zero_dvd_iff, map_sub, map_mul, sub_eq_zero] at h
  · exact isCoprime_charpoly_of_isUnit_aeval (by simp [h0])
  · exact isCoprime_charpoly_of_isUnit_aeval (by simp [h1])

end Matrix
