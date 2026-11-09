/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.IntegralMatrix

/-!
# Braid relations in the doubled minuscule E₆ carrier

The pinned words `xᵢ(1) x₋ᵢ(-1) xᵢ(1)` satisfy the commuting and length-three braid
relations over every commutative ring. These are identities of the actual carrier points,
including their signs, rather than identities only modulo the weight torus. They give
coherence for Weyl-word transport of the numbered root subgroups.

The proof uses the integral root-matrix formulas of
`TauCeti.Algebra.Lie.E6.DoubledMinuscule.IntegralMatrix`. On each of the two minuscule
summands the pinned word is the same signed permutation of the twenty-seven weights.
Only the finite permutation and sign identities are checked by reduction; coefficient
change then gives the identities over arbitrary rings, including nonreduced rings.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §§3 and 6.
* R. W. Carter, *Simple Groups of Lie Type*, §6.4.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate V.
-/

public section

open scoped Matrix
open TauCeti.DynkinType

namespace TauCeti.E6DoubledMinuscule

private noncomputable abbrev rootMatrix (k : Fin 6 ⊕ Fin 6) (t : ℤ) : Matrix (Fin 54) (Fin 54) ℤ :=
  1 + t • rootIntMatrix k

private noncomputable def weylMatrix (i : Fin 6) : Matrix (Fin 54) (Fin 54) ℤ :=
  rootMatrix (.inl i) 1 * rootMatrix (.inr i) (-1) * rootMatrix (.inl i) 1

private def weylSign (i : Fin 6) (a : Fin 27) : ℤ :=
  if e6MinusculeWeight a i = 1 then -1 else 1

private theorem rootMatrix_mulVec_single (k : Fin 6 ⊕ Fin 6) (t : ℤ)
    (a : Fin 27 ⊕ Fin 27) :
    rootMatrix k t *ᵥ Pi.single (matrixIndexEquiv a) 1 =
      Pi.single (matrixIndexEquiv a) 1 +
        (t * if e6DoubledMinusculeWeight a (Sum.elim id id k) =
            (Sum.elim (fun _ ↦ -1) (fun _ ↦ 1) k : ℤ)
          then summandSign a else 0) •
          Pi.single (matrixIndexEquiv (reflection (Sum.elim id id k) a)) 1 := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Matrix.mulVec_single_one]
  ext b
  by_cases hb : b = matrixIndexEquiv (reflection (Sum.elim id id k) a) <;>
    by_cases hw : e6DoubledMinusculeWeight a (Sum.elim id id k) =
      (Sum.elim (fun _ ↦ -1) (fun _ ↦ 1) k : ℤ)
  all_goals simp [rootIntMatrix_apply, hb, hw, matrixWeight_apply, Pi.single_apply]

private theorem weylMatrix_mulVec_single (i : Fin 6) (a : Fin 27 ⊕ Fin 27) :
    weylMatrix i *ᵥ Pi.single (matrixIndexEquiv a) 1 =
      (weylSign i (Sum.elim id id a)) •
        Pi.single (matrixIndexEquiv (reflection i a)) 1 := by
  simp only [weylMatrix, ← Matrix.mulVec_mulVec, rootMatrix_mulVec_single,
    Matrix.mulVec_add, Matrix.mulVec_smul, reflection_apply_apply,
    e6DoubledMinusculeWeight_reflection_apply_self]
  cases a with
  | inl a =>
    rcases e6MinusculeWeight_apply_eq_neg_one_or_eq_zero_or_eq_one a i with h | h | h
    · simp [weylSign, h]
    · simp [weylSign, h, (e6MinusculeReflection_eq_self_iff i a).mpr h]
    · simp [weylSign, h]
  | inr a =>
    rcases e6MinusculeWeight_apply_eq_neg_one_or_eq_zero_or_eq_one a i with h | h | h
    · simp [weylSign, h]
    · simp [weylSign, h, (e6MinusculeReflection_eq_self_iff i a).mpr h]
    · simp [weylSign, h]

private theorem commutingCertificate : ∀ i j : Fin 6, CartanMatrix.E 6 i j = 0 →
    ∀ a : Fin 27,
      (weylSign j a * weylSign i (e6MinusculeReflection j a),
          e6MinusculeReflection i (e6MinusculeReflection j a)) =
        (weylSign i a * weylSign j (e6MinusculeReflection i a),
          e6MinusculeReflection j (e6MinusculeReflection i a)) := by
  intro i j hij a
  fin_cases i <;> fin_cases j <;> norm_num [CartanMatrix.E_six_eq] at hij
  all_goals fin_cases a <;> decide +kernel

private theorem braidCertificate : ∀ i j : Fin 6, CartanMatrix.E 6 i j = -1 →
    ∀ a : Fin 27,
      (weylSign i a * (weylSign j (e6MinusculeReflection i a) *
          weylSign i (e6MinusculeReflection j (e6MinusculeReflection i a))),
        e6MinusculeReflection i (e6MinusculeReflection j (e6MinusculeReflection i a))) =
      (weylSign j a * (weylSign i (e6MinusculeReflection j a) *
          weylSign j (e6MinusculeReflection i (e6MinusculeReflection j a))),
        e6MinusculeReflection j (e6MinusculeReflection i (e6MinusculeReflection j a))) := by
  intro i j hij a
  fin_cases i <;> fin_cases j <;> norm_num [CartanMatrix.E_six_eq] at hij
  all_goals fin_cases a <;> decide +kernel

private theorem weylMatrix_commute (i j : Fin 6) (hij : CartanMatrix.E 6 i j = 0) :
    weylMatrix i * weylMatrix j = weylMatrix j * weylMatrix i := by
  apply Matrix.ext_of_mulVec_single
  intro b
  obtain ⟨a, rfl⟩ := matrixIndexEquiv.surjective b
  cases a <;>
    simp only [← Matrix.mulVec_mulVec, weylMatrix_mulVec_single, Matrix.mulVec_smul,
      reflection_inl, reflection_inr, Sum.elim_inl, Sum.elim_inr, Function.id_def, smul_smul]
  all_goals
    rename_i a
    obtain ⟨hs, hr⟩ := Prod.mk.inj (commutingCertificate i j hij a)
    rw [hs, hr]

private theorem weylMatrix_braid (i j : Fin 6) (hij : CartanMatrix.E 6 i j = -1) :
    weylMatrix i * weylMatrix j * weylMatrix i =
      weylMatrix j * weylMatrix i * weylMatrix j := by
  apply Matrix.ext_of_mulVec_single
  intro b
  obtain ⟨a, rfl⟩ := matrixIndexEquiv.surjective b
  cases a <;>
    simp only [← Matrix.mulVec_mulVec, weylMatrix_mulVec_single, Matrix.mulVec_smul,
      reflection_inl, reflection_inr, Sum.elim_inl, Sum.elim_inr, Function.id_def, smul_smul]
  all_goals
    rename_i a
    obtain ⟨hs, hr⟩ := Prod.mk.inj (braidCertificate i j hij a)
    rw [hs, hr]

private theorem coe_weylWord (A : Type*) [CommRing A] (i : Fin 6) :
    (((rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1)) :
        Matrix.GeneralLinearGroup (Fin 54) A) : Matrix (Fin 54) (Fin 54) A) *
      (((rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-1))) :
        Matrix.GeneralLinearGroup (Fin 54) A) : Matrix (Fin 54) (Fin 54) A) *
      (((rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1)) :
        Matrix.GeneralLinearGroup (Fin 54) A) : Matrix (Fin 54) (Fin 54) A) =
      (Int.castRingHom A).mapMatrix (weylMatrix i) := by
  simp only [coe_rootSubgroupPoints_eq_one_add_smul, toAdd_ofAdd, one_smul, neg_smul]
  simp only [weylMatrix, rootMatrix, one_smul, neg_smul, map_mul, map_add, map_neg,
    map_one]
  -- The matrix ring homomorphism applies the integer coefficient map entrywise.
  rfl

/-- Pinned simple Weyl words at nodes with zero Cartan entry commute in the doubled
minuscule E₆ carrier. -/
theorem commute_weylWord_of_cartanMatrix_eq_zero (A : Type*) [CommRing A]
    (i j : Fin 6) (hij : CartanMatrix.E 6 i j = 0) :
    Commute
      (rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1) *
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-1)) *
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1))
      (rootSubgroupPoints (.inl j) A (Multiplicative.ofAdd 1) *
        rootSubgroupPoints (.inr j) A (Multiplicative.ofAdd (-1)) *
        rootSubgroupPoints (.inl j) A (Multiplicative.ofAdd 1)) := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_weylWord]
  have h := congrArg ((Int.castRingHom A).mapMatrix) (weylMatrix_commute i j hij)
  simpa only [map_mul] using h

/-- Pinned simple Weyl words at nodes with Cartan entry `-1` satisfy the length-three
braid relation in the doubled minuscule E₆ carrier. -/
theorem weylWord_braid_of_cartanMatrix_eq_neg_one (A : Type*) [CommRing A]
    (i j : Fin 6) (hij : CartanMatrix.E 6 i j = -1) :
    (rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1) *
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-1)) *
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1)) *
      (rootSubgroupPoints (.inl j) A (Multiplicative.ofAdd 1) *
        rootSubgroupPoints (.inr j) A (Multiplicative.ofAdd (-1)) *
        rootSubgroupPoints (.inl j) A (Multiplicative.ofAdd 1)) *
      (rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1) *
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-1)) *
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1)) =
    (rootSubgroupPoints (.inl j) A (Multiplicative.ofAdd 1) *
        rootSubgroupPoints (.inr j) A (Multiplicative.ofAdd (-1)) *
        rootSubgroupPoints (.inl j) A (Multiplicative.ofAdd 1)) *
      (rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1) *
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-1)) *
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1)) *
      (rootSubgroupPoints (.inl j) A (Multiplicative.ofAdd 1) *
        rootSubgroupPoints (.inr j) A (Multiplicative.ofAdd (-1)) *
        rootSubgroupPoints (.inl j) A (Multiplicative.ofAdd 1)) := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_weylWord]
  have h := congrArg ((Int.castRingHom A).mapMatrix) (weylMatrix_braid i j hij)
  simpa only [map_mul] using h

end TauCeti.E6DoubledMinuscule
