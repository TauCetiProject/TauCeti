/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Module
public import TauCeti.Algebra.TemperleyLieb.MarkovTrace

/-!
# Coefficient conjugation on Temperley–Lieb algebras

Conjugating the coefficients sends the algebra at loop value `δ` to the algebra at `star δ`,
fixing the generator labels and preserving the order of multiplication. In particular, for
complex coefficients this is distinct from the product-reversing analytic adjoint. The
coefficient map commutes with adding a straight strand and conjugates the unnormalized Markov
trace, with no reality restriction on the loop value.

The construction uses `TemperleyLieb.lift` and twists the target scalar action using
`Algebra.compHom`, as in `TemperleyLieb.instStarRing`, but without passing to the opposite
algebra. Trace transport uses `IsMarkovTrace.unique`.
-/

public section

namespace TauCeti.TemperleyLieb

section Semiring

variable {R : Type*} [CommSemiring R] [StarRing R] {δ δ' : R} {n : ℕ}

private def coeffConjHom (h : star δ = δ') : TemperleyLieb R δ n →+* TemperleyLieb R δ' n := by
  have hsq (i : Fin (n - 1)) :
      e δ' i * e δ' i = algebraMap R (TemperleyLieb R δ' n) δ' * e δ' i := by
    simp [Algebra.smul_def]
  letI : Algebra R (TemperleyLieb R δ' n) := Algebra.compHom _ (starRingEnd R)
  exact (lift (e δ') (fun i ↦ by
    simpa only [Algebra.smul_def, Algebra.compHom_algebraMap_apply, starRingEnd_apply, h]
      using hsq i)
    (fun hadj ↦ e_mul_e_mul_e hadj) (fun hdist ↦ (commute_e hdist).eq)).toRingHom

private theorem coeffConjHom_e (h : star δ = δ') (i : Fin (n - 1)) :
    coeffConjHom h (e δ i) = e δ' i := by
  simp [coeffConjHom]

private theorem coeffConjHom_algebraMap (h : star δ = δ') (r : R) :
    coeffConjHom (n := n) h (algebraMap R _ r) = algebraMap R _ (star r) := by
  simp [coeffConjHom, Algebra.compHom_algebraMap_apply, starRingEnd_apply]

private theorem coeffConjHom_leftInverse (h : star δ = δ') (h' : star δ' = δ) :
    Function.LeftInverse (coeffConjHom (n := n) h') (coeffConjHom h) := by
  intro x
  induction x using TemperleyLieb.induction with
  | e i => simp only [coeffConjHom_e]
  | algebraMap r => simp only [coeffConjHom_algebraMap, star_star]
  | add x y hx hy => simp only [map_add, hx, hy]
  | mul x y hx hy => simp only [map_mul, hx, hy]

/-- Coefficient conjugation between conjugate Temperley–Lieb fibers. This ring isomorphism
fixes the generators and sends scalars through `star`. -/
def coeffConj (h : star δ = δ') : TemperleyLieb R δ n ≃+* TemperleyLieb R δ' n :=
  let h' : star δ' = δ := by simp [← h]
  { coeffConjHom h with
    invFun := coeffConjHom h'
    left_inv := coeffConjHom_leftInverse h h'
    right_inv := coeffConjHom_leftInverse h' h }

/-- Coefficient conjugation leaves the generator index unchanged. -/
@[simp]
theorem coeffConj_e (h : star δ = δ') (i : Fin (n - 1)) :
    coeffConj h (e δ i) = e δ' i :=
  coeffConjHom_e h i

/-- Coefficient conjugation acts by `star` on scalar elements. -/
@[simp]
theorem coeffConj_algebraMap (h : star δ = δ') (r : R) :
    coeffConj (n := n) h (algebraMap R _ r) = algebraMap R _ (star r) :=
  coeffConjHom_algebraMap h r

/-- Coefficient conjugation is semilinear over scalar conjugation. -/
@[simp]
theorem coeffConj_smul (h : star δ = δ') (r : R) (x : TemperleyLieb R δ n) :
    coeffConj h (r • x) = star r • coeffConj h x := by
  simp [Algebra.smul_def]

/-- Coefficient conjugation as a semilinear equivalence, for transporting linear forms between
fibers. -/
def coeffConjLinearEquiv (h : star δ = δ') :
    TemperleyLieb R δ n ≃ₗ⋆[R] TemperleyLieb R δ' n where
  __ := (coeffConj h).toAddEquiv
  map_smul' := coeffConj_smul h

/-- The semilinear and ring equivalences have the same underlying function. -/
@[simp]
theorem coeffConjLinearEquiv_apply (h : star δ = δ') (x : TemperleyLieb R δ n) :
    coeffConjLinearEquiv h x = coeffConj h x := (rfl)

/-- The inverse of coefficient conjugation is coefficient conjugation in the other direction. -/
@[simp]
theorem coeffConj_symm (h : star δ = δ') :
    (coeffConj (n := n) h).symm = coeffConj (by simp [← h] : star δ' = δ) :=
  (rfl)

/-- The inverse semilinear equivalence conjugates coefficients back to the original fiber. -/
@[simp]
theorem coeffConjLinearEquiv_symm_apply (h : star δ = δ') (x : TemperleyLieb R δ' n) :
    (coeffConjLinearEquiv h (n := n)).symm x = coeffConj (by simp [← h]) x :=
  (rfl)

/-- Conjugating twice acts as the identity on the original fiber. -/
@[simp]
theorem coeffConj_coeffConj (h : star δ = δ') (h' : star δ' = δ) (x : TemperleyLieb R δ n) :
    coeffConj h' (coeffConj h x) = x :=
  (coeffConj h).symm_apply_apply x

/-- A ring homomorphism conjugating the scalars and fixing the generators is coefficient
conjugation. -/
theorem eq_coeffConj (h : star δ = δ') (f : TemperleyLieb R δ n →+* TemperleyLieb R δ' n)
    (hs : ∀ r, f (algebraMap R _ r) = algebraMap R _ (star r))
    (he : ∀ i, f (e δ i) = e δ' i) : f = (coeffConj h).toRingHom := by
  ext x
  induction x using TemperleyLieb.induction with
  | e i => simp [he]
  | algebraMap r => simp [hs]
  | add x y hx hy => simp only [map_add, hx, hy]
  | mul x y hx hy => simp only [map_mul, hx, hy]

/-- Conjugating coefficients commutes with adding a straight last strand. -/
@[simp]
theorem coeffConj_strandIncl (h : star δ = δ') (x : TemperleyLieb R δ (n + 1)) :
    coeffConj h (strandIncl x) = strandIncl (coeffConj h x) := by
  induction x using TemperleyLieb.induction with
  | e i => simp
  | algebraMap r => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | mul x y hx hy => simp only [map_mul, hx, hy]

/-- The conjugate of an unnormalized Markov trace agrees with the Markov trace on the
conjugate fiber. -/
theorem IsMarkovTrace.map_coeffConj {tr : ∀ m, TemperleyLieb R δ m →ₗ[R] R}
    {tr' : ∀ m, TemperleyLieb R δ' m →ₗ[R] R} (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R δ' tr') (h : star δ = δ') (x : TemperleyLieb R δ n) :
    tr' n (coeffConj h x) = star (tr n x) := by
  let pull (m : ℕ) : TemperleyLieb R δ m →ₗ[R] R :=
    (starLinearEquiv R).toLinearMap.comp ((tr' m).comp (coeffConjLinearEquiv h).toLinearMap)
  have hp (m : ℕ) (y : TemperleyLieb R δ m) : pull m y = star (tr' m (coeffConj h y)) := by
    simp [pull]
  have hrev : star δ' = δ := by simp [← h]
  -- Conjugating the input and the output gives a linear Markov family on the original fiber.
  have hpull : IsMarkovTrace R δ pull := by
    constructor
    · intro m
      simp [hp, htr'.map_one, hrev]
    · intro m y z
      simp only [hp, map_mul, htr'.map_mul_comm m (coeffConj h y)]
    · intro m y
      simp [hp, htr'.map_strandIncl, hrev]
    · intro m y
      simp [hp, htr'.map_strandIncl_mul_e_last]
  have hval : pull n x = tr n x := LinearMap.congr_fun (congrFun (hpull.unique htr) n) x
  rw [hp] at hval
  rw [← hval, star_star]

end Semiring

/-- The spin-model Markov trace conjugates under simultaneous conjugation of the quantum
parameter, the loop value and the input. -/
@[simp]
theorem markovTrace_coeffConj {R : Type*} [CommRing R] [StarRing R] {δ δ' : R} {n : ℕ}
    (q : Rˣ) (hq : δ = -((q : R) + ↑q⁻¹)) (h : star δ = δ') (x : TemperleyLieb R δ n) :
    markovTrace (star q) (by simp [← h, hq]) (coeffConj h x) = star (markovTrace q hq x) :=
  (isMarkovTrace_markovTrace q hq).map_coeffConj (isMarkovTrace_markovTrace (star q) _) h x

end TauCeti.TemperleyLieb
