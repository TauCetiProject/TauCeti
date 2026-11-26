/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import TauCeti.Algebra.Lie.Matrix.Single
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Tactic.NoncommRing
import TauCeti.Algebra.MvPolynomial.PDeriv
import TauCeti.Algebra.MvPolynomial.PolynomialOperator

/-!
# The oscillator representation of `gl ι` on polynomials

Fix a set of variables `ι` and a predicate `p` on it, the *even* variables. The oscillator
operators on `MvPolynomial ι K` are

* `R i = X i ·` and `L i = ∂ / ∂ X i` when `i` is even,
* `R i = -∂ / ∂ X i` and `L i = X i ·` when `i` is odd.

They satisfy the canonical commutation relations: the `R i` commute with each other, the `L i`
commute with each other, and `L i R j - R j L i = δ i j` (`TauCeti.oscLower_mul_oscRaise`). These
are exactly the relations under which `E i j ↦ R i L j` respects the commutators of the matrix
units, so

`A ↦ ∑ i, ∑ j, A i j • R i L j`

is a Lie algebra homomorphism `TauCeti.oscillatorHom` from `gl ι = Matrix ι ι K` to the
endomorphisms of `MvPolynomial ι K`. With all variables even it is the polarisation action
`E i j ↦ X i ∂ j` of `gl ι` on polynomials; the odd variables are what the theta correspondence
for the dual pairs `(U(p, q), U(r, s))` needs, where `R` and `L` are the two halves of the
infinitesimal Weil representation in its Fock model.

Every monomial is an eigenvector of each `R i L i`, with eigenvalue `m i` for an even `i` and
`-(m i + 1)` for an odd one (`TauCeti.oscRaise_mul_oscLower_monomial`), and `R i L j` preserves
the degree when `i` and `j` have the same parity.

## Main definitions

* `TauCeti.oscRaise K p i`, `TauCeti.oscLower K p i`: the oscillator operators `R i`, `L i`.
* `TauCeti.oscillatorHom K p`: the Lie algebra homomorphism `gl ι → End (MvPolynomial ι K)`,
  `E i j ↦ R i L j`.

## Main results

* `TauCeti.commute_oscRaise`, `TauCeti.commute_oscLower`, `TauCeti.oscLower_mul_oscRaise`: the
  canonical commutation relations.
* `TauCeti.oscillatorHom_single`: the image of a matrix unit.
* `TauCeti.oscRaise_mul_oscLower_monomial`: monomials are weight vectors.
* `TauCeti.rename_oscRaise`, `TauCeti.rename_oscLower`: renaming the variables.
* `TauCeti.oscRaise_mul_oscLower_mem_homogeneousSubmodule`: for two variables of the same parity,
  `R i L j` preserves the degree.
* `TauCeti.oscRaise_mul_oscLower_of_not_iff`: for two variables of opposite parity, `R i L j` is
  multiplication by `X i X j` or the second-order operator `-∂ ∂ / ∂ X i ∂ X j`.

## References

* The operators are adapted from `New.Fock.raiseOp`, `New.Fock.lowerOp` and `New.Fock.glOp` in
  `src/Lib/Weil/Fock/Basic.lean`, and the commutation relations from `New.Fock.raiseOp_comm`,
  `New.Fock.lowerOp_comm`, `New.Fock.lowerOp_raiseOp` and `New.Fock.glOp_commutator` in
  `src/Lib/DiscreteSeries/Theta/FockDualPair.lean`, of grh-lean
  (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC).
* R. Howe, *Transcending classical invariant theory*, J. Amer. Math. Soc. 2 (1989), 535--552.
* M. Kashiwara and M. Vergne, *On the Segal–Shale–Weil representations and harmonic
  polynomials*, Invent. Math. 44 (1978), 1--47.
-/

public section

namespace TauCeti

open MvPolynomial Finset

attribute [local instance 100] LieRing.ofAssociativeRing

variable (K : Type*) [CommRing K] {ι : Type*} (p : ι → Prop) [DecidablePred p]

/-- The oscillator operator `R i` on `MvPolynomial ι K`: multiplication by `X i` if `i` is even
(`p i`), and `-∂ / ∂ X i` if `i` is odd. -/
noncomputable def oscRaise (i : ι) : Module.End K (MvPolynomial ι K) :=
  if p i then LinearMap.mulLeft K (X i) else -(pderiv i).toLinearMap

/-- The oscillator operator `L i` on `MvPolynomial ι K`: `∂ / ∂ X i` if `i` is even (`p i`), and
multiplication by `X i` if `i` is odd. -/
noncomputable def oscLower (i : ι) : Module.End K (MvPolynomial ι K) :=
  if p i then (pderiv i).toLinearMap else LinearMap.mulLeft K (X i)

variable {K p}

@[simp]
theorem oscRaise_apply_of_pos {i : ι} (h : p i) (P : MvPolynomial ι K) :
    oscRaise K p i P = X i * P := by
  simp [oscRaise, h]

@[simp]
theorem oscRaise_apply_of_neg {i : ι} (h : ¬p i) (P : MvPolynomial ι K) :
    oscRaise K p i P = -pderiv i P := by
  simp [oscRaise, h]

@[simp]
theorem oscLower_apply_of_pos {i : ι} (h : p i) (P : MvPolynomial ι K) :
    oscLower K p i P = pderiv i P := by
  simp [oscLower, h]

@[simp]
theorem oscLower_apply_of_neg {i : ι} (h : ¬p i) (P : MvPolynomial ι K) :
    oscLower K p i P = X i * P := by
  simp [oscLower, h]

/-! ### The canonical commutation relations -/

variable (K) in
/-- The operators that make up `R i` and `L i`: multiplication by `X i` and `±∂ / ∂ X i`. -/
private noncomputable def oscPieces (i : ι) : Set (Module.End K (MvPolynomial ι K)) :=
  {LinearMap.mulLeft K (X i), (pderiv i).toLinearMap, -(pderiv i).toLinearMap}

private theorem oscRaise_mem_oscPieces (i : ι) : oscRaise K p i ∈ oscPieces K i := by
  unfold oscRaise oscPieces
  split_ifs <;> simp

private theorem oscLower_mem_oscPieces (i : ι) : oscLower K p i ∈ oscPieces K i := by
  unfold oscLower oscPieces
  split_ifs <;> simp

/-- The pieces of the oscillator operators at two distinct variables commute. -/
private theorem commute_of_mem_oscPieces {i j : ι} (hij : i ≠ j)
    {S T : Module.End K (MvPolynomial ι K)} (hS : S ∈ oscPieces K i) (hT : T ∈ oscPieces K j) :
    Commute S T := by
  simp only [oscPieces, Set.mem_insert_iff, Set.mem_singleton_iff] at hS hT
  refine LinearMap.ext fun P ↦ ?_
  simp only [mul_apply_eq_comp]
  rcases hS with rfl | rfl | rfl <;> rcases hT with rfl | rfl | rfl <;>
    simp [mul_left_comm, pderiv_comm i j, pderiv_X_mul_of_ne hij, pderiv_X_mul_of_ne hij.symm]

/-- The operators `R i` and `R j` commute. -/
theorem commute_oscRaise (i j : ι) : Commute (oscRaise K p i) (oscRaise K p j) := by
  rcases eq_or_ne i j with rfl | hij
  · exact Commute.refl _
  exact commute_of_mem_oscPieces hij (oscRaise_mem_oscPieces i) (oscRaise_mem_oscPieces j)

/-- The operators `L i` and `L j` commute. -/
theorem commute_oscLower (i j : ι) : Commute (oscLower K p i) (oscLower K p j) := by
  rcases eq_or_ne i j with rfl | hij
  · exact Commute.refl _
  exact commute_of_mem_oscPieces hij (oscLower_mem_oscPieces i) (oscLower_mem_oscPieces j)

/-- **The canonical commutation relation** `L i R j = R j L i + δ i j`. For `i = j` this is
Leibniz's rule `∂ (X P) = X ∂ P + P`, whatever the parity of `i`. -/
theorem oscLower_mul_oscRaise [DecidableEq ι] (i j : ι) :
    oscLower K p i * oscRaise K p j = oscRaise K p j * oscLower K p i + if i = j then 1 else 0 := by
  rcases eq_or_ne i j with rfl | hij
  · refine LinearMap.ext fun P ↦ ?_
    by_cases hi : p i <;>
      simp [hi, Derivation.leibniz, add_comm]
  simp only [hij, ite_false, add_zero]
  exact (commute_of_mem_oscPieces hij (oscLower_mem_oscPieces i) (oscRaise_mem_oscPieces j)).eq

/-- The commutator of two products `R i L j` and `R k L m` follows the rule of the matrix units:
it is `δ j k R i L m - δ i m R k L j`. -/
theorem oscRaise_mul_oscLower_commutator [DecidableEq ι] (i j k m : ι) :
    oscRaise K p i * oscLower K p j * (oscRaise K p k * oscLower K p m) -
        oscRaise K p k * oscLower K p m * (oscRaise K p i * oscLower K p j) =
      (if j = k then oscRaise K p i * oscLower K p m else 0) -
        if i = m then oscRaise K p k * oscLower K p j else 0 := by
  -- Move the `L`s to the right; the terms with two `R`s and two `L`s then cancel.
  have h₁ : oscRaise K p i * oscLower K p j * (oscRaise K p k * oscLower K p m) =
      oscRaise K p i * oscRaise K p k * (oscLower K p j * oscLower K p m) +
        if j = k then oscRaise K p i * oscLower K p m else 0 := by
    rw [mul_assoc, ← mul_assoc (oscLower K p j), oscLower_mul_oscRaise]
    split_ifs <;> noncomm_ring
  have h₂ : oscRaise K p k * oscLower K p m * (oscRaise K p i * oscLower K p j) =
      oscRaise K p k * oscRaise K p i * (oscLower K p m * oscLower K p j) +
        if m = i then oscRaise K p k * oscLower K p j else 0 := by
    rw [mul_assoc, ← mul_assoc (oscLower K p m), oscLower_mul_oscRaise]
    split_ifs <;> noncomm_ring
  rw [h₁, h₂, (commute_oscRaise k i).eq, (commute_oscLower m j).eq]
  simp only [@eq_comm _ m i]
  abel

/-! ### Renaming the variables -/

/-- Renaming the variables along an injection `e` intertwines the operators `R i` with the
operators `R (e i)` for a parity `q` with `q (e i) ↔ p i`. -/
theorem rename_oscRaise {κ : Type*} {e : ι → κ} (he : Function.Injective e) {q : κ → Prop}
    [DecidablePred q] (h : ∀ i, q (e i) ↔ p i) (i : ι) (P : MvPolynomial ι K) :
    rename e (oscRaise K p i P) = oscRaise K q (e i) (rename e P) := by
  by_cases hi : p i
  · simp [hi, (h i).2 hi]
  · simp [hi, (h i).not.2 hi, pderiv_rename he]

/-- Renaming the variables along an injection `e` intertwines the operators `L i` with the
operators `L (e i)` for a parity `q` with `q (e i) ↔ p i`. -/
theorem rename_oscLower {κ : Type*} {e : ι → κ} (he : Function.Injective e) {q : κ → Prop}
    [DecidablePred q] (h : ∀ i, q (e i) ↔ p i) (i : ι) (P : MvPolynomial ι K) :
    rename e (oscLower K p i P) = oscLower K q (e i) (rename e P) := by
  by_cases hi : p i
  · simp [hi, (h i).2 hi, pderiv_rename he]
  · simp [hi, (h i).not.2 hi]

/-! ### Weights and degrees -/

/-- **Monomials are weight vectors.** `R i L i` acts on a monomial with exponent `m` by `m i` if
`i` is even and by `-(m i + 1)` if `i` is odd. -/
theorem oscRaise_mul_oscLower_monomial (i : ι) (m : ι →₀ ℕ) (r : K) :
    (oscRaise K p i * oscLower K p i) (monomial m r) =
      (if p i then (m i : K) else -((m i : K) + 1)) • monomial m r := by
  by_cases hi : p i
  · rw [mul_apply_eq_comp, oscLower_apply_of_pos hi, oscRaise_apply_of_pos hi,
      X_mul_pderiv_monomial, ← Nat.cast_smul_eq_nsmul K]
    simp only [hi, ite_true]
  · rw [mul_apply_eq_comp, oscLower_apply_of_neg hi, oscRaise_apply_of_neg hi,
      Derivation.leibniz, pderiv_X_self, smul_eq_mul, smul_eq_mul, mul_one,
      X_mul_pderiv_monomial, ← Nat.cast_smul_eq_nsmul K]
    simp only [hi, ite_false, neg_smul, add_smul, one_smul, neg_add_rev]

/-- The vacuum `1` is killed by `R i L i` for an even `i`, and multiplied by `-1` for an odd
one. -/
theorem oscRaise_mul_oscLower_self_one (i : ι) :
    (oscRaise K p i * oscLower K p i) 1 = if p i then 0 else -1 := by
  by_cases hi : p i <;> simp [hi]

/-- For distinct variables of the same parity, `R i L j` kills the vacuum `1`. -/
theorem oscRaise_mul_oscLower_one_of_ne {i j : ι} (hij : i ≠ j) (h : p i ↔ p j) :
    (oscRaise K p i * oscLower K p j) 1 = 0 := by
  by_cases hj : p j
  · simp [hj]
  · simp [hj, h.not.2 hj, pderiv_X_of_ne hij.symm]

/-- For two variables of opposite parity, `R i L j` is multiplication by `X i X j` if `i` is even,
and the second-order operator `-∂ ∂ / ∂ X i ∂ X j` if `i` is odd. -/
theorem oscRaise_mul_oscLower_of_not_iff {i j : ι} (h : ¬(p i ↔ p j)) (P : MvPolynomial ι K) :
    (oscRaise K p i * oscLower K p j) P =
      (if p i then X i * X j * P else 0) - if p i then 0 else pderiv i (pderiv j P) := by
  by_cases hi : p i
  · have hj : ¬p j := fun hj ↦ h (iff_of_true hi hj)
    simp [hi, hj, mul_assoc]
  · have hj : p j := by tauto
    simp [hi, hj]

/-- For two variables of the same parity, `R i L j` preserves the degree of homogeneous
polynomials. -/
theorem oscRaise_mul_oscLower_mem_homogeneousSubmodule {i j : ι} (h : p i ↔ p j) {d : ℕ}
    {P : MvPolynomial ι K} (hP : P ∈ homogeneousSubmodule ι K d) :
    (oscRaise K p i * oscLower K p j) P ∈ homogeneousSubmodule ι K d := by
  rw [mem_homogeneousSubmodule] at hP ⊢
  by_cases hj : p j
  · rw [mul_apply_eq_comp, oscLower_apply_of_pos hj, oscRaise_apply_of_pos (h.2 hj),
      ← polynomialOperator_apply]
    exact hP.polynomialOperator i j
  · rw [mul_apply_eq_comp, oscLower_apply_of_neg hj, oscRaise_apply_of_neg (h.not.2 hj)]
    simpa using ((isHomogeneous_X K j).mul hP).pderiv.neg

/-! ### The Lie algebra homomorphism -/

variable [Fintype ι] [DecidableEq ι]

variable (K p) in
/-- The linear map underlying `TauCeti.oscillatorHom`. -/
private noncomputable def oscillatorLinearMap :
    Matrix ι ι K →ₗ[K] Module.End K (MvPolynomial ι K) where
  toFun A := ∑ i, ∑ j, A i j • (oscRaise K p i * oscLower K p j)
  map_add' A B := by simp [add_smul, sum_add_distrib]
  map_smul' c A := by simp [smul_sum, smul_smul]

omit [DecidableEq ι] in
private theorem oscillatorLinearMap_apply (A : Matrix ι ι K) :
    oscillatorLinearMap K p A = ∑ i, ∑ j, A i j • (oscRaise K p i * oscLower K p j) :=
  (rfl)

private theorem oscillatorLinearMap_single (i j : ι) (c : K) :
    oscillatorLinearMap K p (Matrix.single i j c) = c • (oscRaise K p i * oscLower K p j) := by
  rw [oscillatorLinearMap_apply, sum_eq_single i, sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp
  · intro a _ ha
    exact sum_eq_zero fun b _ ↦ by simp [Ne.symm ha]
  · simp

private theorem oscillatorLinearMap_lie (A B : Matrix ι ι K) :
    oscillatorLinearMap K p ⁅A, B⁆ =
      ⁅oscillatorLinearMap K p A, oscillatorLinearMap K p B⁆ := by
  -- Both sides are bilinear, so it suffices to compare them on matrix units.
  induction A using Matrix.induction_on' with
  | h_zero => simp
  | h_add A A' hA hA' => rw [add_lie, map_add, map_add, add_lie, hA, hA']
  | h_std_basis a b x =>
    induction B using Matrix.induction_on' with
    | h_zero => simp
    | h_add B B' hB hB' => rw [lie_add, map_add, map_add, lie_add, hB, hB']
    | h_std_basis c d y =>
      rw [Matrix.lie_single_single, map_sub, apply_ite (oscillatorLinearMap K p),
        apply_ite (oscillatorLinearMap K p), oscillatorLinearMap_single,
        oscillatorLinearMap_single, oscillatorLinearMap_single, oscillatorLinearMap_single,
        map_zero, LieRing.of_associative_ring_bracket, smul_mul_smul_comm, smul_mul_smul_comm,
        mul_comm y x]
      have h := congrArg ((x * y) • ·) (oscRaise_mul_oscLower_commutator (K := K) (p := p) a b c d)
      simpa only [smul_sub, smul_ite, smul_zero, @eq_comm _ d a] using h.symm

variable (K p) in
/-- **The oscillator representation** of `gl ι` on `MvPolynomial ι K`: the matrix unit `E i j`
acts by `R i L j`, so a matrix `A` acts by `∑ i, ∑ j, A i j • R i L j`. -/
noncomputable def oscillatorHom : Matrix ι ι K →ₗ⁅K⁆ Module.End K (MvPolynomial ι K) :=
  { oscillatorLinearMap K p with map_lie' := oscillatorLinearMap_lie _ _ }

theorem oscillatorHom_apply (A : Matrix ι ι K) :
    oscillatorHom K p A = ∑ i, ∑ j, A i j • (oscRaise K p i * oscLower K p j) :=
  (rfl)

/-- The matrix unit `E i j` acts by `R i L j`. -/
@[simp]
theorem oscillatorHom_single (i j : ι) (c : K) :
    oscillatorHom K p (Matrix.single i j c) = c • (oscRaise K p i * oscLower K p j) :=
  oscillatorLinearMap_single i j c

end TauCeti
