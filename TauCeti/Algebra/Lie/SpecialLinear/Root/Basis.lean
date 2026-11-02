/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.Finrank
public import TauCeti.Algebra.Lie.SpecialLinear.Diagonal
public import Mathlib.Data.Nat.Dist
public import Mathlib.LinearAlgebra.Pi

/-!
# Signed root coordinates for the special linear Lie algebra

Over a commutative ring, adjacent diagonal differences and signed off-diagonal matrix units
form a basis of the trace-zero matrices. Its diagonal coordinates are initial sums; its root
coordinates are signed matrix entries. The construction composes `specialLinearEntryEquiv`
with a partition of its index set and `partialSumsLinearEquiv`.
-/

public section

namespace TauCeti

open LieAlgebra.SpecialLinear

variable (r : ℕ) (A : Type*) [CommRing A]

/-- The interval-root sign: positive roots have sign one, and a negative root of height `h`
has sign `(-1) ^ (h - 1)`. -/
def specialLinearRootSign (i j : Fin (r + 1)) : A :=
  if i < j then 1 else (-1) ^ (i.val - j.val - 1)

/-- The sign is determined by the orientation and length of the interval. -/
theorem specialLinearRootSign_def (i j : Fin (r + 1)) :
    specialLinearRootSign r A i j =
      if i < j then 1 else (-1) ^ (i.val - j.val - 1) := by
  rfl

/-- A positive interval root has sign one. -/
@[simp]
theorem specialLinearRootSign_of_lt (i j : Fin (r + 1)) (hij : i < j) :
    specialLinearRootSign r A i j = 1 := by
  simp only [specialLinearRootSign_def, ite_eq_left hij]

/-- A negative interval root has the sign determined by its height minus one. -/
@[simp]
theorem specialLinearRootSign_of_gt (i j : Fin (r + 1)) (hji : j < i) :
    specialLinearRootSign r A i j = (-1 : A) ^ (i.val - j.val - 1) := by
  simp only [specialLinearRootSign_def, ite_eq_right (not_lt_of_ge hji.le)]

/-- Reversing and swapping the indices preserves the interval-root sign. -/
@[simp]
theorem specialLinearRootSign_rev_rev (i j : Fin (r + 1)) :
    specialLinearRootSign r A j.rev i.rev = specialLinearRootSign r A i j := by
  have h : j.rev.val - i.rev.val = i.val - j.val := by
    simp only [Fin.val_rev]
    omega
  simp only [specialLinearRootSign_def, Fin.rev_lt_rev, h]

/-- Every interval-root sign is its own inverse. -/
@[simp]
theorem specialLinearRootSign_mul_self (i j : Fin (r + 1)) :
    specialLinearRootSign r A i j * specialLinearRootSign r A i j = 1 := by
  unfold specialLinearRootSign
  split <;> simp [← mul_pow]

/-- The product of opposite root signs depends only on the interval height. -/
theorem specialLinearRootSign_mul_swap (i j : Fin (r + 1)) (hij : i ≠ j) :
    specialLinearRootSign r A i j * specialLinearRootSign r A j i =
      (-1 : A) ^ (Nat.dist i.val j.val - 1) := by
  rcases lt_or_gt_of_ne hij with h | h
  · rw [specialLinearRootSign_of_lt r A i j h,
      specialLinearRootSign_of_gt r A j i h, one_mul]
    congr 1
    unfold Nat.dist
    omega
  · rw [specialLinearRootSign_of_gt r A i j h,
      specialLinearRootSign_of_lt r A j i h, mul_one]
    congr 1
    unfold Nat.dist
    omega

/-- The product of opposite root signs is also the alternating matrix-graph sign. -/
theorem specialLinearRootSign_mul_swap_eq_neg_one_pow
    (i j : Fin (r + 1)) (hij : i ≠ j) :
    specialLinearRootSign r A i j * specialLinearRootSign r A j i =
      (-1 : A) ^ (i.val + j.val + 1) := by
  rw [specialLinearRootSign_mul_swap r A i j hij,
    neg_one_pow_eq_pow_mod_two (Nat.dist i.val j.val - 1),
    neg_one_pow_eq_pow_mod_two (i.val + j.val + 1)]
  congr 1
  have hne : i.val ≠ j.val := fun h ↦ hij (Fin.ext h)
  unfold Nat.dist
  omega

/-- Over `ℤ`, the interval-root sign is `Int.negOnePow` of zero for a positive root and of the
height minus one for a negative root. -/
theorem specialLinearRootSign_eq_negOnePow (i j : Fin (r + 1)) :
    specialLinearRootSign r ℤ i j =
      (((if i < j then 0 else ((i : ℕ) - j - 1 : ℕ)) : ℤ).negOnePow : ℤ) := by
  rw [specialLinearRootSign_def]
  split_ifs <;> simp [Int.coe_negOnePow_natCast]

/-- The signed matrix unit belonging to an unequal pair of indices. -/
def specialLinearSignedRoot (i j : Fin (r + 1)) (h : i ≠ j) : sl (Fin (r + 1)) A :=
  single i j h (specialLinearRootSign r A i j)

/-- The underlying matrix of a signed root is its signed matrix unit. -/
@[simp]
theorem specialLinearSignedRoot_val (i j : Fin (r + 1)) (h : i ≠ j) :
    (specialLinearSignedRoot r A i j h).val =
      Matrix.single i j (specialLinearRootSign r A i j) := by
  rfl

private def rootEntryIndexEquiv :
    (Fin r ⊕ {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2}) ≃
      {p : Fin (r + 1) × Fin (r + 1) // p ≠ (Fin.last r, Fin.last r)} where
  toFun
    | .inl i => ⟨(i.castSucc, i.castSucc), fun h =>
        Fin.castSucc_ne_last i (congrArg Prod.fst h)⟩
    | .inr p => ⟨p.val, fun h =>
        p.property ((congrArg Prod.fst h).trans (congrArg Prod.snd h).symm)⟩
  invFun p := if h : p.val.1 = p.val.2 then
      .inl ⟨p.val.1.val, by
        have hn : p.val.1 ≠ Fin.last r := fun hk =>
          p.property (Prod.ext hk (h.symm.trans hk))
        exact Fin.lt_last_iff_ne_last.mpr hn⟩
    else .inr ⟨p.val, h⟩
  left_inv p := by
    cases p with
    | inl i => simp
    | inr p => simp [p.property]
  right_inv p := by
    dsimp only
    by_cases h : p.val.1 = p.val.2
    · simp only [dite_eq_left h]
      apply Subtype.ext
      exact Prod.ext rfl h
    · simp only [dite_eq_right h]

private def rootSignEquiv :
    ({p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2} → A) ≃ₗ[A]
      ({p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2} → A) :=
  LinearEquiv.ofInvolutive
    (LinearMap.mulLeft A fun p => specialLinearRootSign r A p.val.1 p.val.2)
    (fun d => by
      funext p
      simp only [LinearMap.mulLeft_apply, Pi.mul_apply, ← mul_assoc,
        specialLinearRootSign_mul_self, one_mul])

/-- Coordinates on trace-zero matrices adapted to adjacent coroots and signed interval roots. -/
noncomputable def specialLinearRootEquiv :
    sl (Fin (r + 1)) A ≃ₗ[A]
      (Fin r ⊕ {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2} → A) :=
  let split := LinearEquiv.sumArrowLequivProdArrow
    (Fin r) {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2} A A
  (specialLinearEntryEquiv (R := A) (Fin.last r)).trans
    ((LinearEquiv.piCongrLeft' A (fun _ => A) (rootEntryIndexEquiv r).symm).trans
      (split.trans (((partialSumsLinearEquiv A r).prodCongr
        (rootSignEquiv r A)).trans split.symm)))

/-- Coroot coordinates are the nonempty initial sums of diagonal entries. -/
@[simp]
theorem specialLinearRootEquiv_inl (X : sl (Fin (r + 1)) A) (i : Fin r) :
    specialLinearRootEquiv r A X (.inl i) =
      Fin.partialSum (fun j : Fin r => X.val j.castSucc j.castSucc) i.succ := by
  -- Evaluate the sum/product reindexing and project onto the partial-sum factor.
  change partialSumsLinearEquiv A r (fun j : Fin r =>
    specialLinearEntryEquiv (R := A) (Fin.last r) X
      ((rootEntryIndexEquiv r) (.inl j))) i = _
  rw [partialSumsLinearEquiv_apply]
  simp_rw [specialLinearEntryEquiv_apply]
  rfl

/-- A root coordinate is the corresponding signed matrix entry. -/
@[simp]
theorem specialLinearRootEquiv_inr (X : sl (Fin (r + 1)) A)
    (p : {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2}) :
    specialLinearRootEquiv r A X (.inr p) =
      specialLinearRootSign r A p.val.1 p.val.2 * X.val p.val.1 p.val.2 := by
  -- Evaluate the sum/product reindexing and project onto the sign-multiplication factor.
  change specialLinearRootSign r A p.val.1 p.val.2 *
    specialLinearEntryEquiv (R := A) (Fin.last r) X
      ((rootEntryIndexEquiv r) (.inr p)) = _
  rw [specialLinearEntryEquiv_apply]
  rfl

/-- On diagonal matrices, `specialLinearRootEquiv` agrees with `specialLinearCorootEquiv`. -/
theorem specialLinearRootEquiv_diagonal_inl (X : specialLinearDiagonal r A) (i : Fin r) :
    specialLinearRootEquiv r A X.val (.inl i) = specialLinearCorootEquiv r A X i := by
  rw [specialLinearRootEquiv_inl, specialLinearCorootEquiv_apply]

/-- Diagonal matrices have zero root coordinates. -/
@[simp high]
theorem specialLinearRootEquiv_diagonal_inr (X : specialLinearDiagonal r A)
    (p : {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2}) :
    specialLinearRootEquiv r A X.val (.inr p) = 0 := by
  rw [specialLinearRootEquiv_inr,
    (mem_specialLinearDiagonal_iff r A X.val).mp X.property p.property, mul_zero]

/-- Adjacent coroots and signed interval roots form a basis over every commutative ring. -/
noncomputable def specialLinearRootBasis :
    Module.Basis (Fin r ⊕ {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2}) A
      (sl (Fin (r + 1)) A) :=
  Module.Basis.ofEquivFun (specialLinearRootEquiv r A)

/-- The signed root basis has the coordinates given by the full coordinate equivalence. -/
@[simp]
theorem specialLinearRootBasis_repr (X : sl (Fin (r + 1)) A)
    (p : Fin r ⊕ {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2}) :
    (specialLinearRootBasis r A).repr X p = specialLinearRootEquiv r A X p := by
  exact Module.Basis.ofEquivFun_repr_apply _ _ _

private theorem rootEquiv_basis
    (p : Fin r ⊕ {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2}) :
    specialLinearRootEquiv r A (specialLinearRootBasis r A p) = Pi.single p 1 := by
  ext q
  rw [← specialLinearRootBasis_repr, Module.Basis.repr_self]
  simp only [Finsupp.single_apply, Pi.single_apply, eq_comm]

/-- The first summand of `specialLinearRootBasis` is `specialLinearCorootBasis`. -/
@[simp]
theorem specialLinearRootBasis_inl (i : Fin r) :
    specialLinearRootBasis r A (.inl i) = (specialLinearCorootBasis r A i).val := by
  apply (specialLinearRootEquiv r A).injective
  rw [rootEquiv_basis]
  ext q
  cases q with
  | inl j =>
    rw [specialLinearRootEquiv_diagonal_inl, specialLinearCorootEquiv_apply,
      ← specialLinearCorootBasis_repr, Module.Basis.repr_self]
    simp [Pi.single_apply, Finsupp.single_apply, eq_comm]
  | inr p =>
    rw [specialLinearRootEquiv_diagonal_inr]
    simp

private theorem rootEquiv_signedRoot
    (p : {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2}) :
    specialLinearRootEquiv r A
        (specialLinearSignedRoot r A p.val.1 p.val.2 p.property) =
      Pi.single (.inr p) 1 := by
  ext q
  cases q with
  | inl i =>
    rw [specialLinearRootEquiv_inl]
    have hd : (fun j : Fin r =>
        (specialLinearSignedRoot r A p.val.1 p.val.2 p.property).val
          j.castSucc j.castSucc) = 0 := by
      funext j
      rw [specialLinearSignedRoot_val]
      exact congrFun (Matrix.diag_single_of_ne _ _ _ p.property) j.castSucc
    rw [hd, ← partialSumsLinearEquiv_apply, map_zero]
    simp
  | inr q =>
    rw [specialLinearRootEquiv_inr, specialLinearSignedRoot_val, Matrix.single_apply]
    by_cases h : p = q
    · subst q
      simp
    · have hp : ¬(p.val.1 = q.val.1 ∧ p.val.2 = q.val.2) := by
        intro hp
        exact h (Subtype.ext (Prod.ext hp.1 hp.2))
      simp [hp, Ne.symm h]

/-- The second summand of the full basis consists of the signed off-diagonal units. -/
@[simp]
theorem specialLinearRootBasis_inr
    (p : {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2}) :
    specialLinearRootBasis r A (.inr p) =
      specialLinearSignedRoot r A p.val.1 p.val.2 p.property := by
  apply (specialLinearRootEquiv r A).injective
  rw [rootEquiv_basis, rootEquiv_signedRoot]

end TauCeti
