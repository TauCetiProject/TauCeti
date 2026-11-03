/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.IntegralMatrix

/-!
# Opposite-root Gauss factorization in the doubled E₆ carrier

The numbered positive and negative simple-root points of `V(ϖ₁) ⊕ V(ϖ₆)` satisfy the
rank-one Gauss relation. In simple-coroot coordinates, dual to the fundamental weights,
the simple coroot `αᵢ∨(u)` is `Pi.mulSingle i u`. Both multiplication orders are covered over
every commutative value ring, assuming only that the pivot `1 + a * b` is a unit. Neither
parameter need be invertible, and value rings may be nonreduced.

The carrier is not identified here with the independently pinned simply connected group
scheme of type E₆; transfer of these identities to that group requires such an identification.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, the rank-one relations.
* R. W. Carter, *Simple Groups of Lie Type*, §6.1.
* The root matrices and their signed columns are those of
  `TauCeti.Algebra.Lie.E6.DoubledMinuscule.IntegralMatrix`.
-/

public section

open scoped Matrix

namespace TauCeti.E6DoubledMinuscule

universe v

variable {A : Type v} [CommRing A]

-- On a reflection pair, these are the two columns of the signed SL₂ block.
private theorem inl_mul_inr_mulVec_block (i : Fin 6) (k : Fin 54)
    (hk : matrixWeight k i = -1) (a b x y : A) :
    let r := matrixIndexEquiv (reflection i (matrixIndexEquiv.symm k))
    let s : A := summandSign (matrixIndexEquiv.symm k)
    (((rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd a) :
        Matrix.GeneralLinearGroup (Fin 54) A) : Matrix (Fin 54) (Fin 54) A) *
      ((rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd b) :
        Matrix.GeneralLinearGroup (Fin 54) A) : Matrix (Fin 54) (Fin 54) A)) *ᵥ
        (Pi.single k x + Pi.single r y) =
      Pi.single k (x + b * s * y) + Pi.single r (a * s * x + (1 + a * b) * y) := by
  dsimp only
  set r := matrixIndexEquiv (reflection i (matrixIndexEquiv.symm k)) with hrdef
  set s := (summandSign (matrixIndexEquiv.symm k) : A) with hsdef
  have hr : matrixWeight r i = 1 := by
    simpa [hrdef, matrixWeight_apply] using congrArg Neg.neg hk
  have hs : s ^ 2 = 1 := summandSign_cast_sq _
  have hrback : matrixIndexEquiv (reflection i (matrixIndexEquiv.symm r)) = k := by
    simp [hrdef]
  have hsr : (summandSign (matrixIndexEquiv.symm r) : A) = s := by
    simp [hrdef, hsdef]
  simp only [← Matrix.mulVec_mulVec, Matrix.mulVec_add, rootSubgroupPoints_mulVec_single,
    Sum.elim_inl, Sum.elim_inr, id_eq, hk, hr, hrback, hsr, ← hrdef, ← hsdef,
    Int.reduceEq, ↓reduceIte, add_zero]
  ext l
  simp only [Pi.add_apply, Pi.single_apply]
  split_ifs <;> first | ring1 | linear_combination a * b * y * hs

private theorem inr_torus_inl_mulVec_block (i : Fin 6) (k : Fin 54)
    (hk : matrixWeight k i = -1) (c d x y : A) (u : Aˣ) :
    let r := matrixIndexEquiv (reflection i (matrixIndexEquiv.symm k))
    let s : A := summandSign (matrixIndexEquiv.symm k)
    (((rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd c) :
        Matrix.GeneralLinearGroup (Fin 54) A) : Matrix (Fin 54) (Fin 54) A) *
      ((weightTorusPoints A (Pi.mulSingle i u) : Matrix.GeneralLinearGroup (Fin 54) A) :
        Matrix (Fin 54) (Fin 54) A) *
      ((rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd d) :
        Matrix.GeneralLinearGroup (Fin 54) A) : Matrix (Fin 54) (Fin 54) A)) *ᵥ
        (Pi.single k x + Pi.single r y) =
      Pi.single k (↑u⁻¹ * x + c * s * (↑u * (y + d * s * x))) +
        Pi.single r (↑u * (y + d * s * x)) := by
  dsimp only
  set r := matrixIndexEquiv (reflection i (matrixIndexEquiv.symm k)) with hrdef
  set s := (summandSign (matrixIndexEquiv.symm k) : A) with hsdef
  have hr : matrixWeight r i = 1 := by
    simpa [hrdef, matrixWeight_apply] using congrArg Neg.neg hk
  have hrback : matrixIndexEquiv (reflection i (matrixIndexEquiv.symm r)) = k := by
    simp [hrdef]
  have hsr : (summandSign (matrixIndexEquiv.symm r) : A) = s := by
    simp [hrdef, hsdef]
  simp only [← Matrix.mulVec_mulVec, Matrix.mulVec_add, rootSubgroupPoints_mulVec_single,
    weightTorusPoints_mulVec_single, torusCharacter_mulSingle,
    Sum.elim_inl, Sum.elim_inr, id_eq, hk, hr,
    hrback, hsr, ← hrdef, ← hsdef, Int.reduceEq, ↓reduceIte, add_zero,
    zpow_neg_one, zpow_one]
  ext l
  simp only [Pi.add_apply, Pi.single_apply]
  split_ifs <;> ring

private theorem gauss_mulVec_block (i : Fin 6) (k : Fin 54)
    (hk : matrixWeight k i = -1) (a b x y : A) (u : Aˣ)
    (hu : (u : A) = 1 + a * b) :
    let r := matrixIndexEquiv (reflection i (matrixIndexEquiv.symm k))
    (((rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd a) :
        Matrix.GeneralLinearGroup (Fin 54) A) : Matrix (Fin 54) (Fin 54) A) *
      ((rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd b) :
        Matrix.GeneralLinearGroup (Fin 54) A) : Matrix (Fin 54) (Fin 54) A)) *ᵥ
        (Pi.single k x + Pi.single r y) =
    (((rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (b * ↑u⁻¹)) :
        Matrix.GeneralLinearGroup (Fin 54) A) : Matrix (Fin 54) (Fin 54) A) *
      ((weightTorusPoints A (Pi.mulSingle i u) : Matrix.GeneralLinearGroup (Fin 54) A) :
        Matrix (Fin 54) (Fin 54) A) *
      ((rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd (a * ↑u⁻¹)) :
        Matrix.GeneralLinearGroup (Fin 54) A) : Matrix (Fin 54) (Fin 54) A)) *ᵥ
        (Pi.single k x + Pi.single r y) := by
  dsimp only
  rw [inl_mul_inr_mulVec_block i k hk, inr_torus_inl_mulVec_block i k hk]
  set s := (summandSign (matrixIndexEquiv.symm k) : A)
  have hs : s ^ 2 = 1 := summandSign_cast_sq _
  have htop : (u : A) * (y + a * ↑u⁻¹ * s * x) = a * s * x + (1 + a * b) * y := by
    calc
      _ = a * s * x * (↑u * ↑u⁻¹) + ↑u * y := by ring
      _ = _ := by rw [Units.mul_inv, mul_one, hu]
  rw [htop]
  congr 2
  symm
  calc
    _ = (↑u⁻¹ * (1 + a * b)) * x + (↑u⁻¹ * (1 + a * b)) * b * s * y := by
      linear_combination ↑u⁻¹ * a * b * x * hs
    _ = _ := by rw [← hu, Units.inv_mul]; ring

/-- The positive-negative simple-root product admits Gauss factorization with pivot
`u = 1 + a * b` and simple-coroot factor `αᵢ∨(u)`. -/
theorem rootSubgroupPoints_inl_mul_inr (i : Fin 6) (a b : A) (u : Aˣ)
    (hu : (u : A) = 1 + a * b) :
    rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd a) *
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd b) =
      rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (b * ↑u⁻¹)) *
        weightTorusPoints A (Pi.mulSingle i u) *
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd (a * ↑u⁻¹)) := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
  apply Matrix.ext_of_mulVec_single
  intro k
  -- Nonzero weights lie in the same signed SL₂ block; weight zero is fixed.
  rcases DynkinType.e6DoubledMinusculeWeight_apply_eq_neg_one_or_eq_zero_or_eq_one
    (matrixIndexEquiv.symm k) i with hk | hk | hk
  all_goals rw [← matrixWeight_apply] at hk
  · simpa only [Pi.single_zero, add_zero] using gauss_mulVec_block i k hk a b 1 0 u hu
  · simp only [← Matrix.mulVec_mulVec, rootSubgroupPoints_mulVec_single,
      weightTorusPoints_mulVec_single, torusCharacter_mulSingle,
      Sum.elim_inl, Sum.elim_inr, id_eq, hk,
      Int.reduceEq, ↓reduceIte,
      add_zero, zpow_zero, Units.val_one, one_mul]
  · set r := matrixIndexEquiv (reflection i (matrixIndexEquiv.symm k)) with hrdef
    have hr : matrixWeight r i = -1 := by
      simpa [hrdef, matrixWeight_apply] using congrArg Neg.neg hk
    have hrback : matrixIndexEquiv (reflection i (matrixIndexEquiv.symm r)) = k := by
      simp [hrdef]
    simpa only [hrback, Pi.single_zero, zero_add] using
      gauss_mulVec_block i r hr a b 0 1 u hu

/-- The negative-positive simple-root product has the reverse Gauss factorization, with
simple-coroot factor `αᵢ∨(u⁻¹)` for the same pivot `u = 1 + a * b`. -/
theorem rootSubgroupPoints_inr_mul_inl (i : Fin 6) (a b : A) (u : Aˣ)
    (hu : (u : A) = 1 + a * b) :
    rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd a) *
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd b) =
      rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd (b * ↑u⁻¹)) *
        weightTorusPoints A (Pi.mulSingle i u⁻¹) *
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (a * ↑u⁻¹)) := by
  have hpivot : (u : A) = 1 + (-b) * (-a) := by
    rw [neg_mul_neg, mul_comm b a]
    exact hu
  have h := congrArg Inv.inv (rootSubgroupPoints_inl_mul_inr i (-b) (-a) u hpivot)
  simpa [mul_inv_rev, ← map_inv, ← ofAdd_neg, neg_mul, ← Pi.mulSingle_inv, mul_assoc] using h

end TauCeti.E6DoubledMinuscule
