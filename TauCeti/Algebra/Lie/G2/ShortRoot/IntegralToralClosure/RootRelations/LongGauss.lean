/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.Basic

/-!
# Opposite long-root factorization in the seven-dimensional G₂ carrier

The positive and negative long simple-root subgroups act on two two-dimensional weight
strings. Their Gauss relation has the usual simple-coroot factor: if `z = 1 + a * b` is a
unit, then

`x₂(a) x₋₂(b) = x₋₂(b / z) h₂(z) x₂(a / z)`.

Here division means multiplication by the inverse of the specified unit, not inversion in a
field. The relation and uniqueness of its three parameters hold over every commutative ring,
including nonreduced rings. The coroot is the second coordinate cocharacter of the weight
torus, since the weights use fundamental-weight coordinates. These equations describe the
explicit integral toral closure, not an identification with an independently pinned group.

The calculation uses the existing root matrices and diagonal weight-torus formula from
`TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.Basic`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §6 (rank-one relations).
* R. W. Carter, *Simple Groups of Lie Type*, §6.1.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IX.
-/

public section

namespace TauCeti.G2ShortRoot.IntegralToralClosure

universe v

variable (A : Type v) [CommRing A]

/-- **The long-simple-root Gauss relation.** Only `1 + a * b` must be a unit; neither root
parameter is required to be invertible. The torus parameter is the numbered simple coroot. -/
theorem rootSubgroupPoints_inl_one_mul_inr_one (a b : A) (z : Aˣ)
    (hz : (z : A) = 1 + a * b) :
    rootSubgroupPoints (.inl 1) A (Multiplicative.ofAdd a) *
        rootSubgroupPoints (.inr 1) A (Multiplicative.ofAdd b) =
      rootSubgroupPoints (.inr 1) A (Multiplicative.ofAdd (b * (↑z⁻¹ : A))) *
        weightTorusPoints A (Pi.mulSingle 1 z) *
        rootSubgroupPoints (.inl 1) A (Multiplicative.ofAdd (a * (↑z⁻¹ : A))) := by
  have hcancel : (z : A) * (↑z⁻¹ : A) = 1 := Units.mul_inv z
  have ha : (z : A) * (a * (↑z⁻¹ : A)) = a := by
    calc _ = a * ((z : A) * (↑z⁻¹ : A)) := by ring
         _ = a := by rw [hcancel, mul_one]
  have hb : b * (↑z⁻¹ : A) * (z : A) = b := by
    calc _ = b * ((z : A) * (↑z⁻¹ : A)) := by ring
         _ = b := by rw [hcancel, mul_one]
  have hab : b * (a * (↑z⁻¹ : A)) + (↑z⁻¹ : A) = 1 := by
    calc _ = (1 + a * b) * (↑z⁻¹ : A) := by ring
         _ = 1 := by rw [← hz, hcancel]
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul,
    coe_rootSubgroupPoints_inl_one, coe_rootSubgroupPoints_inr_one,
    coe_weightTorusPoints_eq_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul_diagonal, Fin.sum_univ_succ,
      torusCharacter_mulSingle, weight, ha, hb, hab, ← hz]

/-- **Uniqueness of the long-root Gauss parameters.** A lower-root, coroot, upper-root product
is equal to `x₂(a) x₋₂(b)` precisely for the usual three parameters. -/
@[simp↓]
theorem rootSubgroupPoints_inl_one_mul_inr_one_eq_iff (a b c d : A) (z : Aˣ) :
    rootSubgroupPoints (.inl 1) A (Multiplicative.ofAdd a) *
        rootSubgroupPoints (.inr 1) A (Multiplicative.ofAdd b) =
      rootSubgroupPoints (.inr 1) A (Multiplicative.ofAdd c) *
        weightTorusPoints A (Pi.mulSingle 1 z) *
        rootSubgroupPoints (.inl 1) A (Multiplicative.ofAdd d) ↔
      (z : A) = 1 + a * b ∧ c = b * (↑z⁻¹ : A) ∧ d = a * (↑z⁻¹ : A) := by
  constructor
  · intro h
    have hm := congrArg (fun g : points A =>
      ((g : Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A)) h
    simp only [Subgroup.coe_mul, Units.val_mul,
      coe_rootSubgroupPoints_inl_one, coe_rootSubgroupPoints_inr_one,
      coe_weightTorusPoints_eq_diagonal] at hm
    have h11 : 1 + a * b = (z : A) := by
      simpa [Matrix.mul_apply, Matrix.vecMul_diagonal, Fin.sum_univ_succ,
        torusCharacter_mulSingle, weight] using congrArg (fun m => m 1 1) hm
    have h21 : b = c * (z : A) := by
      simpa [Matrix.mul_apply, Matrix.vecMul_diagonal, Fin.sum_univ_succ,
        torusCharacter_mulSingle, weight] using congrArg (fun m => m 2 1) hm
    have h12 : a = (z : A) * d := by
      simpa [Matrix.mul_apply, Matrix.vecMul_diagonal, Fin.sum_univ_succ,
        torusCharacter_mulSingle, weight] using congrArg (fun m => m 1 2) hm
    refine ⟨h11.symm, ?_, ?_⟩
    · calc c = (c * (z : A)) * (↑z⁻¹ : A) := by simp [mul_assoc]
           _ = b * (↑z⁻¹ : A) := by rw [← h21]
    · calc d = ((z : A) * d) * (↑z⁻¹ : A) := by
                  rw [mul_comm (z : A) d, mul_assoc, Units.mul_inv, mul_one]
           _ = a * (↑z⁻¹ : A) := by rw [← h12]
  · rintro ⟨hz, rfl, rfl⟩
    exact rootSubgroupPoints_inl_one_mul_inr_one A a b z hz

/-- The opposite multiplication order has the inverse simple-coroot factor. As in the forward
relation, the only invertibility hypothesis is on `1 + a * b`. -/
theorem rootSubgroupPoints_inr_one_mul_inl_one (a b : A) (z : Aˣ)
    (hz : (z : A) = 1 + a * b) :
    rootSubgroupPoints (.inr 1) A (Multiplicative.ofAdd a) *
        rootSubgroupPoints (.inl 1) A (Multiplicative.ofAdd b) =
      rootSubgroupPoints (.inl 1) A (Multiplicative.ofAdd (b * (↑z⁻¹ : A))) *
        weightTorusPoints A (Pi.mulSingle 1 z⁻¹) *
        rootSubgroupPoints (.inr 1) A (Multiplicative.ofAdd (a * (↑z⁻¹ : A))) := by
  have h := rootSubgroupPoints_inl_one_mul_inr_one A (-b) (-a) z
    (by simpa [mul_comm] using hz)
  have hi := congrArg (fun g : points A => g⁻¹) h
  simpa only [mul_inv_rev, ← map_inv, ← ofAdd_neg, neg_mul, neg_neg,
    ← Pi.mulSingle_inv, mul_assoc] using hi

end TauCeti.G2ShortRoot.IntegralToralClosure
