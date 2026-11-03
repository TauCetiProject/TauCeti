/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.Minuscule.GroupScheme

/-!
# Braid relations on the E₆ minuscule carrier

The pinned root words `xᵢ(1) x₋ᵢ(-1) xᵢ(1)` on the twenty-seven-dimensional minuscule
carrier satisfy the E₆ braid relations over every commutative ring. Nonadjacent words commute;
adjacent words satisfy the three-factor relation, with their integral signs retained.
These are equalities in the explicit carrier, not just in its Weyl group. They supply the
braid moves needed when transporting root subgroups by such words. No identification with
an independently pinned group scheme or independence of arbitrary root presentations is asserted.

The calculation uses the minuscule weight basis: a root word acts by the simple reflection,
with a minus sign precisely on weights pairing to one with the simple coroot.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §§3 and 6.
* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 7.2.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate V.

The integral generators and weight enumeration are those of
`TauCeti.Algebra.Lie.E6.Minuscule.Basic`.
-/

public section

open Matrix

namespace TauCeti.E6Minuscule

open DynkinType

private theorem rootMatrix_mulVec (i : Fin 6) (c : ℤ)
    (M : Matrix (Fin 27) (Fin 27) ℤ)
    (hM : ∀ a b, M a b =
      if e6MinusculeWeight b i = c ∧ a = e6MinusculeReflection i b then 1 else 0)
    (v : Fin 27 → ℤ) (a : Fin 27) :
    (M *ᵥ v) a =
      if -e6MinusculeWeight a i = c then v (e6MinusculeReflection i a) else 0 := by
  classical
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (e6MinusculeReflection i a)]
  · simp [hM, e6MinusculeWeight_reflection_apply_self]
  · intro b _ hb
    have hab : a ≠ e6MinusculeReflection i b := by
      intro h
      have := congrArg (e6MinusculeReflection i) h
      simp only [e6MinusculeReflection_apply_apply] at this
      exact hb this.symm
    simp [hM, hab]
  · simp

private def reflectionSign (i : Fin 6) (a : Fin 27) : ℤ :=
  if e6MinusculeWeight a i = -1 then -1 else 1

private def weylMatrix (i : Fin 6) : Matrix (Fin 27) (Fin 27) ℤ :=
  (1 + raisingMatrix i) * (1 - loweringMatrix i) * (1 + raisingMatrix i)

private theorem weylMatrix_mulVec (i : Fin 6) (v : Fin 27 → ℤ) (a : Fin 27) :
    (weylMatrix i *ᵥ v) a =
      reflectionSign i a * v (e6MinusculeReflection i a) := by
  simp only [reflectionSign, weylMatrix, ← Matrix.mulVec_mulVec,
    Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.add_apply, Pi.sub_apply,
    rootMatrix_mulVec i (-1) _ (raisingMatrix_apply i),
    rootMatrix_mulVec i 1 _ (loweringMatrix_apply i),
    e6MinusculeWeight_reflection_apply_self, e6MinusculeReflection_apply_apply]
  rcases e6MinusculeWeight_apply_eq_neg_one_or_eq_zero_or_eq_one a i with h | h | h
  · simp [h]
  · have hs : e6MinusculeReflection i a = a := (e6MinusculeReflection_eq_self_iff i a).mpr h
    simp [h, hs]
  · simp [h]

-- These certificates involve only permutations and signs, not dense matrix multiplication.
private theorem commute_certificate (i j : Fin 6) (h : CartanMatrix.E 6 i j = 0)
    (a : Fin 27) :
    e6MinusculeReflection j (e6MinusculeReflection i a) =
        e6MinusculeReflection i (e6MinusculeReflection j a) ∧
      reflectionSign i a * reflectionSign j (e6MinusculeReflection i a) =
        reflectionSign j a * reflectionSign i (e6MinusculeReflection j a) := by
  fin_cases i <;> fin_cases j <;> norm_num [CartanMatrix.E_six_eq] at h
  all_goals decide +kernel +revert

private theorem braid_certificate (i j : Fin 6) (h : CartanMatrix.E 6 i j = -1)
    (a : Fin 27) :
    e6MinusculeReflection i (e6MinusculeReflection j (e6MinusculeReflection i a)) =
        e6MinusculeReflection j (e6MinusculeReflection i (e6MinusculeReflection j a)) ∧
      reflectionSign i a * reflectionSign j (e6MinusculeReflection i a) *
          reflectionSign i (e6MinusculeReflection j (e6MinusculeReflection i a)) =
        reflectionSign j a * reflectionSign i (e6MinusculeReflection j a) *
          reflectionSign j (e6MinusculeReflection i (e6MinusculeReflection j a)) := by
  fin_cases i <;> fin_cases j <;> norm_num [CartanMatrix.E_six_eq] at h
  all_goals decide +kernel +revert

private theorem weylMatrix_commute (i j : Fin 6) (h : CartanMatrix.E 6 i j = 0) :
    weylMatrix i * weylMatrix j = weylMatrix j * weylMatrix i := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  funext a
  simp only [← Matrix.mulVec_mulVec, weylMatrix_mulVec, ← mul_assoc]
  rw [(commute_certificate i j h a).1, (commute_certificate i j h a).2]

private theorem weylMatrix_braid (i j : Fin 6) (h : CartanMatrix.E 6 i j = -1) :
    weylMatrix i * weylMatrix j * weylMatrix i =
      weylMatrix j * weylMatrix i * weylMatrix j := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  funext a
  simp only [← Matrix.mulVec_mulVec, weylMatrix_mulVec, ← mul_assoc]
  rw [(braid_certificate i j h a).1, (braid_certificate i j h a).2]

private theorem coe_root_word (i : Fin 6) (A : Type*) [CommRing A] :
    (((rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1) *
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-1)) *
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1) : points A) :
        Matrix.GeneralLinearGroup (Fin 27) A) : Matrix (Fin 27) (Fin 27) A) =
      (Int.castRingHom A).mapMatrix (weylMatrix i) := by
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [coe_rootSubgroupPoints_inl, coe_rootSubgroupPoints_inr]
  simp only [toAdd_ofAdd, one_smul, neg_smul,
    weightTable_raisingMatrix, weightTable_loweringMatrix]
  simp only [weylMatrix, map_mul, map_add, map_sub, map_one]
  simp only [RingHom.mapMatrix_apply, sub_eq_add_neg]
  -- The remaining scalar-map coercion is the underlying function of `Int.castRingHom A`.
  rfl

/-- Pinned simple Weyl words at nonadjacent E₆ nodes commute over every commutative ring. -/
theorem rootSubgroupPoints_weyl_commute_of_cartanMatrix_eq_zero (i j : Fin 6)
    (h : CartanMatrix.E 6 i j = 0) (A : Type*) [CommRing A] :
    let n := fun k : Fin 6 =>
      rootSubgroupPoints (.inl k) A (Multiplicative.ofAdd 1) *
        rootSubgroupPoints (.inr k) A (Multiplicative.ofAdd (-1)) *
        rootSubgroupPoints (.inl k) A (Multiplicative.ofAdd 1)
    Commute (n i) (n j) := by
  dsimp only
  apply Subtype.ext
  apply Units.ext
  have hword := coe_root_word
  simp only [Subgroup.coe_mul, Units.val_mul] at hword ⊢
  rw [hword, hword, ← map_mul, ← map_mul, weylMatrix_commute i j h]

/-- Pinned simple Weyl words at adjacent E₆ nodes satisfy the length-three braid relation,
including over rings with torsion or nilpotents. -/
theorem rootSubgroupPoints_weyl_braid_of_cartanMatrix_eq_neg_one (i j : Fin 6)
    (h : CartanMatrix.E 6 i j = -1) (A : Type*) [CommRing A] :
    let n := fun k : Fin 6 =>
      rootSubgroupPoints (.inl k) A (Multiplicative.ofAdd 1) *
        rootSubgroupPoints (.inr k) A (Multiplicative.ofAdd (-1)) *
        rootSubgroupPoints (.inl k) A (Multiplicative.ofAdd 1)
    n i * n j * n i = n j * n i * n j := by
  dsimp only
  apply Subtype.ext
  apply Units.ext
  have hword := coe_root_word
  simp only [Subgroup.coe_mul, Units.val_mul] at hword ⊢
  rw [hword, hword, ← map_mul, ← map_mul,
    ← map_mul, ← map_mul, weylMatrix_braid i j h]

end TauCeti.E6Minuscule
