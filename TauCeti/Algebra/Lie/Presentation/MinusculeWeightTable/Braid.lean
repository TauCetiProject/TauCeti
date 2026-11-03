/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Presentation.MinusculeWeightTable.Basic

/-!
# Braid relations for minuscule Weyl matrices

The pinned word `(1 + Eᵢ) (1 - Fᵢ) (1 + Eᵢ)` acts by a signed simple reflection
on any minuscule weight table. These matrices commute at orthogonal nodes and satisfy the
length-three braid relation when both Cartan entries are `-1`. All signs are proved
integrally and retained over every commutative coefficient ring.

## Main declarations

* `TauCeti.MinusculeWeightTable.simpleWeylMatrix`
* `TauCeti.MinusculeWeightTable.simpleWeylMatrix_mulVec_single`
* `TauCeti.MinusculeWeightTable.commute_simpleWeylMatrix_of_cartanMatrix_eq_zero`
* `TauCeti.MinusculeWeightTable.simpleWeylMatrix_braid_of_cartanMatrix_eq_neg_one`

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §6.
* R. W. Carter, *Simple Groups of Lie Type*, §6.4.
-/

public section

open scoped Matrix

namespace TauCeti.MinusculeWeightTable

variable {B ι : Type*} [Fintype ι] [DecidableEq ι] (T : MinusculeWeightTable B ι)

/-- The matrix of the pinned simple Weyl word over a commutative ring. -/
def simpleWeylMatrix (i : B) (R : Type*) [CommRing R] : Matrix ι ι R :=
  (1 + (T.raisingMatrix i).map (Int.cast : ℤ → R)) *
    (1 - (T.loweringMatrix i).map (Int.cast : ℤ → R)) *
    (1 + (T.raisingMatrix i).map (Int.cast : ℤ → R))

/-- The simple Weyl matrix is the specified pinned product of root matrices. -/
theorem simpleWeylMatrix_def (i : B) (R : Type*) [CommRing R] :
    T.simpleWeylMatrix i R =
      (1 + (T.raisingMatrix i).map (Int.cast : ℤ → R)) *
        (1 - (T.loweringMatrix i).map (Int.cast : ℤ → R)) *
        (1 + (T.raisingMatrix i).map (Int.cast : ℤ → R)) := by
  rw [simpleWeylMatrix]

/-- Simple Weyl matrices commute with change of coefficient ring. -/
@[simp]
theorem map_simpleWeylMatrix {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (i : B) :
    (T.simpleWeylMatrix i R).map f = T.simpleWeylMatrix i S := by
  rw [← RingHom.mapMatrix_apply]
  have hcast (M : Matrix ι ι ℤ) :
      f.mapMatrix (M.map (Int.cast : ℤ → R)) = M.map (Int.cast : ℤ → S) := by
    ext a b
    simp
  simp only [simpleWeylMatrix, map_mul, map_add, map_sub, map_one, hcast]

/-- The pinned Weyl matrix sends a weight vector to its reflection, negating it exactly
when its simple-coroot coordinate is `1`. -/
theorem simpleWeylMatrix_mulVec_single (i : B) (R : Type*) [CommRing R] (a : ι) :
    (T.simpleWeylMatrix i R).mulVec (Pi.single a 1) =
      (if T.weight a i = 1 then (-1 : R) else 1) • Pi.single (T.reflection i a) 1 := by
  have hreflect := T.weight_reflection_self i a
  simp only [simpleWeylMatrix, ← Matrix.mulVec_mulVec, Matrix.add_mulVec,
    Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_add, Matrix.mulVec_sub]
  have hsign : (-1 : ℤ) ≠ 1 := by decide
  have hzero : (0 : ℤ) ≠ -1 := by decide
  rcases T.weight_eq_neg_one_or_eq_zero_or_eq_one a i with h | h | h
  all_goals
    simp only [Matrix.mulVec_single_one, T.raisingMatrix_map_col,
      T.loweringMatrix_map_col, hreflect, h, neg_neg, T.reflection_apply_apply,
      hsign, Ne.symm hsign, hzero, zero_ne_one, ite_true, ite_false,
      Matrix.mulVec_zero, add_zero, sub_zero, sub_self, one_smul, neg_one_smul]
  · abel
  · exact congrArg (fun b => Pi.single b 1) ((T.reflection_eq_self_iff i a).mpr h).symm
  · abel

private def simpleWeylSign (i : B) (a : ι) : ℤ :=
  if T.weight a i = 1 then -1 else 1

omit [Fintype ι] [DecidableEq ι] in
private theorem commuting_certificate (i j : B) (a : ι)
    (h : T.cartanMatrix i j = 0) :
    (T.reflection i (T.reflection j a),
        T.simpleWeylSign j a * T.simpleWeylSign i (T.reflection j a)) =
      (T.reflection j (T.reflection i a),
        T.simpleWeylSign i a * T.simpleWeylSign j (T.reflection i a)) := by
  have hc := T.reflection_comm_of_cartanMatrix_eq_zero i j a h
  have hi := T.weight_reflection_of_cartanMatrix_eq_zero j i a
    ((T.cartanMatrix_zero_comm i j).mp h)
  have hj := T.weight_reflection_of_cartanMatrix_eq_zero i j a h
  simp only [hc, simpleWeylSign, hi, hj, mul_comm]

omit [Fintype ι] [DecidableEq ι] in
private theorem braid_certificate (i j : B) (a : ι)
    (h : T.cartanMatrix i j = -1) (hji : T.cartanMatrix j i = -1) :
    (T.reflection i (T.reflection j (T.reflection i a)),
        T.simpleWeylSign i a * T.simpleWeylSign j (T.reflection i a) *
          T.simpleWeylSign i (T.reflection j (T.reflection i a))) =
      (T.reflection j (T.reflection i (T.reflection j a)),
        T.simpleWeylSign j a * T.simpleWeylSign i (T.reflection j a) *
          T.simpleWeylSign j (T.reflection i (T.reflection j a))) := by
  have hc : T.reflection i (T.reflection j (T.reflection i a)) =
      T.reflection j (T.reflection i (T.reflection j a)) := by
    apply T.weight_injective
    funext k
    simp only [T.weight_reflection, T.cartanMatrix_diag, h, hji]
    ring
  -- Along either three-step braid, the final sign reads the other initial coordinate.
  have doubleCoord (i j : B) (hij : T.cartanMatrix i j = -1)
      (hji : T.cartanMatrix j i = -1) :
      T.weight (T.reflection j (T.reflection i a)) i = T.weight a j := by
    simp only [T.weight_reflection, T.cartanMatrix_diag, hij, hji]
    ring
  apply Prod.ext hc
  simp only [simpleWeylSign, doubleCoord i j h hji, doubleCoord j i hji h,
    T.weight_reflection, h, hji, neg_one_mul, sub_neg_eq_add, add_comm,
    mul_comm, mul_left_comm]

private theorem simpleWeylMatrix_commute_int (i j : B) (h : T.cartanMatrix i j = 0) :
    Commute (T.simpleWeylMatrix i ℤ) (T.simpleWeylMatrix j ℤ) := by
  rw [commute_iff_eq]
  apply Matrix.ext_of_mulVec_single
  intro b
  have hc := T.commuting_certificate i j b h
  simp only [simpleWeylSign] at hc
  simp only [← Matrix.mulVec_mulVec, T.simpleWeylMatrix_mulVec_single,
    Matrix.mulVec_smul, smul_smul]
  rw [(Prod.mk.inj hc).1, (Prod.mk.inj hc).2]

private theorem simpleWeylMatrix_braid_int (i j : B)
    (h : T.cartanMatrix i j = -1) (hji : T.cartanMatrix j i = -1) :
    T.simpleWeylMatrix i ℤ * T.simpleWeylMatrix j ℤ * T.simpleWeylMatrix i ℤ =
      T.simpleWeylMatrix j ℤ * T.simpleWeylMatrix i ℤ * T.simpleWeylMatrix j ℤ := by
  apply Matrix.ext_of_mulVec_single
  intro b
  have hc := T.braid_certificate i j b h hji
  simp only [simpleWeylSign] at hc
  simp only [← Matrix.mulVec_mulVec, T.simpleWeylMatrix_mulVec_single,
    Matrix.mulVec_smul, smul_smul, ← mul_assoc]
  rw [(Prod.mk.inj hc).1, (Prod.mk.inj hc).2]

/-- Pinned Weyl matrices at orthogonal nodes commute over every commutative ring. -/
theorem commute_simpleWeylMatrix_of_cartanMatrix_eq_zero (R : Type*) [CommRing R]
    (i j : B) (h : T.cartanMatrix i j = 0) :
    Commute (T.simpleWeylMatrix i R) (T.simpleWeylMatrix j R) := by
  simpa only [RingHom.mapMatrix_apply, T.map_simpleWeylMatrix] using
    (T.simpleWeylMatrix_commute_int i j h).map (Int.castRingHom R).mapMatrix

/-- Pinned Weyl matrices at nodes with both Cartan entries `-1` satisfy the length-three
braid relation, with integral signs retained over every commutative ring. -/
theorem simpleWeylMatrix_braid_of_cartanMatrix_eq_neg_one (R : Type*) [CommRing R]
    (i j : B) (h : T.cartanMatrix i j = -1) (hji : T.cartanMatrix j i = -1) :
    T.simpleWeylMatrix i R * T.simpleWeylMatrix j R * T.simpleWeylMatrix i R =
      T.simpleWeylMatrix j R * T.simpleWeylMatrix i R * T.simpleWeylMatrix j R := by
  simpa only [map_mul, RingHom.mapMatrix_apply, T.map_simpleWeylMatrix] using
    congrArg (Int.castRingHom R).mapMatrix (T.simpleWeylMatrix_braid_int i j h hji)

end TauCeti.MinusculeWeightTable
