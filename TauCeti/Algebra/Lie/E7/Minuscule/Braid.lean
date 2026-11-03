/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E7.Minuscule.Carrier

/-!
# Braid relations in the E₇ minuscule carrier

The pinned root words `nᵢ = xᵢ(1) x₋ᵢ(-1) xᵢ(1)` satisfy the commuting and three-factor
braid relations of the Bourbaki E₇ diagram. These are equalities in the explicit carrier,
not merely equalities modulo its weight torus. They supply coherence for transporting root
subgroups along simple-reflection words, over every commutative coefficient ring.

The integral minuscule matrices of `TauCeti.E7Minuscule.raisingMatrix` and
`TauCeti.E7Minuscule.loweringMatrix` make each root word a signed permutation of the
fifty-six weight vectors. The relations retain these signs, including before reduction in
characteristic two. No identification with an independently pinned group scheme is asserted.

## Main results

* `TauCeti.E7Minuscule.commute_rootWord_of_cartanMatrix_eq_zero`
* `TauCeti.E7Minuscule.rootWord_braid_of_cartanMatrix_eq_neg_one`

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §6, for the relations between pinned Weyl lifts.
* R. W. Carter, *Simple Groups of Lie Type*, §6.4.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VI, for the numbering.

The explicit weight and reflection data are those of
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E7.MinusculeWeight`.
-/

public section

open scoped Matrix

namespace TauCeti.E7Minuscule

open TauCeti.DynkinType

private def rootWordMatrix (i : Fin 7) : Matrix (Fin 56) (Fin 56) ℤ :=
  (1 + raisingMatrix i) * (1 - loweringMatrix i) * (1 + raisingMatrix i)

private def rootWordSign (i : Fin 7) (a : Fin 56) : ℤ :=
  if e7MinusculeWeight a i = 1 then -1 else 1

private theorem rootWordMatrix_mulVec_single (i : Fin 7) (a : Fin 56) :
    (rootWordMatrix i).mulVec (Pi.single a 1) =
      rootWordSign i a • Pi.single (e7MinusculeReflection i a) 1 := by
  have hreflect : e7MinusculeWeight (e7MinusculeReflection i a) i =
      -e7MinusculeWeight a i := by
    simpa only [weightTable_weight, weightTable_reflection] using
      weightTable.weight_reflection_self i a
  have hfix : e7MinusculeWeight a i = 0 → e7MinusculeReflection i a = a := by
    intro h
    simpa only [weightTable_reflection] using
      (weightTable.reflection_eq_self_iff i a).mpr (by simpa only [weightTable_weight] using h)
  -- The existing column formulas are stated after coefficient change; here that change is
  -- the identity on the integral raising and lowering matrices.
  have hE : raisingMatrix i = (weightTable.raisingMatrix i).map (Int.cast : ℤ → ℤ) := by
    ext r c
    simp
  have hF : loweringMatrix i = (weightTable.loweringMatrix i).map (Int.cast : ℤ → ℤ) := by
    ext r c
    simp
  simp only [rootWordMatrix, hE, hF, ← Matrix.mulVec_mulVec, Matrix.add_mulVec,
    Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_add, Matrix.mulVec_sub]
  have hsign : (-1 : ℤ) ≠ 1 := by decide
  have hzero : (0 : ℤ) ≠ -1 := by decide
  rcases e7MinusculeWeight_apply_eq_neg_one_or_eq_zero_or_eq_one a i with h | h | h
  all_goals
    simp only [Matrix.mulVec_single_one, weightTable.raisingMatrix_map_col,
      weightTable.loweringMatrix_map_col, weightTable_weight, weightTable_reflection,
      rootWordSign, hreflect, h, neg_neg, e7MinusculeReflection_apply_apply,
      hsign, Ne.symm hsign, hzero, zero_ne_one, ite_true, ite_false,
      Matrix.mulVec_zero, add_zero, sub_zero, sub_self, one_smul, neg_one_smul]
  · abel
  · exact congrArg (fun b => Pi.single b 1) (hfix h).symm
  · abel

private theorem commuting_certificate (i j : Fin 7) (a : Fin 56)
    (h : CartanMatrix.E 7 i j = 0) :
    (e7MinusculeReflection i (e7MinusculeReflection j a),
        rootWordSign j a * rootWordSign i (e7MinusculeReflection j a)) =
      (e7MinusculeReflection j (e7MinusculeReflection i a),
        rootWordSign i a * rootWordSign j (e7MinusculeReflection i a)) := by
  have hc : e7MinusculeReflection i (e7MinusculeReflection j a) =
      e7MinusculeReflection j (e7MinusculeReflection i a) := by
    simpa only [weightTable_reflection] using
      weightTable.reflection_comm_of_cartanMatrix_eq_zero i j a
        (by simpa only [weightTable_cartanMatrix] using h)
  have hi : e7MinusculeWeight (e7MinusculeReflection j a) i = e7MinusculeWeight a i := by
    simpa only [weightTable_weight, weightTable_reflection, weightTable_cartanMatrix,
      h, mul_zero, sub_zero] using weightTable.weight_reflection j a i
  have hj : e7MinusculeWeight (e7MinusculeReflection i a) j = e7MinusculeWeight a j := by
    have hji : CartanMatrix.E 7 j i = 0 := by rw [(CartanMatrix.E_isSymm 7).apply, h]
    simpa only [weightTable_weight, weightTable_reflection, weightTable_cartanMatrix,
      hji, mul_zero, sub_zero] using weightTable.weight_reflection i a j
  simp only [hc, rootWordSign, hi, hj, mul_comm]

private theorem braid_certificate (i j : Fin 7) (a : Fin 56)
    (h : CartanMatrix.E 7 i j = -1) :
    (e7MinusculeReflection i (e7MinusculeReflection j (e7MinusculeReflection i a)),
        rootWordSign i a * rootWordSign j (e7MinusculeReflection i a) *
          rootWordSign i (e7MinusculeReflection j (e7MinusculeReflection i a))) =
      (e7MinusculeReflection j (e7MinusculeReflection i (e7MinusculeReflection j a)),
        rootWordSign j a * rootWordSign i (e7MinusculeReflection j a) *
          rootWordSign j (e7MinusculeReflection i (e7MinusculeReflection j a))) := by
  have hji : CartanMatrix.E 7 j i = -1 := by rw [(CartanMatrix.E_isSymm 7).apply, h]
  have coord (i : Fin 7) (a : Fin 56) (k : Fin 7) :
      e7MinusculeWeight (e7MinusculeReflection i a) k =
        e7MinusculeWeight a k - e7MinusculeWeight a i * CartanMatrix.E 7 k i := by
    simpa only [weightTable_weight, weightTable_reflection, weightTable_cartanMatrix] using
      weightTable.weight_reflection i a k
  have hc : e7MinusculeReflection i (e7MinusculeReflection j (e7MinusculeReflection i a)) =
      e7MinusculeReflection j (e7MinusculeReflection i (e7MinusculeReflection j a)) := by
    apply e7MinusculeWeight_injective
    funext k
    have scalar (x y z c d : ℤ) :
        z - x * c - (y - -x) * d - (x - x * 2 - -(y - -x)) * c =
          z - y * d - (x - -y) * c - (y - y * 2 - -(x - -y)) * d := by ring
    simpa only [coord, CartanMatrix.E_diag, h, hji, mul_neg_one] using
      scalar (e7MinusculeWeight a i) (e7MinusculeWeight a j) (e7MinusculeWeight a k)
        (CartanMatrix.E 7 k i) (CartanMatrix.E 7 k j)
  -- Along either three-step braid, the final sign reads the other initial coordinate.
  have doubleCoord (i j : Fin 7) (hij : CartanMatrix.E 7 i j = -1)
      (hji : CartanMatrix.E 7 j i = -1) :
      e7MinusculeWeight (e7MinusculeReflection j (e7MinusculeReflection i a)) i =
        e7MinusculeWeight a j := by
    have scalar (x y : ℤ) : x - x * 2 - (y - x * (-1)) * (-1) = y := by ring
    simpa only [coord, CartanMatrix.E_diag, hij, hji] using
      scalar (e7MinusculeWeight a i) (e7MinusculeWeight a j)
  apply Prod.ext hc
  simp only [rootWordSign, doubleCoord i j h hji, doubleCoord j i hji h,
    coord, h, hji, mul_neg_one]
  rw [sub_neg_eq_add, sub_neg_eq_add, add_comm (e7MinusculeWeight a i)]
  ac_rfl

private theorem rootWordMatrix_commute (i j : Fin 7) (h : CartanMatrix.E 7 i j = 0) :
    Commute (rootWordMatrix i) (rootWordMatrix j) := by
  apply Matrix.ext_of_mulVec_single
  intro b
  have hc := commuting_certificate i j b h
  have hv : (rootWordMatrix i * rootWordMatrix j).mulVec (Pi.single b 1) =
      (rootWordMatrix j * rootWordMatrix i).mulVec (Pi.single b 1) := by
    simp only [← Matrix.mulVec_mulVec, rootWordMatrix_mulVec_single,
      Matrix.mulVec_smul, smul_smul]
    rw [(Prod.mk.inj hc).1, (Prod.mk.inj hc).2]
  exact hv

private theorem rootWordMatrix_braid (i j : Fin 7) (h : CartanMatrix.E 7 i j = -1) :
    rootWordMatrix i * rootWordMatrix j * rootWordMatrix i =
      rootWordMatrix j * rootWordMatrix i * rootWordMatrix j := by
  apply Matrix.ext_of_mulVec_single
  intro b
  have hc := braid_certificate i j b h
  have hv : (rootWordMatrix i * rootWordMatrix j * rootWordMatrix i).mulVec (Pi.single b 1) =
      (rootWordMatrix j * rootWordMatrix i * rootWordMatrix j).mulVec (Pi.single b 1) := by
    simp only [← Matrix.mulVec_mulVec, rootWordMatrix_mulVec_single,
      Matrix.mulVec_smul, smul_smul, ← mul_assoc]
    rw [(Prod.mk.inj hc).1, (Prod.mk.inj hc).2]
  exact hv

private theorem coe_rootWord (R : Type*) [CommRing R] (i : Fin 7) :
    (((rootSubgroupPoints (.inl i) R (Multiplicative.ofAdd 1) *
        rootSubgroupPoints (.inr i) R (Multiplicative.ofAdd (-1)) *
        rootSubgroupPoints (.inl i) R (Multiplicative.ofAdd 1) : points R) :
        Matrix.GeneralLinearGroup (Fin 56) R) : Matrix (Fin 56) (Fin 56) R) =
      (Int.castRingHom R).mapMatrix (rootWordMatrix i) := by
  simp only [Subgroup.coe_mul, Units.val_mul, coe_rootSubgroupPoints_inl,
    coe_rootSubgroupPoints_inr, toAdd_ofAdd, one_smul, neg_smul, rootWordMatrix,
    map_mul, map_add, map_sub, map_one, RingHom.mapMatrix_apply, Int.coe_castRingHom]
  simp only [sub_eq_add_neg]

/-- Pinned simple-root words at nonadjacent E₇ nodes commute over every commutative ring. -/
theorem commute_rootWord_of_cartanMatrix_eq_zero (R : Type*) [CommRing R]
    (i j : Fin 7) (h : CartanMatrix.E 7 i j = 0) :
    Commute
      (rootSubgroupPoints (.inl i) R (Multiplicative.ofAdd 1) *
        rootSubgroupPoints (.inr i) R (Multiplicative.ofAdd (-1)) *
        rootSubgroupPoints (.inl i) R (Multiplicative.ofAdd 1))
      (rootSubgroupPoints (.inl j) R (Multiplicative.ofAdd 1) *
        rootSubgroupPoints (.inr j) R (Multiplicative.ofAdd (-1)) *
        rootSubgroupPoints (.inl j) R (Multiplicative.ofAdd 1)) := by
  apply Subtype.ext
  apply Units.ext
  have hm := coe_rootWord R
  simp only [Subgroup.coe_mul, Units.val_mul] at hm ⊢
  rw [hm i, hm j]
  exact ((rootWordMatrix_commute i j h).map (Int.castRingHom R).mapMatrix).eq

/-- The pinned simple-root words at adjacent E₇ nodes satisfy the length-three braid relation,
with their integral signs retained over arbitrary commutative rings. -/
theorem rootWord_braid_of_cartanMatrix_eq_neg_one (R : Type*) [CommRing R]
    (i j : Fin 7) (h : CartanMatrix.E 7 i j = -1) :
    (rootSubgroupPoints (.inl i) R (Multiplicative.ofAdd 1) *
        rootSubgroupPoints (.inr i) R (Multiplicative.ofAdd (-1)) *
        rootSubgroupPoints (.inl i) R (Multiplicative.ofAdd 1)) *
      (rootSubgroupPoints (.inl j) R (Multiplicative.ofAdd 1) *
        rootSubgroupPoints (.inr j) R (Multiplicative.ofAdd (-1)) *
        rootSubgroupPoints (.inl j) R (Multiplicative.ofAdd 1)) *
      (rootSubgroupPoints (.inl i) R (Multiplicative.ofAdd 1) *
        rootSubgroupPoints (.inr i) R (Multiplicative.ofAdd (-1)) *
        rootSubgroupPoints (.inl i) R (Multiplicative.ofAdd 1)) =
    (rootSubgroupPoints (.inl j) R (Multiplicative.ofAdd 1) *
        rootSubgroupPoints (.inr j) R (Multiplicative.ofAdd (-1)) *
        rootSubgroupPoints (.inl j) R (Multiplicative.ofAdd 1)) *
      (rootSubgroupPoints (.inl i) R (Multiplicative.ofAdd 1) *
        rootSubgroupPoints (.inr i) R (Multiplicative.ofAdd (-1)) *
        rootSubgroupPoints (.inl i) R (Multiplicative.ofAdd 1)) *
      (rootSubgroupPoints (.inl j) R (Multiplicative.ofAdd 1) *
        rootSubgroupPoints (.inr j) R (Multiplicative.ofAdd (-1)) *
        rootSubgroupPoints (.inl j) R (Multiplicative.ofAdd 1)) := by
  apply Subtype.ext
  apply Units.ext
  have hm := coe_rootWord R
  simp only [Subgroup.coe_mul, Units.val_mul] at hm ⊢
  rw [hm i, hm j]
  simpa only [map_mul] using
    congrArg (Int.castRingHom R).mapMatrix (rootWordMatrix_braid i j h)

end TauCeti.E7Minuscule
