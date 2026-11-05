/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.Frobenius
public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.Weyl
public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.UpperTriangular
public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.CharacterMap
public import Mathlib.FieldTheory.Perfect

/-!
# A non-based Frobenius-square endomorphism of the rank-one carrier

Conjugating Frobenius on the standard type-`A₁` carrier by the pinned Weyl representative
`n = !![0, 1; -1, 0]` gives an endomorphism whose square is a Frobenius, but which exchanges
the positive and negative root subgroups over a perfect field. It has the negative Frobenius
scaling as a character map.
Thus preserving a torus and having a Frobenius power do not imply preservation of the
chosen positive system or Borel subgroup.

`TauCeti.SlStd.rankOneWeylFrobenius` uses the existing standard carrier, its root subgroups,
weight torus and Frobenius; it introduces no new group model. The formulas hold over any
commutative ring of exponential characteristic `p`. Over a perfect ring the two root subgroup
images are exactly the opposite root subgroups. Over every nontrivial value ring the standard
upper-triangular subgroup is not preserved, witnessed by the positive root element at one.

## References

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Mem. Amer. Math. Soc. **80** (1968).
* R. W. Carter, *Finite Groups of Lie Type*, §1.17.
-/

public section

namespace TauCeti.SlStd

noncomputable section

variable (p k : ℕ) (A : Type*) [CommRing A] [ExpChar A p]

/-- Conjugate the `p ^ k`-power Frobenius of the standard rank-one carrier by its pinned
Weyl representative. Its square is the `p ^ (2 * k)`-power Frobenius, but it sends each
signed root subgroup into the opposite one. -/
def rankOneWeylFrobenius : points 1 A →* points 1 A :=
  (MulAut.conj (simpleWeylPoint 1 0 A)).toMonoidHom.comp (frobenius 1 p k A)

/-- The defining conjugation formula for the Weyl-conjugated Frobenius. -/
theorem rankOneWeylFrobenius_apply (g : points 1 A) :
    rankOneWeylFrobenius p k A g =
      simpleWeylPoint 1 0 A * frobenius 1 p k A g * (simpleWeylPoint 1 0 A)⁻¹ := by
  simp [rankOneWeylFrobenius, MulAut.conj_apply]

private theorem coe_rankOneWeylPoint :
    ((simpleWeylPoint 1 0 A : Matrix.GeneralLinearGroup (Fin 2) A) :
      Matrix (Fin 2) (Fin 2) A) = !![0, 1; -1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_simpleWeylPoint_apply]

private theorem inv_coe_rankOneWeylPoint :
    ((simpleWeylPoint 1 0 A : Matrix.GeneralLinearGroup (Fin 2) A) :
      Matrix (Fin 2) (Fin 2) A)⁻¹ = !![0, -1; 1, 0] := by
  rw [coe_rankOneWeylPoint]
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The matrix of the Weyl-conjugated Frobenius: the diagonal entries are exchanged and
the off-diagonal entries are exchanged and negated after applying Frobenius. -/
theorem coe_rankOneWeylFrobenius (g : points 1 A) :
    ((rankOneWeylFrobenius p k A g : Matrix.GeneralLinearGroup (Fin 2) A) :
        Matrix (Fin 2) (Fin 2) A) =
      !![iterateFrobenius A p k (g.val.val 1 1), -iterateFrobenius A p k (g.val.val 1 0);
        -iterateFrobenius A p k (g.val.val 0 1), iterateFrobenius A p k (g.val.val 0 0)] := by
  rw [rankOneWeylFrobenius_apply]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Matrix.GeneralLinearGroup.coe_mul,
    Matrix.GeneralLinearGroup.coe_inv]
  rw [inv_coe_rankOneWeylPoint, coe_rankOneWeylPoint]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      coe_frobenius_apply, iterateFrobenius_def]

/-- The square of the Weyl-conjugated `p ^ k`-Frobenius is the `p ^ (k + k)`-power
Frobenius. -/
theorem rankOneWeylFrobenius_comp_self :
    (rankOneWeylFrobenius p k A).comp (rankOneWeylFrobenius p k A) =
      frobenius 1 p (k + k) A := by
  ext g : 1
  apply Subtype.ext
  apply Units.ext
  rw [MonoidHom.comp_apply, coe_rankOneWeylFrobenius]
  have h := coe_rankOneWeylFrobenius p k A g
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [h, coe_frobenius_apply, ← iterateFrobenius_def, iterateFrobenius_add_apply]

/-- The positive root element is sent into the negative root subgroup, with negated
Frobenius parameter. -/
@[simp]
theorem rankOneWeylFrobenius_rootSubgroupPoints_inl (u : A) :
    rankOneWeylFrobenius p k A (rootSubgroupPoints 1 (.inl 0) A (.ofAdd u)) =
      rootSubgroupPoints 1 (.inr 0) A (.ofAdd (-iterateFrobenius A p k u)) := by
  rw [rankOneWeylFrobenius_apply, frobenius_rootSubgroupPoints,
    simpleWeylPoint_conj_rootSubgroupPoints]
  simp only [toAdd_ofAdd, iterateFrobenius_def]

/-- The negative root element is sent into the positive root subgroup, with negated
Frobenius parameter. -/
@[simp]
theorem rankOneWeylFrobenius_rootSubgroupPoints_inr (u : A) :
    rankOneWeylFrobenius p k A (rootSubgroupPoints 1 (.inr 0) A (.ofAdd u)) =
      rootSubgroupPoints 1 (.inl 0) A (.ofAdd (-iterateFrobenius A p k u)) := by
  rw [rankOneWeylFrobenius_apply, frobenius_rootSubgroupPoints,
    simpleWeylPoint_conj_rootSubgroupPoints_inr]
  simp only [toAdd_ofAdd, iterateFrobenius_def]

/-- On the rank-one weight torus this endomorphism sends `s` to `(s ^ p ^ k)⁻¹`,
the group inverse of its `p ^ k`-th power. -/
@[simp]
theorem rankOneWeylFrobenius_weightTorusPoints (s : Fin 1 → Aˣ) :
    rankOneWeylFrobenius p k A (weightTorusPoints 1 A s) =
      weightTorusPoints 1 A (s ^ p ^ k)⁻¹ := by
  rw [rankOneWeylFrobenius_apply, frobenius_weightTorusPoints,
    simpleWeylPoint_conj_weightTorusPoints]
  congr 1
  ext i
  fin_cases i
  simp [rootGeneratorWeight_inl, CartanMatrix.A, torusCharacter_def, pow_two]

/-- The negative Frobenius scaling `-p ^ k` is a character map of this endomorphism. -/
theorem isCharacterMap_rankOneWeylFrobenius :
    IsCharacterMap (weightTorusPoints 1 A) (rankOneWeylFrobenius p k A)
      (-((p ^ k : ℕ) • (1 : Module.End ℤ (Fin 1 → ℤ)))) := by
  apply isCharacterMap_iff.mpr
  intro s
  rw [rankOneWeylFrobenius_weightTorusPoints, neg_eq_zero_sub, torusPointMap_sub,
    torusPointMap_nsmul, torusPointMap_one]
  congr 1
  ext i
  simp [torusPointMap_apply]

/-- Over a ring with divisible units, in particular an algebraically closed field, the
Weyl-conjugated Frobenius maps the weight torus onto itself. -/
theorem map_rankOneWeylFrobenius_range_weightTorusPoints [RootableBy Aˣ ℕ] :
    (weightTorusPoints 1 A).range.map (rankOneWeylFrobenius p k A) =
      (weightTorusPoints 1 A).range := by
  apply (isCharacterMap_rankOneWeylFrobenius p k A).map_range_eq
  intro x y h
  apply nsmul_right_injective (pow_ne_zero k (expChar_ne_zero A p))
  simpa only [LinearMap.neg_apply, LinearMap.smul_apply, one_apply_eq_self, neg_inj] using h

private theorem map_rankOneWeylFrobenius_range_rootSubgroupPoints [PerfectRing A p]
    (i j : Fin 1 ⊕ Fin 1)
    (h : ∀ u : A, rankOneWeylFrobenius p k A (rootSubgroupPoints 1 i A (.ofAdd u)) =
      rootSubgroupPoints 1 j A (.ofAdd (-iterateFrobenius A p k u))) :
    (rootSubgroupPoints 1 i A).range.map (rankOneWeylFrobenius p k A) =
      (rootSubgroupPoints 1 j A).range := by
  ext g
  simp only [MonoidHom.mem_range, Subgroup.mem_map]
  constructor
  · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
    exact ⟨.ofAdd (-iterateFrobenius A p k u.toAdd), (h _).symm⟩
  · rintro ⟨u, rfl⟩
    obtain ⟨v, hv⟩ := (bijective_iterateFrobenius A p k).surjective (-u.toAdd)
    refine ⟨rootSubgroupPoints 1 i A (.ofAdd v), ⟨.ofAdd v, rfl⟩, ?_⟩
    simp [h, hv]

/-- Over a perfect ring the image of the positive root subgroup is exactly the negative
root subgroup. -/
theorem map_rankOneWeylFrobenius_range_rootSubgroupPoints_inl [PerfectRing A p] :
    (rootSubgroupPoints 1 (.inl 0) A).range.map (rankOneWeylFrobenius p k A) =
      (rootSubgroupPoints 1 (.inr 0) A).range := by
  exact map_rankOneWeylFrobenius_range_rootSubgroupPoints p k A _ _
    (rankOneWeylFrobenius_rootSubgroupPoints_inl p k A)

/-- Over a perfect ring the image of the negative root subgroup is exactly the positive
root subgroup. -/
theorem map_rankOneWeylFrobenius_range_rootSubgroupPoints_inr [PerfectRing A p] :
    (rootSubgroupPoints 1 (.inr 0) A).range.map (rankOneWeylFrobenius p k A) =
      (rootSubgroupPoints 1 (.inl 0) A).range := by
  exact map_rankOneWeylFrobenius_range_rootSubgroupPoints p k A _ _
    (rankOneWeylFrobenius_rootSubgroupPoints_inr p k A)

/-- The positive root element at one is an explicit obstruction to preservation of the
standard upper-triangular subgroup. In particular this endomorphism is not based. -/
theorem rankOneWeylFrobenius_rootSubgroupPoints_inl_one_notMem_upperTriangularPoints
    [Nontrivial A] :
    (rankOneWeylFrobenius p k A (rootSubgroupPoints 1 (.inl 0) A (.ofAdd 1)) :
      Matrix.GeneralLinearGroup (Fin 2) A) ∉ upperTriangularPoints 1 A := by
  rw [rankOneWeylFrobenius_rootSubgroupPoints_inl,
    rootSubgroupPoints_negative_mem_upperTriangularPoints_iff]
  simp

/-- Even though its square is Frobenius and it preserves the torus, this endomorphism does
not preserve the standard Borel subgroup. -/
theorem not_map_rankOneWeylFrobenius_upperTriangularPoints_le [Nontrivial A] :
    ¬ ((upperTriangularPoints 1 A).subgroupOf (points 1 A)).map
        (rankOneWeylFrobenius p k A) ≤
      (upperTriangularPoints 1 A).subgroupOf (points 1 A) := by
  intro h
  apply rankOneWeylFrobenius_rootSubgroupPoints_inl_one_notMem_upperTriangularPoints p k A
  exact h (Subgroup.mem_map.mpr
    ⟨rootSubgroupPoints 1 (.inl 0) A (.ofAdd 1),
      rootSubgroupPoints_positive_mem_upperTriangularPoints 1 A 0 (.ofAdd 1), rfl⟩)

end

end TauCeti.SlStd
