/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.DeterminantOne

import TauCeti.Data.Fin.Basic

/-!
# The type A weight torus and its maximality on field-valued points

Over any commutative ring, the standard carrier's weight-torus points are precisely the
determinant-one diagonal matrices. Over an infinite field, their centralizer is exactly that
diagonal subgroup, so they form a maximal commutative subgroup of the carrier points.

## Main declarations

* `TauCeti.SlStd.centralizer_range_weightTorusPoints_eq_diagonalPoints`: over an infinite field,
  the centralizer of the weight torus is the determinant-one diagonal subgroup.
* `TauCeti.SlStd.range_weightTorusPoints_eq_diagonalPoints`: the weight torus consists of all
  determinant-one diagonal carrier points.
* `TauCeti.SlStd.eq_range_weightTorusPoints_of_le_of_isMulCommutative`: the weight torus is maximal
  among commutative subgroups of the carrier points over an infinite field.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §7.1.
* J. E. Humphreys, *Linear Algebraic Groups*, §§15.3 and 16.1.
-/

public section

namespace TauCeti.SlStd

universe u

noncomputable section

variable (r : ℕ)

/-- The character of the standard weight at coordinate `k` is the quotient of the adjacent torus
parameters. Missing factors at the two ends are interpreted as one. -/
theorem torusCharacter_weight (K : Type u) [CommRing K]
    (s : Fin r → Kˣ) (k : Fin (r + 1)) :
    torusCharacter s (weight r k) =
      (if hk : (k : ℕ) < r then s ⟨k, hk⟩ else 1) *
        (if hk : 0 < (k : ℕ) then (s ⟨k - 1, by omega⟩)⁻¹ else 1) := by
  rw [weight_eq_ite_single_sub_ite_single, torusCharacter_sub]
  split_ifs <;>
    simp only [← weightChar_apply, weightChar_single, weightChar_zero, MonoidHom.one_apply,
      div_eq_mul_inv, inv_one]

/-- On a determinant-one diagonal tuple, the partial products evaluate under the standard weight
characters to the original tuple. -/
theorem torusCharacter_partialProd {K : Type u} [CommRing K]
    (t : Fin (r + 1) → Kˣ) (ht : ∏ i, t i = 1) (k : Fin (r + 1)) :
    torusCharacter (fun i : Fin r ↦ Fin.partialProd t i.succ.castSucc) (weight r k) = t k := by
  rw [torusCharacter_weight]
  split_ifs with hkr hk0
  · -- The interior coordinates are successive quotients of partial products.
    let i : Fin r := ⟨k, hkr⟩
    let j : Fin r := ⟨k - 1, by omega⟩
    have hi : i.succ.castSucc = k.succ := by
      apply Fin.ext
      simp only [i, Fin.val_castSucc, Fin.val_succ]
    have hj : j.succ.castSucc = k.castSucc := by
      apply Fin.ext
      simp only [j, Fin.val_castSucc, Fin.val_succ]
      omega
    rw [hi, hj]
    simpa only [mul_comm] using (Fin.partialProd_right_inv t k)
  · -- At coordinate zero, the missing lower partial product is one.
    have hkzero : (k : ℕ) = 0 := by omega
    have hkfin : k = 0 := Fin.ext hkzero
    subst k
    have hi : (⟨(0 : Fin (r + 1)), hkr⟩ : Fin r).succ.castSucc =
        (0 : Fin (r + 1)).succ := Fin.ext rfl
    rw [mul_one, hi, Fin.partialProd_succ, Fin.castSucc_zero,
      Fin.partialProd_zero, one_mul]
  · -- At the final coordinate, the determinant-one hypothesis closes the partial product.
    have hkmax : (k : ℕ) = r := by omega
    have hrpos : 0 < r := by omega
    have hkfin : k = ⟨r, Nat.lt_succ_self r⟩ := Fin.ext hkmax
    subst k
    let i : Fin r := ⟨r - 1, by omega⟩
    let k : Fin (r + 1) := ⟨r, Nat.lt_succ_self r⟩
    have hi : i.succ.castSucc = k.castSucc := by
      apply Fin.ext
      simp only [i, k, Fin.val_castSucc, Fin.val_succ]
      omega
    rw [hi]
    have hlast : Fin.partialProd t k.succ = 1 := by
      have hk_last : k.succ = Fin.last (r + 1) := by
        apply Fin.ext
        simp only [k, Fin.val_succ, Fin.val_last]
      rw [hk_last]
      exact (Fin.partialProd_last t).trans ht
    have hright := Fin.partialProd_right_inv t k
    rw [hlast, mul_one] at hright
    simpa only [one_mul, k] using hright
  · -- In rank zero, the determinant-one hypothesis is the only coordinate equation.
    have hrzero : r = 0 := by omega
    subst r
    have hkfin : k = 0 := Fin.eq_zero k
    subst k
    simpa only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one] using ht.symm

/-! ## Diagonal points and the weight-torus range -/

/-- The diagonal points of the standard carrier. -/
def diagonalPoints (K : Type u) [CommRing K] : Subgroup (points r K) :=
  (diagonalTorus K (r + 1)).comap (points r K).subtype

/-- A carrier point lies in `diagonalPoints` exactly when its ambient matrix is diagonal. -/
@[simp]
theorem mem_diagonalPoints_iff {K : Type u} [CommRing K] {g : points r K} :
    g ∈ diagonalPoints r K ↔ g.1.1.IsDiag := by
  rw [diagonalPoints, Subgroup.mem_comap, mem_diagonalTorus_iff]
  rfl

/-- Every standard weight-torus point is diagonal in the ambient general linear group. -/
theorem coe_weightTorusPoints_mem_diagonalTorus (K : Type u) [CommRing K] (s : Fin r → Kˣ) :
    (weightTorusPoints r K s : Matrix.GeneralLinearGroup (Fin (r + 1)) K) ∈
      diagonalTorus K (r + 1) := by
  rw [coe_weightTorusPoints, UniversalEnvelopingAlgebra.kostantTorusMatrix_apply]
  exact mem_diagonalTorus_iff_exists_diagGL.mpr ⟨_, rfl⟩

/-- The partial products of a determinant-one diagonal tuple give an explicit preimage under the
standard weight-torus parametrization. -/
theorem coe_weightTorusPoints_partialProd {K : Type u} [CommRing K]
    (t : Fin (r + 1) → Kˣ) (ht : ∏ i, t i = 1) :
    (weightTorusPoints r K (fun i : Fin r ↦ Fin.partialProd t i.succ.castSucc) :
        Matrix.GeneralLinearGroup (Fin (r + 1)) K) = diagGL t := by
  rw [coe_weightTorusPoints, UniversalEnvelopingAlgebra.kostantTorusMatrix_apply]
  congr 1
  exact funext (torusCharacter_partialProd r t ht)

/-! ## The centralizer and maximality -/

/-- If the standard weight characters are distinct over a ring without zero divisors, the
centralizer of the weight torus in the carrier points is exactly the diagonal subgroup. -/
theorem centralizer_range_weightTorusPoints_eq_diagonalPoints_of_weightChar_weight_injective
    (K : Type u) [CommRing K] [IsCancelMulZero K]
    (hchar : Function.Injective (weightChar K ∘ weight r)) :
    Subgroup.centralizer
        ((weightTorusPoints r K).range : Set (points r K)) = diagonalPoints r K := by
  apply le_antisymm
  · intro g hg
    rw [mem_diagonalPoints_iff]
    intro i j hij
    have hchar_ne : weightChar K (weight r i) ≠ weightChar K (weight r j) :=
      fun h ↦ hij (hchar h)
    obtain ⟨s, hs⟩ := DFunLike.ne_iff.mp hchar_ne
    let d := weightTorusPoints r K s
    have hcomm : Commute d g :=
      Subgroup.mem_centralizer_iff.mp hg d ⟨s, rfl⟩
    have hmatrix : Commute d.1.1 g.1.1 :=
      (hcomm.map (points r K).subtype).map (Units.coeHom _)
    have hd : d = weightTorusPoints r K s := rfl
    rw [hd] at hmatrix
    rw [coe_weightTorusPoints,
      UniversalEnvelopingAlgebra.kostantTorusMatrix_apply, diagGL_coe] at hmatrix
    apply apply_eq_zero_of_commute_diagonal hmatrix
    rw [weightChar_apply, weightChar_apply] at hs
    exact fun h ↦ hs (Units.ext h)
  · intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    obtain ⟨s, rfl⟩ := hd
    have hdDiag := coe_weightTorusPoints_mem_diagonalTorus r K s
    have hcomm : Commute
        (weightTorusPoints r K s : Matrix.GeneralLinearGroup (Fin (r + 1)) K) g :=
      Subgroup.mem_centralizer_iff.mp
        (Subgroup.le_centralizer (diagonalTorus K (r + 1)) hdDiag) g hg |>.symm
    exact (Commute.of_map (points r K).subtype_injective hcomm).eq

/-- Over an infinite field, the centralizer of the weight torus in the carrier points is exactly
the diagonal subgroup. -/
theorem centralizer_range_weightTorusPoints_eq_diagonalPoints
    (K : Type u) [Field K] [Infinite K] :
    Subgroup.centralizer
        ((weightTorusPoints r K).range : Set (points r K)) = diagonalPoints r K :=
  centralizer_range_weightTorusPoints_eq_diagonalPoints_of_weightChar_weight_injective r K
    (weightChar_injective.comp (weight_injective r))

/-- **Over a commutative ring, the standard weight torus consists of all diagonal carrier
points.** Thus every diagonal carrier point admits a standard weight-torus parametrization. -/
@[simp]
theorem range_weightTorusPoints_eq_diagonalPoints (K : Type u) [CommRing K] :
    (weightTorusPoints r K).range = diagonalPoints r K := by
  apply le_antisymm
  · rintro g ⟨s, rfl⟩
    rw [mem_diagonalPoints_iff]
    exact mem_diagonalTorus_iff.mp (coe_weightTorusPoints_mem_diagonalTorus r K s)
  · intro g hg
    rw [mem_diagonalPoints_iff] at hg
    obtain ⟨t, ht⟩ := mem_diagonalTorus_iff_exists_diagGL.mp
      (mem_diagonalTorus_iff.mpr hg)
    have hprod : ∏ i, t i = 1 := by
      have hdet := det_eq_one_of_mem_points r g.property
      have hdet' := congrArg Matrix.GeneralLinearGroup.det ht
      rw [det_diagGL] at hdet'
      exact hdet'.trans hdet
    refine ⟨(fun i : Fin r ↦ Fin.partialProd t i.succ.castSucc), ?_⟩
    apply Subtype.ext
    rw [coe_weightTorusPoints_partialProd r t hprod, ht]

/-- If its weight characters are distinct over a ring without zero divisors, the standard weight
torus is maximal among commutative subgroups of the type `A_r` carrier. -/
theorem eq_range_weightTorusPoints_of_weightChar_weight_injective_of_le_of_isMulCommutative
    (K : Type u) [CommRing K] [IsCancelMulZero K]
    (hchar : Function.Injective (weightChar K ∘ weight r))
    (H : Subgroup (points r K)) [IsMulCommutative H]
    (hle : (weightTorusPoints r K).range ≤ H) :
    H = (weightTorusPoints r K).range :=
  Subgroup.eq_of_centralizer_eq_self_of_le_of_isMulCommutative
    ((centralizer_range_weightTorusPoints_eq_diagonalPoints_of_weightChar_weight_injective
      r K hchar).trans (range_weightTorusPoints_eq_diagonalPoints r K).symm) hle

/-- **The standard weight torus is maximal among commutative subgroups of the type `A_r`
carrier over an infinite field.** -/
theorem eq_range_weightTorusPoints_of_le_of_isMulCommutative
    (K : Type u) [Field K] [Infinite K]
    (H : Subgroup (points r K)) [IsMulCommutative H]
    (hle : (weightTorusPoints r K).range ≤ H) :
    H = (weightTorusPoints r K).range :=
  eq_range_weightTorusPoints_of_weightChar_weight_injective_of_le_of_isMulCommutative r K
    (weightChar_injective.comp (weight_injective r)) H hle

end

end TauCeti.SlStd
