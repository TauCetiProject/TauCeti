/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Enumerative.PerfectMatching
public import TauCeti.GroupTheory.Perm.SumCongr
import TauCeti.Data.Fin.Basic
import TauCeti.GroupTheory.Perm.OrbitCount.FinRotate

/-!
# Pointed matched circles

A pointed matched circle `Z` of Lipshitz, Ozsváth and Thurston is an oriented circle with a
basepoint `z` and `n` further points, together with a matching that pairs these points, such that
surgery on the circle along all the pairs gives a single circle. It is the boundary data of a
bordered three-manifold: its algebra `A(Z)` is the subalgebra of the strands algebra on the `n`
points spanned by sums over matched horizontal strands, and thickening the circle into a disc and
attaching one band for each pair gives a surface with one boundary circle, which capped off is the
closed surface `F(Z)` parametrizing the boundary of the bordered manifold.

Cutting the circle open at the basepoint orders the points, and here they are `0, …, n - 1` in
the order of the orientation. The matching is a perfect matching of `Fin n`
(`TauCeti.IsPerfectMatching`). Surgery along one pair attaches an untwisted band to the disc
bounded by the circle, so the circle produced by surgery along all the pairs is the boundary of
the one-vertex chord diagram studied in `TauCeti.Combinatorics.ChordDiagram`, which is traversed by
`finRotate n * matching`: cross the band at the current point, then follow the circle to the next
point. A pointed matched circle is therefore a perfect matching whose boundary traversal has at
most one orbit; with no points the surgery does nothing and the boundary is the circle itself.

This counting condition forces `n` to be divisible by four (`PointedMatchedCircle.four_dvd`):
when `n ≠ 0`, the boundary traversal is a single cycle of length `n` and `finRotate n` is one too,
so the matching is an even permutation, a product of `n / 2` disjoint transpositions. Writing
`n = 4 * k`, the disc with its `2 * k` bands has Euler characteristic `1 - 2 * k` and one boundary
circle, so `F(Z)` has genus `k`, as in the definition of Lipshitz, Ozsváth and Thurston.

Reversing the orientation of the circle keeps the basepoint and the pairs and reverses the order
of the points (`PointedMatchedCircle.reverse`). Placing the points of a second pointed matched
circle after those of a first gives their connected sum (`PointedMatchedCircle.connectedSum`),
along a band joining the two basepoints. The genus-one pointed matched circle, with pairs `{0, 2}`
and `{1, 3}`, is the only one with four points (`PointedMatchedCircle.eq_genusOne`); connected sums
of copies of it give the split pointed matched circles (`PointedMatchedCircle.split`), and pairing
each point with the opposite one gives the antipodal pointed matched circles
(`PointedMatchedCircle.antipodal`).

## Main definitions

* `TauCeti.PointedMatchedCircle n`: the pointed matched circles with `n` matched points.
* `TauCeti.PointedMatchedCircle.reverse`: the orientation reversal `-Z`.
* `TauCeti.PointedMatchedCircle.connectedSum`: the connected sum `Z₁ # Z₂`.
* `TauCeti.PointedMatchedCircle.genusOne`, `TauCeti.PointedMatchedCircle.split`,
  `TauCeti.PointedMatchedCircle.antipodal`: the standard examples.

## Main results

* `TauCeti.PointedMatchedCircle.sameCycle_finRotate_mul`: surgery along the pairs gives one
  circle, in the form that any two points are joined by the boundary traversal.
* `TauCeti.PointedMatchedCircle.four_dvd`: the number of matched points is a multiple of four.
* `TauCeti.PointedMatchedCircle.eq_genusOne`: there is exactly one pointed matched circle with
  four points.

## References

* R. Lipshitz, P. Ozsváth and D. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer. Math.
  Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), §3.2,
  Definition 3.16 (pointed matched circles) and the genus-one example following it.
-/

public section

namespace TauCeti

open Equiv Equiv.Perm

/-- A **pointed matched circle** with `n` matched points: the points `0, …, n - 1` of an oriented
circle cut open at a basepoint, paired by a perfect matching, such that surgery on the circle
along all the pairs gives a single circle. That circle is traversed by `finRotate n * matching`,
which crosses the band at the current point and then moves on to the next point, so the condition
is that this traversal has at most one orbit: exactly one when there are points, and none for the
empty matching, where the surgery leaves the circle unchanged. -/
@[ext]
structure PointedMatchedCircle (n : ℕ) where
  /-- The matching, sending each point to its partner. -/
  matching : Perm (Fin n)
  /-- Every point is paired with a point other than itself. -/
  isPerfectMatching : IsPerfectMatching matching
  /-- Surgery along all the pairs gives a single circle. -/
  orbitCount_finRotate_mul_le_one : orbitCount (finRotate n * matching) ≤ 1

namespace PointedMatchedCircle

variable {n : ℕ}

section Basic

variable (Z : PointedMatchedCircle n)

/-- The partner of the partner of a point is the point itself. -/
@[simp]
theorem matching_matching (i : Fin n) : Z.matching (Z.matching i) = i :=
  Z.isPerfectMatching.apply_apply i

/-- No point is paired with itself. -/
@[simp]
theorem matching_ne (i : Fin n) : Z.matching i ≠ i :=
  Z.isPerfectMatching.apply_ne i

/-- **Surgery along the pairs gives one circle**: any two points lie on one cycle of the boundary
traversal `finRotate n * matching`. -/
theorem sameCycle_finRotate_mul (i j : Fin n) : (finRotate n * Z.matching).SameCycle i j :=
  orbitCount_le_one_iff.mp Z.orbitCount_finRotate_mul_le_one i j

/-- When there are points, the boundary traversal has exactly one orbit. -/
theorem orbitCount_finRotate_mul [NeZero n] : orbitCount (finRotate n * Z.matching) = 1 :=
  orbitCount_eq_one_of_forall_sameCycle Z.sameCycle_finRotate_mul

/-- **The number of matched points is a multiple of four.** -/
theorem four_dvd (Z : PointedMatchedCircle n) : 4 ∣ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact dvd_zero 4
  have : NeZero n := ⟨hn⟩
  -- The boundary traversal and `finRotate n` are both cycles of length `n`, so the matching, their
  -- quotient, is an even permutation; being a product of `n / 2` disjoint transpositions, it has
  -- `n / 2` even.
  have htrav := sign_eq_neg_one_pow_card_sub_orbitCount (finRotate n * Z.matching)
  rw [Z.orbitCount_finRotate_mul, sign_mul, sign_finRotate, Z.isPerfectMatching.sign_eq,
    Fintype.card_fin] at htrav
  have hpow : (-1 : ℤˣ) ^ (n / 2) = 1 :=
    mul_left_cancel (a := (-1 : ℤˣ) ^ (n - 1)) (by rw [htrav, mul_one])
  obtain ⟨k, hk⟩ := (neg_one_pow_eq_one_iff_even (by decide)).mp hpow
  have htwo := Z.isPerfectMatching.two_mul_orbitCount
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at htwo
  exact ⟨k, by omega⟩

end Basic

/-! ### Orientation reversal -/

section Reverse

variable (Z : PointedMatchedCircle n)

/-- The **orientation reversal** `-Z` of a pointed matched circle: the same circle, basepoint and
pairs, with the orientation reversed, so that the points are numbered in the opposite order. -/
def reverse : PointedMatchedCircle n where
  matching := Fin.revPerm.permCongr Z.matching
  isPerfectMatching := PerfectMatching.isPerfectMatching_permCongr _ Z.isPerfectMatching
  orbitCount_finRotate_mul_le_one := by
    -- Reflecting the circle conjugates the rotation to its inverse, so the new boundary
    -- traversal is conjugate to `(finRotate n)⁻¹ * matching`, the inverse of the old one up to
    -- conjugation by the involution `matching`.
    have hrot : Fin.revPerm.permCongr (finRotate n)⁻¹ = finRotate n :=
      Equiv.ext fun i ↦ by
        have := i.neZero
        simp [Perm.inv_def]
    have hM : Z.matching⁻¹ = Z.matching := inv_eq_of_mul_eq_one_left (Equiv.ext Z.matching_matching)
    have hconj : finRotate n * Fin.revPerm.permCongr Z.matching =
        Fin.revPerm.permCongr ((finRotate n)⁻¹ * Z.matching) := by
      rw [Equiv.permCongr_mul, hrot]
    rw [hconj, Equiv.orbitCount_permCongr, ← Equiv.Perm.orbitCount_inv, mul_inv_rev, hM, inv_inv,
      orbitCount_mul_comm]
    exact Z.orbitCount_finRotate_mul_le_one

/-- The partner of a point of `-Z` is read off from `Z` through the reversed numbering. -/
@[simp]
theorem reverse_matching_apply (i : Fin n) : Z.reverse.matching i = (Z.matching i.rev).rev :=
  (rfl)

/-- Reversing the orientation twice gives back the pointed matched circle. -/
@[simp]
theorem reverse_reverse : Z.reverse.reverse = Z := by
  ext i
  simp

end Reverse

/-! ### Connected sums -/

/-- The **connected sum** `Z₁ # Z₂` of two pointed matched circles: the points of `Z₂` are placed
after those of `Z₁`, keeping both matchings. Surgery joins the two surgered circles into one along
the band through the two basepoints. -/
def connectedSum {m : ℕ} (Z₁ : PointedMatchedCircle m) (Z₂ : PointedMatchedCircle n) :
    PointedMatchedCircle (m + n) where
  matching := finSumPerm Z₁.matching Z₂.matching
  isPerfectMatching := by
    refine isPerfectMatching_iff.mpr ⟨fun x ↦ ?_, fun x ↦ ?_⟩ <;>
      induction x using Fin.addCases <;> simp [matching_ne]
  orbitCount_finRotate_mul_le_one := by
    rcases eq_or_ne m 0 with rfl | hm
    · -- With no points in `Z₁`, the connected sum is `Z₂` renumbered.
      have he : finRotate (0 + n) * finSumPerm Z₁.matching Z₂.matching =
          (finCongr (Nat.zero_add n).symm).permCongr (finRotate n * Z₂.matching) := by
        ext x
        obtain ⟨j, rfl⟩ : ∃ j, Fin.natAdd 0 j = x :=
          ⟨Fin.cast (Nat.zero_add n) x, Fin.ext (by simp)⟩
        rw [Perm.mul_apply, finSumPerm_apply_natAdd, Equiv.permCongr_apply, Perm.mul_apply]
        rw [Fin.coe_finRotate_eq_ite, finCongr_apply, Fin.val_cast, Fin.coe_finRotate_eq_ite]
        simp
      rw [he, Equiv.orbitCount_permCongr]
      exact Z₂.orbitCount_finRotate_mul_le_one
    rcases eq_or_ne n 0 with rfl | hn
    · -- With no points in `Z₂`, the connected sum is `Z₁`.
      have he : finRotate (m + 0) * finSumPerm Z₁.matching Z₂.matching =
          (finCongr (Nat.add_zero m).symm).permCongr (finRotate m * Z₁.matching) := by
        ext x
        obtain ⟨i, rfl⟩ : ∃ i, Fin.castAdd 0 i = x :=
          ⟨Fin.cast (Nat.add_zero m) x, Fin.ext (by simp)⟩
        rw [Perm.mul_apply, finSumPerm_apply_castAdd, Equiv.permCongr_apply, Perm.mul_apply]
        rw [Fin.coe_finRotate_eq_ite, finCongr_apply, Fin.val_cast, Fin.coe_finRotate_eq_ite]
        simp
      rw [he, Equiv.orbitCount_permCongr]
      exact Z₁.orbitCount_finRotate_mul_le_one
    have : NeZero m := ⟨hm⟩
    have : NeZero n := ⟨hn⟩
    -- The rotation of `Fin (m + n)` is the blockwise rotation followed by a transposition
    -- joining the two blocks, which merges the single boundary circles of `Z₁` and `Z₂`.
    rw [finRotate_add_eq_swap_mul_finSumPerm, mul_assoc, finSumPerm_mul]
    have h := orbitCount_swap_mul_add_one_of_not_sameCycle
      (not_sameCycle_finSumPerm_castAdd_natAdd (finRotate m * Z₁.matching)
        (finRotate n * Z₂.matching) 0 0)
    rw [orbitCount_finSumPerm, Z₁.orbitCount_finRotate_mul, Z₂.orbitCount_finRotate_mul] at h
    omega

variable {m : ℕ} (Z₁ : PointedMatchedCircle m) (Z₂ : PointedMatchedCircle n)

/-- In `Z₁ # Z₂`, the points of `Z₁` keep their partners. -/
@[simp]
theorem connectedSum_matching_castAdd (i : Fin m) :
    (Z₁.connectedSum Z₂).matching (Fin.castAdd n i) = Fin.castAdd n (Z₁.matching i) :=
  finSumPerm_apply_castAdd _ _ i

/-- In `Z₁ # Z₂`, the points of `Z₂` keep their partners. -/
@[simp]
theorem connectedSum_matching_natAdd (j : Fin n) :
    (Z₁.connectedSum Z₂).matching (Fin.natAdd m j) = Fin.natAdd m (Z₂.matching j) :=
  finSumPerm_apply_natAdd _ _ j

/-! ### Examples -/

/-- The pointed matched circle with no points: the boundary of the bordered three-ball, whose
surface `F(Z)` is a sphere. -/
def empty : PointedMatchedCircle 0 where
  matching := 1
  isPerfectMatching := isPerfectMatching_iff.mpr ⟨fun i ↦ i.elim0, fun i ↦ i.elim0⟩
  orbitCount_finRotate_mul_le_one := orbitCount_le_one_iff.mpr fun i ↦ i.elim0

/-- The **genus-one pointed matched circle**, with four points paired as `{0, 2}` and `{1, 3}`;
its surface `F(Z)` is a torus. -/
def genusOne : PointedMatchedCircle 4 where
  matching := swap 0 2 * swap 1 3
  isPerfectMatching := by decide
  orbitCount_finRotate_mul_le_one := orbitCount_le_one_iff.mpr (by decide)

/-- The partners in the genus-one pointed matched circle. -/
@[simp]
theorem genusOne_matching : genusOne.matching = swap 0 2 * swap 1 3 :=
  (rfl)

/-- **The genus-one pointed matched circle is the only one with four points.** Of the three
perfect matchings of four points, `{0, 1}, {2, 3}` and `{0, 3}, {1, 2}` do not interleave, and
surgery along them gives three circles. -/
theorem eq_genusOne (Z : PointedMatchedCircle 4) : Z = genusOne := by
  ext1
  rcases (isPerfectMatching_fin_four_iff Z.matching).mp Z.isPerfectMatching with h | h | h
  · exact absurd (Z.sameCycle_finRotate_mul 0 1) (by rw [h]; decide)
  · exact h
  · exact absurd (Z.sameCycle_finRotate_mul 0 1) (by rw [h]; decide)

/-- The genus-one pointed matched circle is the unique pointed matched circle with four points. -/
instance : Unique (PointedMatchedCircle 4) where
  default := genusOne
  uniq := eq_genusOne

/-- The **split pointed matched circle** of genus `k`, the connected sum of `k` copies of the
genus-one pointed matched circle: its points `4 * j, 4 * j + 1, 4 * j + 2, 4 * j + 3` are paired as
`{4 * j, 4 * j + 2}` and `{4 * j + 1, 4 * j + 3}` for each `j < k`. -/
def split : (k : ℕ) → PointedMatchedCircle (4 * k)
  | 0 => empty
  | k + 1 => (split k).connectedSum genusOne

/-- The split pointed matched circle of genus zero has no points. -/
@[simp]
theorem split_zero : split 0 = empty :=
  (rfl)

/-- The split pointed matched circle of genus `k + 1` adds a genus-one summand after the split
pointed matched circle of genus `k`. -/
theorem split_succ (k : ℕ) : split (k + 1) = (split k).connectedSum genusOne :=
  (rfl)

/-- The partners in the split pointed matched circle: a point `i` with `i % 4 < 2` is paired with
`i + 2`, and any other point with `i - 2`. -/
@[simp]
theorem coe_split_matching_apply (k : ℕ) (i : Fin (4 * k)) :
    ((split k).matching i : ℕ) = if (i : ℕ) % 4 < 2 then (i : ℕ) + 2 else (i : ℕ) - 2 := by
  induction k with
  | zero => exact i.elim0
  | succ k ih =>
    rw [split_succ]
    rcases lt_or_ge (i : ℕ) (4 * k) with h | h
    · -- A point of the first `4 * k`, matched as in `split k`.
      obtain ⟨i, rfl⟩ : ∃ i' : Fin (4 * k), Fin.castAdd 4 i' = i := ⟨⟨i, h⟩, Fin.ext (rfl)⟩
      rw [connectedSum_matching_castAdd, Fin.val_castAdd, Fin.val_castAdd, ih]
    · -- One of the last four points, matched as in the genus-one pointed matched circle.
      obtain ⟨j, rfl⟩ : ∃ j : Fin 4, Fin.natAdd (4 * k) j = i :=
        ⟨⟨i - 4 * k, by omega⟩, Fin.ext (by simp; omega)⟩
      rw [connectedSum_matching_natAdd, Fin.val_natAdd, Fin.val_natAdd, genusOne_matching]
      fin_cases j <;> simp [swap_apply_of_ne_of_ne]

/-- The **antipodal pointed matched circle** of genus `k`, which pairs each of its `4 * k` points
with the opposite point of the circle, `i` with `i + 2 * k` modulo `4 * k`. Its boundary traversal
is the rotation by `2 * k + 1`, which is coprime to `4 * k`. -/
def antipodal (k : ℕ) : PointedMatchedCircle (4 * k) where
  matching := finRotate (4 * k) ^ (2 * k)
  isPerfectMatching := by
    refine isPerfectMatching_iff.mpr ⟨fun i ↦ ?_, fun i hi ↦ ?_⟩
    · rw [← Perm.mul_apply, ← pow_add, show 2 * k + 2 * k = 4 * k by ring]
      rcases eq_or_ne k 0 with rfl | hk
      · simp
      · simpa [orderOf_finRotate (by omega : 4 * k ≠ 0)] using
          congrArg (· i) (pow_orderOf_eq_one (finRotate (4 * k)))
    · have h := congrArg Fin.val hi
      have hi' := i.isLt
      rw [Fin.coe_finRotate_pow] at h
      rcases lt_or_ge ((i : ℕ) + 2 * k) (4 * k) with hlt | hge
      · rw [Nat.mod_eq_of_lt hlt] at h
        omega
      · rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)] at h
        omega
  orbitCount_finRotate_mul_le_one := by
    rw [← pow_succ', orbitCount_eq_card_parts_partition]
    rcases eq_or_ne k 0 with rfl | hk
    · simp
    rw [parts_partition_finRotate_pow (by omega)]
    · simp
    · -- `2 * k + 1` is odd and coprime to `k`, hence coprime to `4 * k`.
      refine Nat.Coprime.mul_right ?_ ?_
      · exact Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr ⟨k, by ring⟩)
      · simp

/-- The partner of a point `i` of the antipodal pointed matched circle is `i + 2 * k` modulo
`4 * k`. -/
@[simp]
theorem coe_antipodal_matching_apply (k : ℕ) (i : Fin (4 * k)) :
    ((antipodal k).matching i : ℕ) = ((i : ℕ) + 2 * k) % (4 * k) :=
  Fin.coe_finRotate_pow _ i

end PointedMatchedCircle

end TauCeti
