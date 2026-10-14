/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Fan.ProjectiveSpace.Basic
public import TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Basic

/-!
# Homogeneous-coordinate characters of the projective-space fan

The character of the ratio of homogeneous coordinates `X_j / X_k` pairs with the ray indexed
by `l` as `δ_{jl} - δ_{kl}`. On the maximal cone omitting `k`, these characters, for `j ≠ k`,
freely generate the dual semigroup. Thus its monoid algebra is the polynomial coordinate ring
of the standard projective chart `X_k ≠ 0`, with these characters as its coordinate monomials.

The explicit semigroup equivalence computes the exponent of each ratio by pairing with the
corresponding ray. It supplies homogeneous coordinates for affine complex points without
choosing a second lattice basis. The character addition law gives the change of ratios
`X_j / X_l = (X_j / X_k) * (X_k / X_l)` on overlaps.

## References

* W. Fulton, *Introduction to Toric Varieties*, §1.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§3.1 and 3.4.
-/

public section

open Set

namespace TauCeti.Toric

variable {N V ι : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  [Fintype ι] (b : Module.Basis ι ℤ N) {i : N →+ V}

/-- The integral character of the homogeneous-coordinate ratio `X_j / X_k`. The index `none`
labels the extra ray, the negative sum of the basis vectors. -/
noncomputable def projectiveSpaceRatioCharacter (j k : Option ι) : N →+ ℤ :=
  j.elim 0 (fun j ↦ (b.coord j).toAddMonoidHom) -
    k.elim 0 (fun k ↦ (b.coord k).toAddMonoidHom)

open Classical in
/-- A homogeneous-coordinate ratio pairs with the ray generators by the difference of two
Kronecker deltas. -/
@[simp↓]
theorem projectiveSpaceRatioCharacter_apply_generator (j k l : Option ι) :
    projectiveSpaceRatioCharacter b j k (projectiveSpaceGenerator b l) =
      (if j = l then 1 else 0) - (if k = l then 1 else 0) := by
  classical
  cases j <;> cases k <;> cases l <;>
    simp [projectiveSpaceRatioCharacter, projectiveSpaceGenerator_none,
      projectiveSpaceGenerator_some, Finsupp.single_apply, eq_comm]

omit [Fintype ι] in
@[simp]
theorem projectiveSpaceRatioCharacter_self (k : Option ι) :
    projectiveSpaceRatioCharacter b k k = 0 := by
  simp [projectiveSpaceRatioCharacter]

omit [Fintype ι] in
/-- Multiplication of homogeneous-coordinate ratios is addition of their integral characters. -/
theorem projectiveSpaceRatioCharacter_add (j k l : Option ι) :
    projectiveSpaceRatioCharacter b j k + projectiveSpaceRatioCharacter b k l =
      projectiveSpaceRatioCharacter b j l := by
  simp [projectiveSpaceRatioCharacter]

/-- Pairing a character with the generators of a projective-space cone tests exactly the
inequalities defining its dual semigroup. -/
theorem mem_dualSemigroup_projectiveSpaceCone (hi : IsIntegralLattice i)
    (S : Set (Option ι)) (m : N →+ ℤ) :
    m ∈ dualSemigroup hi (projectiveSpaceCone b i S) ↔
      ∀ j ∈ S, 0 ≤ m (projectiveSpaceGenerator b j) := by
  rw [projectiveSpaceCone_def, mem_dualSemigroup_hull_image]
  simp

/-- A character is determined by its pairings with all projective-space rays but one. -/
theorem projectiveSpaceCharacter_ext (k : Option ι) {m m' : N →+ ℤ}
    (h : ∀ j ≠ k, m (projectiveSpaceGenerator b j) = m' (projectiveSpaceGenerator b j)) :
    m = m' := by
  classical
  have hsum : ∑ j, (m - m') (projectiveSpaceGenerator b j) = 0 := by
    rw [← map_sum, sum_projectiveSpaceGenerator, map_zero]
  have hk : (m - m') (projectiveSpaceGenerator b k) = 0 := by
    rw [Finset.sum_eq_single k] at hsum
    · exact hsum
    · intro j _ hj
      simp [h j hj]
    · simp
  apply AddMonoidHom.toIntLinearMap_injective
  refine b.ext fun j ↦ ?_
  have hj : m (projectiveSpaceGenerator b (some j)) =
      m' (projectiveSpaceGenerator b (some j)) := by
    by_cases heq : some j = k
    · simpa [← heq, sub_eq_zero] using hk
    · exact h _ heq
  simpa only [projectiveSpaceGenerator_some, AddMonoidHom.coe_toIntLinearMap] using hj

/-- The coordinate character `X_j / X_k` of the maximal projective chart omitting `k`. -/
noncomputable def projectiveSpaceChartCharacter (hi : IsIntegralLattice i) (k : Option ι)
    (j : {j : Option ι // j ≠ k}) : dualSemigroup hi (projectiveSpaceCone b i {k}ᶜ) :=
  ⟨projectiveSpaceRatioCharacter b j k,
    (mem_dualSemigroup_projectiveSpaceCone b hi _ _).2 fun l hl ↦ by
      classical
      have hlk : l ≠ k := by simpa using hl
      simp only [projectiveSpaceRatioCharacter_apply_generator, Ne.symm hlk, ↓reduceIte,
        sub_zero]
      split_ifs <;> norm_num⟩

@[simp]
theorem coe_projectiveSpaceChartCharacter (hi : IsIntegralLattice i) (k : Option ι)
    (j : {j : Option ι // j ≠ k}) :
    (projectiveSpaceChartCharacter b hi k j : N →+ ℤ) =
      projectiveSpaceRatioCharacter b j k := (rfl)

open Classical in
private theorem sum_projectiveSpaceRatioCharacter_apply (k : Option ι)
    (a : {j : Option ι // j ≠ k} → ℕ) (l : {j : Option ι // j ≠ k}) :
    (∑ j, a j • projectiveSpaceRatioCharacter b j k) (projectiveSpaceGenerator b l) = a l := by
  classical
  simp [Subtype.coe_inj, Ne.symm l.2]

open Classical in
/-- The dual semigroup of the maximal projective-space cone omitting `k` is freely generated by
the ratios `X_j / X_k`, for `j ≠ k`. Exponents are the pairings with the corresponding rays. -/
noncomputable def projectiveSpaceDualSemigroupEquiv (hi : IsIntegralLattice i) (k : Option ι) :
    dualSemigroup hi (projectiveSpaceCone b i {k}ᶜ) ≃+ ({j : Option ι // j ≠ k} → ℕ) where
  toFun m j := ((m : N →+ ℤ) (projectiveSpaceGenerator b j)).toNat
  invFun a := ∑ j, a j • projectiveSpaceChartCharacter b hi k j
  left_inv m := by
    apply Subtype.ext
    apply projectiveSpaceCharacter_ext b k
    intro j hj
    have hm := (mem_dualSemigroup_projectiveSpaceCone b hi _ _).1 m.2 j (by simpa using hj)
    have hs := sum_projectiveSpaceRatioCharacter_apply b k
      (fun j ↦ ((m : N →+ ℤ) (projectiveSpaceGenerator b j)).toNat) ⟨j, hj⟩
    simpa [Int.toNat_of_nonneg hm] using hs
  right_inv a := by
    funext j
    have hs := sum_projectiveSpaceRatioCharacter_apply b k a j
    simpa using congrArg Int.toNat hs
  map_add' m m' := by
    funext j
    have hm := (mem_dualSemigroup_projectiveSpaceCone b hi _ _).1 m.2 j (by simpa using j.2)
    have hm' := (mem_dualSemigroup_projectiveSpaceCone b hi _ _).1 m'.2 j (by simpa using j.2)
    simp only [AddSubmonoid.coe_add, AddMonoidHom.add_apply, Pi.add_apply]
    exact Int.toNat_add hm hm'

/-- The exponent of a ratio is the nonnegative pairing with its ray. -/
@[simp]
theorem projectiveSpaceDualSemigroupEquiv_apply (hi : IsIntegralLattice i) (k : Option ι)
    (m : dualSemigroup hi (projectiveSpaceCone b i {k}ᶜ)) (j : {j : Option ι // j ≠ k}) :
    projectiveSpaceDualSemigroupEquiv b hi k m j =
      ((m : N →+ ℤ) (projectiveSpaceGenerator b j)).toNat := (rfl)

open Classical in
/-- The inverse exponent map forms the corresponding sum of homogeneous-coordinate characters. -/
@[simp]
theorem projectiveSpaceDualSemigroupEquiv_symm_apply (hi : IsIntegralLattice i) (k : Option ι)
    (a : {j : Option ι // j ≠ k} → ℕ) :
    (projectiveSpaceDualSemigroupEquiv b hi k).symm a =
      ∑ j, a j • projectiveSpaceChartCharacter b hi k j := (rfl)

open Classical in
/-- Each ratio character is a standard free generator of the dual semigroup. -/
@[simp]
theorem projectiveSpaceDualSemigroupEquiv_chartCharacter (hi : IsIntegralLattice i)
    (k : Option ι) (j : {j : Option ι // j ≠ k}) :
    projectiveSpaceDualSemigroupEquiv b hi k (projectiveSpaceChartCharacter b hi k j) =
      Pi.single j 1 := by
  classical
  ext l
  simp [Subtype.coe_inj, Pi.single_apply, Ne.symm l.2, eq_comm]
  split_ifs <;> rfl

end TauCeti.Toric
