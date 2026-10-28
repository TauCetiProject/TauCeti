/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.SuccessiveMinima
import TauCeti.LinearAlgebra.Basis.Flag

/-!
# The successive minima of weighted boxes and cross-polytopes

Let `b` be a basis of a finite-dimensional real normed space `E` of dimension `d`, let
`L = span ℤ (range b)` be the lattice it generates, and let `a : Fin d → ℝ` be positive and
nondecreasing weights. The weighted box and the weighted cross-polytope

```text
{x | ∀ j, a j * |b.repr x j| ≤ 1},      {x | ∑ j, a j * |b.repr x j| ≤ 1}
```

both have the weights as their successive minima with respect to `L`: `λ_i(L, K) = a i`. More
generally, so does every convex body `K` lying between the two. The basis vectors `b 0, …, b i`
lie in `a i • K`, because they lie in the dilated cross-polytope; conversely, a vector of `L` in a
dilate `t • K` with `t < a i` lies in the dilated box, so its coordinates from the `i`-th on are
integers of absolute value less than `1`, hence zero, and such vectors span at most `i` dimensions.

These are the equality cases of Minkowski's second theorem: with these minima, the box is an
equality case of the upper bound `(∏ i, λ_i) * μ K ≤ 2 ^ d * covolume L μ`
(`ZLattice.prod_successiveMin_mul_measureReal_le_two_pow_mul_covolume`), and the cross-polytope,
whose volume is `OrthonormalBasis.volume_weighted_crosspolytope`, of the lower bound
`2 ^ d / d! * covolume L μ ≤ (∏ i, λ_i) * μ K`
(`ZLattice.two_pow_div_factorial_mul_covolume_le_prod_successiveMin_mul_measure`). This file
computes the minima only.

## Main results

* `ZLattice.successiveMin_eq_of_crosspolytope_subset_of_subset_box`: a convex body between the
  weighted cross-polytope and the weighted box has the weights as its successive minima.
* `ZLattice.successiveMin_box`: the successive minima of the weighted box.
* `ZLattice.successiveMin_crosspolytope`: the successive minima of the weighted cross-polytope.

## References

* J.-H. Evertse, *Diophantine approximation, Chapter 2: Geometry of numbers*, lecture notes,
  Leiden University, 2023, §2.3, Examples 2 and 3 and Exercise 2.9.
-/

public section

open Module Submodule
open scoped Pointwise

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {b : Basis (Fin (finrank ℝ E)) ℝ E}
  {a : Fin (finrank ℝ E) → ℝ} {K : ConvexBody E}

/-- **The successive minima of a body between a weighted cross-polytope and a weighted box.** Let
`b` be a basis of `E` and `a` positive nondecreasing weights. If the convex body `K` contains the
weighted cross-polytope `{x | ∑ j, a j * |b.repr x j| ≤ 1}` and is contained in the weighted box
`{x | ∀ j, a j * |b.repr x j| ≤ 1}`, then the successive minima of the lattice `span ℤ (range b)`
with respect to `K` are the weights `a i`. -/
theorem successiveMin_eq_of_crosspolytope_subset_of_subset_box (ha : ∀ j, 0 < a j)
    (hmono : Monotone a) (hcross : {x | ∑ j, a j * |b.repr x j| ≤ 1} ⊆ (K : Set E))
    (hbox : (K : Set E) ⊆ {x | ∀ j, a j * |b.repr x j| ≤ 1}) (i : Fin (finrank ℝ E)) :
    successiveMin (span ℤ (Set.range b)) K i = a i := by
  have := Module.Finite.of_basis b
  -- The basis vector `b j` lies in `t • K` for `t ≥ a j`, since `t⁻¹ • b j` is in the
  -- cross-polytope.
  have hbK {j : Fin (finrank ℝ E)} {t : ℝ} (ht : a j ≤ t) : b j ∈ t • (K : Set E) := by
    have ht₀ : 0 < t := (ha j).trans_le ht
    refine ⟨t⁻¹ • b j, hcross ?_, smul_inv_smul₀ ht₀.ne' _⟩
    simpa [Finsupp.single_apply, apply_ite, abs_of_pos ht₀, ← div_eq_mul_inv] using
      (div_le_one ht₀).2 ht
  -- A lattice vector in `t • K` with `t < a i` lies in the box `t • box`, so its coordinates from
  -- the `i`-th on are integers of absolute value less than `1`: it lies in `b.flag i.castSucc`.
  have hflag {t : ℝ} (ht : 0 ≤ t) (hti : t < a i) {x : E} (hxL : x ∈ span ℤ (Set.range b))
      (hxK : x ∈ t • (K : Set E)) : x ∈ b.flag i.castSucc := by
    rw [Basis.mem_flag_iff_repr_eq_zero]
    intro k hk
    obtain ⟨z, hz⟩ := (b.mem_span_iff_repr_mem ℤ x).1 hxL k
    obtain ⟨y, hyK, rfl⟩ := Set.mem_smul_set.1 hxK
    rw [eq_intCast] at hz
    have hik : a i ≤ a k := hmono (Fin.castSucc_le_castSucc_iff.1 hk)
    have hy : a k * (t * |b.repr y k|) ≤ t := by
      rw [mul_left_comm]
      exact mul_le_of_le_one_right ht (hbox hyK k)
    have hz₁ : |(z : ℝ)| < 1 := by
      rw [hz, map_smul, Finsupp.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg ht]
      by_contra! h
      nlinarith [ha k]
    rw [← hz, Int.cast_eq_zero.2 (Int.abs_lt_one_iff.1 (by exact_mod_cast hz₁))]
  have hmem : ∀ j : Fin (i + 1), b (Fin.castLE i.isLt j) ∈ a i • (K : Set E) := fun j ↦
    hbK (hmono (Fin.le_def.2 (Nat.lt_succ_iff.1 j.isLt)))
  have hlin : LinearIndependent ℝ fun j : Fin (i + 1) ↦ b (Fin.castLE i.isLt j) :=
    b.linearIndependent.comp _ (Fin.castLE_injective _)
  have hL (j : Fin (i + 1)) : b (Fin.castLE i.isLt j) ∈ span ℤ (Set.range b) :=
    subset_span ⟨_, rfl⟩
  refine le_antisymm (successiveMin_le (ha i).le hlin hL hmem) ?_
  rw [successiveMin_def]
  refine le_csInf ⟨a i, (ha i).le, _, hlin, fun j ↦ ⟨hL j, hmem j⟩⟩ ?_
  -- `i + 1` independent lattice vectors in `t • K` with `t < a i` would lie in the
  -- `i`-dimensional subspace `b.flag i.castSucc`.
  rintro t ⟨ht, v, hv, hvLK⟩
  by_contra! hti
  have hle := Submodule.finrank_mono <| span_le.2 <| Set.range_subset_iff.2 fun j ↦
    hflag ht hti (hvLK j).1 (hvLK j).2
  rw [finrank_span_eq_card hv, Fintype.card_fin, Basis.finrank_flag, Fin.val_castSucc] at hle
  omega

/-- With nonnegative weights, the weighted cross-polytope lies in the weighted box. -/
private lemma crosspolytope_subset_box (ha : ∀ j, 0 ≤ a j) :
    {x | ∑ j, a j * |b.repr x j| ≤ 1} ⊆ {x | ∀ j, a j * |b.repr x j| ≤ 1} := fun _ hx j ↦
  (Finset.single_le_sum (fun k _ ↦ mul_nonneg (ha k) (abs_nonneg _)) (Finset.mem_univ j)).trans hx

/-- **The successive minima of a weighted box.** Let `b` be a basis of `E` and `a` positive
nondecreasing weights. The successive minima of the lattice `span ℤ (range b)` with respect to the
weighted box `K = {x | ∀ j, a j * |b.repr x j| ≤ 1}` are the weights `a i`. -/
theorem successiveMin_box (ha : ∀ j, 0 < a j) (hmono : Monotone a)
    (hK : (K : Set E) = {x | ∀ j, a j * |b.repr x j| ≤ 1}) (i : Fin (finrank ℝ E)) :
    successiveMin (span ℤ (Set.range b)) K i = a i :=
  successiveMin_eq_of_crosspolytope_subset_of_subset_box ha hmono
    ((crosspolytope_subset_box fun j ↦ (ha j).le).trans hK.ge) hK.le i

/-- **The successive minima of a weighted cross-polytope.** Let `b` be a basis of `E` and `a`
positive nondecreasing weights. The successive minima of the lattice `span ℤ (range b)` with
respect to the weighted cross-polytope `K = {x | ∑ j, a j * |b.repr x j| ≤ 1}` are the weights
`a i`. -/
theorem successiveMin_crosspolytope (ha : ∀ j, 0 < a j) (hmono : Monotone a)
    (hK : (K : Set E) = {x | ∑ j, a j * |b.repr x j| ≤ 1}) (i : Fin (finrank ℝ E)) :
    successiveMin (span ℤ (Set.range b)) K i = a i :=
  successiveMin_eq_of_crosspolytope_subset_of_subset_box ha hmono hK.ge
    (hK.le.trans (crosspolytope_subset_box fun j ↦ (ha j).le)) i

end ZLattice
