/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import TauCeti.Algebra.Module.ZLattice.SuccessiveMinima
import TauCeti.LinearAlgebra.Basis.Flag
import TauCeti.MeasureTheory.Measure.Lebesgue.Weighted.Box
import TauCeti.MeasureTheory.Measure.Lebesgue.Weighted.Crosspolytope

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

These are the equality cases of Minkowski's second theorem, for every additive Haar measure `μ`
on `E`. The box has measure `2 ^ d / ∏ i, a i` times the covolume of `L`
(`Module.Basis.addHaar_weighted_box`), so it attains the upper bound
`(∏ i, λ_i) * μ K ≤ 2 ^ d * covolume L μ`
(`ZLattice.prod_successiveMin_mul_measureReal_le_two_pow_mul_covolume`). The cross-polytope has
measure `2 ^ d / d! / ∏ i, a i` times the covolume of `L`
(`Module.Basis.addHaar_weighted_crosspolytope`), so it attains the lower bound
`2 ^ d / d! * covolume L μ ≤ (∏ i, λ_i) * μ K`
(`ZLattice.two_pow_div_factorial_mul_covolume_le_prod_successiveMin_mul_measureReal`). Neither
constant `2 ^ d` nor `2 ^ d / d!` can therefore be improved.

## Main results

* `ZLattice.successiveMin_eq_of_crosspolytope_subset_of_subset_box`: a convex body between the
  weighted cross-polytope and the weighted box has the weights as its successive minima.
* `ZLattice.successiveMin_box`: the successive minima of the weighted box.
* `ZLattice.successiveMin_crosspolytope`: the successive minima of the weighted cross-polytope.
* `ZLattice.successiveMin_pi_box`, `ZLattice.successiveMin_pi_crosspolytope`: the same for the
  standard lattice `ℤⁿ ⊆ ℝⁿ` in coordinates, without a choice of basis.
* `ZLattice.prod_successiveMin_mul_measureReal_box`: the weighted box attains the upper bound of
  Minkowski's second theorem.
* `ZLattice.prod_successiveMin_mul_measureReal_crosspolytope`: the weighted cross-polytope attains
  the lower bound of Minkowski's second theorem.

## References

* J.-H. Evertse, *Diophantine approximation, Chapter 2: Geometry of numbers*, lecture notes,
  Leiden University, 2023, §2.3, Examples 2 and 3 and Exercise 2.9.
-/

public section

open MeasureTheory Module Submodule
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

/-- **The successive minima of a weighted box.** Let `b` be a basis of `E` and `a` positive
nondecreasing weights. The successive minima of the lattice `span ℤ (range b)` with respect to the
weighted box `K = {x | ∀ j, a j * |b.repr x j| ≤ 1}` are the weights `a i`. -/
theorem successiveMin_box (ha : ∀ j, 0 < a j) (hmono : Monotone a)
    (hK : (K : Set E) = {x | ∀ j, a j * |b.repr x j| ≤ 1}) (i : Fin (finrank ℝ E)) :
    successiveMin (span ℤ (Set.range b)) K i = a i :=
  successiveMin_eq_of_crosspolytope_subset_of_subset_box ha hmono
    ((TauCeti.weighted_crosspolytope_subset_weighted_box (fun j ↦ (ha j).le) fun x ↦
      b.repr x).trans hK.ge) hK.le i

/-- **The successive minima of a weighted cross-polytope.** Let `b` be a basis of `E` and `a`
positive nondecreasing weights. The successive minima of the lattice `span ℤ (range b)` with
respect to the weighted cross-polytope `K = {x | ∑ j, a j * |b.repr x j| ≤ 1}` are the weights
`a i`. -/
theorem successiveMin_crosspolytope (ha : ∀ j, 0 < a j) (hmono : Monotone a)
    (hK : (K : Set E) = {x | ∑ j, a j * |b.repr x j| ≤ 1}) (i : Fin (finrank ℝ E)) :
    successiveMin (span ℤ (Set.range b)) K i = a i :=
  successiveMin_eq_of_crosspolytope_subset_of_subset_box ha hmono hK.ge
    (hK.le.trans (TauCeti.weighted_crosspolytope_subset_weighted_box (fun j ↦ (ha j).le) fun x ↦
      b.repr x)) i

/-! ### The standard lattice `ℤⁿ ⊆ ℝⁿ`

The statements above, in the coordinates of `Fin n → ℝ`. The successive minima are indexed by
`Fin (finrank ℝ (Fin n → ℝ))`, which is `Fin n` only up to `Module.finrank_fin_fun`, so the weight
attached to the `i`-th minimum is `w (i.cast (finrank_fin_fun ℝ))`. -/

section Pi

variable {n : ℕ} {w : Fin n → ℝ} {C : ConvexBody (Fin n → ℝ)}

/-- **The successive minima of `ℤⁿ` with respect to a body between a weighted cross-polytope and a
weighted box.** If the convex body `C ⊆ ℝⁿ` contains `{x | ∑ j, w j * |x j| ≤ 1}` and is contained
in `{x | ∀ j, w j * |x j| ≤ 1}` for positive nondecreasing weights `w`, then the successive
minima of the standard lattice `ℤⁿ` with respect to `C` are the weights. -/
theorem successiveMin_pi_eq_of_crosspolytope_subset_of_subset_box (hw : ∀ j, 0 < w j)
    (hmono : Monotone w) (hcross : {x | ∑ j, w j * |x j| ≤ 1} ⊆ (C : Set (Fin n → ℝ)))
    (hbox : (C : Set (Fin n → ℝ)) ⊆ {x | ∀ j, w j * |x j| ≤ 1})
    (i : Fin (finrank ℝ (Fin n → ℝ))) :
    successiveMin (span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))) C i =
      w (i.cast (finrank_fin_fun ℝ)) := by
  -- Apply the basis form to the standard basis, reindexed by `Fin (finrank ℝ (Fin n → ℝ))`.
  set e : Fin (finrank ℝ (Fin n → ℝ)) ≃ Fin n := finCongr (finrank_fin_fun ℝ)
  have hrepr (x : Fin n → ℝ) (j) : ((Pi.basisFun ℝ (Fin n)).reindex e.symm).repr x j = x (e j) := by
    simp
  have h := successiveMin_eq_of_crosspolytope_subset_of_subset_box
    (b := (Pi.basisFun ℝ (Fin n)).reindex e.symm) (a := w ∘ e) (K := C) (fun j ↦ hw _)
    (hmono.comp fun _ _ ↦ by simp [e]) (fun x hx ↦ hcross ?_) (fun x hx ↦ ?_) i
  · rwa [Basis.range_reindex] at h
  · simpa [hrepr, e.sum_comp fun j ↦ w j * |x j|] using hx
  · simpa [hrepr, e.forall_congr_left] using hbox hx

/-- **The successive minima of `ℤⁿ` with respect to a weighted box.** For positive nondecreasing
weights `w`, the successive minima of the standard lattice `ℤⁿ` with respect to the box
`C = {x | ∀ j, w j * |x j| ≤ 1}` are the weights. -/
theorem successiveMin_pi_box (hw : ∀ j, 0 < w j) (hmono : Monotone w)
    (hC : (C : Set (Fin n → ℝ)) = {x | ∀ j, w j * |x j| ≤ 1}) (i : Fin (finrank ℝ (Fin n → ℝ))) :
    successiveMin (span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))) C i =
      w (i.cast (finrank_fin_fun ℝ)) :=
  successiveMin_pi_eq_of_crosspolytope_subset_of_subset_box hw hmono
    ((TauCeti.weighted_crosspolytope_subset_weighted_box (fun j ↦ (hw j).le) id).trans hC.ge)
    hC.le i

/-- **The successive minima of `ℤⁿ` with respect to a weighted cross-polytope.** For positive
nondecreasing weights `w`, the successive minima of the standard lattice `ℤⁿ` with respect to the
cross-polytope `C = {x | ∑ j, w j * |x j| ≤ 1}` are the weights. -/
theorem successiveMin_pi_crosspolytope (hw : ∀ j, 0 < w j) (hmono : Monotone w)
    (hC : (C : Set (Fin n → ℝ)) = {x | ∑ j, w j * |x j| ≤ 1})
    (i : Fin (finrank ℝ (Fin n → ℝ))) :
    successiveMin (span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))) C i =
      w (i.cast (finrank_fin_fun ℝ)) :=
  successiveMin_pi_eq_of_crosspolytope_subset_of_subset_box hw hmono hC.ge
    (hC.le.trans (TauCeti.weighted_crosspolytope_subset_weighted_box (fun j ↦ (hw j).le) id))
    i

end Pi

section Measure

variable [MeasurableSpace E] [BorelSpace E]

/-- **Equality in the upper bound of Minkowski's second theorem.** Let `b` be a basis of `E`, `a`
positive nondecreasing weights and `μ` an additive Haar measure on `E`. The weighted box
`K = {x | ∀ j, a j * |b.repr x j| ≤ 1}` satisfies `(∏ i, λ_i) * μ K = 2 ^ d * covolume L μ` for the
lattice `L = span ℤ (range b)`, so the constant `2 ^ d` of
`ZLattice.prod_successiveMin_mul_measureReal_le_two_pow_mul_covolume` is attained. -/
theorem prod_successiveMin_mul_measureReal_box (ha : ∀ j, 0 < a j) (hmono : Monotone a)
    (hK : (K : Set E) = {x | ∀ j, a j * |b.repr x j| ≤ 1}) (μ : Measure E := by volume_tac)
    [μ.IsAddHaarMeasure] :
    (∏ i, successiveMin (span ℤ (Set.range b)) K i) * μ.real K =
      2 ^ finrank ℝ E * covolume (span ℤ (Set.range b)) μ := by
  have := Module.Finite.of_basis b
  have hprod : 0 < ∏ i, a i := Finset.prod_pos fun i _ ↦ ha i
  rw [covolume_eq_measure_fundamentalDomain _ μ (ZSpan.isAddFundamentalDomain b μ),
    Finset.prod_congr rfl fun i _ ↦ successiveMin_box ha hmono hK i, measureReal_def, hK,
    b.addHaar_weighted_box μ ha, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    Fintype.card_fin, ← measureReal_def]
  field_simp

/-- **Equality in the lower bound of Minkowski's second theorem.** Let `b` be a basis of `E`, `a`
positive nondecreasing weights and `μ` an additive Haar measure on `E`. The weighted
cross-polytope `K = {x | ∑ j, a j * |b.repr x j| ≤ 1}` satisfies
`(∏ i, λ_i) * μ K = 2 ^ d / d! * covolume L μ` for the lattice `L = span ℤ (range b)`, so the
constant `2 ^ d / d!` of
`ZLattice.two_pow_div_factorial_mul_covolume_le_prod_successiveMin_mul_measureReal` is
attained. -/
theorem prod_successiveMin_mul_measureReal_crosspolytope (ha : ∀ j, 0 < a j)
    (hmono : Monotone a) (hK : (K : Set E) = {x | ∑ j, a j * |b.repr x j| ≤ 1})
    (μ : Measure E := by volume_tac) [μ.IsAddHaarMeasure] :
    (∏ i, successiveMin (span ℤ (Set.range b)) K i) * μ.real K =
      2 ^ finrank ℝ E / (finrank ℝ E).factorial * covolume (span ℤ (Set.range b)) μ := by
  have := Module.Finite.of_basis b
  have hprod : 0 < ∏ i, a i := Finset.prod_pos fun i _ ↦ ha i
  rw [covolume_eq_measure_fundamentalDomain _ μ (ZSpan.isAddFundamentalDomain b μ),
    Finset.prod_congr rfl fun i _ ↦ successiveMin_crosspolytope ha hmono hK i, measureReal_def,
    hK, b.addHaar_weighted_crosspolytope μ ha, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), Fintype.card_fin, ← measureReal_def]
  field_simp

end Measure

end ZLattice
