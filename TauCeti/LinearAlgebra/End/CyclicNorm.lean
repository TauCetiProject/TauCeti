/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.End.CompositionRange
import Mathlib.Algebra.Ring.GeomSum

/-!
# Cyclic norms of endomorphisms

For an endomorphism `f` satisfying `f ^ n = 1` with `n` invertible, the kernel of the
cyclic norm `∑ j < n, f ^ j` is the image of `1 - f`, and the latter splits off from
the fixed submodule. For a commuting family the simultaneous norm kernels are thus
exactly the image of the product of the differences.

This is the cyclic averaging argument used to identify ramified vectors in
`New.Data.ramifiedSourceForms_eq_range` in lsernau/grh-lean, revision `72fead1`,
`grh/src/New/UpperBound/Size/ShortColumns.lean`.
-/

public section

open LinearMap

namespace Module.End

/-- When `f ^ n = 1` and `n` is invertible in the coefficient ring, the image of
`1 - f` is the kernel of the cyclic norm `1 + f + ⋯ + f ^ (n - 1)`. -/
theorem range_one_sub_eq_ker_geom_sum {R M : Type*} [Ring R] [AddCommGroup M]
    [Module R M] (f : End R M) {n : ℕ} (hn : IsUnit (n : R)) (hf : f ^ n = 1) :
    range (1 - f) = ker (∑ j ∈ Finset.range n, f ^ j) := by
  refine le_antisymm ?_ ?_
  · have h := geom_sum_mul_neg f n
    rw [hf, sub_self] at h
    exact range_le_ker_iff.mpr h
  · intro x hx
    have hsum : ∑ j ∈ Finset.range n, (x - (f ^ j) x) ∈ range (1 - f) := by
      apply Submodule.sum_mem
      intro j _
      exact mem_range.mpr ⟨(∑ i ∈ Finset.range j, f ^ i) x, by
        simpa only [mul_apply_eq_comp, LinearMap.sub_apply, one_apply_eq_self] using
          LinearMap.congr_fun (mul_neg_geom_sum f j) x⟩
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      ← LinearMap.sum_apply, mem_ker.mp hx, sub_zero, ← Nat.cast_smul_eq_nsmul R] at hsum
    exact ((range (1 - f)).smul_mem_iff_of_isUnit hn).mp hsum

/-- The fixed submodule of an endomorphism of invertible period is complementary to
the image of its difference from the identity. -/
theorem isCompl_ker_range_one_sub_of_pow_eq_one {R M : Type*} [Ring R] [AddCommGroup M]
    [Module R M] (f : End R M) {n : ℕ} (hn : IsUnit (n : R)) (hf : f ^ n = 1) :
    IsCompl (ker (1 - f)) (range (1 - f)) := by
  let N : End R M := ∑ j ∈ Finset.range n, f ^ j
  have hr : range (1 - f) = ker N := f.range_one_sub_eq_ker_geom_sum hn hf
  have hfixed (x : M) (hx : x ∈ ker (1 - f)) : N x = (n : R) • x := by
    have hfx : f x = x := (sub_eq_zero.mp (by simpa using mem_ker.mp hx)).symm
    have hpow (j : ℕ) : (f ^ j) x = x := by
      induction j with
      | zero => simp
      | succ j ih => rw [pow_succ', mul_apply_eq_comp, ih, hfx]
    simp [N, LinearMap.sum_apply, hpow, Nat.cast_smul_eq_nsmul]
  refine ⟨disjoint_iff_inf_le.mpr (fun x hx ↦ ?_), codisjoint_iff_le_sup.mpr ?_⟩
  · obtain ⟨hx, hx'⟩ := Submodule.mem_inf.mp hx
    rw [hr, mem_ker, hfixed x hx] at hx'
    exact ((⊥ : Submodule R M).smul_mem_iff_of_isUnit hn).mp (by simpa using hx')
  · intro x _
    obtain ⟨u, hu⟩ := hn
    let y : M := (↑u⁻¹ : R) • N x
    have hNy : N x ∈ ker (1 - f) := by
      apply mem_ker.mpr
      simpa only [mul_apply_eq_comp, hf, sub_self, LinearMap.zero_apply] using
        LinearMap.congr_fun (mul_neg_geom_sum f n) x
    have hy : y ∈ ker (1 - f) := (ker (1 - f)).smul_mem _ hNy
    have hy' : x - y ∈ range (1 - f) := by
      rw [hr, mem_ker, map_sub, hfixed y hy, sub_eq_zero]
      simp [y, ← hu, smul_smul]
    exact Submodule.mem_sup.mpr ⟨y, hy, x - y, hy', add_sub_cancel _ _⟩

end Module.End

namespace List

/-- For a finite family of commuting endomorphisms of invertible periods, the image of the
product of `1 - f i` consists exactly of the vectors with zero cyclic norm for every factor. -/
theorem range_map_prod_one_sub_eq_iInf_ker_geom_sum {R M ι : Type*} [Ring R]
    [AddCommGroup M] [Module R M] (s : List ι) (f : ι → Module.End R M) (n : ι → ℕ)
    (hcomm : s.Pairwise fun i j ↦ Commute (f i) (f j))
    (hn : ∀ i ∈ s, IsUnit (n i : R)) (hf : ∀ i ∈ s, f i ^ n i = 1) :
    (s.map fun i ↦ 1 - f i).prod.range = ⨅ i ∈ s, ker (∑ j ∈ Finset.range (n i), f i ^ j) := by
  rw [s.range_map_prod_eq_iInf_range _
    (hcomm.imp fun {i j} h ↦ (Commute.one_right (1 - f i)).sub_right
      ((Commute.one_left (f j)).sub_left h))
    (fun i hi ↦ (f i).isCompl_ker_range_one_sub_of_pow_eq_one (hn i hi) (hf i hi))]
  exact iInf_congr fun i ↦ iInf_congr fun hi ↦
    (f i).range_one_sub_eq_ker_geom_sum (hn i hi) (hf i hi)

end List
