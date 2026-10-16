/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Infinite sums in ultrametric normed modules

Scalar products of two cofinite-null families form a cofinite-null family on the product index.
Consequently, over a complete ultrametric module the scalar products of two summable families are
summable, and their sum is the scalar product of the two sums.  Grouping this double sum by the
antidiagonals of an additive index monoid gives the corresponding Cauchy-product formula.

The joint-decay statement is stronger than continuity of scalar multiplication at zero: cofinite
decay on a product index requires all but finitely many pairs to be small.  Its proof uses the
global boundedness of each null family together with decay in either coordinate.

The summation API parallels Mathlib's nonarchimedean ring results
`HasSum.mul_of_nonarchimedean` and `Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal`, reusing the
generic module and fiberwise-summation interfaces.
-/

public section

namespace TauCeti

open Filter
open scoped BigOperators Topology

variable {R M : Type*} [SeminormedRing R] [SeminormedAddCommGroup M] [Module R M]
  [IsBoundedSMul R M]

/-- If two normed families tend to zero cofinitely, then their pointwise scalar products, indexed
by pairs, also tend to zero cofinitely. -/
theorem tendsto_smul_cofinite_nhds_zero {α β : Type*} {f : α → R} {g : β → M}
    (hf : Tendsto f cofinite (𝓝 0)) (hg : Tendsto g cofinite (𝓝 0)) :
    Tendsto (fun ij : α × β ↦ f ij.1 • g ij.2) cofinite (𝓝 0) := by
  obtain ⟨A, hA⟩ := hf.norm.bddAbove_range_of_cofinite
  obtain ⟨B, hB⟩ := hg.norm.bddAbove_range_of_cofinite
  let A' := max A 1
  let B' := max B 1
  have hA' (i : α) : ‖f i‖ ≤ A' := (hA ⟨i, rfl⟩).trans (le_max_left _ _)
  have hB' (j : β) : ‖g j‖ ≤ B' := (hB ⟨j, rfl⟩).trans (le_max_left _ _)
  have hA'pos : 0 < A' := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hB'pos : 0 < B' := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  have hfε := Metric.tendsto_nhds.mp hf (ε / B') (div_pos hε hB'pos)
  have hgε := Metric.tendsto_nhds.mp hg (ε / A') (div_pos hε hA'pos)
  -- `mem_cofinite` only exposes the finite exceptional sets after the eventualities are written
  -- explicitly as membership in the cofinite filter.
  change {i | dist (f i) 0 < ε / B'} ∈ cofinite at hfε
  change {j | dist (g j) 0 < ε / A'} ∈ cofinite at hgε
  change {ij : α × β | dist (f ij.1 • g ij.2) 0 < ε} ∈ cofinite
  rw [mem_cofinite] at hfε hgε ⊢
  refine (hfε.prod hgε).subset ?_
  rintro ⟨i, j⟩ hsmall
  simp only [Set.mem_prod, Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt, dist_zero_right]
    at hsmall ⊢
  constructor
  · by_contra hi
    have hi' : ‖f i‖ < ε / B' := lt_of_not_ge hi
    exact (not_lt_of_ge hsmall) <| calc
      ‖f i • g j‖ ≤ ‖f i‖ * ‖g j‖ := norm_smul_le _ _
      _ ≤ ‖f i‖ * B' := mul_le_mul_of_nonneg_left (hB' j) (norm_nonneg _)
      _ < (ε / B') * B' := mul_lt_mul_of_pos_right hi' hB'pos
      _ = ε := div_mul_cancel₀ _ hB'pos.ne'
  · by_contra hj
    have hj' : ‖g j‖ < ε / A' := lt_of_not_ge hj
    exact (not_lt_of_ge hsmall) <| calc
      ‖f i • g j‖ ≤ ‖f i‖ * ‖g j‖ := norm_smul_le _ _
      _ ≤ A' * ‖g j‖ := mul_le_mul_of_nonneg_right (hA' i) (norm_nonneg _)
      _ < A' * (ε / A') := mul_lt_mul_of_pos_left hj' hA'pos
      _ = ε := by field_simp

section Complete

variable [IsUltrametricDist M] [CompleteSpace M]

/-- In a complete ultrametric normed module, the scalar products of two summable families are
summable on the product index. -/
theorem _root_.Summable.smul_of_nonarchimedean {α β : Type*} {f : α → R} {g : β → M}
    (hf : Summable f) (hg : Summable g) :
    Summable fun ij : α × β ↦ f ij.1 • g ij.2 :=
  (NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero _).mpr <|
    tendsto_smul_cofinite_nhds_zero hf.tendsto_cofinite_zero hg.tendsto_cofinite_zero

/-- Scalar multiplication distributes over two infinite sums in a complete ultrametric normed
module. -/
theorem _root_.HasSum.smul_of_nonarchimedean [T2Space M] {α β : Type*} {f : α → R}
    {g : β → M} {a : R} {b : M} (hf : HasSum f a) (hg : HasSum g b) :
    HasSum (fun ij : α × β ↦ f ij.1 • g ij.2) (a • b) :=
  hf.smul hg (hf.summable.smul_of_nonarchimedean hg.summable)

/-- The scalar product of two infinite sums in a complete ultrametric normed module is their
double sum. -/
theorem tsum_smul_tsum_of_nonarchimedean [T2Space M] {α β : Type*} {f : α → R} {g : β → M}
    (hf : Summable f) (hg : Summable g) :
    (∑' i, f i) • (∑' j, g j) = ∑' ij : α × β, f ij.1 • g ij.2 :=
  (hf.hasSum.smul_of_nonarchimedean hg.hasSum).tsum_eq.symm

section CauchyProduct

variable {A : Type*} [AddCommMonoid A] [Finset.HasAntidiagonal A]

private theorem summable_smul_sigma_antidiagonal_of_nonarchimedean {f : A → R} {g : A → M}
    (hf : Summable f) (hg : Summable g) :
    Summable fun ij : Σ n : A, Finset.antidiagonal n ↦
      f (ij.2 : A × A).1 • g (ij.2 : A × A).2 :=
  Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff.mpr
    (hf.smul_of_nonarchimedean hg)

/-- The antidiagonal scalar Cauchy product of two summable families is summable in a complete
ultrametric normed module. -/
theorem summable_sum_smul_antidiagonal_of_nonarchimedean {f : A → R} {g : A → M}
    (hf : Summable f) (hg : Summable g) :
    Summable fun n ↦ ∑ ij ∈ Finset.antidiagonal n, f ij.1 • g ij.2 := by
  have hsigma := summable_smul_sigma_antidiagonal_of_nonarchimedean hf hg
  conv =>
    congr
    ext n
    rw [← Finset.sum_finset_coe, ← tsum_fintype (L := .unconditional _)]
  exact hsigma.sigma' fun n ↦ (hasSum_fintype _).summable

/-- The Cauchy-product formula for the scalar product of two infinite sums, grouped over the
antidiagonals of an additive index monoid. -/
protected theorem _root_.Summable.tsum_smul_tsum_eq_tsum_sum_antidiagonal_of_nonarchimedean
    [T2Space M] {f : A → R} {g : A → M} (hf : Summable f) (hg : Summable g) :
    (∑' n, f n) • (∑' n, g n) =
      ∑' n, ∑ ij ∈ Finset.antidiagonal n, f ij.1 • g ij.2 := by
  have hsigma := summable_smul_sigma_antidiagonal_of_nonarchimedean hf hg
  conv_rhs =>
    congr
    ext n
    rw [← Finset.sum_finset_coe, ← tsum_fintype (L := .unconditional _)]
  rw [tsum_smul_tsum_of_nonarchimedean hf hg,
    ← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq]
  exact hsigma.tsum_sigma' fun n ↦ (hasSum_fintype _).summable

/-- The antidiagonal scalar Cauchy product sums to the scalar product of the original two sums. -/
theorem hasSum_sum_smul_antidiagonal_of_nonarchimedean [T2Space M] {f : A → R} {g : A → M}
    (hf : Summable f) (hg : Summable g) :
    HasSum (fun n ↦ ∑ ij ∈ Finset.antidiagonal n, f ij.1 • g ij.2)
      ((∑' n, f n) • ∑' n, g n) := by
  convert (summable_sum_smul_antidiagonal_of_nonarchimedean hf hg).hasSum
  exact hf.tsum_smul_tsum_eq_tsum_sum_antidiagonal_of_nonarchimedean hg

end CauchyProduct

section Nat

/-- The usual natural-number scalar Cauchy product is summable in a complete ultrametric normed
module. -/
theorem summable_sum_smul_range_of_nonarchimedean {f : ℕ → R} {g : ℕ → M}
    (hf : Summable f) (hg : Summable g) :
    Summable fun n ↦ ∑ k ∈ Finset.range (n + 1), f k • g (n - k) := by
  simp_rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ fun k l ↦ f k • g l]
  exact summable_sum_smul_antidiagonal_of_nonarchimedean hf hg

/-- The natural-number Cauchy-product formula for the scalar product of two infinite sums. -/
protected theorem _root_.Summable.tsum_smul_tsum_eq_tsum_sum_range_of_nonarchimedean
    [T2Space M] {f : ℕ → R} {g : ℕ → M} (hf : Summable f) (hg : Summable g) :
    (∑' n, f n) • (∑' n, g n) =
      ∑' n, ∑ k ∈ Finset.range (n + 1), f k • g (n - k) := by
  simp_rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ fun k l ↦ f k • g l]
  exact hf.tsum_smul_tsum_eq_tsum_sum_antidiagonal_of_nonarchimedean hg

/-- The natural-number scalar Cauchy product sums to the scalar product of the original two
sums. -/
theorem hasSum_sum_smul_range_of_nonarchimedean [T2Space M] {f : ℕ → R} {g : ℕ → M}
    (hf : Summable f) (hg : Summable g) :
    HasSum (fun n ↦ ∑ k ∈ Finset.range (n + 1), f k • g (n - k))
      ((∑' n, f n) • ∑' n, g n) := by
  convert (summable_sum_smul_range_of_nonarchimedean hf hg).hasSum
  exact hf.tsum_smul_tsum_eq_tsum_sum_range_of_nonarchimedean hg

end Nat

end Complete

end TauCeti

end
