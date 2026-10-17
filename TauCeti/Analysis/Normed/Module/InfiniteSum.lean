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
summable, and so are their Cauchy products.  If the module is moreover Hausdorff, the double sum is
the scalar product of the two sums, and grouping it by the antidiagonals of an additive index monoid
gives the corresponding Cauchy-product formula.

The joint-decay statement is stronger than continuity of scalar multiplication at zero: cofinite
decay on a product index requires all but finitely many pairs to be small.

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
    Tendsto (fun ij : α × β ↦ f ij.1 • g ij.2) cofinite (𝓝 0) :=
  squeeze_zero_norm (fun ij ↦ norm_smul_le (f ij.1) (g ij.2))
    (tendsto_mul_cofinite_nhds_zero (by simpa using hf.norm) (by simpa using hg.norm))

section Complete

variable [IsUltrametricDist M] [CompleteSpace M]

/-- In a complete ultrametric normed module, the scalar products of two summable families are
summable on the product index. -/
theorem _root_.Summable.smul_of_nonarchimedean {α β : Type*} {f : α → R} {g : β → M}
    (hf : Summable f) (hg : Summable g) :
    Summable fun ij : α × β ↦ f ij.1 • g ij.2 :=
  (NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero _).mpr <|
    tendsto_smul_cofinite_nhds_zero hf.tendsto_cofinite_zero hg.tendsto_cofinite_zero

/-- Scalar multiplication distributes over two infinite sums in a complete Hausdorff ultrametric
normed module. -/
theorem _root_.HasSum.smul_of_nonarchimedean [T2Space M] {α β : Type*} {f : α → R}
    {g : β → M} {a : R} {b : M} (hf : HasSum f a) (hg : HasSum g b) :
    HasSum (fun ij : α × β ↦ f ij.1 • g ij.2) (a • b) :=
  hf.smul hg (hf.summable.smul_of_nonarchimedean hg.summable)

/-- The scalar product of two infinite sums in a complete Hausdorff ultrametric normed module is
their double sum. -/
protected theorem _root_.Summable.tsum_smul_tsum_of_nonarchimedean [T2Space M] {α β : Type*}
    {f : α → R} {g : β → M} (hf : Summable f) (hg : Summable g) :
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
theorem _root_.Summable.sum_smul_antidiagonal_of_nonarchimedean {f : A → R} {g : A → M}
    (hf : Summable f) (hg : Summable g) :
    Summable fun n ↦ ∑ ij ∈ Finset.antidiagonal n, f ij.1 • g ij.2 := by
  have hsigma := summable_smul_sigma_antidiagonal_of_nonarchimedean hf hg
  conv =>
    congr
    ext n
    rw [← Finset.sum_finset_coe, ← tsum_fintype (L := .unconditional _)]
  exact hsigma.sigma' fun n ↦ (hasSum_fintype _).summable

/-- The Cauchy-product formula for the scalar product of two infinite sums, grouped over the
antidiagonals of an additive index monoid, in a complete Hausdorff ultrametric normed module. -/
protected theorem _root_.Summable.tsum_smul_tsum_eq_tsum_sum_antidiagonal_of_nonarchimedean
    [T2Space M] {f : A → R} {g : A → M} (hf : Summable f) (hg : Summable g) :
    (∑' n, f n) • (∑' n, g n) =
      ∑' n, ∑ ij ∈ Finset.antidiagonal n, f ij.1 • g ij.2 := by
  have hsigma := summable_smul_sigma_antidiagonal_of_nonarchimedean hf hg
  conv_rhs =>
    congr
    ext n
    rw [← Finset.sum_finset_coe, ← tsum_fintype (L := .unconditional _)]
  rw [hf.tsum_smul_tsum_of_nonarchimedean hg,
    ← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq]
  exact hsigma.tsum_sigma' fun n ↦ (hasSum_fintype _).summable

/-- In a complete Hausdorff ultrametric normed module, the antidiagonal scalar Cauchy product sums
to the scalar product of the original two sums. -/
theorem _root_.HasSum.sum_smul_antidiagonal_of_nonarchimedean [T2Space M] {f : A → R}
    {g : A → M} {a : R} {b : M} (hf : HasSum f a) (hg : HasSum g b) :
    HasSum (fun n ↦ ∑ ij ∈ Finset.antidiagonal n, f ij.1 • g ij.2) (a • b) := by
  have hsigma := Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff.mpr
    (hf.smul_of_nonarchimedean hg)
  exact hsigma.sigma fun n ↦ Finset.hasSum (Finset.antidiagonal n) fun ij ↦ f ij.1 • g ij.2

end CauchyProduct

section Nat

/-- The usual natural-number scalar Cauchy product is summable in a complete ultrametric normed
module. -/
theorem _root_.Summable.sum_smul_range_of_nonarchimedean {f : ℕ → R} {g : ℕ → M}
    (hf : Summable f) (hg : Summable g) :
    Summable fun n ↦ ∑ k ∈ Finset.range (n + 1), f k • g (n - k) := by
  simp_rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ fun k l ↦ f k • g l]
  exact hf.sum_smul_antidiagonal_of_nonarchimedean hg

/-- The natural-number Cauchy-product formula for the scalar product of two infinite sums, in a
complete Hausdorff ultrametric normed module. -/
protected theorem _root_.Summable.tsum_smul_tsum_eq_tsum_sum_range_of_nonarchimedean
    [T2Space M] {f : ℕ → R} {g : ℕ → M} (hf : Summable f) (hg : Summable g) :
    (∑' n, f n) • (∑' n, g n) =
      ∑' n, ∑ k ∈ Finset.range (n + 1), f k • g (n - k) := by
  simp_rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ fun k l ↦ f k • g l]
  exact hf.tsum_smul_tsum_eq_tsum_sum_antidiagonal_of_nonarchimedean hg

/-- In a complete Hausdorff ultrametric normed module, the natural-number scalar Cauchy product sums
to the scalar product of the original two sums. -/
theorem _root_.HasSum.sum_smul_range_of_nonarchimedean [T2Space M] {f : ℕ → R} {g : ℕ → M}
    {a : R} {b : M} (hf : HasSum f a) (hg : HasSum g b) :
    HasSum (fun n ↦ ∑ k ∈ Finset.range (n + 1), f k • g (n - k)) (a • b) := by
  simp_rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ fun k l ↦ f k • g l]
  exact hf.sum_smul_antidiagonal_of_nonarchimedean hg

end Nat

end Complete

end TauCeti

end
