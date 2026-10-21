/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Completion
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import Mathlib.Topology.Algebra.InfiniteSum.GroupCompletion
public import TauCeti.Topology.MetricSpace.Ultra.Completion

/-!
# Infinite sums in ultrametric normed modules

Under a bounded scalar action, the pointwise scalar multiples `f i • g j` of two cofinite-null
families form a cofinite-null family on the product index. Consequently, over a complete ultrametric
module this family is summable whenever `f` and `g` are, and so is the Cauchy product induced by
the scalar action. If the action is moreover a module structure, then completeness is not needed:
passing to the completion shows that the double sum of two families with sums `a` and `b` is
`a • b`, and grouping it by the antidiagonals of an additive index type gives the corresponding
Cauchy-product formula. The `tsum` forms of these identities assume the module is Hausdorff
(stated as `T0Space`, which is equivalent for seminormed groups).

The joint-decay statement is stronger than continuity of scalar multiplication at zero: cofinite
decay on a product index requires all but finitely many pairs to be small.

The summation API parallels Mathlib's nonarchimedean ring results
`HasSum.mul_of_nonarchimedean` (whose passage to the completion we follow) and
`Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal`, reusing the generic module and
fiberwise-summation interfaces.
-/

public section

namespace TauCeti

open Filter
open scoped BigOperators Topology

variable {R M : Type*}

/-- If two normed families tend to zero cofinitely, then their pointwise scalar multiples, indexed
by pairs, also tend to zero cofinitely. -/
theorem _root_.Filter.Tendsto.smul_cofinite_nhds_zero [SeminormedAddGroup R] [SeminormedAddGroup M]
    [SMulZeroClass R M] [IsBoundedSMul R M] {α β : Type*} {f : α → R} {g : β → M}
    (hf : Tendsto f cofinite (𝓝 0)) (hg : Tendsto g cofinite (𝓝 0)) :
    Tendsto (fun ij : α × β ↦ f ij.1 • g ij.2) cofinite (𝓝 0) :=
  squeeze_zero_norm (fun ij ↦ norm_smul_le (f ij.1) (g ij.2))
    (tendsto_mul_cofinite_nhds_zero (by simpa using hf.norm) (by simpa using hg.norm))

variable [SeminormedAddCommGroup M] [IsUltrametricDist M]

section SMul

variable [SeminormedAddCommGroup R] [SMulZeroClass R M] [IsBoundedSMul R M] [CompleteSpace M]

/-- In a complete ultrametric normed group with a bounded scalar action, the pointwise scalar
multiples of two summable families are summable on the product index. -/
theorem _root_.Summable.smul_of_nonarchimedean {α β : Type*} {f : α → R} {g : β → M}
    (hf : Summable f) (hg : Summable g) :
    Summable fun ij : α × β ↦ f ij.1 • g ij.2 :=
  (NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero _).mpr <|
    hf.tendsto_cofinite_zero.smul_cofinite_nhds_zero hg.tendsto_cofinite_zero

variable {A : Type*} [Add A] [Finset.HasAntidiagonal A]

private theorem summable_smul_sigma_antidiagonal_of_nonarchimedean {f : A → R} {g : A → M}
    (hf : Summable f) (hg : Summable g) :
    Summable fun ij : Σ n : A, Finset.antidiagonal n ↦
      f (ij.2 : A × A).1 • g (ij.2 : A × A).2 :=
  Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff.mpr
    (hf.smul_of_nonarchimedean hg)

/-- In a complete ultrametric normed group with a bounded scalar action, the antidiagonal Cauchy
product of two summable families is summable. -/
theorem _root_.Summable.sum_smul_antidiagonal_of_nonarchimedean {f : A → R} {g : A → M}
    (hf : Summable f) (hg : Summable g) :
    Summable fun n ↦ ∑ ij ∈ Finset.antidiagonal n, f ij.1 • g ij.2 := by
  simp_rw [← Finset.tsum_subtype]
  exact (summable_smul_sigma_antidiagonal_of_nonarchimedean hf hg).sigma' fun n ↦
    (hasSum_fintype _).summable

/-- In a complete ultrametric normed group with a bounded scalar action, the usual natural-number
Cauchy product of two summable families is summable. -/
theorem _root_.Summable.sum_smul_range_of_nonarchimedean {f : ℕ → R} {g : ℕ → M}
    (hf : Summable f) (hg : Summable g) :
    Summable fun n ↦ ∑ k ∈ Finset.range (n + 1), f k • g (n - k) := by
  simp_rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ fun k l ↦ f k • g l]
  exact hf.sum_smul_antidiagonal_of_nonarchimedean hg

end SMul

section Module

variable [SeminormedRing R] [Module R M] [IsBoundedSMul R M]

/-- Scalar multiplication distributes over two infinite sums in an ultrametric normed module. -/
theorem _root_.HasSum.smul_of_nonarchimedean {α β : Type*} {f : α → R} {g : β → M} {a : R}
    {b : M} (hf : HasSum f a) (hg : HasSum g b) :
    HasSum (fun ij : α × β ↦ f ij.1 • g ij.2) (a • b) := by
  have hg' := (hasSum_iff_hasSum_compl g b).mpr hg
  simp only [Function.comp_def, UniformSpace.Completion.toCompl_apply] at hg'
  rw [← hasSum_iff_hasSum_compl]
  simpa only [Function.comp_def, UniformSpace.Completion.toCompl_apply,
    UniformSpace.Completion.coe_smul] using
    hf.smul hg' (hf.summable.smul_of_nonarchimedean hg'.summable)

/-- The scalar multiple of two infinite sums in a Hausdorff ultrametric normed module is their
double sum. -/
protected theorem _root_.Summable.tsum_smul_tsum_of_nonarchimedean [T0Space M] {α β : Type*}
    {f : α → R} {g : β → M} (hf : Summable f) (hg : Summable g) :
    (∑' i, f i) • (∑' j, g j) = ∑' ij : α × β, f ij.1 • g ij.2 :=
  (hf.hasSum.smul_of_nonarchimedean hg.hasSum).tsum_eq.symm

section CauchyProduct

variable {A : Type*} [Add A] [Finset.HasAntidiagonal A]

/-- In an ultrametric normed module, the antidiagonal Cauchy product sums to the scalar multiple
of the original two sums. -/
theorem _root_.HasSum.sum_smul_antidiagonal_of_nonarchimedean {f : A → R} {g : A → M} {a : R}
    {b : M} (hf : HasSum f a) (hg : HasSum g b) :
    HasSum (fun n ↦ ∑ ij ∈ Finset.antidiagonal n, f ij.1 • g ij.2) (a • b) := by
  have hsigma := Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff.mpr
    (hf.smul_of_nonarchimedean hg)
  exact hsigma.sigma fun n ↦ Finset.hasSum (Finset.antidiagonal n) fun ij ↦ f ij.1 • g ij.2

/-- The Cauchy-product formula for the scalar multiple of two infinite sums, grouped over the
antidiagonals of an additive index type, in a Hausdorff ultrametric normed module. -/
protected theorem _root_.Summable.tsum_smul_tsum_eq_tsum_sum_antidiagonal_of_nonarchimedean
    [T0Space M] {f : A → R} {g : A → M} (hf : Summable f) (hg : Summable g) :
    (∑' n, f n) • (∑' n, g n) =
      ∑' n, ∑ ij ∈ Finset.antidiagonal n, f ij.1 • g ij.2 :=
  (hf.hasSum.sum_smul_antidiagonal_of_nonarchimedean hg.hasSum).tsum_eq.symm

end CauchyProduct

section Nat

/-- The natural-number Cauchy-product formula for the scalar multiple of two infinite sums, in a
Hausdorff ultrametric normed module. -/
protected theorem _root_.Summable.tsum_smul_tsum_eq_tsum_sum_range_of_nonarchimedean
    [T0Space M] {f : ℕ → R} {g : ℕ → M} (hf : Summable f) (hg : Summable g) :
    (∑' n, f n) • (∑' n, g n) =
      ∑' n, ∑ k ∈ Finset.range (n + 1), f k • g (n - k) := by
  simp_rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ fun k l ↦ f k • g l]
  exact hf.tsum_smul_tsum_eq_tsum_sum_antidiagonal_of_nonarchimedean hg

/-- In an ultrametric normed module, the natural-number Cauchy product sums to the scalar multiple
of the original two sums. -/
theorem _root_.HasSum.sum_smul_range_of_nonarchimedean {f : ℕ → R} {g : ℕ → M}
    {a : R} {b : M} (hf : HasSum f a) (hg : HasSum g b) :
    HasSum (fun n ↦ ∑ k ∈ Finset.range (n + 1), f k • g (n - k)) (a • b) := by
  simp_rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ fun k l ↦ f k • g l]
  exact hf.sum_smul_antidiagonal_of_nonarchimedean hg

end Nat

end Module

end TauCeti

end
