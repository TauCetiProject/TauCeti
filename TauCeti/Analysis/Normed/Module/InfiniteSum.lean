/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Completion
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import Mathlib.Topology.Algebra.InfiniteSum.GroupCompletion
public import TauCeti.Topology.MetricSpace.Ultra.Completion

/-!
# Bounded bilinear maps and infinite sums in ultrametric normed modules

A map bounded by a product of norms takes two cofinite-null families to a cofinite-null family
on the product index. In a complete ultrametric target this gives summability; when the map is
bilinear, passage to the completion gives double-sum and Cauchy-product identities without
completeness. In the sum identities, the bilinear map is inferred from its norm bound.
The scalar ring need not carry a norm, and neither source module needs to be
complete or ultrametric. The double-sum argument follows `HasSum.mul_eq` in
`Mathlib.Topology.Algebra.InfiniteSum.Ring`, with bounded bilinear maps in place of multiplication.

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

section Bilinear

variable {R E F G ι κ : Type*}

section Decay

variable [SeminormedAddGroup E] [SeminormedAddGroup F] [SeminormedAddGroup G]

/-- A map bounded by a product of norms takes two cofinite-null families to a
jointly cofinite-null family. No additivity or ultrametric hypothesis is needed. -/
theorem tendsto_bilinear_cofinite_nhds_zero (B : E → F → G) {C : ℝ}
    (hB : ∀ x y, ‖B x y‖ ≤ C * ‖x‖ * ‖y‖)
    {f : ι → E} {g : κ → F} (hf : Tendsto f cofinite (𝓝 0))
    (hg : Tendsto g cofinite (𝓝 0)) :
    Tendsto (fun ij : ι × κ ↦ B (f ij.1) (g ij.2)) cofinite (𝓝 0) := by
  have hprod := tendsto_mul_cofinite_nhds_zero
    (by simpa using hf.norm) (by simpa using hg.norm)
  apply squeeze_zero_norm (fun ij : ι × κ ↦ hB (f ij.1) (g ij.2))
  simpa only [mul_assoc, mul_zero] using hprod.const_mul C

end Decay

variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
  [SeminormedAddCommGroup G] [IsUltrametricDist G]

/-- Two summable families have a summable family of bilinear images in a complete
ultrametric target. The norm bound, rather than additivity, gives summability. -/
theorem summable_bilinear_of_nonarchimedean [CompleteSpace G]
    (B : E → F → G) {C : ℝ} (hB : ∀ x y, ‖B x y‖ ≤ C * ‖x‖ * ‖y‖)
    {f : ι → E} {g : κ → F} (hf : Summable f) (hg : Summable g) :
    Summable fun ij : ι × κ ↦ B (f ij.1) (g ij.2) :=
  NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero <|
    tendsto_bilinear_cofinite_nhds_zero B hB hf.tendsto_cofinite_zero hg.tendsto_cofinite_zero

section Summability

variable (B : E → F → G) {C : ℝ} (hB : ∀ x y, ‖B x y‖ ≤ C * ‖x‖ * ‖y‖)

include hB

variable {A : Type*} [Add A] [Finset.HasAntidiagonal A]

/-- The antidiagonal Cauchy product is summable under a bilinear norm bound.
Additivity of the map is not needed for this assertion. -/
theorem summable_sum_bilinear_antidiagonal_of_nonarchimedean [CompleteSpace G]
    {f : A → E} {g : A → F} (hf : Summable f) (hg : Summable g) :
    Summable fun n ↦ ∑ ij ∈ Finset.antidiagonal n, B (f ij.1) (g ij.2) := by
  simp_rw [← Finset.tsum_subtype]
  have hsigma := Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff.mpr
    (summable_bilinear_of_nonarchimedean B hB hf hg)
  exact hsigma.sigma' fun n ↦ (hasSum_fintype _).summable

/-- The usual natural-number Cauchy product is summable under a bilinear norm bound. -/
theorem summable_sum_bilinear_range_of_nonarchimedean [CompleteSpace G]
    {f : ℕ → E} {g : ℕ → F} (hf : Summable f) (hg : Summable g) :
    Summable fun n ↦ ∑ k ∈ Finset.range (n + 1), B (f k) (g (n - k)) := by
  simp_rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ fun k l ↦ B (f k) (g l)]
  exact summable_sum_bilinear_antidiagonal_of_nonarchimedean B hB hf hg

end Summability

section BilinearIdentities

variable [CommRing R] [Module R E] [Module R F] [Module R G]
variable {B : E →ₗ[R] F →ₗ[R] G} {C : ℝ}
    (hB : ∀ x y, ‖B x y‖ ≤ C * ‖x‖ * ‖y‖)

include hB

/-- A bounded bilinear map commutes with two sums in an ultrametric target,
with the sum taken over the product index. -/
theorem hasSum_bilinear_of_nonarchimedean
    {f : ι → E} {g : κ → F} {a : E} {b : F} (hf : HasSum f a) (hg : HasSum g b) :
    HasSum (fun ij : ι × κ ↦ B (f ij.1) (g ij.2)) (B a b) := by
  let c := UniformSpace.Completion.toCompl (α := G)
  have hbound (x : E) (y : F) : ‖c (B x y)‖ ≤ C * ‖x‖ * ‖y‖ := by
    simpa only [c, UniformSpace.Completion.toCompl_apply, UniformSpace.Completion.norm_coe]
      using hB x y
  have hfg := summable_bilinear_of_nonarchimedean (fun x y ↦ c (B x y)) hbound
    hf.summable hg.summable
  have hright (x : E) : HasSum (fun j ↦ c (B x (g j))) (c (B x b)) := by
    exact ((B x |>.mkContinuous (C * ‖x‖) (hB x)).hasSum hg).map c
      UniformSpace.Completion.continuous_toCompl
  have hleft : HasSum (fun i ↦ c (B (f i) b)) (c (B a b)) := by
    exact ((B.flip b |>.mkContinuous (C * ‖b‖)
      (fun x ↦ by simpa only [LinearMap.flip_apply, mul_right_comm] using hB x b)).hasSum hf).map
      c UniformSpace.Completion.continuous_toCompl
  have hsum : HasSum (fun ij : ι × κ ↦ c (B (f ij.1) (g ij.2))) (c (B a b)) :=
    (hleft.unique (hfg.hasSum.prod_fiberwise (fun i ↦ hright (f i)))) ▸ hfg.hasSum
  rw [← hasSum_iff_hasSum_compl]
  simpa only [Function.comp_def, c, UniformSpace.Completion.toCompl_apply] using hsum

/-- Evaluating a bounded bilinear map on two infinite sums equals its double sum. -/
theorem bilinear_tsum_tsum_of_nonarchimedean [T0Space G]
    {f : ι → E} {g : κ → F} (hf : Summable f) (hg : Summable g) :
    B (∑' i, f i) (∑' j, g j) = ∑' ij : ι × κ, B (f ij.1) (g ij.2) :=
  (hasSum_bilinear_of_nonarchimedean hB hf.hasSum hg.hasSum).tsum_eq.symm

section CauchyProduct

variable {A : Type*} [Add A] [Finset.HasAntidiagonal A]

/-- Grouping a bilinear double sum by antidiagonals preserves its sum. -/
theorem hasSum_sum_bilinear_antidiagonal_of_nonarchimedean
    {f : A → E} {g : A → F} {a : E} {b : F} (hf : HasSum f a) (hg : HasSum g b) :
    HasSum (fun n ↦ ∑ ij ∈ Finset.antidiagonal n, B (f ij.1) (g ij.2)) (B a b) := by
  have hsigma := Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff.mpr
    (hasSum_bilinear_of_nonarchimedean hB hf hg)
  exact hsigma.sigma fun n ↦ Finset.hasSum (Finset.antidiagonal n)
    fun ij ↦ B (f ij.1) (g ij.2)

/-- The bilinear Cauchy-product formula for an additive index type. -/
theorem bilinear_tsum_tsum_eq_tsum_sum_antidiagonal_of_nonarchimedean
    [T0Space G] {f : A → E} {g : A → F}
    (hf : Summable f) (hg : Summable g) :
    B (∑' n, f n) (∑' n, g n) =
      ∑' n, ∑ ij ∈ Finset.antidiagonal n, B (f ij.1) (g ij.2) :=
  (hasSum_sum_bilinear_antidiagonal_of_nonarchimedean hB hf.hasSum hg.hasSum).tsum_eq.symm

end CauchyProduct

/-- The natural-number bilinear Cauchy product sums to the image of the two sums. -/
theorem hasSum_sum_bilinear_range_of_nonarchimedean
    {f : ℕ → E} {g : ℕ → F} {a : E} {b : F} (hf : HasSum f a) (hg : HasSum g b) :
    HasSum (fun n ↦ ∑ k ∈ Finset.range (n + 1), B (f k) (g (n - k))) (B a b) := by
  simp_rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ fun k l ↦ B (f k) (g l)]
  exact hasSum_sum_bilinear_antidiagonal_of_nonarchimedean hB hf hg

/-- The natural-number bilinear Cauchy-product formula. -/
theorem bilinear_tsum_tsum_eq_tsum_sum_range_of_nonarchimedean
    [T0Space G] {f : ℕ → E} {g : ℕ → F}
    (hf : Summable f) (hg : Summable g) :
    B (∑' n, f n) (∑' n, g n) =
      ∑' n, ∑ k ∈ Finset.range (n + 1), B (f k) (g (n - k)) := by
  simp_rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ fun k l ↦ B (f k) (g l)]
  exact bilinear_tsum_tsum_eq_tsum_sum_antidiagonal_of_nonarchimedean hB hf hg

end BilinearIdentities

end Bilinear

variable {R M : Type*}

private theorem norm_smul_le_one_mul [SeminormedAddGroup R] [SeminormedAddGroup M]
    [SMulZeroClass R M] [IsBoundedSMul R M] (x : R) (y : M) :
    ‖x • y‖ ≤ 1 * ‖x‖ * ‖y‖ := by
  simpa only [one_mul] using norm_smul_le x y

/-- If two normed families tend to zero cofinitely, then their pointwise scalar multiples, indexed
by pairs, also tend to zero cofinitely. -/
theorem _root_.Filter.Tendsto.smul_cofinite_nhds_zero [SeminormedAddGroup R] [SeminormedAddGroup M]
    [SMulZeroClass R M] [IsBoundedSMul R M] {α β : Type*} {f : α → R} {g : β → M}
    (hf : Tendsto f cofinite (𝓝 0)) (hg : Tendsto g cofinite (𝓝 0)) :
    Tendsto (fun ij : α × β ↦ f ij.1 • g ij.2) cofinite (𝓝 0) :=
  tendsto_bilinear_cofinite_nhds_zero (· • ·) (C := 1)
    norm_smul_le_one_mul hf hg

variable [SeminormedAddCommGroup M] [IsUltrametricDist M]

section SMul

variable [SeminormedAddCommGroup R] [SMulZeroClass R M] [IsBoundedSMul R M] [CompleteSpace M]

/-- In a complete ultrametric normed group with a bounded scalar action, the pointwise scalar
multiples of two summable families are summable on the product index. -/
theorem _root_.Summable.smul_of_nonarchimedean {α β : Type*} {f : α → R} {g : β → M}
    (hf : Summable f) (hg : Summable g) :
    Summable fun ij : α × β ↦ f ij.1 • g ij.2 :=
  summable_bilinear_of_nonarchimedean (· • ·) (C := 1)
    norm_smul_le_one_mul hf hg

variable {A : Type*} [Add A] [Finset.HasAntidiagonal A]

/-- In a complete ultrametric normed group with a bounded scalar action, the antidiagonal Cauchy
product of two summable families is summable. -/
theorem _root_.Summable.sum_smul_antidiagonal_of_nonarchimedean {f : A → R} {g : A → M}
    (hf : Summable f) (hg : Summable g) :
    Summable fun n ↦ ∑ ij ∈ Finset.antidiagonal n, f ij.1 • g ij.2 :=
  summable_sum_bilinear_antidiagonal_of_nonarchimedean (· • ·) (C := 1)
    norm_smul_le_one_mul hf hg

/-- In a complete ultrametric normed group with a bounded scalar action, the usual natural-number
Cauchy product of two summable families is summable. -/
theorem _root_.Summable.sum_smul_range_of_nonarchimedean {f : ℕ → R} {g : ℕ → M}
    (hf : Summable f) (hg : Summable g) :
    Summable fun n ↦ ∑ k ∈ Finset.range (n + 1), f k • g (n - k) :=
  summable_sum_bilinear_range_of_nonarchimedean (· • ·) (C := 1)
    norm_smul_le_one_mul hf hg

end SMul

section Module

variable [SeminormedRing R] [Module R M] [IsBoundedSMul R M]

omit [IsUltrametricDist M] in
private theorem norm_lsmul_le (r : R) (m : M) :
    ‖(Algebra.lsmul ℤ ℤ M : R →ₐ[ℤ] Module.End ℤ M).toLinearMap r m‖ ≤
      1 * ‖r‖ * ‖m‖ := by
  simpa only [AlgHom.toLinearMap_apply, Algebra.lsmul_apply, one_mul] using norm_smul_le r m

/-- Scalar multiplication distributes over two infinite sums in an ultrametric normed module. -/
theorem _root_.HasSum.smul_of_nonarchimedean {α β : Type*} {f : α → R} {g : β → M} {a : R}
    {b : M} (hf : HasSum f a) (hg : HasSum g b) :
    HasSum (fun ij : α × β ↦ f ij.1 • g ij.2) (a • b) := by
  simpa only [AlgHom.toLinearMap_apply, Algebra.lsmul_apply] using
    hasSum_bilinear_of_nonarchimedean norm_lsmul_le hf hg

/-- The scalar multiple of two infinite sums in a Hausdorff ultrametric normed module is their
double sum. -/
protected theorem _root_.Summable.tsum_smul_tsum_of_nonarchimedean [T0Space M] {α β : Type*}
    {f : α → R} {g : β → M} (hf : Summable f) (hg : Summable g) :
    (∑' i, f i) • (∑' j, g j) = ∑' ij : α × β, f ij.1 • g ij.2 := by
  simpa only [AlgHom.toLinearMap_apply, Algebra.lsmul_apply] using
    bilinear_tsum_tsum_of_nonarchimedean norm_lsmul_le hf hg

section CauchyProduct

variable {A : Type*} [Add A] [Finset.HasAntidiagonal A]

/-- In an ultrametric normed module, the antidiagonal Cauchy product sums to the scalar multiple
of the original two sums. -/
theorem _root_.HasSum.sum_smul_antidiagonal_of_nonarchimedean {f : A → R} {g : A → M} {a : R}
    {b : M} (hf : HasSum f a) (hg : HasSum g b) :
    HasSum (fun n ↦ ∑ ij ∈ Finset.antidiagonal n, f ij.1 • g ij.2) (a • b) := by
  simpa only [AlgHom.toLinearMap_apply, Algebra.lsmul_apply] using
    hasSum_sum_bilinear_antidiagonal_of_nonarchimedean
      norm_lsmul_le hf hg

/-- The Cauchy-product formula for the scalar multiple of two infinite sums, grouped over the
antidiagonals of an additive index type, in a Hausdorff ultrametric normed module. -/
protected theorem _root_.Summable.tsum_smul_tsum_eq_tsum_sum_antidiagonal_of_nonarchimedean
    [T0Space M] {f : A → R} {g : A → M} (hf : Summable f) (hg : Summable g) :
    (∑' n, f n) • (∑' n, g n) =
      ∑' n, ∑ ij ∈ Finset.antidiagonal n, f ij.1 • g ij.2 := by
  simpa only [AlgHom.toLinearMap_apply, Algebra.lsmul_apply] using
    bilinear_tsum_tsum_eq_tsum_sum_antidiagonal_of_nonarchimedean
      norm_lsmul_le hf hg

end CauchyProduct

section Nat

/-- The natural-number Cauchy-product formula for the scalar multiple of two infinite sums, in a
Hausdorff ultrametric normed module. -/
protected theorem _root_.Summable.tsum_smul_tsum_eq_tsum_sum_range_of_nonarchimedean
    [T0Space M] {f : ℕ → R} {g : ℕ → M} (hf : Summable f) (hg : Summable g) :
    (∑' n, f n) • (∑' n, g n) =
      ∑' n, ∑ k ∈ Finset.range (n + 1), f k • g (n - k) := by
  simpa only [AlgHom.toLinearMap_apply, Algebra.lsmul_apply] using
    bilinear_tsum_tsum_eq_tsum_sum_range_of_nonarchimedean
      norm_lsmul_le hf hg

/-- In an ultrametric normed module, the natural-number Cauchy product sums to the scalar multiple
of the original two sums. -/
theorem _root_.HasSum.sum_smul_range_of_nonarchimedean {f : ℕ → R} {g : ℕ → M}
    {a : R} {b : M} (hf : HasSum f a) (hg : HasSum g b) :
    HasSum (fun n ↦ ∑ k ∈ Finset.range (n + 1), f k • g (n - k)) (a • b) := by
  simpa only [AlgHom.toLinearMap_apply, Algebra.lsmul_apply] using
    hasSum_sum_bilinear_range_of_nonarchimedean
      norm_lsmul_le hf hg

end Nat

end Module

end TauCeti

end
