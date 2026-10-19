/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import Mathlib.Analysis.Normed.Group.Ultra

/-!
# Bounded bilinear maps and nonarchimedean sums

A bilinear map with bound `‖B x y‖ ≤ C * ‖x‖ * ‖y‖` takes two cofinite-null
families to a cofinite-null family on the product index. When the target is complete
and ultrametric, this proves summability before exchanging the two sums. Grouping by
antidiagonals gives the bilinear Cauchy-product formula, including empty index types.

The scalar ring need not be a field or carry a norm: the explicit bilinear bound
supplies all the continuity used here. Neither source module needs to be complete or
ultrametric. Only the sum identities require a Hausdorff target.

The proofs use Mathlib's nonarchimedean summability criterion and fiberwise summation.
The double-sum argument follows `HasSum.mul_eq` in
`Mathlib.Topology.Algebra.InfiniteSum.Ring`, with bounded bilinear maps in place of
multiplication. No absolute summability of the norms is required.
-/

public section

namespace TauCeti

open Filter
open scoped Topology BigOperators

variable {R E F G ι κ : Type*}
variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
  [SeminormedAddCommGroup G]

/-- A map bounded by a product of norms takes two cofinite-null families to a
jointly cofinite-null family. No additivity or ultrametric hypothesis is needed. -/
theorem tendsto_bilinear_cofinite_zero (B : E → F → G) {C : ℝ}
    (hB : ∀ x y, ‖B x y‖ ≤ C * ‖x‖ * ‖y‖)
    {f : ι → E} {g : κ → F} (hf : Tendsto f cofinite (𝓝 0))
    (hg : Tendsto g cofinite (𝓝 0)) :
    Tendsto (fun ij : ι × κ ↦ B (f ij.1) (g ij.2)) cofinite (𝓝 0) := by
  have hprod := tendsto_mul_cofinite_nhds_zero
    (by simpa using hf.norm) (by simpa using hg.norm)
  apply squeeze_zero_norm (fun ij : ι × κ ↦ hB (f ij.1) (g ij.2))
  simpa only [mul_assoc, mul_zero] using hprod.const_mul C

variable [IsUltrametricDist G]

/-- Two summable families have a summable family of bilinear images in a complete
ultrametric target. The norm bound, rather than additivity, gives summability. -/
theorem summable_bilinear_of_nonarchimedean [CompleteSpace G]
    (B : E → F → G) {C : ℝ} (hB : ∀ x y, ‖B x y‖ ≤ C * ‖x‖ * ‖y‖)
    {f : ι → E} {g : κ → F} (hf : Summable f) (hg : Summable g) :
    Summable fun ij : ι × κ ↦ B (f ij.1) (g ij.2) :=
  NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero <|
    tendsto_bilinear_cofinite_zero B hB hf.tendsto_cofinite_zero hg.tendsto_cofinite_zero

section Summability

variable (B : E → F → G) {C : ℝ} (hB : ∀ x y, ‖B x y‖ ≤ C * ‖x‖ * ‖y‖)

include hB

variable {A : Type*} [AddCommMonoid A] [Finset.HasAntidiagonal A]

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

section Bilinear

variable [CommRing R] [Module R E] [Module R F] [Module R G]
variable (B : E →ₗ[R] F →ₗ[R] G) {C : ℝ}
    (hB : ∀ x y, ‖B x y‖ ≤ C * ‖x‖ * ‖y‖)

include hB

/-- A bounded bilinear map commutes with two sums in a complete Hausdorff
ultrametric target, with the sum taken over the product index. -/
theorem hasSum_bilinear_of_nonarchimedean [CompleteSpace G] [T0Space G]
    {f : ι → E} {g : κ → F} {a : E} {b : F} (hf : HasSum f a) (hg : HasSum g b) :
    HasSum (fun ij : ι × κ ↦ B (f ij.1) (g ij.2)) (B a b) := by
  have hfg := summable_bilinear_of_nonarchimedean (fun x y ↦ B x y) hB
    hf.summable hg.summable
  have hright (x : E) : HasSum (fun j ↦ B x (g j)) (B x b) := by
    exact (B x |>.mkContinuous (C * ‖x‖) (hB x)).hasSum hg
  have hleft : HasSum (fun i ↦ B (f i) b) (B a b) := by
    exact (B.flip b |>.mkContinuous (C * ‖b‖)
      (fun x ↦ by simpa only [LinearMap.flip_apply, mul_right_comm] using hB x b)).hasSum hf
  exact (hleft.unique (hfg.hasSum.prod_fiberwise (fun i ↦ hright (f i)))) ▸ hfg.hasSum

/-- Evaluating a bounded bilinear map on two infinite sums equals its double sum. -/
theorem bilinear_tsum_tsum_of_nonarchimedean [CompleteSpace G] [T0Space G]
    {f : ι → E} {g : κ → F} (hf : Summable f) (hg : Summable g) :
    B (∑' i, f i) (∑' j, g j) = ∑' ij : ι × κ, B (f ij.1) (g ij.2) :=
  (hasSum_bilinear_of_nonarchimedean B hB hf.hasSum hg.hasSum).tsum_eq.symm

section CauchyProduct

variable {A : Type*} [AddCommMonoid A] [Finset.HasAntidiagonal A]

/-- Grouping a bilinear double sum by antidiagonals preserves its sum. -/
theorem hasSum_sum_bilinear_antidiagonal_of_nonarchimedean [CompleteSpace G] [T0Space G]
    {f : A → E} {g : A → F} {a : E} {b : F} (hf : HasSum f a) (hg : HasSum g b) :
    HasSum (fun n ↦ ∑ ij ∈ Finset.antidiagonal n, B (f ij.1) (g ij.2)) (B a b) := by
  have hsigma := Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff.mpr
    (hasSum_bilinear_of_nonarchimedean B hB hf hg)
  exact hsigma.sigma fun n ↦ Finset.hasSum (Finset.antidiagonal n)
    fun ij ↦ B (f ij.1) (g ij.2)

/-- The bilinear Cauchy-product formula for an additive index monoid. -/
theorem bilinear_tsum_tsum_eq_tsum_sum_antidiagonal_of_nonarchimedean
    [CompleteSpace G] [T0Space G] {f : A → E} {g : A → F}
    (hf : Summable f) (hg : Summable g) :
    B (∑' n, f n) (∑' n, g n) =
      ∑' n, ∑ ij ∈ Finset.antidiagonal n, B (f ij.1) (g ij.2) :=
  (hasSum_sum_bilinear_antidiagonal_of_nonarchimedean B hB hf.hasSum hg.hasSum).tsum_eq.symm

end CauchyProduct

/-- The natural-number bilinear Cauchy product sums to the image of the two sums. -/
theorem hasSum_sum_bilinear_range_of_nonarchimedean [CompleteSpace G] [T0Space G]
    {f : ℕ → E} {g : ℕ → F} {a : E} {b : F} (hf : HasSum f a) (hg : HasSum g b) :
    HasSum (fun n ↦ ∑ k ∈ Finset.range (n + 1), B (f k) (g (n - k))) (B a b) := by
  simp_rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ fun k l ↦ B (f k) (g l)]
  exact hasSum_sum_bilinear_antidiagonal_of_nonarchimedean B hB hf hg

/-- The natural-number bilinear Cauchy-product formula. -/
theorem bilinear_tsum_tsum_eq_tsum_sum_range_of_nonarchimedean
    [CompleteSpace G] [T0Space G] {f : ℕ → E} {g : ℕ → F}
    (hf : Summable f) (hg : Summable g) :
    B (∑' n, f n) (∑' n, g n) =
      ∑' n, ∑ k ∈ Finset.range (n + 1), B (f k) (g (n - k)) := by
  simp_rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ fun k l ↦ B (f k) (g l)]
  exact bilinear_tsum_tsum_eq_tsum_sum_antidiagonal_of_nonarchimedean B hB hf hg

end Bilinear

end TauCeti
