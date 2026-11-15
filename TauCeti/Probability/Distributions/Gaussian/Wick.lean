/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Combinatorics.Enumerative.PerfectMatching.Weighted
public import TauCeti.Probability.Distributions.Gaussian.MomentRecursion
import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-!
# Wick--Isserlis formula for Gaussian mixed moments

The centered mixed moment of finitely many linear observables of a Gaussian measure is the
sum, over perfect matchings of the positions, of the product of the covariances along the
matching. The formula is indexed by positions, so observables and coordinates may repeat. It
also covers empty products, odd degrees, and singular positive-semidefinite covariances.

## Main results

* `ProbabilityTheory.IsGaussian.integral_prod_sub_dual_eq_sum_perfectMatching` is the
  abstract Wick--Isserlis formula for linear observables of a Gaussian measure.
* `ProbabilityTheory.HasGaussianLaw.integral_prod_sub_eq_sum_perfectMatching` transfers
  the formula to jointly Gaussian random variables on an arbitrary measurable space.
* `TauCeti.Probability.integral_prod_sub_multivariateGaussian_eq_sum_perfectMatching`
  specializes the formula to coordinates of a multivariate Gaussian measure.
* `ProbabilityTheory.HasLaw.integral_prod_sub_multivariateGaussian_eq_sum_perfectMatching`
  transfers the coordinate formula to a random vector with that law.

The proof combines the Gaussian contraction recurrence with the recurrence for weighted
perfect matchings at a distinguished vertex.

## References

* L. Isserlis, *On a formula for the product-moment coefficient of any order of a normal
  frequency distribution in any number of variables*, Biometrika 12 (1918), 134--139.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Finset

namespace ProbabilityTheory.IsGaussian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Wick--Isserlis formula.** A centered mixed moment of finitely many linear observables of
a Gaussian measure is the sum of covariance products over perfect matchings of the positions.
The statement includes empty and odd position types. -/
theorem integral_prod_sub_dual_eq_sum_perfectMatching (μ : Measure E) [IsGaussian μ]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (L : ι → StrongDual ℝ E) :
    (∫ x, ∏ i, (L i x - μ[L i]) ∂μ) =
      ∑ D : TauCeti.PerfectMatching ι, ∏ e ∈ D.edgeFinset,
        Sym2.lift ⟨fun i j ↦ cov[L i, L j; μ],
          fun i j ↦ covariance_comm (L i) (L j)⟩ e := by
  classical
  induction hn : Fintype.card ι using Nat.strong_induction_on generalizing ι with
  | _ n ih =>
    let w : Sym2 ι → ℝ :=
      Sym2.lift ⟨fun i j ↦ cov[L i, L j; μ],
        fun i j ↦ covariance_comm (L i) (L j)⟩
    rcases isEmpty_or_nonempty ι with hι | ⟨⟨a⟩⟩
    · simp
    · calc
        _ = ∫ x, (L a x - μ[L a]) * ∏ i ∈ univ.erase a, (L i x - μ[L i]) ∂μ := by
          congr 2 with x
          exact (Finset.mul_prod_erase _ _ (mem_univ a)).symm
        _ = ∑ b ∈ univ.erase a, cov[L a, L b; μ] *
            ∫ x, ∏ j ∈ (univ.erase a).erase b, (L j x - μ[L j]) ∂μ :=
          integral_sub_dual_mul_prod_sub_dual μ (univ.erase a) (L a) L
        _ = ∑ b : {b : ι // b ≠ a}, cov[L a, L b; μ] *
            ∫ x, ∏ j : {x : ι // x ≠ a ∧ x ≠ b}, (L j x - μ[L j]) ∂μ := by
          rw [Finset.sum_subtype (p := fun b : ι ↦ b ≠ a) (univ.erase a) (by simp)]
          apply Finset.sum_congr rfl
          intro b _
          congr 1
          apply integral_congr_ae
          filter_upwards with x
          exact Finset.prod_subtype ((univ.erase a).erase b) (by simp [and_comm]) _
        _ = ∑ b : {b : ι // b ≠ a}, w s(a, b.val) *
            ∑ D : TauCeti.PerfectMatching {x : ι // x ≠ a ∧ x ≠ b.val},
              ∏ e ∈ D.edgeFinset, w (Sym2.map Subtype.val e) := by
          apply Finset.sum_congr rfl
          intro b _
          have hcard : Fintype.card {x : ι // x ≠ a ∧ x ≠ b.val} < n := by
            rw [← hn]
            exact Fintype.card_subtype_lt
              (p := fun x : ι ↦ x ≠ a ∧ x ≠ b.val) (x := a) (by simp)
          have hih := ih _ hcard
            (fun j : {x : ι // x ≠ a ∧ x ≠ b.val} ↦ L j) rfl
          rw [hih]
          congr 1
          apply Finset.sum_congr rfl
          intro D _
          apply Finset.prod_congr rfl
          intro e _
          induction e using Sym2.inductionOn with
          | _ i j => rfl
        _ = _ := (TauCeti.PerfectMatching.sum_prod_edgeFinset_eq_sum_mul_sum w a).symm

end ProbabilityTheory.IsGaussian

namespace ProbabilityTheory.HasGaussianLaw

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
  {P : Measure Ω} {X : Ω → ι → ℝ}

/-- **Wick–Isserlis formula for jointly Gaussian random variables.** Joint Gaussianity is
required; Gaussian marginal laws alone do not suffice. Arbitrary means and correlations,
repeated coordinates, and degenerate laws are allowed. -/
theorem integral_prod_sub_eq_sum_perfectMatching (hX : HasGaussianLaw X P) :
    (∫ ω, ∏ i, (X ω i - ∫ ω', X ω' i ∂P) ∂P) =
      ∑ D : TauCeti.PerfectMatching ι, ∏ e ∈ D.edgeFinset,
        Sym2.lift ⟨fun i j ↦ cov[fun ω ↦ X ω i, fun ω ↦ X ω j; P],
          fun _ _ ↦ covariance_comm _ _⟩ e := by
  let := hX.isGaussian_map
  have hmean (i : ι) :
      (P.map X)[(ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)] = ∫ ω, X ω i ∂P := by
    rw [integral_map hX.aemeasurable
      (ContinuousLinearMap.proj i).continuous.aestronglyMeasurable]
    rfl
  have hcov (i j : ι) :
      cov[(ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ),
        (ContinuousLinearMap.proj j : (ι → ℝ) →L[ℝ] ℝ); P.map X] =
        cov[fun ω ↦ X ω i, fun ω ↦ X ω j; P] := by
    rw [covariance_map (by fun_prop) (by fun_prop) hX.aemeasurable]
    rfl
  have h := IsGaussian.integral_prod_sub_dual_eq_sum_perfectMatching (P.map X)
    (fun i ↦ ContinuousLinearMap.proj i)
  simp only [hmean, hcov] at h
  rw [integral_map hX.aemeasurable (by fun_prop)] at h
  simpa only [ContinuousLinearMap.proj_apply] using h

end ProbabilityTheory.HasGaussianLaw

namespace TauCeti.Probability

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The Wick--Isserlis formula for centered coordinates of a multivariate Gaussian measure.
Positions may select repeated coordinates, and the covariance matrix may be singular. -/
theorem integral_prod_sub_multivariateGaussian_eq_sum_perfectMatching
    (m : EuclideanSpace ℝ κ) {S : Matrix κ κ ℝ} (hS : S.PosSemidef) (f : ι → κ) :
    (∫ x, ∏ i, (x (f i) - m (f i)) ∂multivariateGaussian m S) =
      ∑ D : PerfectMatching ι, ∏ e ∈ D.edgeFinset,
        Sym2.lift ⟨fun i j ↦ S (f i) (f j),
          fun i j ↦ by simpa using hS.isHermitian.apply (f j) (f i)⟩ e := by
  have h := IsGaussian.integral_prod_sub_dual_eq_sum_perfectMatching
    (multivariateGaussian m S) (fun i ↦ EuclideanSpace.proj (f i))
  simp_rw [IsGaussian.integral_dual, integral_id_multivariateGaussian] at h
  have hcov (i j : ι) :
      cov[(fun x : EuclideanSpace ℝ κ ↦ x (f i)), (fun x ↦ x (f j));
        multivariateGaussian m S] = S (f i) (f j) :=
    covariance_eval_multivariateGaussian hS (f i) (f j)
  simp only [EuclideanSpace.coe_proj, hcov] at h
  exact h

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

variable {ι κ Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → EuclideanSpace ℝ κ}
  {m : EuclideanSpace ℝ κ} {S : Matrix κ κ ℝ}

/-- The Wick--Isserlis formula for the centered coordinate products of a random vector with a
multivariate Gaussian law. Positions may select repeated coordinates, and no nondegeneracy is
required. -/
theorem integral_prod_sub_multivariateGaussian_eq_sum_perfectMatching
    (hX : HasLaw X (multivariateGaussian m S) P) (hS : S.PosSemidef) (f : ι → κ) :
    (∫ ω, ∏ i, (X ω (f i) - m (f i)) ∂P) =
      ∑ D : TauCeti.PerfectMatching ι, ∏ e ∈ D.edgeFinset,
        Sym2.lift ⟨fun i j ↦ S (f i) (f j),
          fun i j ↦ by simpa using hS.isHermitian.apply (f j) (f i)⟩ e := by
  calc
    _ = ∫ x, ∏ i, (x (f i) - m (f i)) ∂multivariateGaussian m S :=
      hX.integral_comp (by fun_prop)
    _ = _ := TauCeti.Probability.integral_prod_sub_multivariateGaussian_eq_sum_perfectMatching
      m hS f

end ProbabilityTheory.HasLaw
