/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Combinatorics.Enumerative.PerfectMatching.Weighted
public import TauCeti.Probability.Distributions.Gaussian.MomentRecursion

/-!
# Wick–Isserlis formula for Gaussian mixed moments

The centered mixed moment of finitely many linear observables of a Gaussian measure is the sum
over perfect matchings of the positions, with each edge weighted by the covariance of its two
observables. Positions, rather than observables, form the matching type, so repetitions are
retained. The empty product is covered, while an odd number of positions gives an empty matching
sum and hence a zero moment.

The proof iterates the Gaussian moment recursion and uses the partner decomposition of weighted
perfect matchings. Coordinate specializations cover multivariate Gaussian measures and random
vectors with those laws, including singular positive-semidefinite covariance matrices.

## References

* L. Isserlis, *On a formula for the product-moment coefficient of any order of a normal
  frequency distribution in any number of variables*, Biometrika 12 (1918), 134–139.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Finset
open scoped MatrixOrder

namespace ProbabilityTheory.IsGaussian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [BorelSpace E] in
private theorem integral_prod_sub_dual_eq_sum_perfectMatching_of_isEmpty
    (μ : Measure E) [IsProbabilityMeasure μ]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [IsEmpty ι]
    (L : ι → StrongDual ℝ E) :
    (∫ x, ∏ i, (L i x - μ[L i]) ∂μ) =
      ∑ D : TauCeti.PerfectMatching ι, ∏ e ∈ D.edgeFinset,
        Sym2.lift ⟨fun i j ↦ cov[L i, L j; μ], fun i j ↦ covariance_comm (L i) (L j)⟩ e := by
  let _ : Unique (TauCeti.PerfectMatching ι) := {
    default := TauCeti.PerfectMatching.mk (Equiv.refl ι)
      (fun i ↦ isEmptyElim i) (fun i ↦ isEmptyElim i)
    uniq := fun _ ↦ Subtype.ext (Equiv.ext fun i ↦ isEmptyElim i) }
  simp

/-- **Wick–Isserlis formula.** A centered Gaussian product moment is the sum over perfect
matchings of its positions, with every pair weighted by the covariance of its observables.
This includes the empty product and makes odd moments zero through the empty matching sum. -/
theorem integral_prod_sub_dual_eq_sum_perfectMatching (μ : Measure E) [IsGaussian μ]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (L : ι → StrongDual ℝ E) :
    (∫ x, ∏ i, (L i x - μ[L i]) ∂μ) =
      ∑ D : TauCeti.PerfectMatching ι, ∏ e ∈ D.edgeFinset,
        Sym2.lift
          ⟨fun i j ↦ cov[L i, L j; μ],
            fun i j ↦ covariance_comm (L i) (L j)⟩ e := by
  classical
  induction hn : Fintype.card ι using Nat.strong_induction_on generalizing ι with
  | _ n ih =>
    rcases isEmpty_or_nonempty ι with hι | hι
    · let _ : IsEmpty ι := hι
      exact integral_prod_sub_dual_eq_sum_perfectMatching_of_isEmpty μ L
    · let w : Sym2 ι → ℝ := Sym2.lift
        ⟨fun i j ↦ cov[L i, L j; μ],
          fun i j ↦ covariance_comm (L i) (L j)⟩
      obtain ⟨a⟩ := hι
      rw [TauCeti.PerfectMatching.sum_prod_edgeFinset_eq_sum_mul_sum w a]
      have hrec := integral_sub_dual_mul_prod_sub_dual μ (univ.erase a) (L a) L
      have hsum : (∑ b ∈ univ.erase a, cov[L a, L b; μ] * ∫ x,
          ∏ j ∈ (univ.erase a).erase b, (L j x - μ[L j]) ∂μ) =
          ∑ b : {b : ι // b ≠ a}, cov[L a, L b; μ] * ∫ x,
            ∏ j ∈ (univ.erase a).erase b, (L j x - μ[L j]) ∂μ :=
        Finset.sum_subtype (univ.erase a) (by simp) _
      rw [hsum] at hrec
      calc
        (∫ x, ∏ i, (L i x - μ[L i]) ∂μ) =
            ∫ x, (L a x - μ[L a]) * ∏ i ∈ univ.erase a, (L i x - μ[L i]) ∂μ := by
          congr 1
          funext x
          exact (Finset.mul_prod_erase univ (fun i ↦ L i x - μ[L i]) (mem_univ a)).symm
        _ = ∑ b : {b : ι // b ≠ a}, cov[L a, L b; μ] *
            ∫ x, ∏ j ∈ (univ.erase a).erase b, (L j x - μ[L j]) ∂μ := hrec
        _ = _ := by
          apply sum_congr rfl
          intro b _
          have hint : (∫ x, ∏ j ∈ (univ.erase a).erase b.val,
              (L j x - μ[L j]) ∂μ) =
              ∫ x, ∏ j : {x : ι // x ≠ a ∧ x ≠ b.val},
                (L j.val x - μ[L j.val]) ∂μ := by
            apply integral_congr_ae
            filter_upwards with x
            exact Finset.prod_subtype ((univ.erase a).erase b.val) (by simp [and_comm]) _
          rw [hint, ih (Fintype.card {x : ι // x ≠ a ∧ x ≠ b.val})
            (by
              rw [← hn]
              exact Fintype.card_subtype_lt (p := fun x : ι ↦ x ≠ a ∧ x ≠ b.val)
                (x := a) (by simp)) (fun j ↦ L j.val) rfl]
          rw [show w s(a, b.val) = cov[L a, L b; μ] by simp [w]]
          congr 1
          apply sum_congr rfl
          intro D _
          apply prod_congr rfl
          intro e _
          induction e using Sym2.inductionOn with
          | _ i j => simp [w]

end ProbabilityTheory.IsGaussian

namespace TauCeti.Probability

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The Wick–Isserlis formula for centered coordinates of a multivariate Gaussian. The position
map may repeat coordinates, and the covariance matrix may be singular. -/
theorem integral_prod_sub_multivariateGaussian_eq_sum_perfectMatching
    (m : EuclideanSpace ℝ κ) {S : Matrix κ κ ℝ} (hS : S.PosSemidef) (f : ι → κ) :
    (∫ x, ∏ i, (x (f i) - m (f i)) ∂multivariateGaussian m S) =
      ∑ D : PerfectMatching ι, ∏ e ∈ D.edgeFinset,
        Sym2.lift
          ⟨fun i j ↦ S (f i) (f j),
            fun i j ↦ by simpa using hS.isHermitian.apply (f j) (f i)⟩ e := by
  have h := ProbabilityTheory.IsGaussian.integral_prod_sub_dual_eq_sum_perfectMatching
    (multivariateGaussian m S) (fun i ↦ EuclideanSpace.proj (f i))
  have hcov (i j : ι) : covariance (fun x : EuclideanSpace ℝ κ ↦ x (f i))
      (fun x ↦ x (f j)) (multivariateGaussian m S) = S (f i) (f j) := by
    simpa only [EuclideanSpace.coe_proj] using
      covariance_eval_multivariateGaussian hS (f i) (f j)
  simpa only [EuclideanSpace.coe_proj, integral_eval_multivariateGaussian, hcov] using h

/-- The Wick–Isserlis formula for raw coordinates of a centered multivariate Gaussian. -/
theorem integral_prod_multivariateGaussian_eq_sum_perfectMatching
    {S : Matrix κ κ ℝ} (hS : S.PosSemidef) (f : ι → κ) :
    (∫ x, ∏ i, x (f i) ∂multivariateGaussian 0 S) =
      ∑ D : PerfectMatching ι, ∏ e ∈ D.edgeFinset,
        Sym2.lift
          ⟨fun i j ↦ S (f i) (f j),
            fun i j ↦ by simpa using hS.isHermitian.apply (f j) (f i)⟩ e := by
  simpa using integral_prod_sub_multivariateGaussian_eq_sum_perfectMatching 0 hS f

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

variable {ι κ Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → EuclideanSpace ℝ κ}
  {m : EuclideanSpace ℝ κ} {S : Matrix κ κ ℝ}

/-- The Wick–Isserlis formula for a random vector with a multivariate Gaussian law. The
positions may repeat coordinates, and the covariance matrix may be singular. -/
theorem integral_prod_sub_eq_sum_perfectMatching_multivariateGaussian
    (hX : HasLaw X (multivariateGaussian m S) P) (hS : S.PosSemidef) (f : ι → κ) :
    (∫ ω, ∏ i, (X ω (f i) - m (f i)) ∂P) =
      ∑ D : TauCeti.PerfectMatching ι, ∏ e ∈ D.edgeFinset,
        Sym2.lift
          ⟨fun i j ↦ S (f i) (f j),
            fun i j ↦ by simpa using hS.isHermitian.apply (f j) (f i)⟩ e := by
  calc
    _ = ∫ x, ∏ i, (x (f i) - m (f i)) ∂multivariateGaussian m S :=
      hX.integral_comp (by fun_prop)
    _ = _ := TauCeti.Probability.integral_prod_sub_multivariateGaussian_eq_sum_perfectMatching
      m hS f

end ProbabilityTheory.HasLaw
