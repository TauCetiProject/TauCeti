/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Combinatorics.Enumerative.PerfectMatching.Weighted
public import TauCeti.Probability.Distributions.Gaussian.MomentRecursion
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-!
# Wick–Isserlis formulas for Gaussian moments

The expectation of a finite product of centered Gaussian observables is the sum over
perfect matchings of the positions of the products of their pairwise covariances. Positions
may carry the same observable, and covariance matrices may be singular. The empty product
has expectation one, and odd products vanish because there are no perfect matchings.

The formula is stated for jointly Gaussian real random variables on an arbitrary measurable
space, then specialized to multivariate Gaussian coordinates and random vectors with those
laws. It combines the Gaussian contraction recurrence with the partner decomposition of
weighted perfect matchings; each unordered edge is counted once.
These identities evaluate the Gaussian entry products arising in trace powers and mixed
trace statistics.

## References

* L. Isserlis, *On a formula for the product-moment coefficient of any order of a normal
  frequency distribution in any number of variables*, Biometrika 12 (1918), 134–139.
* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1 and §2.5.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Finset
open TauCeti

universe u

namespace TauCeti.Probability

private theorem integral_prod_sub_dual_eq_sum_perfectMatching
    {d : ℕ} (μ : Measure (Fin d → ℝ)) [IsGaussian μ]
    {ι : Type u} [Fintype ι] [DecidableEq ι] (L : ι → StrongDual ℝ (Fin d → ℝ)) :
    (∫ x, ∏ i, (L i x - μ[L i]) ∂μ) =
      ∑ D : PerfectMatching ι, ∏ e ∈ D.edgeFinset,
        Sym2.lift ⟨fun i j ↦ cov[L i, L j; μ], fun i j ↦ covariance_comm (L i) (L j)⟩ e := by
  classical
  have aux (n : ℕ) : ∀ (ι : Type u) [Fintype ι] [DecidableEq ι],
      Fintype.card ι = n → ∀ L : ι → StrongDual ℝ (Fin d → ℝ),
      (∫ x, ∏ i, (L i x - μ[L i]) ∂μ) =
        ∑ D : PerfectMatching ι, ∏ e ∈ D.edgeFinset,
          Sym2.lift ⟨fun i j ↦ cov[L i, L j; μ], fun i j ↦ covariance_comm (L i) (L j)⟩ e := by
    intro ι _ _ hn L
    induction n using Nat.strong_induction_on generalizing ι with
    | ind n ih =>
      cases isEmpty_or_nonempty ι with
      | inl h => simp
      | inr h =>
        obtain ⟨a⟩ := h
        rw [PerfectMatching.sum_prod_edgeFinset_eq_sum_mul_sum _ a]
        have hrec := IsGaussian.integral_sub_dual_mul_prod_sub_dual μ (univ.erase a) (L a) L
        have hprod (x : Fin d → ℝ) : (∏ i, (L i x - μ[L i])) =
            (L a x - μ[L a]) * ∏ i ∈ univ.erase a, (L i x - μ[L i]) :=
          (mul_prod_erase _ _ (mem_univ a)).symm
        simp_rw [hprod]
        rw [hrec, sum_subtype (univ.erase a) (p := fun b ↦ b ≠ a) (by simp)]
        refine Finset.sum_congr rfl fun b _ ↦ ?_
        simp only [Sym2.lift_mk]
        congr 1
        let ρ := {x : ι // x ≠ a ∧ x ≠ b.val}
        have hk : Fintype.card ρ < n := by
          rw [← hn]
          exact Fintype.card_subtype_lt (x := a) (by simp)
        have hsmall := ih (Fintype.card ρ) hk ρ rfl (fun i ↦ L i.val)
        have hindex (x : Fin d → ℝ) :
            (∏ i ∈ (univ.erase a).erase b.val, (L i x - μ[L i])) =
              ∏ i : ρ, (L i.val x - μ[L i.val]) := by
          exact prod_subtype _ (by simp [and_comm]) _
        simp_rw [hindex]
        rw [hsmall]
        refine Finset.sum_congr rfl fun D _ ↦ Finset.prod_congr rfl fun e _ ↦ ?_
        induction e using Sym2.inductionOn
        simp
  exact aux (Fintype.card ι) ι rfl L

end TauCeti.Probability

namespace ProbabilityTheory.HasGaussianLaw

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
  {P : Measure Ω} {X : Ω → ι → ℝ}

/-- **Wick–Isserlis formula for jointly Gaussian random variables.** Joint Gaussianity is
required; Gaussian marginal laws alone do not suffice. Arbitrary means and correlations,
repeated coordinates, and degenerate laws are allowed. -/
theorem integral_prod_sub_eq_sum_perfectMatching (hX : HasGaussianLaw X P) :
    (∫ ω, ∏ i, (X ω i - ∫ ω', X ω' i ∂P) ∂P) =
      ∑ D : PerfectMatching ι, ∏ e ∈ D.edgeFinset,
        Sym2.lift ⟨fun i j ↦ cov[fun ω ↦ X ω i, fun ω ↦ X ω j; P],
          fun _ _ ↦ covariance_comm _ _⟩ e := by
  let e := Fintype.equivFin ι
  let Y : Ω → Fin (Fintype.card ι) → ℝ := fun ω j ↦ X ω (e.symm j)
  have hY : HasGaussianLaw Y P :=
    hX.map_fun (ContinuousLinearMap.pi fun j ↦ ContinuousLinearMap.proj (e.symm j))
  let := hY.isGaussian_map
  have hmean (i : ι) :
      (P.map Y)[(ContinuousLinearMap.proj (e i) : (Fin (Fintype.card ι) → ℝ) →L[ℝ] ℝ)] =
        ∫ ω, X ω i ∂P := by
    rw [integral_map hY.aemeasurable
      (ContinuousLinearMap.proj (e i)).continuous.aestronglyMeasurable]
    simp [Y]
  have hcov (i j : ι) :
      cov[(ContinuousLinearMap.proj (e i) : (Fin (Fintype.card ι) → ℝ) →L[ℝ] ℝ),
        (ContinuousLinearMap.proj (e j) : (Fin (Fintype.card ι) → ℝ) →L[ℝ] ℝ); P.map Y] =
        cov[fun ω ↦ X ω i, fun ω ↦ X ω j; P] := by
    rw [covariance_map (by fun_prop) (by fun_prop) hY.aemeasurable]
    simp [Y, Function.comp_def]
  have h := TauCeti.Probability.integral_prod_sub_dual_eq_sum_perfectMatching (P.map Y)
    (fun i ↦ ContinuousLinearMap.proj (e i))
  simp only [hmean, hcov] at h
  rw [integral_map hY.aemeasurable (by fun_prop)] at h
  simpa [Y] using h

end ProbabilityTheory.HasGaussianLaw

namespace TauCeti.Probability

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The Wick pairing formula for coordinates of a multivariate Gaussian. The map `f`
labels the positions and need not be injective. Positive-semidefinite singular covariance
matrices and empty coordinate types are included. -/
theorem integral_prod_sub_multivariateGaussian_eq_sum_perfectMatching
    (m : EuclideanSpace ℝ κ) {S : Matrix κ κ ℝ} (hS : S.PosSemidef) (f : ι → κ) :
    (∫ x, ∏ i, (x (f i) - m (f i)) ∂multivariateGaussian m S) =
      ∑ D : PerfectMatching ι, ∏ e ∈ D.edgeFinset,
        Sym2.lift ⟨fun i j ↦ S (f i) (f j), fun i j ↦ by
          simpa using congrFun (congrFun hS.isHermitian.eq (f j)) (f i)⟩ e := by
  have hX := (IsGaussian.hasGaussianLaw_id (μ := multivariateGaussian m S)).map_fun
    (ContinuousLinearMap.pi fun i : ι ↦ EuclideanSpace.proj (f i))
  have h := hX.integral_prod_sub_eq_sum_perfectMatching
  simp only [ContinuousLinearMap.pi_apply, EuclideanSpace.coe_proj, id_eq] at h
  have hcov (i j : ι) : cov[EuclideanSpace.proj (f i), EuclideanSpace.proj (f j);
      multivariateGaussian m S] = S (f i) (f j) :=
    covariance_eval_multivariateGaussian hS _ _
  simp only [EuclideanSpace.coe_proj] at hcov
  simpa only [hcov, integral_eval_multivariateGaussian] using h

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

variable {Ω ι κ : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] {P : Measure Ω} {X : Ω → EuclideanSpace ℝ κ}
  {m : EuclideanSpace ℝ κ} {S : Matrix κ κ ℝ}

/-- The Wick pairing formula transported to a random vector with a multivariate Gaussian
law. The indexing map allows each coordinate to occur any number of times. -/
theorem integral_prod_sub_multivariateGaussian_eq_sum_perfectMatching
    (hX : HasLaw X (multivariateGaussian m S) P) (hS : S.PosSemidef) (f : ι → κ) :
    (∫ ω, ∏ i, (X ω (f i) - m (f i)) ∂P) =
      ∑ D : PerfectMatching ι, ∏ e ∈ D.edgeFinset,
        Sym2.lift ⟨fun i j ↦ S (f i) (f j), fun i j ↦ by
          simpa using congrFun (congrFun hS.isHermitian.eq (f j)) (f i)⟩ e := by
  calc
    _ = ∫ x, ∏ i, (x (f i) - m (f i)) ∂multivariateGaussian m S :=
      hX.integral_comp (by fun_prop)
    _ = _ :=
      TauCeti.Probability.integral_prod_sub_multivariateGaussian_eq_sum_perfectMatching m hS f

end ProbabilityTheory.HasLaw
