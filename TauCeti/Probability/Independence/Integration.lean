/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Integrability and expectations of products and quadratic forms under independence

The product of two independent square-integrable real random variables is square integrable
(`ProbabilityTheory.IndepFun.memLp_two_mul`). For a finite family of pairwise independent
mean-zero square-integrable `RCLike`-valued random variables `W` and `A : Matrix ι ι 𝕜`,
`star W ⬝ᵥ A *ᵥ W` is integrable with expectation `∑ i, A i i * E[‖W i‖ ^ 2]`
(`TauCeti.integral_star_dotProduct_mulVec_eq_sum_diag_of_pairwise_indepFun`).

For an independent family `Y`, the expectation of a finite product of functions of members of
`Y`, several factors possibly reading the same member, is the product over the members of the
expectations of the products of the factors reading them
(`ProbabilityTheory.iIndepFun.integral_fun_prod_comp_fiberwise`). This is the factorization
used to evaluate expected products of entries of random matrices along trace words.
-/

public section

open MeasureTheory

namespace ProbabilityTheory.IndepFun

/-- The product of independent square-integrable real random variables is square integrable. -/
theorem memLp_two_mul {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X Y : Ω → ℝ} (h : IndepFun X Y P) (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    MemLp (X * Y) 2 P := by
  refine (memLp_two_iff_integrable_sq
    (hX.aestronglyMeasurable.mul hY.aestronglyMeasurable)).2 ?_
  simpa only [Pi.mul_def, mul_pow, Function.comp_def, id_eq] using
    (h.comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)).integrable_mul
      hX.integrable_sq hY.integrable_sq

end ProbabilityTheory.IndepFun

namespace ProbabilityTheory.iIndepFun

/-- **Expected products of functions of independent variables.** Let `Y` be an independent
family indexed by a finite type, and let the factors `φ s (Y (e s))` of a finite product read
members of `Y`, several factors possibly reading the same member. The expectation of the product
is the product, over the members `j`, of the expectations of the products of the factors reading
`j`. -/
theorem integral_fun_prod_comp_fiberwise {Ω κ ι β 𝕜 : Type*} {mΩ : MeasurableSpace Ω}
    {mβ : MeasurableSpace β} [RCLike 𝕜] [Fintype κ] [DecidableEq κ] [Fintype ι]
    {P : Measure Ω} {Y : κ → Ω → β} (hY : iIndepFun Y P) (mY : ∀ j, AEMeasurable (Y j) P)
    (e : ι → κ) {φ : ι → β → 𝕜} (hφ : ∀ s, Measurable (φ s)) :
    ∫ ω, ∏ s, φ s (Y (e s) ω) ∂P = ∏ j, ∫ ω, ∏ s with e s = j, φ s (Y j ω) ∂P := by
  rw [← hY.integral_fun_prod_comp mY fun j ↦
    (Finset.measurable_prod _ fun s _ ↦ hφ s).aestronglyMeasurable]
  congr with ω
  rw [← Finset.prod_fiberwise Finset.univ e]
  exact Finset.prod_congr rfl fun j _ ↦ Finset.prod_congr rfl fun s hs ↦ by
    rw [(Finset.mem_filter.1 hs).2]

end ProbabilityTheory.iIndepFun

open ProbabilityTheory Matrix

namespace TauCeti

/-- For pairwise independent mean-zero square-integrable `RCLike`-valued coordinates `W` and
`A : Matrix ι ι 𝕜`, `star W ⬝ᵥ A *ᵥ W` is integrable with expectation
`∑ i, A i i * E[‖W i‖ ^ 2]`. -/
theorem integral_star_dotProduct_mulVec_eq_sum_diag_of_pairwise_indepFun {Ω ι 𝕜 : Type*}
    [MeasurableSpace Ω] [Fintype ι] [RCLike 𝕜] {P : Measure Ω} {W : ι → Ω → 𝕜}
    (hindep : Pairwise fun i j ↦ W i ⟂ᵢ[P] W j) (hW_int : ∀ i, Integrable (W i) P)
    (hW_sq : ∀ i, Integrable (fun ω ↦ ‖W i ω‖ ^ 2) P) (hW_mean : ∀ i, ∫ ω, W i ω ∂P = 0)
    (A : Matrix ι ι 𝕜) :
    Integrable (fun ω ↦ star (fun i ↦ W i ω) ⬝ᵥ A *ᵥ (fun i ↦ W i ω)) P ∧
      ∫ ω, star (fun i ↦ W i ω) ⬝ᵥ A *ᵥ (fun i ↦ W i ω) ∂P =
        ∑ i, A i i * ((P[fun ω ↦ ‖W i ω‖ ^ 2] : ℝ) : 𝕜) := by
  have hW_star (i : ι) : Integrable (fun ω ↦ star (W i ω)) P :=
    (hW_int i).mono (continuous_star.comp_aestronglyMeasurable (hW_int i).1)
      (.of_forall fun _ ↦ by simp)
  have hexpand (ω : Ω) : star (fun i ↦ W i ω) ⬝ᵥ A *ᵥ (fun i ↦ W i ω) =
      ∑ i, ∑ j, A i j * (star (W i ω) * W j ω) := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
  have hcast (i : ι) (ω : Ω) :
      A i i * (star (W i ω) * W i ω) = A i i * ((‖W i ω‖ ^ 2 : ℝ) : 𝕜) := by
    rw [RCLike.star_def, RCLike.conj_mul]; norm_cast
  have hterm_int (i j : ι) : Integrable (fun ω ↦ A i j * (star (W i ω) * W j ω)) P := by
    by_cases hij : i = j
    · subst hij; exact (((RCLike.ofRealCLM (K := 𝕜)).integrable_comp (hW_sq i)).const_mul
        (A i i)).congr (.of_forall fun ω ↦ (hcast i ω).symm)
    · exact (((hindep hij).comp continuous_star.measurable measurable_id).integrable_smul
        (hW_star i) (hW_int j)).const_mul (A i j)
  refine ⟨(integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hterm_int i j).congr
    (.of_forall fun ω ↦ (hexpand ω).symm), ?_⟩
  rw [integral_congr_ae (.of_forall hexpand),
    integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hterm_int i j]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [integral_finsetSum _ fun j _ ↦ hterm_int i j, Finset.sum_eq_single i]
  · rw [integral_congr_ae (.of_forall (hcast i)), integral_const_mul]
    exact congrArg (A i i * ·) ((RCLike.ofRealCLM (K := 𝕜)).integral_comp_comm (hW_sq i))
  · intro j _ hji
    have hmul := ((hindep hji.symm).comp continuous_star.measurable
      measurable_id).integral_fun_mul_eq_mul_integral (hW_star i).1 (hW_int j).1
    dsimp only [Function.comp_def, id_eq] at hmul
    rw [integral_const_mul, hmul, hW_mean j, mul_zero, mul_zero]
  · exact fun hi ↦ absurd (Finset.mem_univ i) hi

end TauCeti
