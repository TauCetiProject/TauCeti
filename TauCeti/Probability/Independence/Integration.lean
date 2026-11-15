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

A finite product of independent integrable variables is integrable
(`ProbabilityTheory.iIndepFun.integrable_fun_prod`).
The product of two independent square-integrable real random variables is square integrable
(`ProbabilityTheory.IndepFun.memLp_two_mul`). For a finite family of pairwise independent
mean-zero square-integrable `RCLike`-valued random variables `W` and `A : Matrix ι ι 𝕜`,
`star W ⬝ᵥ A *ᵥ W` is integrable with expectation `∑ i, A i i * E[‖W i‖ ^ 2]`
(`TauCeti.integral_star_dotProduct_mulVec_eq_sum_diag_of_pairwise_indepFun`).
-/

public section

open MeasureTheory

namespace ProbabilityTheory.iIndepFun

/-- A product over a finite subset of an independent family of integrable variables is
integrable. The index type need not be finite. -/
theorem integrable_finsetProd {Ω ι E : Type*} [MeasurableSpace Ω]
    [NormedCommRing E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {P : Measure Ω} {X : ι → Ω → E}
    (h : iIndepFun X P) (s : Finset ι) (hX : ∀ i ∈ s, Integrable (X i) P) :
    Integrable (fun ω ↦ ∏ i ∈ s, X i ω) P := by
  classical
  have := h.isProbabilityMeasure
  let Y (i : ι) (ω : Ω) := ‖X i ω‖
  have hY : iIndepFun Y P := h.comp (fun _ ↦ norm) (fun _ ↦ continuous_norm.measurable)
  have hm (i : s) : AEMeasurable (Y i) P := (hX i i.property).norm.aemeasurable
  have hint : Integrable (fun x : s → ℝ ↦ ∏ i, x i)
      (Measure.pi fun i : s ↦ P.map (Y i)) :=
    Integrable.fintype_prod fun (i : s) ↦
      (integrable_map_measure
        (hX i i.property).norm.aestronglyMeasurable.aestronglyMeasurable_id_map
        (hm i)).2 (hX i i.property).norm
  rw [← (hY.restrict s).map_fun_eq_pi_map hm] at hint
  have hp := hint.comp_aemeasurable (aemeasurable_pi_iff.2 hm)
  have hprod : Integrable (fun ω ↦ ∏ i ∈ s, Y i ω) P :=
    hp.congr (.of_forall fun ω ↦ Finset.prod_coe_sort s (fun i ↦ Y i ω))
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simpa only [Finset.prod_empty] using integrable_const (1 : E)
  · exact hprod.mono' (s.aestronglyMeasurable_fun_prod fun i hi ↦ (hX i hi).aestronglyMeasurable)
      (.of_forall fun ω ↦ s.norm_prod_le' hs (fun i ↦ X i ω))

/-- A finite product of independent integrable random variables is integrable. -/
theorem integrable_fun_prod {Ω ι E : Type*} [MeasurableSpace Ω] [Fintype ι]
    [NormedCommRing E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {P : Measure Ω} {X : ι → Ω → E}
    (h : iIndepFun X P) (hX : ∀ i, Integrable (X i) P) :
    Integrable (fun ω ↦ ∏ i, X i ω) P :=
  h.integrable_finsetProd Finset.univ (fun i _ ↦ hX i)

end ProbabilityTheory.iIndepFun

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
