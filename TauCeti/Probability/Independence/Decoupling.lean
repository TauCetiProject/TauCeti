/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Convex decoupling of off-diagonal order-two chaos

Let `(Xᵢ)` be a finite family of independent random variables taking values in a measurable space
`E`, and let `fᵢⱼ : E → E → ℝ` be measurable kernels that vanish on the diagonal (`fᵢᵢ = 0`) and
are centred in each variable when `i ≠ j`. This file proves **convex decoupling** for the
homogeneous order-two statistic `∑ i, ∑ j, fᵢⱼ (Xᵢ) (Xⱼ)`: for every continuous convex function
`Φ : ℝ → ℝ`, its expectation is bounded above by the expectation of
`Φ (4 * ∑ i, ∑ j, fᵢⱼ (Xᵢ) (X'ⱼ))` over an independent copy `(X'ᵢ)` of `(Xᵢ)`.

The proof combines two elementary symmetries on the doubled product space:

1. Averaging over coordinate selectors `δ : ι → Bool` rewrites the off-diagonal sum as the uniform
   average of the bipartition sums `4 * ∑_{δ i = true, δ j = false} fᵢⱼ (zᵢ) (zⱼ)`.
2. For each fixed `δ`, swapping `(zₖ, wₖ)` on the coordinates where `δ k = false` preserves the
   doubled product measure and turns `4 * ∑ i, ∑ j, fᵢⱼ (xᵢ) (yⱼ)` into an integrand whose
   conditional expectation over `w` equals that bipartition sum by coordinatewise centring.

Jensen's inequality in both `w` and `δ` yields the upper bound with constant `4`. When `Φ` is
nonnegative (for example `Φ z = exp (t * z)`), integrability of the coupled statistic follows
automatically from integrability of the decoupled one. Both the product-measure form and its
transfer to an `iIndepFun` family are provided, together with the exponential-moment decoupling
bounds for real off-diagonal quadratic forms and `RCLike` off-diagonal sesquilinear forms.

## Main results

* `ProbabilityTheory.integral_convex_offDiag_pi_le`: convex decoupling on a finite product measure.
* `ProbabilityTheory.integrable_of_nonneg_convex_offDiag_pi` and
  `ProbabilityTheory.integral_nonneg_convex_offDiag_pi_le`: for nonnegative `Φ`, integrability on
  the doubled product measure implies integrability on a single copy and the decoupling bound.
* `ProbabilityTheory.iIndepFun.integral_convex_offDiag_le`,
  `ProbabilityTheory.iIndepFun.integrable_of_nonneg_convex_offDiag`, and
  `ProbabilityTheory.iIndepFun.integral_nonneg_convex_offDiag_le`: convex decoupling for an
  independent family `(Xᵢ)` against `P.prod P`.
* `ProbabilityTheory.iIndepFun.mgf_offDiag_dotProduct_mulVec_le` and
  `ProbabilityTheory.iIndepFun.mgf_offDiag_re_star_dotProduct_mulVec_le`: moment-generating
  function decoupling for real quadratic and `RCLike` sesquilinear off-diagonal forms.

## References

* V. H. de la Peña and E. Giné, *Decoupling: From Dependence to Independence*, Springer (1999),
  Theorem 3.1.1.
* R. Vershynin, *High-Dimensional Probability: An Introduction with Applications in Data Science*,
  Cambridge University Press (2018), Theorem 6.1.1.
-/

public section

open MeasureTheory Real Matrix

namespace ProbabilityTheory

section ProductMeasure

variable {ι E : Type*} [MeasurableSpace E]

/-- Coordinatewise exchange between two copies of `ι → E` on the coordinates where `δ k = false`. -/
private def swapCoords (δ : ι → Bool) (p : (ι → E) × (ι → E)) : (ι → E) × (ι → E) :=
  (fun k ↦ if δ k then p.1 k else p.2 k, fun k ↦ if δ k then p.2 k else p.1 k)

omit [MeasurableSpace E] in
private theorem involutive_swapCoords (δ : ι → Bool) :
    Function.Involutive (swapCoords (E := E) δ) := by
  intro ⟨x, y⟩
  ext k <;> dsimp [swapCoords] <;> cases δ k <;> rfl

private theorem measurable_swapCoords (δ : ι → Bool) :
    Measurable (swapCoords (E := E) δ) := by
  refine Measurable.prodMk (Measurable.of_eval fun k ↦ ?_) (Measurable.of_eval fun k ↦ ?_)
  · cases δ k
    · exact (measurable_pi_apply k).comp measurable_snd
    · exact (measurable_pi_apply k).comp measurable_fst
  · cases δ k
    · exact (measurable_pi_apply k).comp measurable_fst
    · exact (measurable_pi_apply k).comp measurable_snd

/-- `swapCoords δ` packaged as a measurable equivalence via its involutivity. -/
private noncomputable def swapCoordsEquiv (δ : ι → Bool) :
    ((ι → E) × (ι → E)) ≃ᵐ ((ι → E) × (ι → E)) :=
  MeasurableEquiv.ofInvolutive (swapCoords δ) (involutive_swapCoords δ) (measurable_swapCoords δ)

private theorem measurePreserving_swapCoords [Fintype ι] (μ : ι → Measure E)
    [∀ k, SigmaFinite (μ k)] (δ : ι → Bool) :
    MeasurePreserving (swapCoordsEquiv (E := E) δ)
      ((Measure.pi μ).prod (Measure.pi μ)) ((Measure.pi μ).prod (Measure.pi μ)) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow E E ι
  have he : MeasurePreserving e (Measure.pi fun k ↦ (μ k).prod (μ k))
      ((Measure.pi μ).prod (Measure.pi μ)) :=
    measurePreserving_arrowProdEquivProdArrow E E ι μ μ
  let step : ∀ k : ι, E × E → E × E := fun k p ↦ if δ k then p else p.swap
  have hstep_meas : ∀ k, Measurable (step k) := fun k ↦ by
    cases h : δ k
    · have : step k = Prod.swap := funext fun p ↦ by simp [step, h]
      rw [this]; exact measurable_swap
    · have : step k = id := funext fun p ↦ by simp [step, h]
      rw [this]; exact measurable_id
  have hstep_map : ∀ k, ((μ k).prod (μ k)).map (step k) = (μ k).prod (μ k) := fun k ↦ by
    cases h : δ k
    · have : step k = Prod.swap := funext fun p ↦ by simp [step, h]
      rw [this]; exact Measure.prod_swap
    · have : step k = id := funext fun p ↦ by simp [step, h]
      rw [this]; exact Measure.map_id
  have hpi : MeasurePreserving (fun h k ↦ step k (h k))
      (Measure.pi fun k ↦ (μ k).prod (μ k)) (Measure.pi fun k ↦ (μ k).prod (μ k)) := by
    refine ⟨Measurable.of_eval fun k ↦ (hstep_meas k).comp (measurable_pi_apply k), ?_⟩
    have : ∀ k, SigmaFinite (((μ k).prod (μ k)).map (step k)) := fun k ↦ by
      rw [hstep_map k]; infer_instance
    rw [Measure.pi_map_pi fun k ↦ (hstep_meas k).aemeasurable]
    simp only [hstep_map]
  have hswap_apply : ∀ p : (ι → E) × (ι → E), swapCoordsEquiv δ p = swapCoords δ p :=
    fun _ ↦ rfl
  have he_apply : ∀ f : ι → E × E, e f = (fun k ↦ (f k).1, fun k ↦ (f k).2) := fun _ ↦ rfl
  have he_symm : ∀ p : (ι → E) × (ι → E), e.symm p = fun k ↦ (p.1 k, p.2 k) := fun _ ↦ rfl
  have hcomp : (swapCoordsEquiv (E := E) δ : ((ι → E) × (ι → E)) → ((ι → E) × (ι → E))) =
      (e ∘ (fun h k ↦ step k (h k)) ∘ e.symm) := by
    ext ⟨x, y⟩ k
    · simp only [Function.comp_apply, hswap_apply, he_apply, he_symm, swapCoords, step]
      cases δ k <;> rfl
    · simp only [Function.comp_apply, hswap_apply, he_apply, he_symm, swapCoords, step]
      cases δ k <;> rfl
  refine ⟨(swapCoordsEquiv δ).measurable, ?_⟩
  rw [hcomp]
  exact (he.comp (hpi.comp he.symm)).map_eq

/-- For `i ≠ j`, a quarter of all Boolean selectors satisfy `δ i = true` and `δ j = false`. -/
private theorem selector_avg_eq_one [Fintype ι] [DecidableEq ι] {i j : ι} (hij : i ≠ j) :
    (Fintype.card (ι → Bool) : ℝ)⁻¹ *
      ∑ δ : ι → Bool, (if δ i = true ∧ δ j = false then (4 : ℝ) else 0) = 1 := by
  let g : (ι → Bool) → ℝ := fun δ ↦ if δ i = true ∧ δ j = false then 1 else 0
  let fi_fn : (ι → Bool) → (ι → Bool) := fun δ ↦ Function.update δ i (!δ i)
  let fj_fn : (ι → Bool) → (ι → Bool) := fun δ ↦ Function.update δ j (!δ j)
  let fi : (ι → Bool) ≃ (ι → Bool) := Function.Involutive.toPerm fi_fn fun δ ↦ by
    ext k; dsimp [fi_fn]; by_cases hk : k = i <;> simp [hk]
  let fj : (ι → Bool) ≃ (ι → Bool) := Function.Involutive.toPerm fj_fn fun δ ↦ by
    ext k; dsimp [fj_fn]; by_cases hk : k = j <;> simp [hk]
  have hsum4 : 4 * ∑ δ : ι → Bool, g δ = (Fintype.card (ι → Bool) : ℝ) := by
    have h1 : ∑ δ, g (fi_fn δ) = ∑ δ, g δ := Equiv.sum_comp fi g
    have h2 : ∑ δ, g (fj_fn δ) = ∑ δ, g δ := Equiv.sum_comp fj g
    have h3 : ∑ δ, g (fj_fn (fi_fn δ)) = ∑ δ, g δ := Equiv.sum_comp (fi.trans fj) g
    have hpt : ∀ δ : ι → Bool,
        g δ + g (fi_fn δ) + g (fj_fn δ) + g (fj_fn (fi_fn δ)) = 1 := by
      intro δ
      have hfi_i : fi_fn δ i = !δ i := Function.update_self i (!δ i) δ
      have hfi_j : fi_fn δ j = δ j := Function.update_of_ne hij.symm (!δ i) δ
      have hfj_i : fj_fn δ i = δ i := Function.update_of_ne hij (!δ j) δ
      have hfj_j : fj_fn δ j = !δ j := Function.update_self j (!δ j) δ
      have hfij_i : fj_fn (fi_fn δ) i = !δ i := by
        dsimp [fj_fn]; rw [Function.update_of_ne hij, hfi_i]
      have hfij_j : fj_fn (fi_fn δ) j = !δ j := by
        dsimp [fj_fn]; rw [Function.update_self, hfi_j]
      dsimp [g]
      rw [hfi_i, hfi_j, hfj_i, hfj_j, hfij_i, hfij_j]
      cases δ i <;> cases δ j <;> norm_num
    have htot : ∑ δ : ι → Bool, (g δ + g (fi_fn δ) + g (fj_fn δ) + g (fj_fn (fi_fn δ))) =
        (Fintype.card (ι → Bool) : ℝ) := by
      rw [Finset.sum_congr rfl fun δ _ ↦ hpt δ, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one]
    simp only [Finset.sum_add_distrib, h1, h2, h3] at htot
    linarith
  have hcard : (Fintype.card (ι → Bool) : ℝ) ≠ 0 := by
    have : Nonempty (ι → Bool) := ⟨fun _ ↦ false⟩
    exact Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hrew : ∑ δ : ι → Bool, (if δ i = true ∧ δ j = false then (4 : ℝ) else 0) =
      4 * ∑ δ : ι → Bool, g δ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun δ _ ↦ ?_
    dsimp [g]
    split_ifs <;> ring
  rw [hrew, hsum4, inv_mul_cancel₀ hcard]

private theorem measurePreserving_eval_pair [Fintype ι] (μ : ι → Measure E)
    [∀ k, IsProbabilityMeasure (μ k)] {i j : ι} (hij : i ≠ j) :
    MeasurePreserving (fun w : ι → E ↦ (w i, w j)) (Measure.pi μ) ((μ i).prod (μ j)) := by
  have hindep : iIndepFun (fun k (w : ι → E) ↦ w k) (Measure.pi μ) :=
    iIndepFun_pi fun _ ↦ aemeasurable_id
  have hij_indep : IndepFun (fun w : ι → E ↦ w i) (fun w : ι → E ↦ w j) (Measure.pi μ) :=
    hindep.indepFun hij
  refine ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j), ?_⟩
  rw [hij_indep.map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
      (measurable_pi_apply j).aemeasurable,
    (measurePreserving_eval μ i).map_eq, (measurePreserving_eval μ j).map_eq]

/-- Conditional expectation of the `δ`-swapped decoupled sum over the second coordinate family. -/
private theorem ae_integral_swapped_eq [Fintype ι] {μ : ι → Measure E}
    [∀ k, IsProbabilityMeasure (μ k)] {f : ι → ι → E → E → ℝ}
    (hf_meas : ∀ i j, Measurable (Function.uncurry (f i j)))
    (hf_diag : ∀ i x y, f i i x y = 0)
    (hf_int : ∀ i j, i ≠ j → Integrable (Function.uncurry (f i j)) ((μ i).prod (μ j)))
    (hf_zero_right : ∀ i j, i ≠ j → ∀ᵐ x ∂μ i, ∫ y, f i j x y ∂μ j = 0)
    (hf_zero_left : ∀ i j, i ≠ j → ∀ᵐ y ∂μ j, ∫ x, f i j x y ∂μ i = 0)
    (δ : ι → Bool) :
    ∀ᵐ z ∂Measure.pi μ,
      Integrable (fun w : ι → E ↦
        4 * ∑ i, ∑ j, f i j (if δ i then z i else w i) (if δ j then w j else z j))
        (Measure.pi μ) ∧
      (∫ w : ι → E,
        (4 * ∑ i, ∑ j, f i j (if δ i then z i else w i) (if δ j then w j else z j))
        ∂Measure.pi μ) =
        4 * ∑ i, ∑ j, if δ i = true ∧ δ j = false then f i j (z i) (z j) else 0 := by
  classical
  have hcell (i j : ι) :
      ∀ᵐ z ∂Measure.pi μ,
        Integrable (fun w : ι → E ↦ f i j (if δ i then z i else w i) (if δ j then w j else z j))
          (Measure.pi μ) ∧
        (∫ w : ι → E, f i j (if δ i then z i else w i) (if δ j then w j else z j) ∂Measure.pi μ) =
          if δ i = true ∧ δ j = false then f i j (z i) (z j) else 0 := by
    by_cases hij : i = j
    · subst hij
      exact Filter.Eventually.of_forall fun z ↦ by simp [hf_diag]
    · have hmeas_ij : Measurable (Function.uncurry (f i j)) := hf_meas i j
      cases hdi : δ i <;> cases hdj : δ j
      · -- `δ i = false, δ j = false`: integrand is `w ↦ f i j (w i) (z j)`.
        have hae_int : ∀ᵐ y ∂μ j, Integrable (fun x ↦ f i j x y) (μ i) :=
          (hf_int i j hij).prod_left_ae
        have hp_int := (measurePreserving_eval μ j).quasiMeasurePreserving.ae hae_int
        have hp_zero := (measurePreserving_eval μ j).quasiMeasurePreserving.ae
          (hf_zero_left i j hij)
        filter_upwards [hp_int, hp_zero] with z hz_int hz_zero
        simp only [Bool.false_eq_true, false_and, ↓reduceIte]
        have hslice_meas : Measurable (fun x ↦ f i j x (z j)) :=
          hmeas_ij.comp (f := fun x ↦ (x, z j)) (measurable_id.prodMk measurable_const)
        have heval := (measurePreserving_eval μ i).map_eq
        refine ⟨?_, ?_⟩
        · rw [← heval, integrable_map_measure hslice_meas.aestronglyMeasurable
              (measurable_pi_apply i).aemeasurable] at hz_int
          exact hz_int
        · rw [← hz_zero, ← heval,
            integral_map (measurable_pi_apply i).aemeasurable hslice_meas.aestronglyMeasurable]
      · -- `δ i = false, δ j = true`: integrand is `w ↦ f i j (w i) (w j)`.
        have hpair := measurePreserving_eval_pair μ hij
        refine Filter.Eventually.of_forall fun z ↦ ?_
        simp only [Bool.false_eq_true, false_and, ↓reduceIte]
        have hint_pair : Integrable (Function.uncurry (f i j)) ((μ i).prod (μ j)) := hf_int i j hij
        refine ⟨?_, ?_⟩
        · rw [← hpair.map_eq, integrable_map_measure hmeas_ij.aestronglyMeasurable
              hpair.measurable.aemeasurable] at hint_pair
          exact hint_pair
        · have hzero : ∫ p, Function.uncurry (f i j) p ∂((μ i).prod (μ j)) = 0 := by
            rw [integral_prod _ (hf_int i j hij)]
            simpa using integral_congr_ae (hf_zero_right i j hij)
          rw [← hzero, ← hpair.map_eq,
            integral_map hpair.measurable.aemeasurable hmeas_ij.aestronglyMeasurable]
          rfl
      · -- `δ i = true, δ j = false`: integrand is constant `f i j (z i) (z j)`.
        exact Filter.Eventually.of_forall fun z ↦ by simp
      · -- `δ i = true, δ j = true`: integrand is `w ↦ f i j (z i) (w j)`.
        have hae_int : ∀ᵐ x ∂μ i, Integrable (fun y ↦ f i j x y) (μ j) :=
          (hf_int i j hij).prod_right_ae
        have hp_int := (measurePreserving_eval μ i).quasiMeasurePreserving.ae hae_int
        have hp_zero := (measurePreserving_eval μ i).quasiMeasurePreserving.ae
          (hf_zero_right i j hij)
        filter_upwards [hp_int, hp_zero] with z hz_int hz_zero
        simp only [Bool.true_eq_false, and_false, ↓reduceIte]
        have hslice_meas : Measurable (fun y ↦ f i j (z i) y) :=
          hmeas_ij.comp (f := fun y ↦ (z i, y)) (measurable_const.prodMk measurable_id)
        have heval := (measurePreserving_eval μ j).map_eq
        refine ⟨?_, ?_⟩
        · rw [← heval, integrable_map_measure hslice_meas.aestronglyMeasurable
              (measurable_pi_apply j).aemeasurable] at hz_int
          exact hz_int
        · rw [← hz_zero, ← heval,
            integral_map (measurable_pi_apply j).aemeasurable hslice_meas.aestronglyMeasurable]
  have hall : ∀ᵐ z ∂Measure.pi μ, ∀ i j : ι,
      Integrable (fun w : ι → E ↦ f i j (if δ i then z i else w i) (if δ j then w j else z j))
        (Measure.pi μ) ∧
      (∫ w : ι → E, f i j (if δ i then z i else w i) (if δ j then w j else z j) ∂Measure.pi μ) =
        if δ i = true ∧ δ j = false then f i j (z i) (z j) else 0 :=
    ae_all_iff.2 fun i ↦ ae_all_iff.2 fun j ↦ hcell i j
  filter_upwards [hall] with z hz
  have hint_inner : ∀ i : ι, Integrable (fun w : ι → E ↦
      ∑ j, f i j (if δ i then z i else w i) (if δ j then w j else z j)) (Measure.pi μ) :=
    fun i ↦ integrable_finsetSum _ fun j _ ↦ (hz i j).1
  have hint_outer : Integrable (fun w : ι → E ↦
      ∑ i, ∑ j, f i j (if δ i then z i else w i) (if δ j then w j else z j)) (Measure.pi μ) :=
    integrable_finsetSum _ fun i _ ↦ hint_inner i
  refine ⟨hint_outer.const_mul 4, ?_⟩
  rw [integral_const_mul, integral_finsetSum _ fun i _ ↦ hint_inner i]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [integral_finsetSum _ fun j _ ↦ (hz i j).1]
  exact Finset.sum_congr rfl fun j _ ↦ (hz i j).2

/-- Pointwise majorant behind convex decoupling on `Measure.pi μ`, together with its integrability
and integral identity. -/
private theorem ae_le_convex_offDiag_pi [Fintype ι] {μ : ι → Measure E}
    [∀ k, IsProbabilityMeasure (μ k)] {f : ι → ι → E → E → ℝ}
    (hf_meas : ∀ i j, Measurable (Function.uncurry (f i j)))
    (hf_diag : ∀ i x y, f i i x y = 0)
    (hf_int : ∀ i j, i ≠ j → Integrable (Function.uncurry (f i j)) ((μ i).prod (μ j)))
    (hf_zero_right : ∀ i j, i ≠ j → ∀ᵐ x ∂μ i, ∫ y, f i j x y ∂μ j = 0)
    (hf_zero_left : ∀ i j, i ≠ j → ∀ᵐ y ∂μ j, ∫ x, f i j x y ∂μ i = 0)
    {Φ : ℝ → ℝ} (hΦ_conv : ConvexOn ℝ Set.univ Φ) (hΦ_cont : Continuous Φ)
    (hΦ_int_dec : Integrable (fun p : (ι → E) × (ι → E) ↦
      Φ (4 * ∑ i, ∑ j, f i j (p.1 i) (p.2 j))) ((Measure.pi μ).prod (Measure.pi μ))) :
    ∃ M : (ι → E) → ℝ,
      Integrable M (Measure.pi μ) ∧
      (∀ᵐ z ∂Measure.pi μ, Φ (∑ i, ∑ j, f i j (z i) (z j)) ≤ M z) ∧
      ∫ z, M z ∂Measure.pi μ =
        ∫ p : (ι → E) × (ι → E), Φ (4 * ∑ i, ∑ j, f i j (p.1 i) (p.2 j))
          ∂((Measure.pi μ).prod (Measure.pi μ)) := by
  classical
  let F : ((ι → E) × (ι → E)) → ℝ := fun p ↦ Φ (4 * ∑ i, ∑ j, f i j (p.1 i) (p.2 j))
  let G : (ι → Bool) → ((ι → E) × (ι → E)) → ℝ := fun δ p ↦
    Φ (4 * ∑ i, ∑ j, f i j (if δ i then p.1 i else p.2 i) (if δ j then p.2 j else p.1 j))
  have hG_eq : ∀ δ : ι → Bool, G δ = F ∘ swapCoordsEquiv δ := by
    intro δ
    ext ⟨z, w⟩
    simp only [G, F, Function.comp_apply, swapCoordsEquiv, MeasurableEquiv.ofInvolutive_apply,
      swapCoords]
  have hG_int : ∀ δ : ι → Bool, Integrable (G δ) ((Measure.pi μ).prod (Measure.pi μ)) := by
    intro δ
    rw [hG_eq δ]
    exact ((measurePreserving_swapCoords μ δ).integrable_comp_emb
      (swapCoordsEquiv δ).measurableEmbedding).2 hΦ_int_dec
  have hG_prod_int : ∀ δ : ι → Bool,
      Integrable (fun z ↦ ∫ w, G δ (z, w) ∂Measure.pi μ) (Measure.pi μ) :=
    fun δ ↦ (hG_int δ).integral_prod_left
  let c : ℝ := (Fintype.card (ι → Bool) : ℝ)⁻¹
  have hc_pos : 0 ≤ c := by positivity
  have hcard_ne : (Fintype.card (ι → Bool) : ℝ) ≠ 0 := by
    have : Nonempty (ι → Bool) := ⟨fun _ ↦ false⟩
    exact Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hc_sum : ∑ _δ : ι → Bool, c = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hcard_ne]
  let M : (ι → E) → ℝ := fun z ↦ ∑ δ : ι → Bool, c * ∫ w, G δ (z, w) ∂Measure.pi μ
  have hM_int : Integrable M (Measure.pi μ) :=
    integrable_finsetSum _ fun δ _ ↦ (hG_prod_int δ).const_mul c
  have hδ_ae : ∀ᵐ z ∂Measure.pi μ, ∀ δ : ι → Bool,
      Φ (4 * ∑ i, ∑ j, if δ i = true ∧ δ j = false then f i j (z i) (z j) else 0) ≤
        ∫ w, G δ (z, w) ∂Measure.pi μ := by
    refine ae_all_iff.2 fun δ ↦ ?_
    filter_upwards [ae_integral_swapped_eq hf_meas hf_diag hf_int hf_zero_right hf_zero_left δ,
      (hG_int δ).prod_right_ae] with z hz hG_z
    rw [← hz.2]
    exact hΦ_conv.map_integral_le hΦ_cont.continuousOn isClosed_univ
      (Filter.Eventually.of_forall fun _ ↦ Set.mem_univ _) hz.1 hG_z
  have hsum_avg : ∀ z : ι → E,
      ∑ i, ∑ j, f i j (z i) (z j) =
        ∑ δ : ι → Bool, c • (4 * ∑ i, ∑ j,
          if δ i = true ∧ δ j = false then f i j (z i) (z j) else 0) := by
    intro z
    simp only [smul_eq_mul, ← Finset.mul_sum]
    calc
      ∑ i, ∑ j, f i j (z i) (z j)
        = ∑ i, ∑ j, (c * ∑ δ : ι → Bool,
            if δ i = true ∧ δ j = false then (4 : ℝ) else 0) * f i j (z i) (z j) := by
          refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
          by_cases hij : i = j
          · subst hij; simp [hf_diag]
          · rw [selector_avg_eq_one hij, one_mul]
      _ = c * ∑ i, ∑ j, (∑ δ : ι → Bool,
            if δ i = true ∧ δ j = false then (4 : ℝ) else 0) * f i j (z i) (z j) := by
          simp_rw [mul_assoc, ← Finset.mul_sum]
      _ = c * (4 * ∑ δ : ι → Bool, ∑ i, ∑ j,
            if δ i = true ∧ δ j = false then f i j (z i) (z j) else 0) := by
          congr 1
          have hinner : ∀ i j : ι,
              (∑ δ : ι → Bool, if δ i = true ∧ δ j = false then (4 : ℝ) else 0) *
                f i j (z i) (z j) =
              ∑ δ : ι → Bool, 4 * (if δ i = true ∧ δ j = false then f i j (z i) (z j) else 0) := by
            intro i j
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun δ _ ↦ ?_
            split_ifs <;> ring
          simp_rw [hinner]
          have hswap1 : ∑ i : ι, ∑ j : ι, ∑ δ : ι → Bool,
              4 * (if δ i = true ∧ δ j = false then f i j (z i) (z j) else 0) =
              ∑ i : ι, ∑ δ : ι → Bool, ∑ j : ι,
              4 * (if δ i = true ∧ δ j = false then f i j (z i) (z j) else 0) :=
            Finset.sum_congr rfl fun i _ ↦ Finset.sum_comm
          rw [hswap1, Finset.sum_comm]
          simp_rw [← Finset.mul_sum]
  refine ⟨M, hM_int, ?_, ?_⟩
  · filter_upwards [hδ_ae] with z hz
    calc
      Φ (∑ i, ∑ j, f i j (z i) (z j))
        = Φ (∑ δ : ι → Bool, c • (4 * ∑ i, ∑ j,
            if δ i = true ∧ δ j = false then f i j (z i) (z j) else 0)) := by
          rw [hsum_avg z]
      _ ≤ ∑ δ : ι → Bool, c • Φ (4 * ∑ i, ∑ j,
            if δ i = true ∧ δ j = false then f i j (z i) (z j) else 0) :=
          hΦ_conv.map_sum_le (fun _ _ ↦ hc_pos) hc_sum (fun _ _ ↦ Set.mem_univ _)
      _ ≤ M z := by
          refine Finset.sum_le_sum fun δ _ ↦ ?_
          simpa only [smul_eq_mul] using mul_le_mul_of_nonneg_left (hz δ) hc_pos
  · dsimp [M]
    rw [integral_finsetSum _ fun δ _ ↦ (hG_prod_int δ).const_mul c]
    have hterm : ∀ δ : ι → Bool,
        ∫ z, c * (∫ w, G δ (z, w) ∂Measure.pi μ) ∂Measure.pi μ =
          c * ∫ p, F p ∂((Measure.pi μ).prod (Measure.pi μ)) := by
      intro δ
      rw [integral_const_mul, ← integral_prod _ (hG_int δ), hG_eq δ]
      congr 1
      exact (measurePreserving_swapCoords μ δ).integral_comp' F
    simp_rw [hterm, ← Finset.sum_mul, hc_sum, one_mul]
    rfl

/-- **Convex decoupling on a finite product measure.** For off-diagonal measurable kernels `fᵢⱼ`
centred in each variable under `μ`, every continuous convex function `Φ : ℝ → ℝ` satisfies
`∫ z, Φ (∑ i, ∑ j, fᵢⱼ (zᵢ) (zⱼ)) ∂(Measure.pi μ) ≤
  ∫ p, Φ (4 * ∑ i, ∑ j, fᵢⱼ (p.1 i) (p.2 j)) ∂((Measure.pi μ).prod (Measure.pi μ))`
whenever both integrals are finite. -/
theorem integral_convex_offDiag_pi_le [Fintype ι] {μ : ι → Measure E}
    [∀ k, IsProbabilityMeasure (μ k)] {f : ι → ι → E → E → ℝ}
    (hf_meas : ∀ i j, Measurable (Function.uncurry (f i j)))
    (hf_diag : ∀ i x y, f i i x y = 0)
    (hf_int : ∀ i j, i ≠ j → Integrable (Function.uncurry (f i j)) ((μ i).prod (μ j)))
    (hf_zero_right : ∀ i j, i ≠ j → ∀ᵐ x ∂μ i, ∫ y, f i j x y ∂μ j = 0)
    (hf_zero_left : ∀ i j, i ≠ j → ∀ᵐ y ∂μ j, ∫ x, f i j x y ∂μ i = 0)
    {Φ : ℝ → ℝ} (hΦ_conv : ConvexOn ℝ Set.univ Φ) (hΦ_cont : Continuous Φ)
    (hΦ_int : Integrable (fun z : ι → E ↦ Φ (∑ i, ∑ j, f i j (z i) (z j))) (Measure.pi μ))
    (hΦ_int_dec : Integrable (fun p : (ι → E) × (ι → E) ↦
      Φ (4 * ∑ i, ∑ j, f i j (p.1 i) (p.2 j))) ((Measure.pi μ).prod (Measure.pi μ))) :
    ∫ z : ι → E, Φ (∑ i, ∑ j, f i j (z i) (z j)) ∂Measure.pi μ ≤
      ∫ p : (ι → E) × (ι → E), Φ (4 * ∑ i, ∑ j, f i j (p.1 i) (p.2 j))
        ∂((Measure.pi μ).prod (Measure.pi μ)) := by
  obtain ⟨M, hM_int, hle, hM_eq⟩ := ae_le_convex_offDiag_pi hf_meas hf_diag hf_int
    hf_zero_right hf_zero_left hΦ_conv hΦ_cont hΦ_int_dec
  exact (integral_mono_ae hΦ_int hM_int hle).trans_eq hM_eq

/-- For a nonnegative continuous convex function `Φ`, integrability of the decoupled order-two sum
on `(Measure.pi μ).prod (Measure.pi μ)` automatically implies integrability of the coupled sum on
`Measure.pi μ`. -/
theorem integrable_of_nonneg_convex_offDiag_pi [Fintype ι] {μ : ι → Measure E}
    [∀ k, IsProbabilityMeasure (μ k)] {f : ι → ι → E → E → ℝ}
    (hf_meas : ∀ i j, Measurable (Function.uncurry (f i j)))
    (hf_diag : ∀ i x y, f i i x y = 0)
    (hf_int : ∀ i j, i ≠ j → Integrable (Function.uncurry (f i j)) ((μ i).prod (μ j)))
    (hf_zero_right : ∀ i j, i ≠ j → ∀ᵐ x ∂μ i, ∫ y, f i j x y ∂μ j = 0)
    (hf_zero_left : ∀ i j, i ≠ j → ∀ᵐ y ∂μ j, ∫ x, f i j x y ∂μ i = 0)
    {Φ : ℝ → ℝ} (hΦ_conv : ConvexOn ℝ Set.univ Φ) (hΦ_cont : Continuous Φ)
    (hΦ_nonneg : ∀ x, 0 ≤ Φ x)
    (hΦ_int_dec : Integrable (fun p : (ι → E) × (ι → E) ↦
      Φ (4 * ∑ i, ∑ j, f i j (p.1 i) (p.2 j))) ((Measure.pi μ).prod (Measure.pi μ))) :
    Integrable (fun z : ι → E ↦ Φ (∑ i, ∑ j, f i j (z i) (z j))) (Measure.pi μ) := by
  obtain ⟨M, hM_int, hle, _⟩ := ae_le_convex_offDiag_pi hf_meas hf_diag hf_int
    hf_zero_right hf_zero_left hΦ_conv hΦ_cont hΦ_int_dec
  have hS_meas : Measurable fun z : ι → E ↦ Φ (∑ i, ∑ j, f i j (z i) (z j)) := by
    refine hΦ_cont.measurable.comp (Finset.measurable_sum _ fun i _ ↦
      Finset.measurable_sum _ fun j _ ↦ ?_)
    exact (hf_meas i j).comp (f := fun z : ι → E ↦ (z i, z j))
      ((measurable_pi_apply i).prodMk (measurable_pi_apply j))
  refine hM_int.mono' hS_meas.aestronglyMeasurable ?_
  filter_upwards [hle] with z hz
  rwa [Real.norm_of_nonneg (hΦ_nonneg _)]

/-- **Convex decoupling on a finite product measure for nonnegative `Φ`.** No separate
integrability hypothesis on the coupled sum is needed. -/
theorem integral_nonneg_convex_offDiag_pi_le [Fintype ι] {μ : ι → Measure E}
    [∀ k, IsProbabilityMeasure (μ k)] {f : ι → ι → E → E → ℝ}
    (hf_meas : ∀ i j, Measurable (Function.uncurry (f i j)))
    (hf_diag : ∀ i x y, f i i x y = 0)
    (hf_int : ∀ i j, i ≠ j → Integrable (Function.uncurry (f i j)) ((μ i).prod (μ j)))
    (hf_zero_right : ∀ i j, i ≠ j → ∀ᵐ x ∂μ i, ∫ y, f i j x y ∂μ j = 0)
    (hf_zero_left : ∀ i j, i ≠ j → ∀ᵐ y ∂μ j, ∫ x, f i j x y ∂μ i = 0)
    {Φ : ℝ → ℝ} (hΦ_conv : ConvexOn ℝ Set.univ Φ) (hΦ_cont : Continuous Φ)
    (hΦ_nonneg : ∀ x, 0 ≤ Φ x)
    (hΦ_int_dec : Integrable (fun p : (ι → E) × (ι → E) ↦
      Φ (4 * ∑ i, ∑ j, f i j (p.1 i) (p.2 j))) ((Measure.pi μ).prod (Measure.pi μ))) :
    ∫ z : ι → E, Φ (∑ i, ∑ j, f i j (z i) (z j)) ∂Measure.pi μ ≤
      ∫ p : (ι → E) × (ι → E), Φ (4 * ∑ i, ∑ j, f i j (p.1 i) (p.2 j))
        ∂((Measure.pi μ).prod (Measure.pi μ)) :=
  integral_convex_offDiag_pi_le hf_meas hf_diag hf_int hf_zero_right hf_zero_left hΦ_conv hΦ_cont
    (integrable_of_nonneg_convex_offDiag_pi hf_meas hf_diag hf_int hf_zero_right hf_zero_left
      hΦ_conv hΦ_cont hΦ_nonneg hΦ_int_dec) hΦ_int_dec

end ProductMeasure

namespace iIndepFun

section General

variable {Ω ι E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [Fintype ι]
  {P : Measure Ω} {X : ι → Ω → E}

omit [Fintype ι] in
/-- Shared pushforward setup from `(Ω, P)` to `Measure.pi (fun i ↦ P.map (X i))`. -/
private theorem pi_hypotheses_of_indep (hindep : iIndepFun X P)
    (hX : ∀ i, AEMeasurable (X i) P) {f : ι → ι → E → E → ℝ}
    (hf_meas : ∀ i j, Measurable (Function.uncurry (f i j)))
    (hf_int : ∀ i j, i ≠ j → Integrable (fun p : Ω × Ω ↦ f i j (X i p.1) (X j p.2)) (P.prod P))
    (hf_zero_right : ∀ i j x, i ≠ j → ∫ ω', f i j x (X j ω') ∂P = 0)
    (hf_zero_left : ∀ i j y, i ≠ j → ∫ ω, f i j (X i ω) y ∂P = 0) :
    (∀ i j, i ≠ j → Integrable (Function.uncurry (f i j)) ((P.map (X i)).prod (P.map (X j)))) ∧
    (∀ i j, i ≠ j → ∀ᵐ x ∂P.map (X i), ∫ y, f i j x y ∂P.map (X j) = 0) ∧
    (∀ i j, i ≠ j → ∀ᵐ y ∂P.map (X j), ∫ x, f i j x y ∂P.map (X i) = 0) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  refine ⟨fun i j hij ↦ ?_, fun i j hij ↦ ?_, fun i j hij ↦ ?_⟩
  · have hpair_map : (P.prod P).map (fun p : Ω × Ω ↦ (X i p.1, X j p.2)) =
        (P.map (X i)).prod (P.map (X j)) :=
      (Measure.map_prod_map_of_aemeasurable P P (hX i) (hX j)).symm
    have hpair_meas : AEMeasurable (fun p : Ω × Ω ↦ (X i p.1, X j p.2)) (P.prod P) :=
      ((hX i).comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).prodMk
        ((hX j).comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
    rw [← hpair_map, integrable_map_measure (hf_meas i j).aestronglyMeasurable hpair_meas]
    exact hf_int i j hij
  · refine Filter.Eventually.of_forall fun x ↦ ?_
    have hm : Measurable (fun y ↦ f i j x y) :=
      (hf_meas i j).comp (f := fun y ↦ (x, y)) (measurable_const.prodMk measurable_id)
    rw [integral_map (hX j) hm.aestronglyMeasurable]
    exact hf_zero_right i j x hij
  · refine Filter.Eventually.of_forall fun y ↦ ?_
    have hm : Measurable (fun x ↦ f i j x y) :=
      (hf_meas i j).comp (f := fun x ↦ (x, y)) (measurable_id.prodMk measurable_const)
    rw [integral_map (hX i) hm.aestronglyMeasurable]
    exact hf_zero_left i j y hij

/-- **Convex decoupling for an independent family.** Let `(Xᵢ)` be independent and a.e.-measurable,
and let `fᵢⱼ : E → E → ℝ` be measurable off-diagonal kernels centred in each variable against `X`.
Then for every continuous convex function `Φ : ℝ → ℝ`,
`∫ ω, Φ (∑ i, ∑ j, fᵢⱼ (Xᵢ ω) (Xⱼ ω)) ∂P ≤
  ∫ p, Φ (4 * ∑ i, ∑ j, fᵢⱼ (Xᵢ p.1) (Xⱼ p.2)) ∂(P.prod P)`. -/
theorem integral_convex_offDiag_le (hindep : iIndepFun X P) (hX : ∀ i, AEMeasurable (X i) P)
    {f : ι → ι → E → E → ℝ}
    (hf_meas : ∀ i j, Measurable (Function.uncurry (f i j)))
    (hf_diag : ∀ i x y, f i i x y = 0)
    (hf_int : ∀ i j, i ≠ j → Integrable (fun p : Ω × Ω ↦ f i j (X i p.1) (X j p.2)) (P.prod P))
    (hf_zero_right : ∀ i j x, i ≠ j → ∫ ω', f i j x (X j ω') ∂P = 0)
    (hf_zero_left : ∀ i j y, i ≠ j → ∫ ω, f i j (X i ω) y ∂P = 0)
    {Φ : ℝ → ℝ} (hΦ_conv : ConvexOn ℝ Set.univ Φ) (hΦ_cont : Continuous Φ)
    (hΦ_int : Integrable (fun ω ↦ Φ (∑ i, ∑ j, f i j (X i ω) (X j ω))) P)
    (hΦ_int_dec : Integrable (fun p : Ω × Ω ↦
      Φ (4 * ∑ i, ∑ j, f i j (X i p.1) (X j p.2))) (P.prod P)) :
    ∫ ω, Φ (∑ i, ∑ j, f i j (X i ω) (X j ω)) ∂P ≤
      ∫ p : Ω × Ω, Φ (4 * ∑ i, ∑ j, f i j (X i p.1) (X j p.2)) ∂(P.prod P) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  obtain ⟨hf_int_μ, hf_zr_μ, hf_zl_μ⟩ :=
    hindep.pi_hypotheses_of_indep hX hf_meas hf_int hf_zero_right hf_zero_left
  let μ : ι → Measure E := fun i ↦ P.map (X i)
  have hvec : AEMeasurable (fun ω i ↦ X i ω) P := AEMeasurable.of_eval hX
  have hvec2 : AEMeasurable (fun p : Ω × Ω ↦ (fun i ↦ X i p.1, fun i ↦ X i p.2)) (P.prod P) :=
    (hvec.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).prodMk
      (hvec.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
  have hmap1 : P.map (fun ω i ↦ X i ω) = Measure.pi μ := hindep.map_fun_eq_pi_map hX
  have hmap2 : (P.prod P).map (fun p : Ω × Ω ↦ (fun i ↦ X i p.1, fun i ↦ X i p.2)) =
      (Measure.pi μ).prod (Measure.pi μ) := by
    rw [← hmap1]
    exact (Measure.map_prod_map_of_aemeasurable P P hvec hvec).symm
  have hS1_meas : Measurable (fun z : ι → E ↦ Φ (∑ i, ∑ j, f i j (z i) (z j))) :=
    hΦ_cont.measurable.comp <| Finset.measurable_sum _ fun i _ ↦
      Finset.measurable_sum _ fun j _ ↦
        (hf_meas i j).comp (f := fun z : ι → E ↦ (z i, z j))
          ((measurable_pi_apply i).prodMk (measurable_pi_apply j))
  have hS2_meas : Measurable (fun q : (ι → E) × (ι → E) ↦
      Φ (4 * ∑ i, ∑ j, f i j (q.1 i) (q.2 j))) :=
    hΦ_cont.measurable.comp <| measurable_const.mul <| Finset.measurable_sum _ fun i _ ↦
      Finset.measurable_sum _ fun j _ ↦
        (hf_meas i j).comp (f := fun q : (ι → E) × (ι → E) ↦ (q.1 i, q.2 j))
          (((measurable_pi_apply i).comp measurable_fst).prodMk
            ((measurable_pi_apply j).comp measurable_snd))
  have hΦ_int_pi : Integrable (fun z : ι → E ↦ Φ (∑ i, ∑ j, f i j (z i) (z j)))
      (Measure.pi μ) := by
    rw [← hmap1, integrable_map_measure hS1_meas.aestronglyMeasurable hvec]
    exact hΦ_int
  have hΦ_int_dec_pi : Integrable (fun q : (ι → E) × (ι → E) ↦
      Φ (4 * ∑ i, ∑ j, f i j (q.1 i) (q.2 j))) ((Measure.pi μ).prod (Measure.pi μ)) := by
    rw [← hmap2, integrable_map_measure hS2_meas.aestronglyMeasurable hvec2]
    exact hΦ_int_dec
  have hle := integral_convex_offDiag_pi_le hf_meas hf_diag hf_int_μ hf_zr_μ hf_zl_μ
    hΦ_conv hΦ_cont hΦ_int_pi hΦ_int_dec_pi
  rwa [← hmap2, integral_map hvec2 hS2_meas.aestronglyMeasurable,
    ← hmap1, integral_map hvec hS1_meas.aestronglyMeasurable] at hle

/-- For nonnegative continuous convex `Φ`, integrability of the decoupled statistic on `P.prod P`
implies integrability of the coupled off-diagonal statistic on `P`. -/
theorem integrable_of_nonneg_convex_offDiag (hindep : iIndepFun X P)
    (hX : ∀ i, AEMeasurable (X i) P) {f : ι → ι → E → E → ℝ}
    (hf_meas : ∀ i j, Measurable (Function.uncurry (f i j)))
    (hf_diag : ∀ i x y, f i i x y = 0)
    (hf_int : ∀ i j, i ≠ j → Integrable (fun p : Ω × Ω ↦ f i j (X i p.1) (X j p.2)) (P.prod P))
    (hf_zero_right : ∀ i j x, i ≠ j → ∫ ω', f i j x (X j ω') ∂P = 0)
    (hf_zero_left : ∀ i j y, i ≠ j → ∫ ω, f i j (X i ω) y ∂P = 0)
    {Φ : ℝ → ℝ} (hΦ_conv : ConvexOn ℝ Set.univ Φ) (hΦ_cont : Continuous Φ)
    (hΦ_nonneg : ∀ x, 0 ≤ Φ x)
    (hΦ_int_dec : Integrable (fun p : Ω × Ω ↦
      Φ (4 * ∑ i, ∑ j, f i j (X i p.1) (X j p.2))) (P.prod P)) :
    Integrable (fun ω ↦ Φ (∑ i, ∑ j, f i j (X i ω) (X j ω))) P := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  obtain ⟨hf_int_μ, hf_zr_μ, hf_zl_μ⟩ :=
    hindep.pi_hypotheses_of_indep hX hf_meas hf_int hf_zero_right hf_zero_left
  let μ : ι → Measure E := fun i ↦ P.map (X i)
  have hvec : AEMeasurable (fun ω i ↦ X i ω) P := AEMeasurable.of_eval hX
  have hvec2 : AEMeasurable (fun p : Ω × Ω ↦ (fun i ↦ X i p.1, fun i ↦ X i p.2)) (P.prod P) :=
    (hvec.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).prodMk
      (hvec.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
  have hmap1 : P.map (fun ω i ↦ X i ω) = Measure.pi μ := hindep.map_fun_eq_pi_map hX
  have hmap2 : (P.prod P).map (fun p : Ω × Ω ↦ (fun i ↦ X i p.1, fun i ↦ X i p.2)) =
      (Measure.pi μ).prod (Measure.pi μ) := by
    rw [← hmap1]
    exact (Measure.map_prod_map_of_aemeasurable P P hvec hvec).symm
  have hS1_meas : Measurable (fun z : ι → E ↦ Φ (∑ i, ∑ j, f i j (z i) (z j))) :=
    hΦ_cont.measurable.comp <| Finset.measurable_sum _ fun i _ ↦
      Finset.measurable_sum _ fun j _ ↦
        (hf_meas i j).comp (f := fun z : ι → E ↦ (z i, z j))
          ((measurable_pi_apply i).prodMk (measurable_pi_apply j))
  have hS2_meas : Measurable (fun q : (ι → E) × (ι → E) ↦
      Φ (4 * ∑ i, ∑ j, f i j (q.1 i) (q.2 j))) :=
    hΦ_cont.measurable.comp <| measurable_const.mul <| Finset.measurable_sum _ fun i _ ↦
      Finset.measurable_sum _ fun j _ ↦
        (hf_meas i j).comp (f := fun q : (ι → E) × (ι → E) ↦ (q.1 i, q.2 j))
          (((measurable_pi_apply i).comp measurable_fst).prodMk
            ((measurable_pi_apply j).comp measurable_snd))
  have hΦ_int_dec_pi : Integrable (fun q : (ι → E) × (ι → E) ↦
      Φ (4 * ∑ i, ∑ j, f i j (q.1 i) (q.2 j))) ((Measure.pi μ).prod (Measure.pi μ)) := by
    rw [← hmap2, integrable_map_measure hS2_meas.aestronglyMeasurable hvec2]
    exact hΦ_int_dec
  have hpi := integrable_of_nonneg_convex_offDiag_pi hf_meas hf_diag hf_int_μ hf_zr_μ hf_zl_μ
    hΦ_conv hΦ_cont hΦ_nonneg hΦ_int_dec_pi
  rwa [← hmap1, integrable_map_measure hS1_meas.aestronglyMeasurable hvec] at hpi

/-- **Convex decoupling for an independent family and nonnegative `Φ`.** -/
theorem integral_nonneg_convex_offDiag_le (hindep : iIndepFun X P)
    (hX : ∀ i, AEMeasurable (X i) P) {f : ι → ι → E → E → ℝ}
    (hf_meas : ∀ i j, Measurable (Function.uncurry (f i j)))
    (hf_diag : ∀ i x y, f i i x y = 0)
    (hf_int : ∀ i j, i ≠ j → Integrable (fun p : Ω × Ω ↦ f i j (X i p.1) (X j p.2)) (P.prod P))
    (hf_zero_right : ∀ i j x, i ≠ j → ∫ ω', f i j x (X j ω') ∂P = 0)
    (hf_zero_left : ∀ i j y, i ≠ j → ∫ ω, f i j (X i ω) y ∂P = 0)
    {Φ : ℝ → ℝ} (hΦ_conv : ConvexOn ℝ Set.univ Φ) (hΦ_cont : Continuous Φ)
    (hΦ_nonneg : ∀ x, 0 ≤ Φ x)
    (hΦ_int_dec : Integrable (fun p : Ω × Ω ↦
      Φ (4 * ∑ i, ∑ j, f i j (X i p.1) (X j p.2))) (P.prod P)) :
    ∫ ω, Φ (∑ i, ∑ j, f i j (X i ω) (X j ω)) ∂P ≤
      ∫ p : Ω × Ω, Φ (4 * ∑ i, ∑ j, f i j (X i p.1) (X j p.2)) ∂(P.prod P) :=
  hindep.integral_convex_offDiag_le hX hf_meas hf_diag hf_int hf_zero_right hf_zero_left
    hΦ_conv hΦ_cont
    (hindep.integrable_of_nonneg_convex_offDiag hX hf_meas hf_diag hf_int hf_zero_right
      hf_zero_left hΦ_conv hΦ_cont hΦ_nonneg hΦ_int_dec) hΦ_int_dec

end General

section QuadraticForms

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {P : Measure Ω}

/-- **Exponential-moment decoupling for real off-diagonal quadratic forms.** Let `(Xᵢ)` be
independent, integrable, mean-zero real random variables and let `B` be a real square matrix with
zero diagonal. If the decoupled bilinear form `(p : Ω × Ω) ↦ (fun i ↦ X i p.1) ⬝ᵥ B *ᵥ
(fun i ↦ X i p.2)` has finite exponential moment at `4 * t` under `P.prod P`, then the coupled
quadratic form `ω ↦ (fun i ↦ X i ω) ⬝ᵥ B *ᵥ (fun i ↦ X i ω)` has finite exponential moment at `t`
under `P` and its moment-generating function at `t` is bounded by the decoupled one at `4 * t`. -/
theorem mgf_offDiag_dotProduct_mulVec_le {X : ι → Ω → ℝ} (hindep : iIndepFun X P)
    (hX_int : ∀ i, Integrable (X i) P) (hX_mean : ∀ i, P[X i] = 0)
    {B : Matrix ι ι ℝ} (hB_diag : ∀ i, B i i = 0) {t : ℝ}
    (hint_dec : Integrable (fun p : Ω × Ω ↦
      exp (4 * t * ((fun i ↦ X i p.1) ⬝ᵥ B *ᵥ (fun i ↦ X i p.2)))) (P.prod P)) :
    Integrable (fun ω ↦ exp (t * ((fun i ↦ X i ω) ⬝ᵥ B *ᵥ (fun i ↦ X i ω)))) P ∧
    mgf (fun ω ↦ (fun i ↦ X i ω) ⬝ᵥ B *ᵥ (fun i ↦ X i ω)) P t ≤
      mgf (fun p : Ω × Ω ↦ (fun i ↦ X i p.1) ⬝ᵥ B *ᵥ (fun i ↦ X i p.2)) (P.prod P) (4 * t) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  let f : ι → ι → ℝ → ℝ → ℝ := fun i j x y ↦ x * (B i j * y)
  have hquad : ∀ u v : ι → ℝ, u ⬝ᵥ B *ᵥ v = ∑ i, ∑ j, f i j (u i) (v j) := by
    intro u v
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, f]
  let Φ : ℝ → ℝ := fun z ↦ exp (t * z)
  have hΦ_conv : ConvexOn ℝ Set.univ Φ :=
    convexOn_exp.comp_linearMap (LinearMap.mul ℝ ℝ t)
  have hΦ_cont : Continuous Φ := by fun_prop
  have hΦ_nonneg : ∀ z, 0 ≤ Φ z := fun z ↦ (exp_pos _).le
  have hf_meas : ∀ i j, Measurable (Function.uncurry (f i j)) := by
    intro i j
    dsimp only [Function.uncurry, f]
    fun_prop
  have hf_diag : ∀ i x y, f i i x y = 0 := fun i x y ↦ by simp [f, hB_diag i]
  have hf_int : ∀ i j, i ≠ j →
      Integrable (fun p : Ω × Ω ↦ f i j (X i p.1) (X j p.2)) (P.prod P) :=
    fun i j _ ↦ (hX_int i).mul_prod ((hX_int j).const_mul (B i j))
  have hf_zr : ∀ i j x, i ≠ j → ∫ ω', f i j x (X j ω') ∂P = 0 := by
    intro i j x _
    simp only [f, ← mul_assoc, integral_const_mul, hX_mean j, mul_zero]
  have hf_zl : ∀ i j y, i ≠ j → ∫ ω, f i j (X i ω) y ∂P = 0 := by
    intro i j y _
    simp only [f, integral_mul_const, hX_mean i, zero_mul]
  have hint_dec' : Integrable (fun p : Ω × Ω ↦
      Φ (4 * ∑ i, ∑ j, f i j (X i p.1) (X j p.2))) (P.prod P) := by
    refine hint_dec.congr (Filter.Eventually.of_forall fun p ↦ ?_)
    simp only [Φ, ← hquad]
    ring_nf
  have hint_coup := hindep.integrable_of_nonneg_convex_offDiag
    (fun i ↦ (hX_int i).aemeasurable) hf_meas hf_diag hf_int hf_zr hf_zl
    hΦ_conv hΦ_cont hΦ_nonneg hint_dec'
  have hle := hindep.integral_nonneg_convex_offDiag_le
    (fun i ↦ (hX_int i).aemeasurable) hf_meas hf_diag hf_int hf_zr hf_zl
    hΦ_conv hΦ_cont hΦ_nonneg hint_dec'
  refine ⟨?_, ?_⟩
  · simpa only [Φ, ← hquad] using hint_coup
  · simp only [mgf]
    refine (integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)).trans_le
      (hle.trans_eq (integral_congr_ae (Filter.Eventually.of_forall fun p ↦ ?_)))
    · simp only [Φ, ← hquad]
    · simp only [Φ, ← hquad]; ring_nf

/-- **Exponential-moment decoupling for `RCLike` off-diagonal sesquilinear forms.** Let `(Zᵢ)` be
independent, integrable, mean-zero `𝕜`-valued random variables (`[RCLike 𝕜]`) and let `B` be a
`𝕜`-matrix with zero diagonal. Then the real part of `star Z ⬝ᵥ B *ᵥ Z` decouples with constant
`4` in exponential moments. -/
theorem mgf_offDiag_re_star_dotProduct_mulVec_le {𝕜 : Type*} [RCLike 𝕜]
    {Z : ι → Ω → 𝕜} (hindep : iIndepFun Z P)
    (hZ_int : ∀ i, Integrable (Z i) P) (hZ_mean : ∀ i, ∫ ω, Z i ω ∂P = 0)
    {B : Matrix ι ι 𝕜} (hB_diag : ∀ i, B i i = 0) {t : ℝ}
    (hint_dec : Integrable (fun p : Ω × Ω ↦
      exp (4 * t * RCLike.re (star (fun i ↦ Z i p.1) ⬝ᵥ B *ᵥ (fun i ↦ Z i p.2))))
      (P.prod P)) :
    Integrable (fun ω ↦
      exp (t * RCLike.re (star (fun i ↦ Z i ω) ⬝ᵥ B *ᵥ (fun i ↦ Z i ω)))) P ∧
    mgf (fun ω ↦ RCLike.re (star (fun i ↦ Z i ω) ⬝ᵥ B *ᵥ (fun i ↦ Z i ω))) P t ≤
      mgf (fun p : Ω × Ω ↦ RCLike.re (star (fun i ↦ Z i p.1) ⬝ᵥ B *ᵥ (fun i ↦ Z i p.2)))
        (P.prod P) (4 * t) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  let f : ι → ι → 𝕜 → 𝕜 → ℝ := fun i j x y ↦ RCLike.re (star x * (B i j * y))
  have hsesq : ∀ u v : ι → 𝕜,
      RCLike.re (star u ⬝ᵥ B *ᵥ v) = ∑ i, ∑ j, f i j (u i) (v j) := by
    intro u v
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, map_sum, f]
  let Φ : ℝ → ℝ := fun z ↦ exp (t * z)
  have hΦ_conv : ConvexOn ℝ Set.univ Φ :=
    convexOn_exp.comp_linearMap (LinearMap.mul ℝ ℝ t)
  have hΦ_cont : Continuous Φ := by fun_prop
  have hΦ_nonneg : ∀ z, 0 ≤ Φ z := fun z ↦ (exp_pos _).le
  have hf_meas : ∀ i j, Measurable (Function.uncurry (f i j)) := by
    intro i j
    dsimp only [Function.uncurry, f]
    fun_prop
  have hf_diag : ∀ i x y, f i i x y = 0 := fun i x y ↦ by simp [f, hB_diag i]
  have hZ_star_int : ∀ i, Integrable (fun ω ↦ star (Z i ω)) P := fun i ↦
    (hZ_int i).mono (continuous_star.comp_aestronglyMeasurable (hZ_int i).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω ↦ by simp)
  have hf_int : ∀ i j, i ≠ j →
      Integrable (fun p : Ω × Ω ↦ f i j (Z i p.1) (Z j p.2)) (P.prod P) := by
    intro i j _
    exact ((hZ_star_int i).mul_prod ((hZ_int j).const_mul (B i j))).re
  have hf_zr : ∀ i j x, i ≠ j → ∫ ω', f i j x (Z j ω') ∂P = 0 := by
    intro i j x _
    dsimp only [f]
    rw [integral_re (((hZ_int j).const_mul (B i j)).const_mul (star x))]
    simp [← mul_assoc, integral_const_mul, hZ_mean j]
  have hf_zl : ∀ i j y, i ≠ j → ∫ ω, f i j (Z i ω) y ∂P = 0 := by
    intro i j y _
    dsimp only [f]
    rw [integral_re ((hZ_star_int i).mul_const (B i j * y)), integral_mul_const]
    have hstar : ∫ ω, star (Z i ω) ∂P = 0 := by
      simp_rw [RCLike.star_def, integral_conj, hZ_mean i, map_zero]
    rw [hstar, zero_mul, map_zero]
  have hint_dec' : Integrable (fun p : Ω × Ω ↦
      Φ (4 * ∑ i, ∑ j, f i j (Z i p.1) (Z j p.2))) (P.prod P) := by
    refine hint_dec.congr (Filter.Eventually.of_forall fun p ↦ ?_)
    simp only [Φ, ← hsesq]
    ring_nf
  have hint_coup := hindep.integrable_of_nonneg_convex_offDiag
    (fun i ↦ (hZ_int i).aemeasurable) hf_meas hf_diag hf_int hf_zr hf_zl
    hΦ_conv hΦ_cont hΦ_nonneg hint_dec'
  have hle := hindep.integral_nonneg_convex_offDiag_le
    (fun i ↦ (hZ_int i).aemeasurable) hf_meas hf_diag hf_int hf_zr hf_zl
    hΦ_conv hΦ_cont hΦ_nonneg hint_dec'
  refine ⟨?_, ?_⟩
  · simpa only [Φ, ← hsesq] using hint_coup
  · simp only [mgf]
    refine (integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)).trans_le
      (hle.trans_eq (integral_congr_ae (Filter.Eventually.of_forall fun p ↦ ?_)))
    · simp only [Φ, ← hsesq]
    · simp only [Φ, ← hsesq]; ring_nf

end QuadraticForms

end iIndepFun

end ProbabilityTheory
