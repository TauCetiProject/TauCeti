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

For independent random variables `(Xᵢ)` in `E` and measurable off-diagonal kernels `fᵢⱼ : E → E → ℝ`
centred in each variable (`fᵢᵢ = 0`), every continuous convex function `Φ : ℝ → ℝ` satisfies
`E[Φ (∑ i, ∑ j, fᵢⱼ (Xᵢ) (Xⱼ))] ≤ E[Φ (4 * ∑ i, ∑ j, fᵢⱼ (Xᵢ) (X'ⱼ))]` against an independent copy
`(X'ᵢ)` (de la Peña–Giné 1999, Theorem 3.1.1; Vershynin 2018, Theorem 6.1.1). We prove this on
product measures and for `iIndepFun` families, and specialize to MGFs of real and `RCLike`
off-diagonal quadratic forms.
-/

public section

open MeasureTheory Real Matrix

namespace ProbabilityTheory

section ProductMeasure

variable {ι E : Type*} [MeasurableSpace E]

private def swapCoords (δ : ι → Bool) (p : (ι → E) × (ι → E)) : (ι → E) × (ι → E) :=
  (fun k ↦ if δ k then p.1 k else p.2 k, fun k ↦ if δ k then p.2 k else p.1 k)
omit [MeasurableSpace E] in
private theorem involutive_swapCoords (δ : ι → Bool) :
    Function.Involutive (swapCoords (E := E) δ) := fun ⟨_, _⟩ ↦ by
  ext k <;> dsimp [swapCoords] <;> cases δ k <;> rfl
private theorem measurable_swapCoords (δ : ι → Bool) : Measurable (swapCoords (E := E) δ) := by
  refine (Measurable.of_eval fun k ↦ ?_).prodMk (Measurable.of_eval fun k ↦ ?_) <;> cases δ k <;>
    exact (measurable_pi_apply k).comp (by first | exact measurable_fst | exact measurable_snd)
private noncomputable def swapCoordsEquiv (δ : ι → Bool) :
    ((ι → E) × (ι → E)) ≃ᵐ ((ι → E) × (ι → E)) :=
  MeasurableEquiv.ofInvolutive (swapCoords δ) (involutive_swapCoords δ) (measurable_swapCoords δ)
private theorem measurePreserving_swapCoords [Fintype ι] (μ : ι → Measure E)
    [∀ k, SigmaFinite (μ k)] (δ : ι → Bool) :
    MeasurePreserving (swapCoordsEquiv (E := E) δ)
      ((Measure.pi μ).prod (Measure.pi μ)) ((Measure.pi μ).prod (Measure.pi μ)) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow E E ι
  have he := measurePreserving_arrowProdEquivProdArrow E E ι μ μ
  let step : ∀ k : ι, E × E → E × E := fun k p ↦ if δ k then p else p.swap
  have hstep_meas (k : ι) : Measurable (step k) := by
    cases h : δ k <;> simpa [step, h] using (by first | exact measurable_swap | exact measurable_id)
  have hstep_map (k : ι) : ((μ k).prod (μ k)).map (step k) = (μ k).prod (μ k) := by
    cases h : δ k <;> [simpa [step, h] using Measure.prod_swap; simp [step, h]]
  have hpi : MeasurePreserving (fun h k ↦ step k (h k))
      (Measure.pi fun k ↦ (μ k).prod (μ k)) (Measure.pi fun k ↦ (μ k).prod (μ k)) := by
    refine ⟨Measurable.of_eval fun k ↦ (hstep_meas k).comp (measurable_pi_apply k), ?_⟩
    have (k : ι) : SigmaFinite (((μ k).prod (μ k)).map (step k)) :=
      (hstep_map k).symm ▸ inferInstance
    rw [Measure.pi_map_pi fun k ↦ (hstep_meas k).aemeasurable]; simp only [hstep_map]
  have hcomp : (swapCoordsEquiv (E := E) δ : ((ι → E) × (ι → E)) → ((ι → E) × (ι → E))) =
      e ∘ (fun h k ↦ step k (h k)) ∘ e.symm := by
    change swapCoords δ = (fun f ↦ (fun k ↦ (f k).1, fun k ↦ (f k).2)) ∘
      (fun h k ↦ step k (h k)) ∘ (fun p k ↦ (p.1 k, p.2 k))
    ext ⟨_, _⟩ k <;> (dsimp [swapCoords, step]; cases δ k <;> rfl)
  exact ⟨(swapCoordsEquiv δ).measurable, hcomp ▸ (he.comp (hpi.comp he.symm)).map_eq⟩
private theorem selector_avg_eq_one [Fintype ι] [DecidableEq ι] {i j : ι} (hij : i ≠ j) :
    (Fintype.card (ι → Bool) : ℝ)⁻¹ *
      ∑ δ : ι → Bool, (if δ i = true ∧ δ j = false then (4 : ℝ) else 0) = 1 := by
  let g : (ι → Bool) → ℝ := fun δ ↦ if δ i = true ∧ δ j = false then 1 else 0
  let upd (k : ι) (δ : ι → Bool) := Function.update δ k (!δ k)
  have hinv (k : ι) : Function.Involutive (upd k) := fun δ ↦ by
    ext l; by_cases h : l = k <;> simp [upd, h]
  have hpt (δ : ι → Bool) : g δ + g (upd i δ) + g (upd j δ) + g (upd j (upd i δ)) = 1 := by
    simp only [g, upd, Function.update_self, Function.update_of_ne hij,
      Function.update_of_ne hij.symm]; cases δ i <;> cases δ j <;> norm_num
  have htot : ∑ δ : ι → Bool, (g δ + g (upd i δ) + g (upd j δ) + g (upd j (upd i δ))) =
      Fintype.card (ι → Bool) := by simp [hpt]
  simp only [Finset.sum_add_distrib] at htot
  have h1 : ∑ δ, g (upd i δ) = ∑ δ, g δ := Equiv.sum_comp (hinv i).toPerm g
  have h2 : ∑ δ, g (upd j δ) = ∑ δ, g δ := Equiv.sum_comp (hinv j).toPerm g
  have h3 : ∑ δ, g (upd j (upd i δ)) = ∑ δ, g δ :=
    Equiv.sum_comp ((hinv i).toPerm.trans (hinv j).toPerm) g
  have : Nonempty (ι → Bool) := ⟨fun _ ↦ false⟩
  have hcard : (Fintype.card (ι → Bool) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [show ∑ δ : ι → Bool, (if δ i = true ∧ δ j = false then (4 : ℝ) else 0) = 4 * ∑ δ, g δ by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ ↦ ?_; dsimp [g]; split_ifs <;> ring,
    show 4 * ∑ δ, g δ = Fintype.card (ι → Bool) by linarith, inv_mul_cancel₀ hcard]
private theorem measurePreserving_eval_pair [Fintype ι] (μ : ι → Measure E)
    [∀ k, IsProbabilityMeasure (μ k)] {i j : ι} (hij : i ≠ j) :
    MeasurePreserving (fun w : ι → E ↦ (w i, w j)) (Measure.pi μ) ((μ i).prod (μ j)) := by
  refine ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j), ?_⟩
  rw [((iIndepFun_pi (μ := μ) fun _ ↦ aemeasurable_id).indepFun hij).map_prod_eq_prod_map_map
      (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable,
    (measurePreserving_eval μ i).map_eq, (measurePreserving_eval μ j).map_eq]
private theorem ae_slice_pi_eq_zero [Fintype ι] (μ : ι → Measure E)
    [∀ k, IsProbabilityMeasure (μ k)] (g : E → E → ℝ) (hg : Measurable (Function.uncurry g))
    (a b : ι) (hae_int : ∀ᵐ x ∂μ a, Integrable (g x) (μ b))
    (hae_zero : ∀ᵐ x ∂μ a, ∫ y, g x y ∂μ b = 0) :
    ∀ᵐ z ∂Measure.pi μ, Integrable (fun w : ι → E ↦ g (z a) (w b)) (Measure.pi μ) ∧
      (∫ w : ι → E, g (z a) (w b) ∂Measure.pi μ) = 0 := by
  filter_upwards [(measurePreserving_eval μ a).quasiMeasurePreserving.ae hae_int,
    (measurePreserving_eval μ a).quasiMeasurePreserving.ae hae_zero] with z hz_int hz_zero
  have hm : Measurable (g (z a)) := hg.comp (measurable_const.prodMk measurable_id)
  have heval := (measurePreserving_eval μ b).map_eq
  have ha : AEMeasurable (fun w : ι → E ↦ w b) (Measure.pi μ) :=
    (measurable_pi_apply b).aemeasurable
  exact ⟨(integrable_map_measure hm.aestronglyMeasurable ha).mp (heval.symm ▸ hz_int),
    (heval ▸ integral_map ha hm.aestronglyMeasurable).symm.trans hz_zero⟩
private theorem ae_integral_swapped_eq [Fintype ι] {μ : ι → Measure E}
    [∀ k, IsProbabilityMeasure (μ k)] {f : ι → ι → E → E → ℝ}
    (hf_meas : ∀ i j, Measurable (Function.uncurry (f i j))) (hf_diag : ∀ i x y, f i i x y = 0)
    (hf_int : ∀ i j, i ≠ j → Integrable (Function.uncurry (f i j)) ((μ i).prod (μ j)))
    (hf_zero_right : ∀ i j, i ≠ j → ∀ᵐ x ∂μ i, ∫ y, f i j x y ∂μ j = 0)
    (hf_zero_left : ∀ i j, i ≠ j → ∀ᵐ y ∂μ j, ∫ x, f i j x y ∂μ i = 0) (δ : ι → Bool) :
    ∀ᵐ z ∂Measure.pi μ, Integrable (fun w : ι → E ↦
        4 * ∑ i, ∑ j, f i j (if δ i then z i else w i) (if δ j then w j else z j)) (Measure.pi μ) ∧
      (∫ w : ι → E, (4 * ∑ i, ∑ j, f i j (if δ i then z i else w i) (if δ j then w j else z j))
        ∂Measure.pi μ) =
        4 * ∑ i, ∑ j, if δ i = true ∧ δ j = false then f i j (z i) (z j) else 0 := by
  classical
  have hcell (i j : ι) : ∀ᵐ z ∂Measure.pi μ,
      Integrable (fun w : ι → E ↦ f i j (if δ i then z i else w i) (if δ j then w j else z j))
        (Measure.pi μ) ∧
      (∫ w : ι → E, f i j (if δ i then z i else w i) (if δ j then w j else z j) ∂Measure.pi μ) =
        if δ i = true ∧ δ j = false then f i j (z i) (z j) else 0 := by
    by_cases hij : i = j
    · subst hij; exact .of_forall fun _ ↦ by simp [hf_diag]
    · cases hdi : δ i <;> cases hdj : δ j
      · simpa using ae_slice_pi_eq_zero μ (fun y x ↦ f i j x y)
          ((hf_meas i j).comp measurable_swap) j i (hf_int i j hij).prod_left_ae
          (hf_zero_left i j hij)
      · have hpair := measurePreserving_eval_pair μ hij
        refine .of_forall fun _ ↦ ?_
        simp only [Bool.false_eq_true, false_and, ↓reduceIte]
        refine ⟨(integrable_map_measure (hf_meas i j).aestronglyMeasurable
          hpair.measurable.aemeasurable).mp (hpair.map_eq.symm ▸ hf_int i j hij),
          (integral_map hpair.measurable.aemeasurable
            (hf_meas i j).aestronglyMeasurable).symm.trans ?_⟩
        rw [hpair.map_eq, integral_prod _ (hf_int i j hij)]
        simpa using integral_congr_ae (hf_zero_right i j hij)
      · exact .of_forall fun _ ↦ by simp
      · simpa using ae_slice_pi_eq_zero μ (f i j) (hf_meas i j) i j
          (hf_int i j hij).prod_right_ae (hf_zero_right i j hij)
  filter_upwards [ae_all_iff.2 fun i ↦ ae_all_iff.2 fun j ↦ hcell i j] with z hz
  have hint (i : ι) := integrable_finsetSum Finset.univ fun j _ ↦ (hz i j).1
  refine ⟨(integrable_finsetSum Finset.univ fun i _ ↦ hint i).const_mul 4, ?_⟩
  rw [integral_const_mul, integral_finsetSum _ fun i _ ↦ hint i]
  congr 1; refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [integral_finsetSum _ fun j _ ↦ (hz i j).1]
  exact Finset.sum_congr rfl fun j _ ↦ (hz i j).2
private theorem ae_le_convex_offDiag_pi [Fintype ι] {μ : ι → Measure E}
    [∀ k, IsProbabilityMeasure (μ k)] {f : ι → ι → E → E → ℝ}
    (hf_meas : ∀ i j, Measurable (Function.uncurry (f i j))) (hf_diag : ∀ i x y, f i i x y = 0)
    (hf_int : ∀ i j, i ≠ j → Integrable (Function.uncurry (f i j)) ((μ i).prod (μ j)))
    (hf_zero_right : ∀ i j, i ≠ j → ∀ᵐ x ∂μ i, ∫ y, f i j x y ∂μ j = 0)
    (hf_zero_left : ∀ i j, i ≠ j → ∀ᵐ y ∂μ j, ∫ x, f i j x y ∂μ i = 0)
    {Φ : ℝ → ℝ} (hΦ_conv : ConvexOn ℝ Set.univ Φ) (hΦ_cont : Continuous Φ)
    (hΦ_int_dec : Integrable (fun p : (ι → E) × (ι → E) ↦
      Φ (4 * ∑ i, ∑ j, f i j (p.1 i) (p.2 j))) ((Measure.pi μ).prod (Measure.pi μ))) :
    ∃ M : (ι → E) → ℝ, Integrable M (Measure.pi μ) ∧
      (∀ᵐ z ∂Measure.pi μ, Φ (∑ i, ∑ j, f i j (z i) (z j)) ≤ M z) ∧
      ∫ z, M z ∂Measure.pi μ = ∫ p : (ι → E) × (ι → E), Φ (4 * ∑ i, ∑ j, f i j (p.1 i) (p.2 j))
        ∂((Measure.pi μ).prod (Measure.pi μ)) := by
  classical
  let F : ((ι → E) × (ι → E)) → ℝ := fun p ↦ Φ (4 * ∑ i, ∑ j, f i j (p.1 i) (p.2 j))
  let G : (ι → Bool) → ((ι → E) × (ι → E)) → ℝ := fun δ ↦ F ∘ swapCoordsEquiv δ
  have hG_int (δ : ι → Bool) : Integrable (G δ) ((Measure.pi μ).prod (Measure.pi μ)) :=
    ((measurePreserving_swapCoords μ δ).integrable_comp_emb
      (swapCoordsEquiv δ).measurableEmbedding).2 hΦ_int_dec
  let c : ℝ := (Fintype.card (ι → Bool) : ℝ)⁻¹
  have hc_pos : 0 ≤ c := by positivity
  have : Nonempty (ι → Bool) := ⟨fun _ ↦ false⟩
  have hcard_ne : (Fintype.card (ι → Bool) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hc_sum : ∑ _δ : ι → Bool, c = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hcard_ne]
  let M : (ι → E) → ℝ := fun z ↦ ∑ δ : ι → Bool, c * ∫ w, G δ (z, w) ∂Measure.pi μ
  have hδ_ae : ∀ᵐ z ∂Measure.pi μ, ∀ δ : ι → Bool,
      Φ (4 * ∑ i, ∑ j, if δ i = true ∧ δ j = false then f i j (z i) (z j) else 0) ≤
        ∫ w, G δ (z, w) ∂Measure.pi μ :=
    ae_all_iff.2 fun δ ↦ by
      filter_upwards [ae_integral_swapped_eq hf_meas hf_diag hf_int hf_zero_right hf_zero_left δ,
        (hG_int δ).prod_right_ae] with z hz hG_z
      exact hz.2 ▸ hΦ_conv.map_integral_le hΦ_cont.continuousOn isClosed_univ
        (.of_forall fun _ ↦ Set.mem_univ _) hz.1 hG_z
  have hsum_avg (z : ι → E) : ∑ i, ∑ j, f i j (z i) (z j) = ∑ δ : ι → Bool,
      c • (4 * ∑ i, ∑ j, if δ i = true ∧ δ j = false then f i j (z i) (z j) else 0) := by
    simp only [smul_eq_mul, ← Finset.mul_sum]
    rw [show ∑ i, ∑ j, f i j (z i) (z j) = ∑ i, ∑ j,
      (c * ∑ δ : ι → Bool, if δ i = true ∧ δ j = false then (4 : ℝ) else 0) * f i j (z i) (z j) from
      Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by
        by_cases hij : i = j
        · subst hij; simp [hf_diag]
        · rw [selector_avg_eq_one hij, one_mul]]
    simp_rw [mul_assoc, ← Finset.mul_sum]; congr 1
    have hinner (i j : ι) : (∑ δ : ι → Bool, if δ i = true ∧ δ j = false then (4 : ℝ) else 0) *
        f i j (z i) (z j) =
        ∑ δ : ι → Bool, 4 * if δ i = true ∧ δ j = false then f i j (z i) (z j) else 0 := by
      rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun _ _ ↦ ?_; split_ifs <;> ring
    simp_rw [hinner]
    rw [Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm (s := Finset.univ) (t := Finset.univ),
      Finset.sum_comm]; simp_rw [← Finset.mul_sum]
  refine ⟨M, integrable_finsetSum _ fun δ _ ↦ (hG_int δ).integral_prod_left.const_mul c, ?_, ?_⟩
  · filter_upwards [hδ_ae] with z hz
    exact (congrArg Φ (hsum_avg z)).trans_le <|
      (hΦ_conv.map_sum_le (fun _ _ ↦ hc_pos) hc_sum fun _ _ ↦ Set.mem_univ _).trans <|
      Finset.sum_le_sum fun δ _ ↦ by
        simpa [smul_eq_mul] using mul_le_mul_of_nonneg_left (hz δ) hc_pos
  · simp only [M, integral_finsetSum _ fun δ _ ↦ (hG_int δ).integral_prod_left.const_mul c]
    have hterm (δ : ι → Bool) : ∫ z, c * (∫ w, G δ (z, w) ∂Measure.pi μ) ∂Measure.pi μ =
        c * ∫ p, F p ∂((Measure.pi μ).prod (Measure.pi μ)) := by
      rw [integral_const_mul, ← integral_prod _ (hG_int δ)]
      exact congrArg (c * ·) ((measurePreserving_swapCoords μ δ).integral_comp' F)
    simp_rw [hterm, ← Finset.sum_mul, hc_sum, one_mul]; rfl

/-- **Convex decoupling on a finite product measure.** -/
theorem integral_convex_offDiag_pi_le [Fintype ι] {μ : ι → Measure E}
    [∀ k, IsProbabilityMeasure (μ k)] {f : ι → ι → E → E → ℝ}
    (hf_meas : ∀ i j, Measurable (Function.uncurry (f i j))) (hf_diag : ∀ i x y, f i i x y = 0)
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

/-- Integrability of the decoupled order-two sum for nonnegative convex `Φ` implies integrability of
the coupled sum on `Measure.pi μ`. -/
theorem integrable_of_nonneg_convex_offDiag_pi [Fintype ι] {μ : ι → Measure E}
    [∀ k, IsProbabilityMeasure (μ k)] {f : ι → ι → E → E → ℝ}
    (hf_meas : ∀ i j, Measurable (Function.uncurry (f i j))) (hf_diag : ∀ i x y, f i i x y = 0)
    (hf_int : ∀ i j, i ≠ j → Integrable (Function.uncurry (f i j)) ((μ i).prod (μ j)))
    (hf_zero_right : ∀ i j, i ≠ j → ∀ᵐ x ∂μ i, ∫ y, f i j x y ∂μ j = 0)
    (hf_zero_left : ∀ i j, i ≠ j → ∀ᵐ y ∂μ j, ∫ x, f i j x y ∂μ i = 0)
    {Φ : ℝ → ℝ} (hΦ_conv : ConvexOn ℝ Set.univ Φ) (hΦ_cont : Continuous Φ)
    (hΦ_nonneg : ∀ x, 0 ≤ Φ x) (hΦ_int_dec : Integrable (fun p : (ι → E) × (ι → E) ↦
      Φ (4 * ∑ i, ∑ j, f i j (p.1 i) (p.2 j))) ((Measure.pi μ).prod (Measure.pi μ))) :
    Integrable (fun z : ι → E ↦ Φ (∑ i, ∑ j, f i j (z i) (z j))) (Measure.pi μ) := by
  obtain ⟨M, hM_int, hle, _⟩ := ae_le_convex_offDiag_pi hf_meas hf_diag hf_int
    hf_zero_right hf_zero_left hΦ_conv hΦ_cont hΦ_int_dec
  have hS_meas : Measurable fun z : ι → E ↦ Φ (∑ i, ∑ j, f i j (z i) (z j)) :=
    hΦ_cont.measurable.comp <| Finset.measurable_sum _ fun i _ ↦ Finset.measurable_sum _ fun j _ ↦
      (hf_meas i j).comp (by fun_prop : Measurable fun z : ι → E ↦ (z i, z j))
  refine hM_int.mono' hS_meas.aestronglyMeasurable ?_
  filter_upwards [hle] with z hz; rwa [Real.norm_of_nonneg (hΦ_nonneg _)]

/-- **Convex decoupling on a finite product measure for nonnegative `Φ`.** -/
theorem integral_nonneg_convex_offDiag_pi_le [Fintype ι] {μ : ι → Measure E}
    [∀ k, IsProbabilityMeasure (μ k)] {f : ι → ι → E → E → ℝ}
    (hf_meas : ∀ i j, Measurable (Function.uncurry (f i j))) (hf_diag : ∀ i x y, f i i x y = 0)
    (hf_int : ∀ i j, i ≠ j → Integrable (Function.uncurry (f i j)) ((μ i).prod (μ j)))
    (hf_zero_right : ∀ i j, i ≠ j → ∀ᵐ x ∂μ i, ∫ y, f i j x y ∂μ j = 0)
    (hf_zero_left : ∀ i j, i ≠ j → ∀ᵐ y ∂μ j, ∫ x, f i j x y ∂μ i = 0)
    {Φ : ℝ → ℝ} (hΦ_conv : ConvexOn ℝ Set.univ Φ) (hΦ_cont : Continuous Φ)
    (hΦ_nonneg : ∀ x, 0 ≤ Φ x) (hΦ_int_dec : Integrable (fun p : (ι → E) × (ι → E) ↦
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

private theorem pushforward_setup (hindep : iIndepFun X P) (hX : ∀ i, AEMeasurable (X i) P)
    {f : ι → ι → E → E → ℝ} (hf_meas : ∀ i j, Measurable (Function.uncurry (f i j)))
    (hf_int : ∀ i j, i ≠ j → Integrable (fun p : Ω × Ω ↦ f i j (X i p.1) (X j p.2)) (P.prod P))
    (hf_zero_right : ∀ i j x, i ≠ j → ∫ ω', f i j x (X j ω') ∂P = 0)
    (hf_zero_left : ∀ i j y, i ≠ j → ∫ ω, f i j (X i ω) y ∂P = 0)
    {Φ : ℝ → ℝ} (hΦ_cont : Continuous Φ) (hΦ_int_dec : Integrable (fun p : Ω × Ω ↦
      Φ (4 * ∑ i, ∑ j, f i j (X i p.1) (X j p.2))) (P.prod P)) :
    (∀ i j, i ≠ j → Integrable (Function.uncurry (f i j)) ((P.map (X i)).prod (P.map (X j)))) ∧
    (∀ i j, i ≠ j → ∀ᵐ x ∂P.map (X i), ∫ y, f i j x y ∂P.map (X j) = 0) ∧
    (∀ i j, i ≠ j → ∀ᵐ y ∂P.map (X j), ∫ x, f i j x y ∂P.map (X i) = 0) ∧
    Measurable (fun z : ι → E ↦ Φ (∑ i, ∑ j, f i j (z i) (z j))) ∧
    Measurable (fun q : (ι → E) × (ι → E) ↦ Φ (4 * ∑ i, ∑ j, f i j (q.1 i) (q.2 j))) ∧
    AEMeasurable (fun p : Ω × Ω ↦ (fun i ↦ X i p.1, fun i ↦ X i p.2)) (P.prod P) ∧
    (P.prod P).map (fun p : Ω × Ω ↦ (fun i ↦ X i p.1, fun i ↦ X i p.2)) =
      (Measure.pi fun i ↦ P.map (X i)).prod (Measure.pi fun i ↦ P.map (X i)) ∧
    Integrable (fun q : (ι → E) × (ι → E) ↦ Φ (4 * ∑ i, ∑ j, f i j (q.1 i) (q.2 j)))
      ((Measure.pi fun i ↦ P.map (X i)).prod (Measure.pi fun i ↦ P.map (X i))) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  have hS1 : Measurable (fun z : ι → E ↦ Φ (∑ i, ∑ j, f i j (z i) (z j))) :=
    hΦ_cont.measurable.comp <| Finset.measurable_sum _ fun i _ ↦ Finset.measurable_sum _ fun j _ ↦
      (hf_meas i j).comp (by fun_prop : Measurable fun z : ι → E ↦ (z i, z j))
  have hS2 : Measurable (fun q : (ι → E) × (ι → E) ↦ Φ (4 * ∑ i, ∑ j, f i j (q.1 i) (q.2 j))) :=
    hΦ_cont.measurable.comp <| measurable_const.mul <| Finset.measurable_sum _ fun i _ ↦
      Finset.measurable_sum _ fun j _ ↦ (hf_meas i j).comp
        (by fun_prop : Measurable fun q : (ι → E) × (ι → E) ↦ (q.1 i, q.2 j))
  have hvec : AEMeasurable (fun ω i ↦ X i ω) P := AEMeasurable.of_eval hX
  have hvec2 : AEMeasurable (fun p : Ω × Ω ↦ (fun i ↦ X i p.1, fun i ↦ X i p.2)) (P.prod P) :=
    (hvec.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).prodMk
      (hvec.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
  have hmap2 : (P.prod P).map (fun p : Ω × Ω ↦ (fun i ↦ X i p.1, fun i ↦ X i p.2)) =
      (Measure.pi fun i ↦ P.map (X i)).prod (Measure.pi fun i ↦ P.map (X i)) :=
    (hindep.map_fun_eq_pi_map hX) ▸ (Measure.map_prod_map_of_aemeasurable P P hvec hvec).symm
  refine ⟨fun i j hij ↦ ?_, fun i j hij ↦ .of_forall fun x ↦ ?_,
      fun i j hij ↦ .of_forall fun y ↦ ?_, hS1, hS2, hvec2, hmap2, ?_⟩
  · have hm : AEMeasurable (Prod.map (X i) (X j)) (P.prod P) :=
      ((hX i).comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).prodMk
        ((hX j).comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
    rw [Measure.map_prod_map_of_aemeasurable P P (hX i) (hX j),
      integrable_map_measure (hf_meas i j).aestronglyMeasurable hm]
    exact hf_int i j hij
  · have hm : Measurable (f i j x) := (hf_meas i j).comp (measurable_const.prodMk measurable_id)
    exact (integral_map (hX j) hm.aestronglyMeasurable).trans (hf_zero_right i j x hij)
  · have hm : Measurable (f i j · y) := (hf_meas i j).comp (measurable_id.prodMk measurable_const)
    exact (integral_map (hX i) hm.aestronglyMeasurable).trans (hf_zero_left i j y hij)
  · rwa [← hmap2, integrable_map_measure hS2.aestronglyMeasurable hvec2]

/-- **Convex decoupling for an independent family.** -/
theorem integral_convex_offDiag_le (hindep : iIndepFun X P) (hX : ∀ i, AEMeasurable (X i) P)
    {f : ι → ι → E → E → ℝ} (hf_meas : ∀ i j, Measurable (Function.uncurry (f i j)))
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
  obtain ⟨hf_int_μ, hf_zr_μ, hf_zl_μ, hS1, hS2, hvec2, hmap2, hΦ_int_dec_pi⟩ :=
    hindep.pushforward_setup hX hf_meas hf_int hf_zero_right hf_zero_left hΦ_cont hΦ_int_dec
  have hmap1 := hindep.map_fun_eq_pi_map hX
  have hΦ_pi : Integrable (fun z : ι → E ↦ Φ (∑ i, ∑ j, f i j (z i) (z j)))
      (Measure.pi fun i ↦ P.map (X i)) := by
    rwa [← hmap1, integrable_map_measure hS1.aestronglyMeasurable (AEMeasurable.of_eval hX)]
  have hle := integral_convex_offDiag_pi_le hf_meas hf_diag hf_int_μ hf_zr_μ hf_zl_μ
    hΦ_conv hΦ_cont hΦ_pi hΦ_int_dec_pi
  rwa [← hmap2, integral_map hvec2 hS2.aestronglyMeasurable,
    ← hmap1, integral_map (AEMeasurable.of_eval hX) hS1.aestronglyMeasurable] at hle

/-- For nonnegative continuous convex `Φ`, integrability of the decoupled statistic on `P.prod P`
implies integrability of the coupled off-diagonal statistic on `P`. -/
theorem integrable_of_nonneg_convex_offDiag (hindep : iIndepFun X P)
    (hX : ∀ i, AEMeasurable (X i) P) {f : ι → ι → E → E → ℝ}
    (hf_meas : ∀ i j, Measurable (Function.uncurry (f i j))) (hf_diag : ∀ i x y, f i i x y = 0)
    (hf_int : ∀ i j, i ≠ j → Integrable (fun p : Ω × Ω ↦ f i j (X i p.1) (X j p.2)) (P.prod P))
    (hf_zero_right : ∀ i j x, i ≠ j → ∫ ω', f i j x (X j ω') ∂P = 0)
    (hf_zero_left : ∀ i j y, i ≠ j → ∫ ω, f i j (X i ω) y ∂P = 0)
    {Φ : ℝ → ℝ} (hΦ_conv : ConvexOn ℝ Set.univ Φ) (hΦ_cont : Continuous Φ)
    (hΦ_nonneg : ∀ x, 0 ≤ Φ x) (hΦ_int_dec : Integrable (fun p : Ω × Ω ↦
      Φ (4 * ∑ i, ∑ j, f i j (X i p.1) (X j p.2))) (P.prod P)) :
    Integrable (fun ω ↦ Φ (∑ i, ∑ j, f i j (X i ω) (X j ω))) P := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  obtain ⟨hf_int_μ, hf_zr_μ, hf_zl_μ, hS1, _, _, _, hΦ_int_dec_pi⟩ :=
    hindep.pushforward_setup hX hf_meas hf_int hf_zero_right hf_zero_left hΦ_cont hΦ_int_dec
  have hpi := integrable_of_nonneg_convex_offDiag_pi hf_meas hf_diag hf_int_μ hf_zr_μ hf_zl_μ
    hΦ_conv hΦ_cont hΦ_nonneg hΦ_int_dec_pi
  rwa [← hindep.map_fun_eq_pi_map hX,
    integrable_map_measure hS1.aestronglyMeasurable (AEMeasurable.of_eval hX)] at hpi

/-- **Convex decoupling for an independent family and nonnegative `Φ`.** -/
theorem integral_nonneg_convex_offDiag_le (hindep : iIndepFun X P) (hX : ∀ i, AEMeasurable (X i) P)
    {f : ι → ι → E → E → ℝ} (hf_meas : ∀ i j, Measurable (Function.uncurry (f i j)))
    (hf_diag : ∀ i x y, f i i x y = 0)
    (hf_int : ∀ i j, i ≠ j → Integrable (fun p : Ω × Ω ↦ f i j (X i p.1) (X j p.2)) (P.prod P))
    (hf_zero_right : ∀ i j x, i ≠ j → ∫ ω', f i j x (X j ω') ∂P = 0)
    (hf_zero_left : ∀ i j y, i ≠ j → ∫ ω, f i j (X i ω) y ∂P = 0)
    {Φ : ℝ → ℝ} (hΦ_conv : ConvexOn ℝ Set.univ Φ) (hΦ_cont : Continuous Φ)
    (hΦ_nonneg : ∀ x, 0 ≤ Φ x) (hΦ_int_dec : Integrable (fun p : Ω × Ω ↦
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

/-- **Exponential-moment decoupling for `RCLike` off-diagonal sesquilinear forms.** -/
theorem mgf_offDiag_re_star_dotProduct_mulVec_le {𝕜 : Type*} [RCLike 𝕜] {Z : ι → Ω → 𝕜}
    (hindep : iIndepFun Z P) (hZ_int : ∀ i, Integrable (Z i) P) (hZ_mean : ∀ i, ∫ ω, Z i ω ∂P = 0)
    {B : Matrix ι ι 𝕜} (hB_diag : ∀ i, B i i = 0) {t : ℝ} (hint_dec : Integrable (fun p : Ω × Ω ↦
      exp (4 * t * RCLike.re (star (fun i ↦ Z i p.1) ⬝ᵥ B *ᵥ (fun i ↦ Z i p.2)))) (P.prod P)) :
    Integrable (fun ω ↦ exp (t * RCLike.re (star (fun i ↦ Z i ω) ⬝ᵥ B *ᵥ (fun i ↦ Z i ω)))) P ∧
    mgf (fun ω ↦ RCLike.re (star (fun i ↦ Z i ω) ⬝ᵥ B *ᵥ (fun i ↦ Z i ω))) P t ≤
      mgf (fun p : Ω × Ω ↦ RCLike.re (star (fun i ↦ Z i p.1) ⬝ᵥ B *ᵥ (fun i ↦ Z i p.2)))
        (P.prod P) (4 * t) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  let f : ι → ι → 𝕜 → 𝕜 → ℝ := fun i j x y ↦ RCLike.re (star x * (B i j * y))
  have hsesq (u v : ι → 𝕜) : RCLike.re (star u ⬝ᵥ B *ᵥ v) = ∑ i, ∑ j, f i j (u i) (v j) := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, map_sum, f]
  let Φ : ℝ → ℝ := fun z ↦ exp (t * z)
  have hΦ_conv : ConvexOn ℝ Set.univ Φ := convexOn_exp.comp_linearMap (LinearMap.mul ℝ ℝ t)
  have hΦ_cont : Continuous Φ := by fun_prop
  have hΦ_nonneg : ∀ z, 0 ≤ Φ z := fun _ ↦ (exp_pos _).le
  have hf_meas (i j : ι) : Measurable (Function.uncurry (f i j)) := by
    dsimp only [Function.uncurry, f]; fun_prop
  have hf_diag (i : ι) (x y : 𝕜) : f i i x y = 0 := by simp [f, hB_diag i]
  have hZ_star (i : ι) : Integrable (fun ω ↦ star (Z i ω)) P :=
    (hZ_int i).mono (continuous_star.comp_aestronglyMeasurable (hZ_int i).aestronglyMeasurable)
      (.of_forall fun _ ↦ by simp)
  have hf_int (i j : ι) (_ : i ≠ j) :
      Integrable (fun p : Ω × Ω ↦ f i j (Z i p.1) (Z j p.2)) (P.prod P) :=
    ((hZ_star i).mul_prod ((hZ_int j).const_mul (B i j))).re
  have hf_zr (i j : ι) (x : 𝕜) (_ : i ≠ j) : ∫ ω', f i j x (Z j ω') ∂P = 0 := by
    dsimp only [f]; rw [integral_re (((hZ_int j).const_mul (B i j)).const_mul (star x))]
    simp [← mul_assoc, integral_const_mul, hZ_mean j]
  have hf_zl (i j : ι) (y : 𝕜) (_ : i ≠ j) : ∫ ω, f i j (Z i ω) y ∂P = 0 := by
    have h0 : ∫ ω, star (Z i ω) ∂P = 0 := by
      simp_rw [RCLike.star_def, integral_conj, hZ_mean i, map_zero]
    dsimp only [f]; rw [integral_re ((hZ_star i).mul_const _), integral_mul_const, h0]; simp
  have hint_dec' : Integrable (fun p : Ω × Ω ↦
      Φ (4 * ∑ i, ∑ j, f i j (Z i p.1) (Z j p.2))) (P.prod P) :=
    hint_dec.congr (.of_forall fun _ ↦ by simp only [Φ, ← hsesq]; ring_nf)
  refine ⟨?_, (integral_congr_ae (.of_forall fun _ ↦ by simp only [Φ, ← hsesq])).trans_le <|
    (hindep.integral_nonneg_convex_offDiag_le (fun i ↦ (hZ_int i).aemeasurable) hf_meas hf_diag
      hf_int hf_zr hf_zl hΦ_conv hΦ_cont hΦ_nonneg hint_dec').trans_eq <|
    integral_congr_ae (.of_forall fun _ ↦ by simp only [Φ, ← hsesq]; ring_nf)⟩
  simpa only [Φ, ← hsesq] using hindep.integrable_of_nonneg_convex_offDiag
    (fun i ↦ (hZ_int i).aemeasurable) hf_meas hf_diag hf_int hf_zr hf_zl
    hΦ_conv hΦ_cont hΦ_nonneg hint_dec'

/-- **Exponential-moment decoupling for real off-diagonal quadratic forms.** -/
theorem mgf_offDiag_dotProduct_mulVec_le {X : ι → Ω → ℝ} (hindep : iIndepFun X P)
    (hX_int : ∀ i, Integrable (X i) P) (hX_mean : ∀ i, P[X i] = 0) {B : Matrix ι ι ℝ}
    (hB_diag : ∀ i, B i i = 0) {t : ℝ} (hint_dec : Integrable (fun p : Ω × Ω ↦
      exp (4 * t * ((fun i ↦ X i p.1) ⬝ᵥ B *ᵥ (fun i ↦ X i p.2)))) (P.prod P)) :
    Integrable (fun ω ↦ exp (t * ((fun i ↦ X i ω) ⬝ᵥ B *ᵥ (fun i ↦ X i ω)))) P ∧
    mgf (fun ω ↦ (fun i ↦ X i ω) ⬝ᵥ B *ᵥ (fun i ↦ X i ω)) P t ≤
      mgf (fun p : Ω × Ω ↦ (fun i ↦ X i p.1) ⬝ᵥ B *ᵥ (fun i ↦ X i p.2)) (P.prod P) (4 * t) := by
  simpa using hindep.mgf_offDiag_re_star_dotProduct_mulVec_le (𝕜 := ℝ) hX_int hX_mean hB_diag
    hint_dec

end QuadraticForms

end iIndepFun

end ProbabilityTheory
