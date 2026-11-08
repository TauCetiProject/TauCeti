/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Concentration.Poincare.Tensorization

/-!
# Optimal Poincaré constants and finite products

The optimal Poincaré constant is the infimum of the nonnegative finite constants for which
`MeasureTheory.Measure.PoincareInequality` holds. It takes values in `ℝ≥0∞`, with value `∞`
when there is no finite valid constant. The optimal constant of a finite Hilbert product of
probability measures is the supremum of the factor constants. The empty product has constant zero.

## References

* D. Bakry, I. Gentil and M. Ledoux, *Analysis and Geometry of Markov Diffusion Operators*,
  Proposition 4.3.1 (tensorization).
* The optimal-constant argument is adapted from the KLS formalization,
  `FunctionalInequalities/Poincare/FiniteProduct/Tensorization.lean`, at
  https://github.com/human-ai-mathematics/kls-lean/tree/65810c73f9dd7945fc646ab484cb19d673f5291d.
-/

public section

noncomputable section

open ProbabilityTheory MeasureTheory
open scoped ENNReal NNReal ContDiff

namespace MeasureTheory.Measure

section Constant

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]

/-- The optimal nonnegative Poincaré constant, or `∞` if no finite constant is valid. -/
def poincareConstant (μ : Measure E) : ℝ≥0∞ :=
  ⨅ C : {C : ℝ≥0 // PoincareInequality μ C}, (C.1 : ℝ≥0∞)

/-- A valid nonnegative constant bounds the optimal Poincaré constant from above. -/
theorem PoincareInequality.poincareConstant_le {μ : Measure E} {C : ℝ≥0}
    (h : PoincareInequality μ C) : poincareConstant μ ≤ (C : ℝ≥0∞) :=
  iInf_le_of_le ⟨C, h⟩ le_rfl

/-- To bound the optimal Poincaré constant from below, bound every finite valid constant. -/
theorem le_poincareConstant {μ : Measure E} {r : ℝ≥0∞}
    (h : ∀ C : ℝ≥0, PoincareInequality μ C → r ≤ (C : ℝ≥0∞)) :
    r ≤ poincareConstant μ :=
  le_iInf fun C ↦ h C.1 C.2

/-- A strict upper bound on the optimal constant admits a finite valid constant below it. -/
theorem poincareConstant_lt_iff {μ : Measure E} {r : ℝ≥0∞} :
    poincareConstant μ < r ↔
      ∃ C : ℝ≥0, PoincareInequality μ C ∧ (C : ℝ≥0∞) < r := by
  rw [poincareConstant, iInf_lt_iff]
  exact ⟨fun ⟨C, hC⟩ ↦ ⟨C.1, C.2, hC⟩, fun ⟨C, hC, hr⟩ ↦ ⟨⟨C, hC⟩, hr⟩⟩

/-- The optimal Poincaré constant is infinite exactly when no finite nonnegative constant works. -/
theorem poincareConstant_eq_top_iff {μ : Measure E} :
    poincareConstant μ = ⊤ ↔ ∀ C : ℝ≥0, ¬ PoincareInequality μ C := by
  constructor
  · intro h C hC
    exact ENNReal.coe_ne_top (top_unique (h ▸ hC.poincareConstant_le))
  · intro h
    apply top_unique
    exact le_poincareConstant fun C hC ↦ (h C hC).elim

end Constant

section Marginals

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
  [∀ i, MeasurableSpace (E i)]
  [∀ i, BorelSpace (E i)] [∀ i, SecondCountableTopology (E i)]

/-- Every marginal of a finite `PiLp 2` product inherits its Poincaré inequality. -/
theorem PoincareInequality.of_piLp {μ : ∀ i, Measure (E i)}
    [∀ i, IsProbabilityMeasure (μ i)] {C : ℝ}
    (h : PoincareInequality ((Measure.pi μ).map (WithLp.toLp 2)) C) (i : ι) :
    PoincareInequality (μ i) C := by
  classical
  let ρ := (Measure.pi μ).map (WithLp.toLp 2)
  let q := (PiLp.proj 2 E i : PiLp 2 E →L[ℝ] E i)
  have hm : MeasurePreserving q ρ (μ i) := by
    refine ⟨q.continuous.measurable, ?_⟩
    change ((Measure.pi μ).map (WithLp.toLp 2)).map q = μ i
    rw [Measure.map_map q.continuous.measurable (WithLp.measurable_toLp 2 _)]
    exact (measurePreserving_eval μ i).map_eq
  rw [PoincareInequality_def]
  intro f hf hfL hdf
  have hn (x : PiLp 2 E) :
      ‖fderiv ℝ (fun y : PiLp 2 E ↦ f (q y)) x‖ = ‖fderiv ℝ f (q x)‖ := by
    have hderiv : fderiv ℝ (fun y : PiLp 2 E ↦ f (q y)) x =
        (fderiv ℝ f (q x)).comp q := by
      simpa only [Function.comp_def] using
        ((hf.differentiable (by simp) (q x)).hasFDerivAt.comp x q.hasFDerivAt).fderiv
    rw [hderiv]
    apply le_antisymm
    · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (fderiv ℝ f (q x))) fun y ↦ ?_
      exact ((fderiv ℝ f (q x)).le_opNorm (q y)).trans
        (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le y i) (norm_nonneg _))
    · refine ContinuousLinearMap.opNorm_le_bound _
        (norm_nonneg ((fderiv ℝ f (q x)).comp q)) fun y ↦ ?_
      have hle := ((fderiv ℝ f (q x)).comp q).le_opNorm (PiLp.single 2 i y)
      simpa only [ContinuousLinearMap.comp_apply, q, PiLp.proj_apply,
        PiLp.ofLp_single, Pi.single_eq_same, PiLp.norm_single] using hle
  have hd : MemLp (fun x : PiLp 2 E ↦ ‖fderiv ℝ (fun y ↦ f (q y)) x‖) 2 ρ := by
    simp only [hn]
    exact hdf.comp_measurePreserving hm
  have hv := h.apply (fun x ↦ f (q x)) (hf.comp q.contDiff)
    (hfL.comp_measurePreserving hm) hd
  rw [hm.variance_fun_comp hfL.aemeasurable] at hv
  have he : (∫ x, ‖fderiv ℝ (fun y ↦ f (q y)) x‖ ^ 2 ∂ρ) =
      ∫ y, ‖fderiv ℝ f y‖ ^ 2 ∂μ i := by
    simp only [hn]
    have hint : AEStronglyMeasurable (fun y ↦ ‖fderiv ℝ f y‖ ^ 2) (ρ.map q) :=
      hm.map_eq.symm ▸ hdf.integrable_sq.aestronglyMeasurable
    rw [← hm.map_eq, integral_map hm.measurable.aemeasurable hint]
  rwa [he] at hv

/-- Each factor's optimal Poincaré constant is bounded by the product constant. -/
theorem poincareConstant_le_piLp (μ : ∀ i, Measure (E i))
    [∀ i, IsProbabilityMeasure (μ i)] (i : ι) :
    poincareConstant (μ i) ≤ poincareConstant ((Measure.pi μ).map (WithLp.toLp 2)) :=
  le_poincareConstant fun _ h ↦ (h.of_piLp i).poincareConstant_le

/-- A factor with infinite optimal constant forces the product constant to be infinite. -/
theorem poincareConstant_piLp_eq_top {μ : ∀ i, Measure (E i)}
    [∀ i, IsProbabilityMeasure (μ i)] (i : ι) (hi : poincareConstant (μ i) = ⊤) :
    poincareConstant ((Measure.pi μ).map (WithLp.toLp 2)) = ⊤ :=
  top_unique (hi ▸ poincareConstant_le_piLp μ i)

end Marginals

section Products

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, CompleteSpace (E i)] [∀ i, MeasurableSpace (E i)]
  [∀ i, BorelSpace (E i)] [∀ i, SecondCountableTopology (E i)]

/-- The optimal Poincaré constant of a finite Hilbert product is the supremum of its factors. -/
theorem poincareConstant_piLp (μ : ∀ i, Measure (E i))
    [∀ i, IsProbabilityMeasure (μ i)] :
    poincareConstant ((Measure.pi μ).map (WithLp.toLp 2)) = ⨆ i, poincareConstant (μ i) := by
  classical
  apply le_antisymm
  · by_contra h
    rw [not_le] at h
    have hbot : (⊥ : ℝ≥0∞) < poincareConstant ((Measure.pi μ).map (WithLp.toLp 2)) :=
      bot_le.trans_lt h
    have hex : ∀ i, ∃ C : ℝ≥0, PoincareInequality (μ i) C ∧
        (C : ℝ≥0∞) < poincareConstant ((Measure.pi μ).map (WithLp.toLp 2)) := by
      intro i
      exact poincareConstant_lt_iff.mp ((le_iSup (fun i ↦ poincareConstant (μ i)) i).trans_lt h)
    choose C hC hlt using hex
    have hle := (PoincareInequality.piLp_sup μ C hC).poincareConstant_le
    have hcoe : ((Finset.univ.sup C : ℝ≥0) : ℝ≥0∞) =
        Finset.univ.sup fun i ↦ (C i : ℝ≥0∞) :=
      Finset.apply_sup_eq_sup_comp ((↑) : ℝ≥0 → ℝ≥0∞)
        (fun x y ↦ ENNReal.coe_mono.map_sup x y) (by simp)
    rw [hcoe] at hle
    exact (not_lt_of_ge hle) ((Finset.sup_lt_iff hbot).mpr fun i _ ↦ hlt i)
  · exact iSup_le fun i ↦ poincareConstant_le_piLp μ i

/-- An empty product has optimal Poincaré constant zero. -/
@[simp]
theorem poincareConstant_piLp_empty [IsEmpty ι] (μ : ∀ i, Measure (E i))
    [∀ i, IsProbabilityMeasure (μ i)] :
    poincareConstant ((Measure.pi μ).map (WithLp.toLp 2)) = 0 := by
  simp [poincareConstant_piLp]

end Products

end MeasureTheory.Measure
