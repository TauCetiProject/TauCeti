/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Probability.IdentDistribIndep
public import TauCeti.Probability.Distributions.Rademacher.Basic
public import TauCeti.Probability.Independence.DisjointBlocks

/-!
# The symmetrization inequality

Let `X = (Xᵢ)` be a finite family of real random variables and `X'` an independent copy, all
defined on one probability space and jointly independent, that is, the family `X ⊕ X'` indexed by
`ι ⊕ ι` is `iIndepFun` and `Xᵢ`, `X'ᵢ` are identically distributed. Let `Φ : ℝ → ℝ` be convex, let
the `Xᵢ` be integrable and centred, and let `Φ (∑ Xᵢ)` and `Φ (∑ (Xᵢ - X'ᵢ))` be integrable. Let
`εᵢ` be signs, almost surely `±1`, whose vector is independent of the vector `(Xᵢ - X'ᵢ)ᵢ`. Then
`E Φ(∑ Xᵢ) ≤ E Φ(∑ (Xᵢ - X'ᵢ)) = E Φ(∑ εᵢ (Xᵢ - X'ᵢ))`.

The inequality is Jensen's inequality for the conditional expectation over `X'`; the equality
holds because swapping `Xᵢ` and `X'ᵢ` preserves the joint law and negates `Xᵢ - X'ᵢ`.

## Main results

* `ConvexOn.integral_comp_sum_le_integral_comp_sum_sub`: the desymmetrization inequality, which
  only needs `X` to be independent of `X'` as vectors and `X'` to be centred.
* `ProbabilityTheory.iIndepFun.map_fun_mul_sub_eq_of_identDistrib`: for fixed signs, the vector
  `(sᵢ (Xᵢ - X'ᵢ))ᵢ` has the same law as `(Xᵢ - X'ᵢ)ᵢ`.
* `ProbabilityTheory.IndepFun.map_fun_mul_sub_eq_of_identDistrib`: the same for signs independent
  of the differences and almost surely equal to `±1`.
* `ProbabilityTheory.IndepFun.integral_comp_sum_mul_sub_eq`: the resulting equality of
  expectations.
* `ConvexOn.symmetrization_inequality`: the full chain
  `E Φ(∑ Xᵢ) ≤ E Φ(∑ (Xᵢ - X'ᵢ)) = E Φ(∑ εᵢ (Xᵢ - X'ᵢ))`, and
  `ConvexOn.symmetrization_inequality_of_map_eq_rademacherMeasure` for Rademacher signs.

## References

* [R. Vershynin, *High-Dimensional Probability*, Lemma 6.4.2]
* [M. Ledoux, M. Talagrand, *Probability in Banach Spaces*, Lemma 6.3]
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X X' : ι → Ω → ℝ}

omit [IsProbabilityMeasure μ] in
/-- Swapping the two coordinates `Xᵢ`, `X'ᵢ` of a jointly independent family of independent copies,
for the indices `i` with `s i = -1`, does not change the law of the family `X ⊕ X'`, hence
the vector `(sᵢ (Xᵢ - X'ᵢ))ᵢ` has the same law as `(Xᵢ - X'ᵢ)ᵢ` for a fixed sign pattern
`s : ι → ℝ` with values in `{1, -1}`. -/
theorem iIndepFun.map_fun_mul_sub_eq_of_identDistrib [Countable ι]
    (hind : iIndepFun (Sum.elim X X') μ) (hid : ∀ i, IdentDistrib (X i) (X' i) μ μ)
    (hX : ∀ i, Measurable (X i)) (hX' : ∀ i, Measurable (X' i))
    (s : ι → ℝ) (hs : ∀ i, s i = 1 ∨ s i = -1) :
    μ.map (fun ω i ↦ s i * (X i ω - X' i ω)) = μ.map (fun ω i ↦ X i ω - X' i ω) := by
  classical
  let σ : ι ⊕ ι → ι ⊕ ι := Sum.elim (fun i ↦ if s i = -1 then Sum.inr i else Sum.inl i)
    (fun i ↦ if s i = -1 then Sum.inl i else Sum.inr i)
  have hσ : σ.Involutive := by
    rintro (i | i) <;> by_cases h : s i = -1 <;> simp [σ, h]
  let Z : ι ⊕ ι → Ω → ℝ := Sum.elim X X'
  have hZ : ∀ j, Measurable (Z j) := by
    rintro (i | i)
    exacts [hX i, hX' i]
  have hZ' : ∀ j, Measurable (Z (σ j)) := fun j ↦ hZ _
  have hmarg : ∀ j, μ.map (Z (σ j)) = μ.map (Z j) := by
    rintro (i | i) <;> by_cases h : s i = -1
    · simpa [σ, Z, h] using (hid i).map_eq.symm
    · simp [σ, Z, h]
    · simpa [σ, Z, h] using (hid i).map_eq
    · simp [σ, Z, h]
  have hperm : μ.map (fun ω j ↦ Z (σ j) ω) = μ.map (fun ω j ↦ Z j ω) :=
    (IdentDistrib.pi (fun j ↦ ⟨(hZ' j).aemeasurable, (hZ j).aemeasurable, hmarg j⟩)
      (hind.precomp hσ.injective) hind).map_eq
  let H : (ι ⊕ ι → ℝ) → ι → ℝ := fun z i ↦ z (Sum.inl i) - z (Sum.inr i)
  have hH : Measurable H := by fun_prop
  have hZm : Measurable fun ω j ↦ Z j ω := Measurable.of_eval hZ
  have hZ'm : Measurable fun ω j ↦ Z (σ j) ω := Measurable.of_eval hZ'
  have key : (fun ω i ↦ s i * (X i ω - X' i ω)) = H ∘ fun ω j ↦ Z (σ j) ω := by
    ext ω i
    rcases hs i with h | h
    · have h' : ¬ s i = -1 := by rw [h]; norm_num
      norm_num [H, σ, Z, h, h']
    · simp [H, σ, Z, h]
  rw [key, ← Measure.map_map hH hZ'm, hperm, Measure.map_map hH hZm]
  rfl

/-- If `Sum.elim X X'` is independent, `Xᵢ` and `X'ᵢ` are identically distributed, and the signs
`εᵢ` are independent of the differences `Xᵢ - X'ᵢ` as vectors and almost surely equal to `±1`,
then the vector `(εᵢ (Xᵢ - X'ᵢ))ᵢ` has the same law as `(Xᵢ - X'ᵢ)ᵢ`. -/
theorem IndepFun.map_fun_mul_sub_eq_of_identDistrib [Countable ι] {ε : ι → Ω → ℝ}
    (hindep : IndepFun (fun ω i ↦ ε i ω) (fun ω i ↦ X i ω - X' i ω) μ)
    (hind : iIndepFun (Sum.elim X X') μ) (hid : ∀ i, IdentDistrib (X i) (X' i) μ μ)
    (hX : ∀ i, Measurable (X i)) (hX' : ∀ i, Measurable (X' i)) (hε : ∀ i, Measurable (ε i))
    (hsign : ∀ i, ∀ᵐ ω ∂μ, ε i ω = 1 ∨ ε i ω = -1) :
    μ.map (fun ω i ↦ ε i ω * (X i ω - X' i ω)) = μ.map (fun ω i ↦ X i ω - X' i ω) := by
  have hEm : Measurable (fun ω i ↦ ε i ω) := Measurable.of_eval hε
  have hDm : Measurable (fun ω i ↦ X i ω - X' i ω) := Measurable.of_eval fun i ↦ (hX i).sub (hX' i)
  have hprod := hindep.map_prod_eq_prod_map_map hEm.aemeasurable hDm.aemeasurable
  have : IsProbabilityMeasure (μ.map fun ω i ↦ ε i ω) :=
    ⟨by rw [Measure.map_apply hEm MeasurableSet.univ]; simp⟩
  let H : (ι → ℝ) × (ι → ℝ) → ι → ℝ := fun p i ↦ p.1 i * p.2 i
  have hH : Measurable H := by fun_prop
  have hpm : Measurable fun ω ↦ ((fun i ↦ ε i ω), fun i ↦ X i ω - X' i ω) := hEm.prodMk hDm
  have hset : MeasurableSet {s : ι → ℝ | ∀ i, s i = 1 ∨ s i = -1} := by
    simp only [Set.ofPred_forall, Set.ofPred_or]
    exact MeasurableSet.iInter fun i ↦
      ((measurable_pi_apply i) (measurableSet_singleton _)).union
        ((measurable_pi_apply i) (measurableSet_singleton _))
  have hae : ∀ᵐ s ∂(μ.map fun ω i ↦ ε i ω), ∀ i, s i = 1 ∨ s i = -1 := by
    rw [ae_map_iff hEm.aemeasurable hset]
    filter_upwards [ae_all_iff.2 hsign] with ω h using h
  have key : (fun ω i ↦ ε i ω * (X i ω - X' i ω)) =
      H ∘ fun ω ↦ ((fun i ↦ ε i ω), fun i ↦ X i ω - X' i ω) := rfl
  rw [key, ← Measure.map_map hH hpm, hprod]
  have hg : ∀ᵐ s ∂(μ.map fun ω i ↦ ε i ω),
      (μ.map fun ω i ↦ X i ω - X' i ω).map (fun d i ↦ s i * d i) =
        μ.map fun ω i ↦ X i ω - X' i ω := by
    filter_upwards [hae] with s hs
    have hg : Measurable fun d : ι → ℝ ↦ fun i ↦ s i * d i := by fun_prop
    rw [Measure.map_map hg hDm]
    exact hind.map_fun_mul_sub_eq_of_identDistrib hid hX hX' s hs
  have hmp := (MeasurePreserving.id (μ.map fun ω i ↦ ε i ω)).skew_product
    (g := fun (s d : ι → ℝ) i ↦ s i * d i) hH hg
  exact ((measurePreserving_snd (μ := μ.map fun ω i ↦ ε i ω)
    (ν := μ.map fun ω i ↦ X i ω - X' i ω)).comp hmp).map_eq

/-- For measurable `Φ`, if `Sum.elim X X'` is independent, `Xᵢ` and `X'ᵢ` are identically
distributed, and the signs `εᵢ` are independent of the differences `Xᵢ - X'ᵢ` and almost surely
equal to `±1`, then `E Φ(∑ εᵢ (Xᵢ - X'ᵢ)) = E Φ(∑ (Xᵢ - X'ᵢ))`. -/
theorem IndepFun.integral_comp_sum_mul_sub_eq [Fintype ι] {ε : ι → Ω → ℝ} {Φ : ℝ → ℝ}
    (hindep : IndepFun (fun ω i ↦ ε i ω) (fun ω i ↦ X i ω - X' i ω) μ)
    (hind : iIndepFun (Sum.elim X X') μ) (hid : ∀ i, IdentDistrib (X i) (X' i) μ μ)
    (hX : ∀ i, Measurable (X i)) (hX' : ∀ i, Measurable (X' i)) (hε : ∀ i, Measurable (ε i))
    (hsign : ∀ i, ∀ᵐ ω ∂μ, ε i ω = 1 ∨ ε i ω = -1) (hΦ : Measurable Φ) :
    ∫ ω, Φ (∑ i, ε i ω * (X i ω - X' i ω)) ∂μ = ∫ ω, Φ (∑ i, (X i ω - X' i ω)) ∂μ := by
  have hG : Measurable fun v : ι → ℝ ↦ Φ (∑ i, v i) := hΦ.comp (by fun_prop)
  have hV : Measurable fun ω i ↦ ε i ω * (X i ω - X' i ω) :=
    Measurable.of_eval fun i ↦ (hε i).mul ((hX i).sub (hX' i))
  have hD : Measurable fun ω i ↦ X i ω - X' i ω :=
    Measurable.of_eval fun i ↦ (hX i).sub (hX' i)
  calc ∫ ω, Φ (∑ i, ε i ω * (X i ω - X' i ω)) ∂μ
      = ∫ v, Φ (∑ i, v i) ∂(μ.map fun ω i ↦ ε i ω * (X i ω - X' i ω)) :=
        (integral_map hV.aemeasurable hG.aestronglyMeasurable).symm
    _ = ∫ v, Φ (∑ i, v i) ∂(μ.map fun ω i ↦ X i ω - X' i ω) := by
        rw [hindep.map_fun_mul_sub_eq_of_identDistrib hind hid hX hX' hε hsign]
    _ = ∫ ω, Φ (∑ i, (X i ω - X' i ω)) ∂μ :=
        integral_map hD.aemeasurable hG.aestronglyMeasurable

end ProbabilityTheory

open ProbabilityTheory

/-- **Desymmetrization.** If `X` is independent of `X'` as a vector and the `X'ᵢ` are integrable
and centred, then for convex `Φ` with `Φ (∑ Xᵢ)` and `Φ (∑ (Xᵢ - X'ᵢ))` integrable,
`E Φ(∑ Xᵢ) ≤ E Φ(∑ (Xᵢ - X'ᵢ))`. -/
theorem ConvexOn.integral_comp_sum_le_integral_comp_sum_sub {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] {μ : Measure Ω} [IsProbabilityMeasure μ] {X X' : ι → Ω → ℝ} {Φ : ℝ → ℝ}
    (hΦ : ConvexOn ℝ univ Φ)
    (hindep : IndepFun (fun ω i ↦ X i ω) (fun ω i ↦ X' i ω) μ)
    (hX : ∀ i, Measurable (X i)) (hX' : ∀ i, Measurable (X' i))
    (hint' : ∀ i, Integrable (X' i) μ) (h0 : ∀ i, ∫ ω, X' i ω ∂μ = 0)
    (h1 : Integrable (fun ω ↦ Φ (∑ i, X i ω)) μ)
    (h2 : Integrable (fun ω ↦ Φ (∑ i, (X i ω - X' i ω))) μ) :
    ∫ ω, Φ (∑ i, X i ω) ∂μ ≤ ∫ ω, Φ (∑ i, (X i ω - X' i ω)) ∂μ := by
  have hΦc : Continuous Φ := continuousOn_univ.1 (hΦ.continuousOn isOpen_univ)
  have hAm : Measurable fun ω i ↦ X i ω := Measurable.of_eval hX
  have hBm : Measurable fun ω i ↦ X' i ω := Measurable.of_eval hX'
  have : IsProbabilityMeasure (μ.map fun ω i ↦ X i ω) :=
    ⟨by rw [Measure.map_apply hAm MeasurableSet.univ]; simp⟩
  have : IsProbabilityMeasure (μ.map fun ω i ↦ X' i ω) :=
    ⟨by rw [Measure.map_apply hBm MeasurableSet.univ]; simp⟩
  have hprod := hindep.map_prod_eq_prod_map_map hAm.aemeasurable hBm.aemeasurable
  let F : (ι → ℝ) × (ι → ℝ) → ℝ := fun p ↦ Φ (∑ i, (p.1 i - p.2 i))
  have hF : Measurable F := by fun_prop
  have hFint : Integrable F ((μ.map fun ω i ↦ X i ω).prod (μ.map fun ω i ↦ X' i ω)) := by
    rw [← hprod]
    exact (integrable_map_measure hF.aestronglyMeasurable (hAm.prodMk hBm).aemeasurable).2 h2
  have hG : Measurable fun x : ι → ℝ ↦ Φ (∑ i, x i) := by fun_prop
  have hGint : Integrable (fun x : ι → ℝ ↦ Φ (∑ i, x i)) (μ.map fun ω i ↦ X i ω) :=
    (integrable_map_measure hG.aestronglyMeasurable hAm.aemeasurable).2 h1
  have hcoord : ∀ i, Integrable (fun d : ι → ℝ ↦ d i) (μ.map fun ω i ↦ X' i ω) := fun i ↦
    (integrable_map_measure (measurable_pi_apply i).aestronglyMeasurable
      hBm.aemeasurable).2 (hint' i)
  have hcoord0 : ∀ i, ∫ d, d i ∂(μ.map fun ω i ↦ X' i ω) = 0 := fun i ↦ by
    rw [integral_map hBm.aemeasurable (measurable_pi_apply i).aestronglyMeasurable]
    exact h0 i
  have hjensen : ∀ᵐ x ∂(μ.map fun ω i ↦ X i ω),
      Φ (∑ i, x i) ≤ ∫ d, F (x, d) ∂(μ.map fun ω i ↦ X' i ω) := by
    filter_upwards [hFint.prod_right_ae] with x hx
    have hf : Integrable (fun d : ι → ℝ ↦ ∑ i, (x i - d i)) (μ.map fun ω i ↦ X' i ω) :=
      integrable_finsetSum _ fun i _ ↦ (integrable_const (x i)).sub (hcoord i)
    have hmean : ∫ d, ∑ i, (x i - d i) ∂(μ.map fun ω i ↦ X' i ω) = ∑ i, x i := by
      rw [integral_finsetSum (f := fun i (d : ι → ℝ) ↦ x i - d i) Finset.univ
        fun i _ ↦ (integrable_const (x i)).sub (hcoord i)]
      simp [integral_sub (integrable_const _) (hcoord _), hcoord0]
    have := hΦ.map_integral_le hΦc.continuousOn isClosed_univ (ae_of_all _ fun _ ↦ mem_univ _)
      hf hx
    rwa [hmean] at this
  calc ∫ ω, Φ (∑ i, X i ω) ∂μ
      = ∫ x, Φ (∑ i, x i) ∂(μ.map fun ω i ↦ X i ω) :=
        (integral_map hAm.aemeasurable hG.aestronglyMeasurable).symm
    _ ≤ ∫ x, ∫ d, F (x, d) ∂(μ.map fun ω i ↦ X' i ω) ∂(μ.map fun ω i ↦ X i ω) :=
        integral_mono_ae hGint hFint.integral_prod_left hjensen
    _ = ∫ p, F p ∂((μ.map fun ω i ↦ X i ω).prod (μ.map fun ω i ↦ X' i ω)) :=
        (integral_prod F hFint).symm
    _ = ∫ ω, Φ (∑ i, (X i ω - X' i ω)) ∂μ := by
        rw [← hprod, integral_map (hAm.prodMk hBm).aemeasurable hF.aestronglyMeasurable]

/-- **The symmetrization inequality.** Let `X` and `X'` be jointly independent (the family
`Sum.elim X X'` is `iIndepFun`) with `Xᵢ` and `X'ᵢ` identically distributed, and let the `Xᵢ`
be integrable and centred. Let `εᵢ` be signs, almost surely equal to `±1` and independent of the
vector `(Xᵢ - X'ᵢ)ᵢ`. Then for convex `Φ` with `Φ (∑ Xᵢ)` and `Φ (∑ (Xᵢ - X'ᵢ))` integrable,
`E Φ(∑ Xᵢ) ≤ E Φ(∑ (Xᵢ - X'ᵢ)) = E Φ(∑ εᵢ (Xᵢ - X'ᵢ))`. -/
theorem ConvexOn.symmetrization_inequality {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X X' ε : ι → Ω → ℝ} {Φ : ℝ → ℝ}
    (hΦ : ConvexOn ℝ univ Φ) (hind : iIndepFun (Sum.elim X X') μ)
    (hid : ∀ i, IdentDistrib (X i) (X' i) μ μ)
    (hX : ∀ i, Measurable (X i)) (hX' : ∀ i, Measurable (X' i)) (hε : ∀ i, Measurable (ε i))
    (hint : ∀ i, Integrable (X i) μ) (h0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hindep : IndepFun (fun ω i ↦ ε i ω) (fun ω i ↦ X i ω - X' i ω) μ)
    (hsign : ∀ i, ∀ᵐ ω ∂μ, ε i ω = 1 ∨ ε i ω = -1)
    (h1 : Integrable (fun ω ↦ Φ (∑ i, X i ω)) μ)
    (h2 : Integrable (fun ω ↦ Φ (∑ i, (X i ω - X' i ω))) μ) :
    ∫ ω, Φ (∑ i, X i ω) ∂μ ≤ ∫ ω, Φ (∑ i, (X i ω - X' i ω)) ∂μ ∧
      ∫ ω, Φ (∑ i, (X i ω - X' i ω)) ∂μ = ∫ ω, Φ (∑ i, ε i ω * (X i ω - X' i ω)) ∂μ := by
  have hΦc : Continuous Φ := continuousOn_univ.1 (hΦ.continuousOn isOpen_univ)
  refine ⟨hΦ.integral_comp_sum_le_integral_comp_sum_sub (hind.indepFun_fun_sumElim hX hX') hX hX'
    (fun i ↦ (hid i).integrable_snd (hint i)) (fun i ↦ ?_) h1 h2, ?_⟩
  · rw [← (hid i).integral_eq, h0 i]
  · exact (hindep.integral_comp_sum_mul_sub_eq hind hid hX hX' hε hsign hΦc.measurable).symm

/-- **The symmetrization inequality with Rademacher signs.** With the notation and hypotheses of
`ConvexOn.symmetrization_inequality`, the signs `εᵢ` may be taken to have the Rademacher law
`TauCeti.Probability.rademacherMeasure` and to be independent of the vector `(Xᵢ - X'ᵢ)ᵢ`. -/
theorem ConvexOn.symmetrization_inequality_of_map_eq_rademacherMeasure {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X X' ε : ι → Ω → ℝ} {Φ : ℝ → ℝ}
    (hΦ : ConvexOn ℝ univ Φ) (hind : iIndepFun (Sum.elim X X') μ)
    (hid : ∀ i, IdentDistrib (X i) (X' i) μ μ)
    (hX : ∀ i, Measurable (X i)) (hX' : ∀ i, Measurable (X' i)) (hε : ∀ i, Measurable (ε i))
    (hint : ∀ i, Integrable (X i) μ) (h0 : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hindep : IndepFun (fun ω i ↦ ε i ω) (fun ω i ↦ X i ω - X' i ω) μ)
    (hlaw : ∀ i, μ.map (ε i) = TauCeti.Probability.rademacherMeasure)
    (h1 : Integrable (fun ω ↦ Φ (∑ i, X i ω)) μ)
    (h2 : Integrable (fun ω ↦ Φ (∑ i, (X i ω - X' i ω))) μ) :
    ∫ ω, Φ (∑ i, X i ω) ∂μ ≤ ∫ ω, Φ (∑ i, (X i ω - X' i ω)) ∂μ ∧
      ∫ ω, Φ (∑ i, (X i ω - X' i ω)) ∂μ = ∫ ω, Φ (∑ i, ε i ω * (X i ω - X' i ω)) ∂μ :=
  hΦ.symmetrization_inequality hind hid hX hX' hε hint h0 hindep
    (fun i ↦ TauCeti.Probability.ae_eq_one_or_eq_neg_one_of_map_eq_rademacherMeasure (hε i)
      (hlaw i)) h1 h2
