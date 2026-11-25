/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Banach
public import TauCeti.Analysis.Normed.Operator.Restrict
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Basic

/-!
# Bounded bilinear maps of Sobolev sections from pointwise products

Let `C₁`, `C₂` and `C₃` be chart data (`TauCeti.SectionChartData`) over the same space `E`, with
model fibres `F₁`, `F₂` and `F₃`, and let `b : F₁ →L[ℝ] F₂ →L[ℝ] F₃` be continuous bilinear. Suppose
that for all Sobolev sections `x` of `C₁` and `y` of `C₂` some Sobolev section of `C₃` has, in every
chart, chart data equal almost everywhere to the pointwise product `b (x t) (y t)` of the chart data
of `x` and `y`. Then this product is a bounded bilinear map
(`TauCeti.SectionChartData.bilinOfAeEq`).

No norm estimate is needed: when the Sobolev spaces are complete, continuity in each variable
follows from the closed graph theorem, because convergence of Sobolev sections gives almost
everywhere convergence of their chart data along a subsequence
(`TauCeti.SectionChartData.chartValueL_ae_eq_of_tendsto`). So the analytic content of a
multiplication theorem for Sobolev sections is only that the products lie in the target space.

The charts of `C₃` are matched with those of `C₁` and `C₂` by maps of indices `e₁` and `e₂`, with
the image of each chart of `C₃` inside the images of the matching charts.

## Main definitions

* `TauCeti.SectionChartData.bilinOfAeEq`: the product as a continuous bilinear map.

## Main results

* `TauCeti.SectionChartData.chartValueL_ae_eq_of_tendsto`: chart data of limits are limits of chart
  data, almost everywhere.
* `TauCeti.SectionChartData.chartValueL_bilinOfAeEq_ae`,
  `TauCeti.SectionChartData.eq_bilinOfAeEq_iff`: the chart data of the product, which determine it.
-/

public section

noncomputable section

open Filter MeasureTheory Module Set
open scoped ENNReal Topology

universe u

namespace TauCeti.SectionChartData

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {F' F₁ F₂ F₃ : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
  [NormedAddCommGroup F₃] [NormedSpace ℝ F₃] [FiniteDimensional ℝ F₃]
  {S' S₁ S₂ S₃ : Type*} [AddCommGroup S'] [Module ℝ S'] [AddCommGroup S₁] [Module ℝ S₁]
  [AddCommGroup S₂] [Module ℝ S₂] [AddCommGroup S₃] [Module ℝ S₃]
  {p' p₁ p₂ p₃ : ℝ≥0∞} [Fact (1 ≤ p')] [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] [Fact (1 ≤ p₃)]
  {k' k₁ k₂ k₃ : ℕ}

/-- **Chart data of limits.** Let `x n → x₀` be Sobolev sections of `C'` and `z n → z₀` Sobolev
sections of `C`, such that in chart `i` the chart data of `z n` are those of `x n` in chart `i'`
followed by pointwise continuous linear maps `Φ t`. Then the same holds for the limits `z₀` and
`x₀`, almost everywhere on the image of chart `i`. -/
theorem chartValueL_ae_eq_of_tendsto {C : SectionChartData E F₃ S₃} {C' : SectionChartData E F' S'}
    {i : Fin C.n} {i' : Fin C'.n} (hi : (C.image i : Set E) ⊆ C'.image i')
    (Φ : E → F' →L[ℝ] F₃) {x : ℕ → C'.sobolevSections μ p' k'} {x₀ : C'.sobolevSections μ p' k'}
    {z : ℕ → C.sobolevSections μ p₃ k₃} {z₀ : C.sobolevSections μ p₃ k₃}
    (hx : Tendsto x atTop (𝓝 x₀)) (hz : Tendsto z atTop (𝓝 z₀))
    (h : ∀ n, C.chartValueL μ p₃ k₃ i (z n) =ᵐ[μ.restrict (C.image i)]
      fun t ↦ Φ t (C'.chartValueL μ p' k' i' (x n) t)) :
    C.chartValueL μ p₃ k₃ i z₀ =ᵐ[μ.restrict (C.image i)]
      fun t ↦ Φ t (C'.chartValueL μ p' k' i' x₀ t) := by
  -- Almost everywhere convergence of the chart data of `z` along a subsequence, then of those of
  -- `x` along a further subsequence.
  obtain ⟨ns, hns, hz'⟩ := (tendstoInMeasure_of_tendsto_Lp
    (((C.chartValueL μ p₃ k₃ i).continuous.tendsto z₀).comp
      ((continuous_subtypeVal.tendsto z₀).comp hz))).exists_seq_tendsto_ae
  obtain ⟨ms, hms, hx'⟩ := (tendstoInMeasure_of_tendsto_Lp
    ((((C'.chartValueL μ p' k' i').continuous.tendsto x₀).comp
      ((continuous_subtypeVal.tendsto x₀).comp hx)).comp
      hns.tendsto_atTop)).exists_seq_tendsto_ae
  filter_upwards [ae_all_iff.2 h, hz', ae_restrict_of_ae_restrict_of_subset hi hx']
    with t ht hzt hxt
  refine tendsto_nhds_unique (hzt.comp hms.tendsto_atTop) ?_
  exact (((Φ t).continuous.tendsto _).comp hxt).congr fun m ↦ (ht (ns (ms m))).symm

variable (C₃ : SectionChartData E F₃ S₃) (C₁ : SectionChartData E F₁ S₁)
  (C₂ : SectionChartData E F₂ S₂) (b : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
  (e₁ : Fin C₃.n → Fin C₁.n) (e₂ : Fin C₃.n → Fin C₂.n)

/-- The pointwise product of the chart data of Sobolev sections of `C₁` and `C₂`, read in chart
`i` of `C₃` through the matching charts `e₁ i` and `e₂ i`. -/
def chartProduct (x : C₁.sobolevSections μ p₁ k₁) (y : C₂.sobolevSections μ p₂ k₂)
    (i : Fin C₃.n) (t : E) : F₃ :=
  b (C₁.chartValueL μ p₁ k₁ (e₁ i) x t) (C₂.chartValueL μ p₂ k₂ (e₂ i) y t)

/-- Products of Sobolev sections of `C₁` and `C₂` exist in the Sobolev sections of `C₃`: some
Sobolev section of `C₃` has chart data equal almost everywhere to the pointwise product. -/
def HasAeProducts (μ : Measure E) [μ.IsAddHaarMeasure] (p₁ p₂ p₃ : ℝ≥0∞) [Fact (1 ≤ p₁)]
    [Fact (1 ≤ p₂)] [Fact (1 ≤ p₃)] (k₁ k₂ k₃ : ℕ) : Prop :=
  ∀ (x : C₁.sobolevSections μ p₁ k₁) (y : C₂.sobolevSections μ p₂ k₂),
    ∃ z : C₃.sobolevSections μ p₃ k₃, ∀ i, C₃.chartValueL μ p₃ k₃ i z
      =ᵐ[μ.restrict (C₃.image i)] C₃.chartProduct C₁ C₂ b e₁ e₂ x y i

variable {C₃ C₁ C₂ b e₁ e₂}
  (h₁ : ∀ i, (C₃.image i : Set E) ⊆ C₁.image (e₁ i))
  (h₂ : ∀ i, (C₃.image i : Set E) ⊆ C₂.image (e₂ i))
  (hb : C₃.HasAeProducts C₁ C₂ b e₁ e₂ μ p₁ p₂ p₃ k₁ k₂ k₃)

omit [FiniteDimensional ℝ F₃] in
@[simp]
theorem chartProduct_apply (x : C₁.sobolevSections μ p₁ k₁) (y : C₂.sobolevSections μ p₂ k₂)
    (i : Fin C₃.n) (t : E) : C₃.chartProduct C₁ C₂ b e₁ e₂ x y i t =
      b (C₁.chartValueL μ p₁ k₁ (e₁ i) x t) (C₂.chartValueL μ p₂ k₂ (e₂ i) y t) :=
  (rfl)

theorem hasAeProducts_iff : C₃.HasAeProducts C₁ C₂ b e₁ e₂ μ p₁ p₂ p₃ k₁ k₂ k₃ ↔
    ∀ (x : C₁.sobolevSections μ p₁ k₁) (y : C₂.sobolevSections μ p₂ k₂),
      ∃ z : C₃.sobolevSections μ p₃ k₃, ∀ i, C₃.chartValueL μ p₃ k₃ i z
        =ᵐ[μ.restrict (C₃.image i)] C₃.chartProduct C₁ C₂ b e₁ e₂ x y i :=
  Iff.rfl

/-- The product chosen by `TauCeti.SectionChartData.HasAeProducts`. -/
private def mulAux (x : C₁.sobolevSections μ p₁ k₁) (y : C₂.sobolevSections μ p₂ k₂) :
    C₃.sobolevSections μ p₃ k₃ :=
  (hb x y).choose

private theorem chartValueL_mulAux (x : C₁.sobolevSections μ p₁ k₁)
    (y : C₂.sobolevSections μ p₂ k₂) (i : Fin C₃.n) :
    C₃.chartValueL μ p₃ k₃ i (mulAux hb x y)
      =ᵐ[μ.restrict (C₃.image i)] C₃.chartProduct C₁ C₂ b e₁ e₂ x y i :=
  (hb x y).choose_spec i

/-- A Sobolev section of `C₃` with chart data the pointwise product is the chosen product. -/
private theorem eq_mulAux {x : C₁.sobolevSections μ p₁ k₁} {y : C₂.sobolevSections μ p₂ k₂}
    {z : C₃.sobolevSections μ p₃ k₃}
    (hz : ∀ i, C₃.chartValueL μ p₃ k₃ i z
      =ᵐ[μ.restrict (C₃.image i)] C₃.chartProduct C₁ C₂ b e₁ e₂ x y i) :
    z = mulAux hb x y :=
  eq_of_chartValueL_ae_eq fun i ↦ (hz i).trans (chartValueL_mulAux hb x y i).symm

/-- **Linearity of the chosen product.** If the chart products of `x` and `y` are the combination
`c • (x₁ ⬝ y₁) + d • (x₂ ⬝ y₂)` of two chart products, the chosen products combine in the same
way. -/
private theorem mulAux_eq_smul_add_smul {x x₁ x₂ : C₁.sobolevSections μ p₁ k₁}
    {y y₁ y₂ : C₂.sobolevSections μ p₂ k₂} (c d : ℝ)
    (h : ∀ i, C₃.chartProduct C₁ C₂ b e₁ e₂ x y i =ᵐ[μ.restrict (C₃.image i)]
      c • C₃.chartProduct C₁ C₂ b e₁ e₂ x₁ y₁ i + d • C₃.chartProduct C₁ C₂ b e₁ e₂ x₂ y₂ i) :
    mulAux hb x y = c • mulAux hb x₁ y₁ + d • mulAux hb x₂ y₂ :=
  (eq_mulAux hb fun i ↦ by
    filter_upwards [h i, chartValueL_mulAux hb x₁ y₁ i, chartValueL_mulAux hb x₂ y₂ i,
      Lp.coeFn_add (c • C₃.chartValueL μ p₃ k₃ i (mulAux hb x₁ y₁))
        (d • C₃.chartValueL μ p₃ k₃ i (mulAux hb x₂ y₂)),
      Lp.coeFn_smul c (C₃.chartValueL μ p₃ k₃ i (mulAux hb x₁ y₁)),
      Lp.coeFn_smul d (C₃.chartValueL μ p₃ k₃ i (mulAux hb x₂ y₂))] with t ht h₁ h₂ hadd hs₁ hs₂
    simp only [Submodule.coe_add, Submodule.coe_smul, map_add, map_smul, hadd, Pi.add_apply, hs₁,
      hs₂, Pi.smul_apply, h₁, h₂, ht]).symm

omit [FiniteDimensional ℝ F₃] in
include h₁ in
/-- The chart products are additive in the first factor, almost everywhere. -/
theorem chartProduct_add_left_ae (x x' : C₁.sobolevSections μ p₁ k₁)
    (y : C₂.sobolevSections μ p₂ k₂) (i : Fin C₃.n) :
    C₃.chartProduct C₁ C₂ b e₁ e₂ (x + x') y i =ᵐ[μ.restrict (C₃.image i)]
      C₃.chartProduct C₁ C₂ b e₁ e₂ x y i + C₃.chartProduct C₁ C₂ b e₁ e₂ x' y i := by
  filter_upwards [ae_restrict_of_ae_restrict_of_subset (h₁ i) (Lp.coeFn_add
    (C₁.chartValueL μ p₁ k₁ (e₁ i) x) (C₁.chartValueL μ p₁ k₁ (e₁ i) x'))] with t ht
  simp only [chartProduct_apply, Submodule.coe_add, map_add, ht, Pi.add_apply, add_apply]

omit [FiniteDimensional ℝ F₃] in
include h₁ in
/-- The chart products are homogeneous in the first factor, almost everywhere. -/
theorem chartProduct_smul_left_ae (c : ℝ) (x : C₁.sobolevSections μ p₁ k₁)
    (y : C₂.sobolevSections μ p₂ k₂) (i : Fin C₃.n) :
    C₃.chartProduct C₁ C₂ b e₁ e₂ (c • x) y i =ᵐ[μ.restrict (C₃.image i)]
      c • C₃.chartProduct C₁ C₂ b e₁ e₂ x y i := by
  filter_upwards [ae_restrict_of_ae_restrict_of_subset (h₁ i)
    (Lp.coeFn_smul c (C₁.chartValueL μ p₁ k₁ (e₁ i) x))] with t ht
  simp only [chartProduct_apply, Submodule.coe_smul, map_smul, ht, Pi.smul_apply, smul_apply]

omit [FiniteDimensional ℝ F₃] in
include h₂ in
/-- The chart products are additive in the second factor, almost everywhere. -/
theorem chartProduct_add_right_ae (x : C₁.sobolevSections μ p₁ k₁)
    (y y' : C₂.sobolevSections μ p₂ k₂) (i : Fin C₃.n) :
    C₃.chartProduct C₁ C₂ b e₁ e₂ x (y + y') i =ᵐ[μ.restrict (C₃.image i)]
      C₃.chartProduct C₁ C₂ b e₁ e₂ x y i + C₃.chartProduct C₁ C₂ b e₁ e₂ x y' i := by
  filter_upwards [ae_restrict_of_ae_restrict_of_subset (h₂ i) (Lp.coeFn_add
    (C₂.chartValueL μ p₂ k₂ (e₂ i) y) (C₂.chartValueL μ p₂ k₂ (e₂ i) y'))] with t ht
  simp only [chartProduct_apply, Submodule.coe_add, map_add, ht, Pi.add_apply]

omit [FiniteDimensional ℝ F₃] in
include h₂ in
/-- The chart products are homogeneous in the second factor, almost everywhere. -/
theorem chartProduct_smul_right_ae (c : ℝ) (x : C₁.sobolevSections μ p₁ k₁)
    (y : C₂.sobolevSections μ p₂ k₂) (i : Fin C₃.n) :
    C₃.chartProduct C₁ C₂ b e₁ e₂ x (c • y) i =ᵐ[μ.restrict (C₃.image i)]
      c • C₃.chartProduct C₁ C₂ b e₁ e₂ x y i := by
  filter_upwards [ae_restrict_of_ae_restrict_of_subset (h₂ i)
    (Lp.coeFn_smul c (C₂.chartValueL μ p₂ k₂ (e₂ i) y))] with t ht
  simp only [chartProduct_apply, Submodule.coe_smul, map_smul, ht, Pi.smul_apply]

include h₁ h₂

/-- The chosen product, as a bilinear map: each linearity law is `mulAux_eq_smul_add_smul` applied
to the corresponding law of the chart products. -/
private def mulₗ : C₁.sobolevSections μ p₁ k₁ →ₗ[ℝ] C₂.sobolevSections μ p₂ k₂ →ₗ[ℝ]
    C₃.sobolevSections μ p₃ k₃ :=
  LinearMap.mk₂ ℝ (mulAux hb)
    (fun x x' y ↦ by simpa using mulAux_eq_smul_add_smul hb 1 1 fun i ↦
      (chartProduct_add_left_ae h₁ x x' y i).trans (by simp))
    (fun c x y ↦ by simpa using mulAux_eq_smul_add_smul hb c 0 (x₂ := x) (y₂ := y) fun i ↦
      (chartProduct_smul_left_ae h₁ c x y i).trans (by simp))
    (fun x y y' ↦ by simpa using mulAux_eq_smul_add_smul hb 1 1 fun i ↦
      (chartProduct_add_right_ae h₂ x y y' i).trans (by simp))
    (fun c x y ↦ by simpa using mulAux_eq_smul_add_smul hb c 0 (x₂ := x) (y₂ := y) fun i ↦
      (chartProduct_smul_right_ae h₂ c x y i).trans (by simp))

private theorem mulₗ_apply (x : C₁.sobolevSections μ p₁ k₁) (y : C₂.sobolevSections μ p₂ k₂) :
    mulₗ h₁ h₂ hb x y = mulAux hb x y :=
  (rfl)

variable [CompleteSpace (C₁.sobolevSections μ p₁ k₁)] [CompleteSpace (C₂.sobolevSections μ p₂ k₂)]
  [CompleteSpace (C₃.sobolevSections μ p₃ k₃)]

/-- For fixed `x`, the product is continuous in `y`, by the closed graph theorem. -/
private def mulRightL (x : C₁.sobolevSections μ p₁ k₁) :
    C₂.sobolevSections μ p₂ k₂ →L[ℝ] C₃.sobolevSections μ p₃ k₃ :=
  ContinuousLinearMap.ofSeqClosedGraph (g := mulₗ h₁ h₂ hb x) fun u y z hu hz ↦
    eq_of_chartValueL_ae_eq fun i ↦ by
      refine (chartValueL_ae_eq_of_tendsto (h₂ i)
        (fun t ↦ b (C₁.chartValueL μ p₁ k₁ (e₁ i) x t)) hu hz fun n ↦ ?_).trans
          (chartValueL_mulAux hb x y i).symm
      exact chartValueL_mulAux hb x (u n) i

omit [CompleteSpace (C₁.sobolevSections μ p₁ k₁)] in
private theorem mulRightL_apply (x : C₁.sobolevSections μ p₁ k₁)
    (y : C₂.sobolevSections μ p₂ k₂) : mulRightL h₁ h₂ hb x y = mulAux hb x y := by
  rw [mulRightL, ContinuousLinearMap.coeFn_ofSeqClosedGraph, mulₗ_apply]

/-- `x ↦ mulRightL x`, followed by the inclusion of the Sobolev sections into the tuples of
Sobolev functions, as a linear map into the continuous linear maps. -/
private def mulRightₗ : C₁.sobolevSections μ p₁ k₁ →ₗ[ℝ]
    C₂.sobolevSections μ p₂ k₂ →L[ℝ] C₃.SobolevData μ p₃ k₃ where
  toFun x := (C₃.sobolevSections μ p₃ k₃).subtypeL.comp (mulRightL h₁ h₂ hb x)
  map_add' x x' := ContinuousLinearMap.ext fun y ↦ by
    simp only [add_apply, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
      mulRightL_apply, ← mulₗ_apply h₁ h₂, map_add, LinearMap.add_apply]
  map_smul' c x := ContinuousLinearMap.ext fun y ↦ by
    simp only [smul_apply, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
      mulRightL_apply, ← mulₗ_apply h₁ h₂, map_smul, LinearMap.smul_apply, RingHom.id_apply]

omit [CompleteSpace (C₁.sobolevSections μ p₁ k₁)] in
private theorem mulRightₗ_apply (x : C₁.sobolevSections μ p₁ k₁)
    (y : C₂.sobolevSections μ p₂ k₂) :
    mulRightₗ h₁ h₂ hb x y = (mulAux hb x y : C₃.SobolevData μ p₃ k₃) := by
  simp only [mulRightₗ, LinearMap.coe_mk, AddHom.coe_mk, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply, mulRightL_apply]

/-- The product, as a continuous bilinear map into the tuples of Sobolev functions. Continuity in
the first variable is the closed graph theorem: a limit of products is the product of the limits,
by `TauCeti.SectionChartData.chartValueL_ae_eq_of_tendsto`. -/
private def mulData : C₁.sobolevSections μ p₁ k₁ →L[ℝ] C₂.sobolevSections μ p₂ k₂ →L[ℝ]
    C₃.SobolevData μ p₃ k₃ := by
  -- Naming the normed structures of the Sobolev sections keeps the instances of the space of
  -- continuous linear maps those of the statement.
  letI : NormedAddCommGroup (C₁.sobolevSections μ p₁ k₁) := inferInstance
  letI : NormedSpace ℝ (C₁.sobolevSections μ p₁ k₁) := inferInstance
  letI : NormedAddCommGroup (C₂.sobolevSections μ p₂ k₂) := inferInstance
  letI : NormedSpace ℝ (C₂.sobolevSections μ p₂ k₂) := inferInstance
  exact ContinuousLinearMap.ofSeqClosedGraph (g := mulRightₗ h₁ h₂ hb) fun u x T hu hT ↦
    ContinuousLinearMap.ext fun y ↦ by
      have hTy : Tendsto (fun n ↦ (mulAux hb (u n) y : C₃.SobolevData μ p₃ k₃)) atTop
          (𝓝 (T y)) :=
        (((ContinuousLinearMap.apply ℝ (C₃.SobolevData μ p₃ k₃) y).continuous.tendsto
          T).comp hT).congr fun n ↦ mulRightₗ_apply h₁ h₂ hb (u n) y
      -- The limit lies in the closed subspace of Sobolev sections.
      have hmem : T y ∈ C₃.sobolevSections μ p₃ k₃ :=
        (completeSpace_coe_iff_isComplete.1 inferInstance).isClosed.mem_of_tendsto hTy
          (Eventually.of_forall fun n ↦ (mulAux hb (u n) y).property)
      have hz : Tendsto (fun n ↦ mulAux hb (u n) y) atTop (𝓝 ⟨T y, hmem⟩) :=
        tendsto_subtype_rng.2 hTy
      rw [mulRightₗ_apply]
      refine congrArg Subtype.val (eq_of_chartValueL_ae_eq (w := ⟨T y, hmem⟩) fun i ↦ ?_)
      refine (chartValueL_ae_eq_of_tendsto (h₁ i)
        (fun t ↦ b.flip (C₂.chartValueL μ p₂ k₂ (e₂ i) y t)) hu hz fun n ↦ ?_).trans ?_
      · filter_upwards [chartValueL_mulAux hb (u n) y i] with t ht
        rw [ht, chartProduct_apply, ContinuousLinearMap.flip_apply]
      · filter_upwards [chartValueL_mulAux hb x y i] with t ht
        rw [ht, chartProduct_apply, ContinuousLinearMap.flip_apply]

/-- **Products of Sobolev sections as a bounded bilinear map.** Under
`TauCeti.SectionChartData.HasAeProducts`, the product of Sobolev sections of `C₁` and `C₂`, whose
chart data are the pointwise products `b (x t) (y t)` of their chart data, is a continuous bilinear
map into the Sobolev sections of `C₃`. Continuity in each variable is the closed graph theorem. -/
def bilinOfAeEq : C₁.sobolevSections μ p₁ k₁ →L[ℝ] C₂.sobolevSections μ p₂ k₂ →L[ℝ]
    C₃.sobolevSections μ p₃ k₃ :=
  (mulData h₁ h₂ hb).codRestrictBilin (C₃.sobolevSections μ p₃ k₃) fun x y ↦ by
    rw [mulData, ContinuousLinearMap.coeFn_ofSeqClosedGraph, mulRightₗ_apply]
    exact (mulAux hb x y).property

private theorem bilinOfAeEq_apply (x : C₁.sobolevSections μ p₁ k₁)
    (y : C₂.sobolevSections μ p₂ k₂) : bilinOfAeEq h₁ h₂ hb x y = mulAux hb x y := by
  refine Subtype.ext ?_
  rw [bilinOfAeEq, ContinuousLinearMap.coe_codRestrictBilin_apply, mulData,
    ContinuousLinearMap.coeFn_ofSeqClosedGraph, mulRightₗ_apply]

/-- The chart data of the product are the pointwise products of the chart data. -/
theorem chartValueL_bilinOfAeEq_ae (x : C₁.sobolevSections μ p₁ k₁)
    (y : C₂.sobolevSections μ p₂ k₂) (i : Fin C₃.n) :
    C₃.chartValueL μ p₃ k₃ i (bilinOfAeEq h₁ h₂ hb x y)
      =ᵐ[μ.restrict (C₃.image i)] C₃.chartProduct C₁ C₂ b e₁ e₂ x y i := by
  rw [bilinOfAeEq_apply]
  exact chartValueL_mulAux hb x y i

/-- **Uniqueness.** The product is the only Sobolev section of `C₃` whose chart data are the
pointwise products of the chart data. -/
theorem eq_bilinOfAeEq_iff {x : C₁.sobolevSections μ p₁ k₁} {y : C₂.sobolevSections μ p₂ k₂}
    {z : C₃.sobolevSections μ p₃ k₃} :
    z = bilinOfAeEq h₁ h₂ hb x y ↔ ∀ i, C₃.chartValueL μ p₃ k₃ i z
      =ᵐ[μ.restrict (C₃.image i)] C₃.chartProduct C₁ C₂ b e₁ e₂ x y i :=
  ⟨fun h ↦ h ▸ chartValueL_bilinOfAeEq_ae h₁ h₂ hb x y, fun h ↦ eq_of_chartValueL_ae_eq fun i ↦
    (h i).trans (chartValueL_bilinOfAeEq_ae h₁ h₂ hb x y i).symm⟩

end TauCeti.SectionChartData
