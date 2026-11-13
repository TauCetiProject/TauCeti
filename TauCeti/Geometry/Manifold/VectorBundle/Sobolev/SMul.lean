/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.Structures
public import TauCeti.Analysis.Sobolev.Wkp.SmoothMultiplication
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Basic

/-!
# Multiplication by a smooth function on Sobolev sections

Let `M` be a smooth manifold without boundary modelled on a finite-dimensional real inner product
space `E`, let `V → M` be a real vector bundle with finite-dimensional model fibre `F`, and let `A`
be a finite bundle atlas. For a smooth function `φ : M → ℝ`, multiplication by `φ` is a continuous
linear endomorphism of the Sobolev space `W^{k,p}(V)` of `TauCeti.SobolevSection`, for every order
`k` and every `1 ≤ p ≤ ∞` (`TauCeti.SobolevSection.contMDiffSMulL`).

In chart `i` the function `φ` is read as `φ ∘ (chart i).symm`, which is smooth on the chart
target. This open set contains the compact closure of the chart image `A.image i`, so each
component of a tuple in chart `i` is multiplied by `φ ∘ (chart i).symm` using
`TauCeti.Wkp.contDiffOnSMulL`. Since the bundle charts are fibrewise linear, multiplying the
components of a section `s` gives the components of the section `x ↦ φ x • s x`
(`TauCeti.SobolevSection.chartValueL_contMDiffSMulL_ae_coord`), so the product tuple is again an
element of `W^{k,p}(V)`.

## Main definitions

* `TauCeti.SobolevSection.contMDiffSMulL`: multiplication by a smooth function as an element of
  `W^{k,p}(V) →L[ℝ] W^{k,p}(V)`.

## Main results

* `TauCeti.SobolevSection.contMDiffSMulL_apply`: in chart `i`, each component of `φ • w` is the
  corresponding component of `w` multiplied by `φ ∘ (chart i).symm` using
  `TauCeti.Wkp.contDiffOnSMulL`.
* `TauCeti.SobolevSection.value_contMDiffSMulL_ae`,
  `TauCeti.SobolevSection.chartValueL_contMDiffSMulL_ae`: the components and the chart data of
  `φ • w` are those of `w` multiplied by `φ` read in the chart.
* `TauCeti.SobolevSection.eq_contMDiffSMulL_iff`: `φ • w` is characterized by its components.
* `TauCeti.SobolevSection.chartValueL_contMDiffSMulL_ae_coord`: if `w` consists of the components
  of a section `s`, then `φ • w` consists of the components of `x ↦ φ x • s x`.
* `TauCeti.SobolevSection.contMDiffSMulL_const`, `TauCeti.SobolevSection.contMDiffSMulL_one`,
  `TauCeti.SobolevSection.contMDiffSMulL_add`, `TauCeti.SobolevSection.contMDiffSMulL_mul`:
  multiplication by constants, additivity and multiplicativity in the multiplier.
* `TauCeti.SobolevSection.sum_contMDiffSMulL_eq_self_of_sum_eq_one`: a finite family of smooth
  functions summing to one decomposes every element of `W^{k,p}(V)`.
* `TauCeti.SobolevSection.lowerOrderL_contMDiffSMulL`: multiplication commutes with the inclusion
  `W^{k+1,p}(V) → W^{k,p}(V)`.

## References

* R. S. Palais, *Foundations of Global Non-linear Analysis*, Benjamin (1968), §9.
-/

public section

noncomputable section

open Bundle MeasureTheory Module Set TopologicalSpace
open scoped Manifold ContDiff ENNReal

universe u

namespace TauCeti

open FiniteBundleAtlas

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  (A : FiniteBundleAtlas E M F V) (μ : Measure E) [μ.IsAddHaarMeasure] (p : ℝ≥0∞) [Fact (1 ≤ p)]
  (k : ℕ)

namespace SobolevSection

variable {A μ p k} [IsManifold 𝓘(ℝ, E) ∞ M] {φ ψ : M → ℝ}

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- If the chart-`i` components of `w'` are those of `w` multiplied by `φ` read in chart `i`, the
chart data of `w'` are those of `w` multiplied by `φ` read in chart `i`. -/
private theorem chartValueL_ae_of_value_ae {w w' : A.sectionChartData.SobolevData μ p k}
    {i : Fin A.n}
    (h : ∀ j, (Wkp.value k (w' i j) : E → ℝ) =ᵐ[μ.restrict (A.image i)]
      fun y ↦ φ ((A.chart i).symm y) * Wkp.value k (w i j) y) :
    A.sectionChartData.chartValueL μ p k i w' =ᵐ[μ.restrict (A.image i)]
      fun y ↦ φ ((A.chart i).symm y) • A.sectionChartData.chartValueL μ p k i w y := by
  filter_upwards [A.sectionChartData.chartValueL_apply_ae μ p k i w',
    A.sectionChartData.chartValueL_apply_ae μ p k i w, ae_all_iff.2 h] with y hy' hy hj
  rw [hy', hy, Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [hj j, mul_smul]

variable (A μ p k) in
/-- **Smooth multiplication on `W^{k,p}(V)`.** For a smooth function `φ : M → ℝ`, multiplication
by `φ` is a continuous linear endomorphism of the Sobolev space of sections: in chart `i` each
component is multiplied by `φ ∘ (chart i).symm`. If `w` consists of the components of a section
`s`, then `contMDiffSMulL A μ p k hφ w` consists of the components of `x ↦ φ x • s x`
(`TauCeti.SobolevSection.chartValueL_contMDiffSMulL_ae_coord`). -/
def contMDiffSMulL (hφ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ φ) :
    SobolevSection A μ p k →L[ℝ] SobolevSection A μ p k :=
  ((SectionChartData.SobolevData.mapL fun i ↦ Wkp.contDiffOnSMulL (A.chart i).open_target
      (A.isCompact_closure_image i) (A.closure_image_subset_target i) k
      (A.contDiffOn_comp_chart_symm hφ i)).comp
        (A.sectionChartData.sobolevSections μ p k).subtypeL).codRestrict
    (A.sectionChartData.sobolevSections μ p k) fun w ↦ by
      obtain ⟨s, hs⟩ := (A.sectionChartData.mem_sobolevSections_iff μ p k).1 w.2
      refine (A.sectionChartData.mem_sobolevSections_iff μ p k).2 ⟨fun x ↦ φ x • s x, fun i ↦ ?_⟩
      rw [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
      refine (chartValueL_ae_of_value_ae (φ := φ) (w := (w : A.sectionChartData.SobolevData μ p k))
        fun j ↦ ?_).trans ?_
      · erw [SectionChartData.SobolevData.mapL_apply]
        exact Wkp.value_contDiffOnSMulL_ae _ _ _ k _ _
      · filter_upwards [hs i, ae_restrict_mem (A.image i).isOpen.measurableSet] with y hsy hy
        rw [hsy, A.sectionChartData_coord_of_mem _ hy, A.sectionChartData_coord_of_mem _ hy,
          A.coord_fun_smul i φ s hy]

/-- The components in chart `i` of `φ • w` are those of `w` multiplied by `φ` read in chart `i`,
using `TauCeti.Wkp.contDiffOnSMulL`. -/
@[simp]
theorem contMDiffSMulL_apply (hφ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ φ) (w : SobolevSection A μ p k)
    (i : Fin A.n) (j : Fin (finrank ℝ F)) :
    (contMDiffSMulL A μ p k hφ w : A.sectionChartData.SobolevData μ p k) i j =
      Wkp.contDiffOnSMulL (A.chart i).open_target (A.isCompact_closure_image i)
        (A.closure_image_subset_target i) k (A.contDiffOn_comp_chart_symm hφ i)
        ((w : A.sectionChartData.SobolevData μ p k) i j) := by
  rw [contMDiffSMulL, ContinuousLinearMap.coe_codRestrict_apply, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply]
  erw [SectionChartData.SobolevData.mapL_apply]
  rfl

/-- The components in chart `i` of `φ • w` are those of `w` multiplied by `φ ∘ (chart i).symm`,
almost everywhere on the image of the chart. -/
theorem value_contMDiffSMulL_ae (hφ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ φ) (w : SobolevSection A μ p k)
    (i : Fin A.n) (j : Fin (finrank ℝ F)) :
    (Wkp.value k
      ((contMDiffSMulL A μ p k hφ w : A.sectionChartData.SobolevData μ p k) i j) : E → ℝ)
      =ᵐ[μ.restrict (A.image i)] fun y ↦ φ ((A.chart i).symm y) *
        Wkp.value k ((w : A.sectionChartData.SobolevData μ p k) i j) y := by
  rw [contMDiffSMulL_apply]
  exact Wkp.value_contDiffOnSMulL_ae _ _ _ k _ _

/-- **Characterization.** An element of `W^{k,p}(V)` equals `φ • w` exactly when each of its
components in chart `i` is the corresponding component of `w` multiplied by
`φ ∘ (chart i).symm`, almost everywhere on the image of the chart. -/
theorem eq_contMDiffSMulL_iff (hφ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ φ)
    {w w' : SobolevSection A μ p k} :
    w' = contMDiffSMulL A μ p k hφ w ↔ ∀ i j,
      (Wkp.value k ((w' : A.sectionChartData.SobolevData μ p k) i j) : E → ℝ)
        =ᵐ[μ.restrict (A.image i)] fun y ↦ φ ((A.chart i).symm y) *
          Wkp.value k ((w : A.sectionChartData.SobolevData μ p k) i j) y := by
  refine ⟨fun h ↦ h ▸ value_contMDiffSMulL_ae hφ w, fun h ↦ ?_⟩
  refine Subtype.ext <| funext fun (i : Fin A.n) ↦ funext fun j ↦ ?_
  rw [contMDiffSMulL_apply]
  exact (Wkp.eq_contDiffOnSMulL_iff _ _ _ k _).2 (h i j)

/-- The chart data in chart `i` of `φ • w` are those of `w` multiplied by `φ ∘ (chart i).symm`,
almost everywhere on the image of the chart. -/
theorem chartValueL_contMDiffSMulL_ae (hφ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ φ)
    (w : SobolevSection A μ p k) (i : Fin A.n) :
    A.sectionChartData.chartValueL μ p k i (contMDiffSMulL A μ p k hφ w) =ᵐ[μ.restrict (A.image i)]
      fun y ↦ φ ((A.chart i).symm y) • A.sectionChartData.chartValueL μ p k i w y :=
  chartValueL_ae_of_value_ae (value_contMDiffSMulL_ae hφ w i)

/-- **Sections.** If `w` consists of the chartwise components of a section `s`, then `φ • w`
consists of the chartwise components of the section `x ↦ φ x • s x`. -/
theorem chartValueL_contMDiffSMulL_ae_coord (hφ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ φ)
    {w : SobolevSection A μ p k} {s : ∀ x, V x}
    (hs : ∀ i, A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s)
    (i : Fin A.n) :
    A.sectionChartData.chartValueL μ p k i (contMDiffSMulL A μ p k hφ w) =ᵐ[μ.restrict (A.image i)]
      A.coord i fun x ↦ φ x • s x := by
  filter_upwards [chartValueL_contMDiffSMulL_ae hφ w i, hs i,
    ae_restrict_mem (A.image i).isOpen.measurableSet] with y h hsy hy
  rw [h, hsy, A.coord_fun_smul i φ s hy]

/-- Multiplication by a constant function is scalar multiplication. -/
@[simp]
theorem contMDiffSMulL_const (c : ℝ) :
    contMDiffSMulL A μ p k (contMDiff_const (c := c)) = c • ContinuousLinearMap.id ℝ _ := by
  ext1 w
  refine Subtype.ext <| funext fun (i : Fin A.n) ↦ funext fun j ↦ ?_
  rw [contMDiffSMulL_apply]
  exact Wkp.contDiffOnSMulL_const _ _ _ k c _

/-- Multiplication by the constant function `1` is the identity. -/
theorem contMDiffSMulL_one :
    contMDiffSMulL A μ p k (contMDiff_const (c := (1 : ℝ))) = ContinuousLinearMap.id ℝ _ := by
  rw [contMDiffSMulL_const, one_smul]

/-- Smooth multiplication is additive in the multiplier: `(φ + ψ) • w = φ • w + ψ • w`. -/
theorem contMDiffSMulL_add (hφ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ φ)
    (hψ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ ψ) :
    contMDiffSMulL A μ p k (hφ.add hψ) = contMDiffSMulL A μ p k hφ + contMDiffSMulL A μ p k hψ := by
  ext1 w
  refine Subtype.ext <| funext fun (i : Fin A.n) ↦ funext fun j ↦ ?_
  erw [add_apply, Submodule.coe_add, Pi.add_apply, Pi.add_apply,
    contMDiffSMulL_apply, contMDiffSMulL_apply, contMDiffSMulL_apply]
  exact DFunLike.congr_fun (Wkp.contDiffOnSMulL_add (mu := μ) (p := p) _ _ _ k _ _) _

/-- Smooth multiplication is multiplicative in the multiplier: `(φ ψ) • w = φ • (ψ • w)`. -/
theorem contMDiffSMulL_mul (hφ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ φ)
    (hψ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ ψ) :
    contMDiffSMulL A μ p k (hφ.mul hψ) =
      (contMDiffSMulL A μ p k hφ).comp (contMDiffSMulL A μ p k hψ) := by
  ext1 w
  refine Subtype.ext <| funext fun (i : Fin A.n) ↦ funext fun j ↦ ?_
  rw [ContinuousLinearMap.comp_apply, contMDiffSMulL_apply, contMDiffSMulL_apply,
    contMDiffSMulL_apply]
  exact DFunLike.congr_fun (Wkp.contDiffOnSMulL_mul (mu := μ) (p := p) _ _ _ k _ _) _

/-- Smooth multiplication depends only on the multiplier, not on the proof of its smoothness. -/
theorem contMDiffSMulL_congr (hφ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ φ)
    (hψ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ ψ) (h : φ = ψ) :
    contMDiffSMulL A μ p k hφ = contMDiffSMulL A μ p k hψ := by
  subst h
  rfl

/-- **Partition of unity.** If smooth functions `φ i`, finitely many, sum to one at every point,
then every element of `W^{k,p}(V)` is the sum of its products with the `φ i`. -/
theorem sum_contMDiffSMulL_eq_self_of_sum_eq_one {ι : Type*} [Fintype ι] {φ : ι → M → ℝ}
    (hφ : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (φ i)) (h : ∀ x, ∑ i, φ i x = 1)
    (w : SobolevSection A μ p k) : ∑ i, contMDiffSMulL A μ p k (hφ i) w = w := by
  classical
  -- The sum over a finite set `s` is multiplication by the partial sum of the `φ i`.
  have key : ∀ s : Finset ι, ∃ hs : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ fun x ↦ ∑ i ∈ s, φ i x,
      ∑ i ∈ s, contMDiffSMulL A μ p k (hφ i) w = contMDiffSMulL A μ p k hs w := by
    intro s
    induction s using Finset.cons_induction with
    | empty =>
      refine ⟨by simpa using contMDiff_const (c := (0 : ℝ)), ?_⟩
      rw [Finset.sum_empty, contMDiffSMulL_congr _ (contMDiff_const (c := (0 : ℝ)))
        (funext fun x ↦ Finset.sum_empty), contMDiffSMulL_const]
      simp
    | cons a s ha ih =>
      obtain ⟨hs, hsum⟩ := ih
      have hcons : (fun x ↦ ∑ i ∈ Finset.cons a s ha, φ i x) =
          φ a + fun x ↦ ∑ i ∈ s, φ i x := funext fun x ↦ by rw [Finset.sum_cons, Pi.add_apply]
      refine ⟨hcons ▸ (hφ a).add hs, ?_⟩
      rw [Finset.sum_cons, hsum, contMDiffSMulL_congr _ ((hφ a).add hs) hcons, contMDiffSMulL_add,
        add_apply]
  obtain ⟨hs, hsum⟩ := key Finset.univ
  rw [hsum, contMDiffSMulL_congr _ (contMDiff_const (c := (1 : ℝ))) (funext h),
    contMDiffSMulL_const]
  simp

/-- Smooth multiplication commutes with the inclusion `W^{k+1,p}(V) → W^{k,p}(V)`. -/
theorem lowerOrderL_contMDiffSMulL (hφ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ φ)
    (w : SobolevSection A μ p (k + 1)) :
    A.sectionChartData.lowerOrderL μ p k (contMDiffSMulL A μ p (k + 1) hφ w) =
      contMDiffSMulL A μ p k hφ (A.sectionChartData.lowerOrderL μ p k w) := by
  refine Subtype.ext <| funext fun (i : Fin A.n) ↦ funext fun j ↦ ?_
  erw [SectionChartData.lowerOrderL_apply, contMDiffSMulL_apply, contMDiffSMulL_apply,
    SectionChartData.lowerOrderL_apply]
  exact Wkp.lowerOrder_contDiffOnSMulL _ _ _ k _ _

end SobolevSection

end TauCeti
