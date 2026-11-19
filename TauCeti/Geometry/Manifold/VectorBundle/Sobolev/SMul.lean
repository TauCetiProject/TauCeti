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

The construction is carried out for general chart data `C : TauCeti.SectionChartData E F S`
(`TauCeti.SectionChartData.contDiffOnSMulL`): if the closure of the image of chart `i` is compact
and contained in a set `U i` of unique differentiability on which `ψ i` is smooth, each component
of a tuple in chart `i` is multiplied by `ψ i` using `TauCeti.Wkp.contDiffOnSMulL`, and the product
tuple consists of the components of a section as soon as multiplying the readings of sections by
`ψ` gives the readings of a section. The same construction serves bases with boundary.

For a finite bundle atlas, `φ` is read in chart `i` as `φ ∘ (chart i).symm`, which is smooth on the
chart target. This open set contains the compact closure of the chart image `A.image i`. Since the
bundle charts are fibrewise linear, multiplying the components of a section `s` gives the
components of the section `x ↦ φ x • s x`
(`TauCeti.SobolevSection.chartValueL_contMDiffSMulL_ae_coord`).

## Main definitions

* `TauCeti.SectionChartData.contDiffOnSMulL`: chartwise multiplication by smooth functions on the
  Sobolev sections of chart data.
* `TauCeti.SobolevSection.contMDiffSMulL`: multiplication by a smooth function as an element of
  `W^{k,p}(V) →L[ℝ] W^{k,p}(V)`.

## Main results

* `TauCeti.SectionChartData.contDiffOnSMulL_apply`,
  `TauCeti.SectionChartData.eq_contDiffOnSMulL_iff`,
  `TauCeti.SectionChartData.chartValueL_contDiffOnSMulL_ae`: the components and chart data of a
  chartwise product, and its characterization by its components.
* `TauCeti.SectionChartData.contDiffOnSMulL_const`, `TauCeti.SectionChartData.contDiffOnSMulL_add`,
  `TauCeti.SectionChartData.contDiffOnSMulL_mul`,
  `TauCeti.SectionChartData.lowerOrderL_contDiffOnSMulL`: constants, additivity and
  multiplicativity in the multiplier, and compatibility with lowering the order.
* `TauCeti.SobolevSection.contMDiffSMulL_apply`: in chart `i`, each component of `φ • w` is the
  corresponding component of `w` multiplied by `φ ∘ (chart i).symm` using
  `TauCeti.Wkp.contDiffOnSMulL`.
* `TauCeti.SobolevSection.value_contMDiffSMulL_ae`,
  `TauCeti.SobolevSection.chartValueL_contMDiffSMulL_ae`: the components and the chart data of
  `φ • w` are those of `w` multiplied by `φ` read in the chart.
* `TauCeti.SobolevSection.eq_contMDiffSMulL_iff`: `φ • w` is characterized by its components.
* `TauCeti.SobolevSection.chartValueL_contMDiffSMulL_ae_coord`: if `w` consists of the components
  of a section `s`, then `φ • w` consists of the components of `x ↦ φ x • s x`.
* `TauCeti.SobolevSection.contMDiffSMulL_const`, `TauCeti.SobolevSection.contMDiffSMulL_add`,
  `TauCeti.SobolevSection.contMDiffSMulL_mul`: multiplication by constants, additivity and
  multiplicativity in the multiplier.
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

namespace SectionChartData

section SMul

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {S : Type*} [AddCommGroup S] [Module ℝ S] (C : SectionChartData E F S)
  (μ : Measure E) [μ.IsAddHaarMeasure] (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ) {U : Fin C.n → Set E}
  (hU : ∀ i, UniqueDiffOn ℝ (U i)) (hK : ∀ i, IsCompact (closure (C.image i : Set E)))
  (hKU : ∀ i, closure (C.image i : Set E) ⊆ U i) {ψ φ : Fin C.n → E → ℝ}
  (hψ : ∀ i, ContDiffOn ℝ ∞ (ψ i) (U i))
  (hsec : ∀ s, ∃ t, ∀ i, ∀ y ∈ C.image i, C.coord i t y = ψ i y • C.coord i s y)

include hsec in
/-- **Chartwise smooth multiplication on the Sobolev sections.** Let the closure of the image of
chart `i` be compact and contained in a set `U i` of unique differentiability, on which `ψ i` is
smooth, and suppose that multiplying the readings of every section by `ψ` gives the readings of a
section. Then multiplying each chart-`i` component by `ψ i` using `TauCeti.Wkp.contDiffOnSMulL` is
a continuous linear endomorphism of the Sobolev sections. -/
def contDiffOnSMulL : C.sobolevSections μ p k →L[ℝ] C.sobolevSections μ p k :=
  ((SobolevData.mapL fun i ↦ Wkp.contDiffOnSMulL (hU i) (hK i) (hKU i) k (hψ i)).comp
    (C.sobolevSections μ p k).subtypeL).codRestrict (C.sobolevSections μ p k) fun w ↦ by
      obtain ⟨s, hs⟩ := (C.mem_sobolevSections_iff μ p k).1 w.2
      obtain ⟨t, ht⟩ := hsec s
      refine (C.mem_sobolevSections_iff μ p k).2 ⟨t, fun i ↦ ?_⟩
      refine (C.chartValueL_ae_eq_smul μ p k (ψ := ψ i) (w := (w : C.SobolevData μ p k))
        fun j ↦ ?_).trans ?_
      · rw [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, SobolevData.mapL_apply]
        exact Wkp.value_contDiffOnSMulL_ae _ _ _ k _ _
      · filter_upwards [hs i, ae_restrict_mem (C.image i).isOpen.measurableSet] with y hsy hy
        rw [hsy, ht i y hy]

/-- Each chart-`i` component of `ψ • w` is the corresponding component of `w` multiplied by `ψ i`
using `TauCeti.Wkp.contDiffOnSMulL`. -/
@[simp]
theorem contDiffOnSMulL_apply (w : C.sobolevSections μ p k) (i : Fin C.n)
    (j : Fin (finrank ℝ F)) :
    (C.contDiffOnSMulL μ p k hU hK hKU hψ hsec w : C.SobolevData μ p k) i j =
      Wkp.contDiffOnSMulL (hU i) (hK i) (hKU i) k (hψ i) ((w : C.SobolevData μ p k) i j) := by
  rw [contDiffOnSMulL, ContinuousLinearMap.coe_codRestrict_apply, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply, SobolevData.mapL_apply]

/-- The chart-`i` components of `ψ • w` are those of `w` multiplied by `ψ i`, almost everywhere
on the image of the chart. -/
theorem value_contDiffOnSMulL_ae (w : C.sobolevSections μ p k) (i : Fin C.n)
    (j : Fin (finrank ℝ F)) :
    (Wkp.value k ((C.contDiffOnSMulL μ p k hU hK hKU hψ hsec w : C.SobolevData μ p k) i j) :
      E → ℝ) =ᵐ[μ.restrict (C.image i)]
        fun y ↦ ψ i y * Wkp.value k ((w : C.SobolevData μ p k) i j) y := by
  rw [contDiffOnSMulL_apply]
  exact Wkp.value_contDiffOnSMulL_ae _ _ _ k _ _

/-- **Characterization.** An element of the Sobolev sections equals `ψ • w` exactly when each of
its chart-`i` components is the corresponding component of `w` multiplied by `ψ i`, almost
everywhere on the image of the chart. -/
theorem eq_contDiffOnSMulL_iff {w w' : C.sobolevSections μ p k} :
    w' = C.contDiffOnSMulL μ p k hU hK hKU hψ hsec w ↔ ∀ i j,
      (Wkp.value k ((w' : C.SobolevData μ p k) i j) : E → ℝ) =ᵐ[μ.restrict (C.image i)]
        fun y ↦ ψ i y * Wkp.value k ((w : C.SobolevData μ p k) i j) y :=
  ⟨fun h ↦ h ▸ C.value_contDiffOnSMulL_ae μ p k hU hK hKU hψ hsec w, fun h ↦
    Subtype.ext <| funext fun i ↦ funext fun j ↦ by
      rw [contDiffOnSMulL_apply]
      exact (Wkp.eq_contDiffOnSMulL_iff _ _ _ k _).2 (h i j)⟩

/-- The chart data in chart `i` of `ψ • w` are those of `w` multiplied by `ψ i`, almost everywhere
on the image of the chart. -/
theorem chartValueL_contDiffOnSMulL_ae (w : C.sobolevSections μ p k) (i : Fin C.n) :
    C.chartValueL μ p k i (C.contDiffOnSMulL μ p k hU hK hKU hψ hsec w)
      =ᵐ[μ.restrict (C.image i)] fun y ↦ ψ i y • C.chartValueL μ p k i w y :=
  C.chartValueL_ae_eq_smul μ p k (C.value_contDiffOnSMulL_ae μ p k hU hK hKU hψ hsec w i)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ F] in
/-- Multiplying the readings of a section by a constant gives the readings of a section. -/
theorem exists_coord_eq_const_smul (c : ℝ) (s : S) :
    ∃ t, ∀ i, ∀ y ∈ C.image i, C.coord i t y = c • C.coord i s y :=
  ⟨c • s, fun i y hy ↦ C.coord_smul i c s y hy⟩

include hsec in
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ F] in
/-- If multiplying the readings of sections by `ψ` and by `φ` gives the readings of sections,
then so does multiplying them by `ψ + φ`. -/
theorem exists_coord_eq_add_smul
    (hsecφ : ∀ s, ∃ t, ∀ i, ∀ y ∈ C.image i, C.coord i t y = φ i y • C.coord i s y) (s : S) :
    ∃ t, ∀ i, ∀ y ∈ C.image i, C.coord i t y = (ψ i y + φ i y) • C.coord i s y := by
  obtain ⟨t₁, ht₁⟩ := hsec s
  obtain ⟨t₂, ht₂⟩ := hsecφ s
  exact ⟨t₁ + t₂, fun i y hy ↦ by rw [C.coord_add i t₁ t₂ y hy, ht₁ i y hy, ht₂ i y hy, add_smul]⟩

include hsec in
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ F] in
/-- If multiplying the readings of sections by `ψ` and by `φ` gives the readings of sections,
then so does multiplying them by `ψ * φ`. -/
theorem exists_coord_eq_mul_smul
    (hsecφ : ∀ s, ∃ t, ∀ i, ∀ y ∈ C.image i, C.coord i t y = φ i y • C.coord i s y) (s : S) :
    ∃ t, ∀ i, ∀ y ∈ C.image i, C.coord i t y = (ψ i y * φ i y) • C.coord i s y := by
  obtain ⟨t₁, ht₁⟩ := hsecφ s
  obtain ⟨t₂, ht₂⟩ := hsec t₁
  exact ⟨t₂, fun i y hy ↦ by rw [ht₂ i y hy, ht₁ i y hy, mul_smul]⟩

/-- Multiplication by a constant is scalar multiplication. -/
@[simp]
theorem contDiffOnSMulL_const (c : ℝ) :
    C.contDiffOnSMulL μ p k hU hK hKU (ψ := fun _ _ ↦ c) (fun _ ↦ contDiffOn_const)
      (C.exists_coord_eq_const_smul c) = c • ContinuousLinearMap.id ℝ _ := by
  ext1 w
  refine Subtype.ext <| funext fun i ↦ funext fun j ↦ ?_
  rw [contDiffOnSMulL_apply, smul_apply, ContinuousLinearMap.id_apply,
    Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply]
  exact Wkp.contDiffOnSMulL_const _ _ _ k c _

/-- Chartwise smooth multiplication is additive in the multiplier: `(ψ + φ) • w = ψ • w + φ • w`. -/
theorem contDiffOnSMulL_add (hφ : ∀ i, ContDiffOn ℝ ∞ (φ i) (U i))
    (hsecφ : ∀ s, ∃ t, ∀ i, ∀ y ∈ C.image i, C.coord i t y = φ i y • C.coord i s y) :
    C.contDiffOnSMulL μ p k hU hK hKU (fun i ↦ (hψ i).add (hφ i))
      (C.exists_coord_eq_add_smul hsec hsecφ) =
      C.contDiffOnSMulL μ p k hU hK hKU hψ hsec + C.contDiffOnSMulL μ p k hU hK hKU hφ hsecφ := by
  ext1 w
  refine Subtype.ext <| funext fun i ↦ funext fun j ↦ ?_
  rw [contDiffOnSMulL_apply, add_apply, Submodule.coe_add, Pi.add_apply,
    Pi.add_apply, contDiffOnSMulL_apply, contDiffOnSMulL_apply]
  exact DFunLike.congr_fun (Wkp.contDiffOnSMulL_add (mu := μ) (p := p) _ _ _ k _ _) _

/-- Chartwise smooth multiplication is multiplicative in the multiplier:
`(ψ φ) • w = ψ • (φ • w)`. -/
theorem contDiffOnSMulL_mul (hφ : ∀ i, ContDiffOn ℝ ∞ (φ i) (U i))
    (hsecφ : ∀ s, ∃ t, ∀ i, ∀ y ∈ C.image i, C.coord i t y = φ i y • C.coord i s y) :
    C.contDiffOnSMulL μ p k hU hK hKU (fun i ↦ (hψ i).mul (hφ i))
      (C.exists_coord_eq_mul_smul hsec hsecφ) =
      (C.contDiffOnSMulL μ p k hU hK hKU hψ hsec).comp
        (C.contDiffOnSMulL μ p k hU hK hKU hφ hsecφ) := by
  ext1 w
  refine Subtype.ext <| funext fun i ↦ funext fun j ↦ ?_
  rw [contDiffOnSMulL_apply, ContinuousLinearMap.comp_apply, contDiffOnSMulL_apply,
    contDiffOnSMulL_apply]
  exact DFunLike.congr_fun (Wkp.contDiffOnSMulL_mul (mu := μ) (p := p) _ _ _ k _ _) _

/-- Chartwise smooth multiplication commutes with the inclusion of the Sobolev sections of order
`k + 1` into those of order `k`. -/
theorem lowerOrderL_contDiffOnSMulL (w : C.sobolevSections μ p (k + 1)) :
    C.lowerOrderL μ p k (C.contDiffOnSMulL μ p (k + 1) hU hK hKU hψ hsec w) =
      C.contDiffOnSMulL μ p k hU hK hKU hψ hsec (C.lowerOrderL μ p k w) := by
  refine Subtype.ext <| funext fun i ↦ funext fun j ↦ ?_
  rw [lowerOrderL_apply, contDiffOnSMulL_apply, contDiffOnSMulL_apply, lowerOrderL_apply]
  exact Wkp.lowerOrder_contDiffOnSMulL _ _ _ k _ _

end SMul

end SectionChartData

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

variable (A μ p k) in
/-- **Smooth multiplication on `W^{k,p}(V)`.** For a smooth function `φ : M → ℝ`, multiplication
by `φ` is a continuous linear endomorphism of the Sobolev space of sections: in chart `i` each
component is multiplied by `φ ∘ (chart i).symm`. If `w` consists of the components of a section
`s`, then `contMDiffSMulL A μ p k hφ w` consists of the components of `x ↦ φ x • s x`
(`TauCeti.SobolevSection.chartValueL_contMDiffSMulL_ae_coord`). -/
def contMDiffSMulL (hφ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ φ) :
    SobolevSection A μ p k →L[ℝ] SobolevSection A μ p k :=
  A.sectionChartData.contDiffOnSMulL μ p k (fun i ↦ (A.chart i).open_target.uniqueDiffOn)
    A.isCompact_closure_image A.closure_image_subset_target (A.contDiffOn_comp_chart_symm hφ)
    fun s ↦ ⟨fun x ↦ φ x • s x, fun i y hy ↦ by
      rw [A.sectionChartData_coord_of_mem _ hy, A.sectionChartData_coord_of_mem _ hy,
        A.coord_fun_smul i φ s hy]⟩

/-- The components in chart `i` of `φ • w` are those of `w` multiplied by `φ` read in chart `i`,
using `TauCeti.Wkp.contDiffOnSMulL`. -/
@[simp]
theorem contMDiffSMulL_apply (hφ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ φ) (w : SobolevSection A μ p k)
    (i : Fin A.n) (j : Fin (finrank ℝ F)) :
    (contMDiffSMulL A μ p k hφ w : A.sectionChartData.SobolevData μ p k) i j =
      Wkp.contDiffOnSMulL (A.chart i).open_target.uniqueDiffOn (A.isCompact_closure_image i)
        (A.closure_image_subset_target i) k (A.contDiffOn_comp_chart_symm hφ i)
        ((w : A.sectionChartData.SobolevData μ p k) i j) :=
  A.sectionChartData.contDiffOnSMulL_apply μ p k _ _ _ _ _ w i j

/-- The components in chart `i` of `φ • w` are those of `w` multiplied by `φ ∘ (chart i).symm`,
almost everywhere on the image of the chart. -/
theorem value_contMDiffSMulL_ae (hφ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ φ) (w : SobolevSection A μ p k)
    (i : Fin A.n) (j : Fin (finrank ℝ F)) :
    (Wkp.value k
      ((contMDiffSMulL A μ p k hφ w : A.sectionChartData.SobolevData μ p k) i j) : E → ℝ)
      =ᵐ[μ.restrict (A.image i)] fun y ↦ φ ((A.chart i).symm y) *
        Wkp.value k ((w : A.sectionChartData.SobolevData μ p k) i j) y :=
  A.sectionChartData.value_contDiffOnSMulL_ae μ p k _ _ _ _ _ w i j

/-- **Characterization.** An element of `W^{k,p}(V)` equals `φ • w` exactly when each of its
components in chart `i` is the corresponding component of `w` multiplied by
`φ ∘ (chart i).symm`, almost everywhere on the image of the chart. -/
theorem eq_contMDiffSMulL_iff (hφ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ φ)
    {w w' : SobolevSection A μ p k} :
    w' = contMDiffSMulL A μ p k hφ w ↔ ∀ i j,
      (Wkp.value k ((w' : A.sectionChartData.SobolevData μ p k) i j) : E → ℝ)
        =ᵐ[μ.restrict (A.image i)] fun y ↦ φ ((A.chart i).symm y) *
          Wkp.value k ((w : A.sectionChartData.SobolevData μ p k) i j) y :=
  A.sectionChartData.eq_contDiffOnSMulL_iff μ p k _ _ _ _ _

/-- The chart data in chart `i` of `φ • w` are those of `w` multiplied by `φ ∘ (chart i).symm`,
almost everywhere on the image of the chart. -/
theorem chartValueL_contMDiffSMulL_ae (hφ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ φ)
    (w : SobolevSection A μ p k) (i : Fin A.n) :
    A.sectionChartData.chartValueL μ p k i (contMDiffSMulL A μ p k hφ w) =ᵐ[μ.restrict (A.image i)]
      fun y ↦ φ ((A.chart i).symm y) • A.sectionChartData.chartValueL μ p k i w y :=
  A.sectionChartData.chartValueL_contDiffOnSMulL_ae μ p k _ _ _ _ _ w i

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
    contMDiffSMulL A μ p k (contMDiff_const (c := c)) = c • ContinuousLinearMap.id ℝ _ :=
  A.sectionChartData.contDiffOnSMulL_const μ p k _ _ _ c

/-- Smooth multiplication is additive in the multiplier: `(φ + ψ) • w = φ • w + ψ • w`. -/
theorem contMDiffSMulL_add (hφ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ φ)
    (hψ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ ψ) :
    contMDiffSMulL A μ p k (hφ.add hψ) = contMDiffSMulL A μ p k hφ + contMDiffSMulL A μ p k hψ :=
  A.sectionChartData.contDiffOnSMulL_add μ p k _ _ _ _ _ _ _

/-- Smooth multiplication is multiplicative in the multiplier: `(φ ψ) • w = φ • (ψ • w)`. -/
theorem contMDiffSMulL_mul (hφ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ φ)
    (hψ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ ψ) :
    contMDiffSMulL A μ p k (hφ.mul hψ) =
      (contMDiffSMulL A μ p k hφ).comp (contMDiffSMulL A μ p k hψ) :=
  A.sectionChartData.contDiffOnSMulL_mul μ p k _ _ _ _ _ _ _

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
      contMDiffSMulL A μ p k hφ (A.sectionChartData.lowerOrderL μ p k w) :=
  A.sectionChartData.lowerOrderL_contDiffOnSMulL μ p k _ _ _ _ _ w

end SobolevSection

end TauCeti
