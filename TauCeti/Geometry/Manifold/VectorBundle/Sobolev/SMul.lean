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
`k` and every `1 ≤ p ≤ ∞` (`TauCeti.SobolevSection.smulL`).

In chart `i` the function `φ` is read as `φ ∘ (chart i).symm`, which is smooth on the chart
target. This open set contains the compact closure of the chart image `A.image i`, so each
component of a tuple in chart `i` is multiplied by `φ ∘ (chart i).symm` using
`TauCeti.Wkp.contDiffOnSMulL`. Since the bundle charts are fibrewise linear, multiplying the
components of a section `s` gives the components of the section `x ↦ φ x • s x`
(`TauCeti.SobolevSection.chartValueL_smulL_ae_coord`), so the product tuple is again an element of
`W^{k,p}(V)`.

## Main definitions

* `TauCeti.SobolevSection.smulL`: multiplication by a smooth function as an element of
  `W^{k,p}(V) →L[ℝ] W^{k,p}(V)`.

## Main results

* `TauCeti.SobolevSection.value_smulL_ae`, `TauCeti.SobolevSection.chartValueL_smulL_ae`: the
  components and the chart data of `φ • w` are those of `w` multiplied by `φ` read in the chart.
* `TauCeti.SobolevSection.eq_smulL_iff`: `φ • w` is characterized by its components.
* `TauCeti.SobolevSection.chartValueL_smulL_ae_coord`: if `w` consists of the components of a
  section `s`, then `φ • w` consists of the components of `x ↦ φ x • s x`.
* `TauCeti.SobolevSection.smulL_const`, `TauCeti.SobolevSection.smulL_one`,
  `TauCeti.SobolevSection.smulL_add`, `TauCeti.SobolevSection.smulL_mul`: multiplication by
  constants, additivity and multiplicativity in the multiplier.
* `TauCeti.SobolevSection.lowerOrderL_smulL`: multiplication commutes with the inclusion
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

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [VectorBundle ℝ F V] in
/-- The closure of the image of chart `i` lies in the image of the closure of the chart domain. -/
private theorem closure_image_subset (i : Fin A.n) :
    closure (A.image i : Set E) ⊆ A.chart i '' closure (A.dom i) :=
  closure_minimal (A.image_subset_chart_image_closure_dom i)
    (A.isCompact_chart_image_closure_dom i).isClosed

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [VectorBundle ℝ F V] in
private theorem isCompact_closure_image (i : Fin A.n) : IsCompact (closure (A.image i : Set E)) :=
  (A.isCompact_chart_image_closure_dom i).of_isClosed_subset isClosed_closure
    (closure_image_subset A i)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [VectorBundle ℝ F V] in
private theorem closure_image_subset_target (i : Fin A.n) :
    closure (A.image i : Set E) ⊆ (A.chart i).target :=
  (closure_image_subset A i).trans ((A.chart_image_closure_dom_subset i).trans inter_subset_left)

variable {A μ p k} [IsManifold 𝓘(ℝ, E) ∞ M] {φ ψ : M → ℝ}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [VectorBundle ℝ F V] in
/-- A smooth function on `M`, read in chart `i`, is smooth on the chart target. -/
private theorem contDiffOn_comp_chart_symm (hφ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ φ) (i : Fin A.n) :
    ContDiffOn ℝ ∞ (fun y ↦ φ ((A.chart i).symm y)) (A.chart i).target := by
  rw [← contMDiffOn_iff_contDiffOn]
  exact hφ.contMDiffOn.comp (t := univ) contMDiffOn_chart_symm fun _ _ ↦ mem_univ _

variable (μ p k) in
/-- Multiplication by the smooth function `φ`, read in chart `i`, on the scalar Sobolev space of
the image of chart `i`. -/
private def chartSMulL (hφ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ φ) (i : Fin A.n) :
    Wkp μ (A.image i) p k →L[ℝ] Wkp μ (A.image i) p k :=
  Wkp.contDiffOnSMulL (A.chart i).open_target (isCompact_closure_image A i)
    (closure_image_subset_target A i) k (contDiffOn_comp_chart_symm hφ i)

variable (μ p k) in
/-- Componentwise multiplication by `φ` read in the charts, on tuples of chartwise Sobolev
components. -/
private def dataSMulL (hφ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ φ) :
    SobolevData A μ p k →L[ℝ] SobolevData A μ p k :=
  ContinuousLinearMap.pi fun i ↦ ContinuousLinearMap.pi fun j ↦ (chartSMulL μ p k hφ i).comp
    ((ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin (finrank ℝ F) ↦ Wkp μ (A.image i) p k) j).comp
      (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun i : Fin A.n ↦ ∀ _ : Fin (finrank ℝ F), Wkp μ (A.image i) p k) i))

omit [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [VectorBundle ℝ F V]
  [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- If the chart-`i` components of `w'` are those of `w` multiplied by `φ` read in chart `i`, the
chart data of `w'` are those of `w` multiplied by `φ` read in chart `i`. -/
private theorem chartValueL_ae_of_value_ae {w w' : SobolevData A μ p k} {i : Fin A.n}
    (h : ∀ j, (Wkp.value k (w' i j) : E → ℝ) =ᵐ[μ.restrict (A.image i)]
      fun y ↦ φ ((A.chart i).symm y) * Wkp.value k (w i j) y) :
    A.chartValueL μ p k i w' =ᵐ[μ.restrict (A.image i)]
      fun y ↦ φ ((A.chart i).symm y) • A.chartValueL μ p k i w y := by
  filter_upwards [A.chartValueL_apply_ae μ p k i w', A.chartValueL_apply_ae μ p k i w,
    ae_all_iff.2 h] with y hy' hy hj
  rw [hy', hy, Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [hj j, mul_smul]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ F] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The chart coordinates of `x ↦ φ x • s x` are those of `s` multiplied by `φ` read in the
chart, because the bundle chart is fibrewise linear. -/
private theorem coord_smul_fun (i : Fin A.n) (s : ∀ x, V x) {y : E} (hy : y ∈ A.image i) :
    A.coord i (fun x ↦ φ x • s x) y = φ ((A.chart i).symm y) • A.coord i s y := by
  have h := A.dom_subset_baseSet i (A.symm_mem_dom hy)
  simp only [coord_def, ← (A.triv i).continuousLinearMapAt_apply_of_mem (R := ℝ) h, map_smul]

variable (A μ p k) in
/-- **Smooth multiplication on `W^{k,p}(V)`.** For a smooth function `φ : M → ℝ`, multiplication
by `φ` is a continuous linear endomorphism of the Sobolev space of sections: in chart `i` each
component is multiplied by `φ ∘ (chart i).symm`. If `w` consists of the components of a section
`s`, then `smulL A μ p k hφ w` consists of the components of `x ↦ φ x • s x`
(`TauCeti.SobolevSection.chartValueL_smulL_ae_coord`). -/
def smulL (hφ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ φ) :
    SobolevSection A μ p k →L[ℝ] SobolevSection A μ p k :=
  ((dataSMulL μ p k hφ).comp (sobolevSections A μ p k).subtypeL).codRestrict
    (sobolevSections A μ p k) fun w ↦ by
      obtain ⟨s, hs⟩ := (mem_sobolevSections_iff A μ p k).1 w.2
      refine (mem_sobolevSections_iff A μ p k).2
        ⟨fun x ↦ φ x • s x, fun i ↦ ?_⟩
      filter_upwards [chartValueL_ae_of_value_ae (w := (w : SobolevData A μ p k))
          (w' := dataSMulL μ p k hφ w) fun j ↦ Wkp.value_contDiffOnSMulL_ae _ _ _ k _ _, hs i,
        ae_restrict_mem (A.image i).isOpen.measurableSet] with y h hsy hy
      rw [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, h, hsy,
        coord_smul_fun i s hy]

/-- The components in chart `i` of `φ • w` are those of `w` multiplied by `φ ∘ (chart i).symm`,
almost everywhere on the image of the chart. -/
theorem value_smulL_ae (hφ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ φ) (w : SobolevSection A μ p k)
    (i : Fin A.n) (j : Fin (finrank ℝ F)) :
    (Wkp.value k ((smulL A μ p k hφ w : SobolevData A μ p k) i j) : E → ℝ)
      =ᵐ[μ.restrict (A.image i)]
        fun y ↦ φ ((A.chart i).symm y) * Wkp.value k ((w : SobolevData A μ p k) i j) y :=
  Wkp.value_contDiffOnSMulL_ae _ _ _ k _ _

/-- **Characterization.** An element of `W^{k,p}(V)` equals `φ • w` exactly when each of its
components in chart `i` is the corresponding component of `w` multiplied by
`φ ∘ (chart i).symm`, almost everywhere on the image of the chart. -/
theorem eq_smulL_iff (hφ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ φ) {w w' : SobolevSection A μ p k} :
    w' = smulL A μ p k hφ w ↔ ∀ i j,
      (Wkp.value k ((w' : SobolevData A μ p k) i j) : E → ℝ) =ᵐ[μ.restrict (A.image i)]
        fun y ↦ φ ((A.chart i).symm y) * Wkp.value k ((w : SobolevData A μ p k) i j) y := by
  refine ⟨fun h ↦ h ▸ value_smulL_ae hφ w, fun h ↦ ?_⟩
  refine Subtype.ext <| funext fun i ↦ funext fun j ↦ ?_
  exact (Wkp.eq_contDiffOnSMulL_iff _ _ _ k _).2 (h i j)

/-- The chart data in chart `i` of `φ • w` are those of `w` multiplied by `φ ∘ (chart i).symm`,
almost everywhere on the image of the chart. -/
theorem chartValueL_smulL_ae (hφ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ φ) (w : SobolevSection A μ p k)
    (i : Fin A.n) :
    A.chartValueL μ p k i (smulL A μ p k hφ w) =ᵐ[μ.restrict (A.image i)]
      fun y ↦ φ ((A.chart i).symm y) • A.chartValueL μ p k i w y :=
  chartValueL_ae_of_value_ae (value_smulL_ae hφ w i)

/-- **Sections.** If `w` consists of the chartwise components of a section `s`, then `φ • w`
consists of the chartwise components of the section `x ↦ φ x • s x`. -/
theorem chartValueL_smulL_ae_coord (hφ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ φ)
    {w : SobolevSection A μ p k} {s : ∀ x, V x}
    (hs : ∀ i, A.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s) (i : Fin A.n) :
    A.chartValueL μ p k i (smulL A μ p k hφ w) =ᵐ[μ.restrict (A.image i)]
      A.coord i fun x ↦ φ x • s x := by
  filter_upwards [chartValueL_smulL_ae hφ w i, hs i,
    ae_restrict_mem (A.image i).isOpen.measurableSet] with y h hsy hy
  rw [h, hsy, coord_smul_fun i s hy]

/-- Multiplication by a constant function is scalar multiplication. -/
theorem smulL_const (c : ℝ) :
    smulL A μ p k (contMDiff_const (c := c)) = c • ContinuousLinearMap.id ℝ _ := by
  ext1 w
  symm
  refine (eq_smulL_iff _).2 fun i j ↦ ?_
  simp only [smul_apply, ContinuousLinearMap.id_apply, Submodule.coe_smul,
    Pi.smul_apply, Wkp.value_smul]
  exact Lp.coeFn_smul c _

/-- Multiplication by the constant function `1` is the identity. -/
@[simp]
theorem smulL_one :
    smulL A μ p k (contMDiff_const (c := (1 : ℝ))) = ContinuousLinearMap.id ℝ _ := by
  rw [smulL_const, one_smul]

/-- Smooth multiplication is additive in the multiplier: `(φ + ψ) • w = φ • w + ψ • w`. -/
theorem smulL_add (hφ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ φ) (hψ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ ψ) :
    smulL A μ p k (hφ.add hψ) = smulL A μ p k hφ + smulL A μ p k hψ := by
  ext1 w
  symm
  refine (eq_smulL_iff _).2 fun i j ↦ ?_
  simp only [add_apply, Submodule.coe_add, Pi.add_apply, Wkp.value_add]
  filter_upwards [Lp.coeFn_add (Wkp.value k ((smulL A μ p k hφ w : SobolevData A μ p k) i j))
      (Wkp.value k ((smulL A μ p k hψ w : SobolevData A μ p k) i j)),
    value_smulL_ae hφ w i j, value_smulL_ae hψ w i j] with y h₁ h₂ h₃
  rw [h₁, Pi.add_apply, h₂, h₃, add_mul]

/-- Smooth multiplication is multiplicative in the multiplier: `(φ ψ) • w = φ • (ψ • w)`. -/
theorem smulL_mul (hφ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ φ) (hψ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ ψ) :
    smulL A μ p k (hφ.mul hψ) = (smulL A μ p k hφ).comp (smulL A μ p k hψ) := by
  ext1 w
  symm
  refine (eq_smulL_iff _).2 fun i j ↦ ?_
  filter_upwards [value_smulL_ae hφ (smulL A μ p k hψ w) i j, value_smulL_ae hψ w i j]
    with y h₁ h₂
  rw [ContinuousLinearMap.comp_apply, h₁, h₂, Pi.mul_apply, mul_assoc]

/-- Smooth multiplication commutes with the inclusion `W^{k+1,p}(V) → W^{k,p}(V)`. -/
theorem lowerOrderL_smulL (hφ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ φ)
    (w : SobolevSection A μ p (k + 1)) :
    lowerOrderL A μ p k (smulL A μ p (k + 1) hφ w) = smulL A μ p k hφ (lowerOrderL A μ p k w) := by
  refine (eq_smulL_iff _).2 fun i j ↦ ?_
  rw [lowerOrderL_apply, lowerOrderL_apply, ← Wkp.value_succ, ← Wkp.value_succ]
  exact value_smulL_ae hφ w i j

end SobolevSection

end TauCeti
