/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Bordered.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.SMul

/-!
# Multiplication by a smooth function on Sobolev sections over a base with boundary

Let `M` be a smooth manifold modelled on the closed upper half-plane `ClosedUpperHalfPlane`, for
instance a surface with boundary, let `V → M` be a real vector bundle with finite-dimensional
model fibre `F`, and let `A` be a finite bundle atlas. For a smooth function `φ : M → ℝ`,
multiplication by `φ` is a continuous linear endomorphism of the Sobolev space `W^{k,p}(V)` of
`TauCeti.BorderedSobolevSection`, for every order `k` and every `1 ≤ p ≤ ∞`
(`TauCeti.BorderedSobolevSection.contMDiffSMulL`). This is the analogue for bases with boundary of
`TauCeti.SobolevSection.contMDiffSMulL`.

In chart `i` the function `φ` is read in `ℂ` as `z ↦ φ ((chart i).symm z)`, which is smooth up to
the real axis on the target of the extended chart, a relatively open subset of the closed upper
half-plane
(`TauCeti.FiniteBundleAtlas.contDiffOn_comp_chart_symm_closedUpperHalfPlaneModel_symm`). This set
contains the compact closure of the interior `A.halfImage i` of the chart image
(`TauCeti.FiniteBundleAtlas.closure_halfImage_subset_extChartAt_target`) and is a set of unique
differentiability, so each component of a tuple in chart `i` is multiplied by the chart reading of
`φ` using `TauCeti.Wkp.contDiffOnSMulL`, as in the chartwise construction
`TauCeti.SectionChartData.contDiffOnSMulL` shared with bases without boundary. The chart reading
is in general not smooth on any open neighbourhood of that closure in `ℂ`, which is why that
multiplier is stated for sets of unique differentiability rather than open sets. Since the bundle
charts are fibrewise linear, multiplying the components of a section `s` gives the components of
the section `x ↦ φ x • s x`
(`TauCeti.BorderedSobolevSection.chartValueL_contMDiffSMulL_ae_halfCoord`), so the product tuple
is again an element of `W^{k,p}(V)`.

## Main definitions

* `TauCeti.BorderedSobolevSection.contMDiffSMulL`: multiplication by a smooth function as an
  element of `W^{k,p}(V) →L[ℝ] W^{k,p}(V)`.

## Main results

* `TauCeti.BorderedSobolevSection.contMDiffSMulL_apply`: in chart `i`, each component of `φ • w`
  is the corresponding component of `w` multiplied by the chart reading of `φ` using
  `TauCeti.Wkp.contDiffOnSMulL`.
* `TauCeti.BorderedSobolevSection.value_contMDiffSMulL_ae`,
  `TauCeti.BorderedSobolevSection.chartValueL_contMDiffSMulL_ae`: the components and the chart data
  of `φ • w` on `A.halfImage i` are the componentwise products with the chart reading of `φ`.
* `TauCeti.BorderedSobolevSection.eq_contMDiffSMulL_iff`: `φ • w` is characterized by its
  components.
* `TauCeti.BorderedSobolevSection.chartValueL_contMDiffSMulL_ae_halfCoord`: if `w` consists of
  the components of a section `s`, then `φ • w` consists of the components of `x ↦ φ x • s x`.
* `TauCeti.BorderedSobolevSection.contMDiffSMulL_const`,
  `TauCeti.BorderedSobolevSection.contMDiffSMulL_add`,
  `TauCeti.BorderedSobolevSection.contMDiffSMulL_mul`: multiplication by constants, additivity
  and multiplicativity in the multiplier.
* `TauCeti.BorderedSobolevSection.lowerOrderL_contMDiffSMulL`: multiplication commutes with the
  inclusion `W^{k+1,p}(V) → W^{k,p}(V)`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1.
* R. S. Palais, *Foundations of Global Non-linear Analysis*, Benjamin (1968), §9.
-/

public section

noncomputable section

open Bundle MeasureTheory Module Set TopologicalSpace
open scoped Manifold ContDiff ENNReal

namespace TauCeti

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  {A : FiniteBundleAtlas ClosedUpperHalfPlane M F V} {p : ℝ≥0∞} [Fact (1 ≤ p)] {k : ℕ}

namespace BorderedSobolevSection

open FiniteBundleAtlas

variable [IsManifold closedUpperHalfPlaneModel ∞ M] {φ ψ : M → ℝ}

variable (A p k) in
/-- **Smooth multiplication on `W^{k,p}(V)` over a base with boundary.** For a smooth function
`φ : M → ℝ`, multiplication by `φ` is a continuous linear endomorphism of the Sobolev space of
sections: in chart `i` each component is multiplied by the chart reading of `φ`, which is smooth up
to the real axis. If `w` consists of the components of a section `s`, then
`contMDiffSMulL A p k hφ w` consists of the components of `x ↦ φ x • s x`
(`TauCeti.BorderedSobolevSection.chartValueL_contMDiffSMulL_ae_halfCoord`). -/
def contMDiffSMulL (hφ : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ) ∞ φ) :
    BorderedSobolevSection A p k →L[ℝ] BorderedSobolevSection A p k :=
  A.halfSectionChartData.contDiffOnSMulL volume p k
    (fun i ↦ uniqueDiffOn_extChartAt_target (I := closedUpperHalfPlaneModel) (A.center i))
    A.isCompact_closure_halfImage A.closure_halfImage_subset_extChartAt_target
    (A.contDiffOn_comp_chart_symm_closedUpperHalfPlaneModel_symm hφ)
    fun s ↦ ⟨fun x ↦ φ x • s x, fun i z hz ↦ by
      rw [A.halfSectionChartData_coord_of_mem _ hz, A.halfSectionChartData_coord_of_mem _ hz,
        A.halfCoord_fun_smul i φ s (A.mem_halfImage.1 hz).1]⟩

/-- The components in chart `i` of `φ • w` are those of `w` multiplied by the chart reading of `φ`,
using `TauCeti.Wkp.contDiffOnSMulL`. -/
@[simp]
theorem contMDiffSMulL_apply (hφ : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ) ∞ φ)
    (w : BorderedSobolevSection A p k) (i : Fin A.n) (j : Fin (finrank ℝ F)) :
    (contMDiffSMulL A p k hφ w : A.halfSectionChartData.SobolevData volume p k) i j =
      Wkp.contDiffOnSMulL (uniqueDiffOn_extChartAt_target (I := closedUpperHalfPlaneModel)
        (A.center i)) (A.isCompact_closure_halfImage i)
        (A.closure_halfImage_subset_extChartAt_target i) k
        (A.contDiffOn_comp_chart_symm_closedUpperHalfPlaneModel_symm hφ i)
        ((w : A.halfSectionChartData.SobolevData volume p k) i j) :=
  A.halfSectionChartData.contDiffOnSMulL_apply volume p k _ _ _ _ _ w i j

/-- The components in chart `i` of `φ • w` are those of `w` multiplied by the chart reading of `φ`,
almost everywhere on the interior `A.halfImage i` of the chart image. -/
theorem value_contMDiffSMulL_ae (hφ : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ) ∞ φ)
    (w : BorderedSobolevSection A p k) (i : Fin A.n) (j : Fin (finrank ℝ F)) :
    (Wkp.value k
      ((contMDiffSMulL A p k hφ w : A.halfSectionChartData.SobolevData volume p k) i j) : ℂ → ℝ)
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] fun z ↦
        φ ((A.chart i).symm (closedUpperHalfPlaneModel.symm z)) *
          Wkp.value k ((w : A.halfSectionChartData.SobolevData volume p k) i j) z :=
  A.halfSectionChartData.value_contDiffOnSMulL_ae volume p k _ _ _ _ _ w i j

/-- **Characterization.** An element of `W^{k,p}(V)` equals `φ • w` exactly when each of its
components in chart `i` is the corresponding component of `w` multiplied by the chart reading of
`φ`, almost everywhere on the interior `A.halfImage i` of the chart image. -/
theorem eq_contMDiffSMulL_iff (hφ : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ) ∞ φ)
    {w w' : BorderedSobolevSection A p k} :
    w' = contMDiffSMulL A p k hφ w ↔ ∀ i j,
      (Wkp.value k ((w' : A.halfSectionChartData.SobolevData volume p k) i j) : ℂ → ℝ)
        =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] fun z ↦
          φ ((A.chart i).symm (closedUpperHalfPlaneModel.symm z)) *
            Wkp.value k ((w : A.halfSectionChartData.SobolevData volume p k) i j) z :=
  A.halfSectionChartData.eq_contDiffOnSMulL_iff volume p k _ _ _ _ _

/-- The chart data in chart `i` of `φ • w` are those of `w` multiplied by the chart reading of `φ`,
almost everywhere on the interior `A.halfImage i` of the chart image. -/
theorem chartValueL_contMDiffSMulL_ae (hφ : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ) ∞ φ)
    (w : BorderedSobolevSection A p k) (i : Fin A.n) :
    A.halfSectionChartData.chartValueL volume p k i (contMDiffSMulL A p k hφ w)
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] fun z ↦
        φ ((A.chart i).symm (closedUpperHalfPlaneModel.symm z)) •
          A.halfSectionChartData.chartValueL volume p k i w z :=
  A.halfSectionChartData.chartValueL_contDiffOnSMulL_ae volume p k _ _ _ _ _ w i

/-- **Sections.** If `w` consists of the chartwise components of a section `s`, then `φ • w`
consists of the chartwise components of the section `x ↦ φ x • s x`. -/
theorem chartValueL_contMDiffSMulL_ae_halfCoord
    (hφ : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ) ∞ φ) {w : BorderedSobolevSection A p k}
    {s : ∀ x, V x}
    (hs : ∀ i, A.halfSectionChartData.chartValueL volume p k i w
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] A.halfCoord i s)
    (i : Fin A.n) :
    A.halfSectionChartData.chartValueL volume p k i (contMDiffSMulL A p k hφ w)
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] A.halfCoord i fun x ↦ φ x • s x := by
  filter_upwards [chartValueL_contMDiffSMulL_ae hφ w i, hs i,
    ae_restrict_mem (A.halfImage i).isOpen.measurableSet] with z h hsz hz
  rw [h, hsz, A.halfCoord_fun_smul i φ s (A.mem_halfImage.1 hz).1]

/-- Multiplication by a constant function is scalar multiplication. -/
@[simp]
theorem contMDiffSMulL_const (c : ℝ) :
    contMDiffSMulL A p k (contMDiff_const (c := c)) = c • ContinuousLinearMap.id ℝ _ :=
  A.halfSectionChartData.contDiffOnSMulL_const volume p k _ _ _ c

/-- Smooth multiplication is additive in the multiplier: `(φ + ψ) • w = φ • w + ψ • w`. -/
theorem contMDiffSMulL_add (hφ : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ) ∞ φ)
    (hψ : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ) ∞ ψ) :
    contMDiffSMulL A p k (hφ.add hψ) = contMDiffSMulL A p k hφ + contMDiffSMulL A p k hψ :=
  A.halfSectionChartData.contDiffOnSMulL_add volume p k _ _ _ _ _ _ _

/-- Smooth multiplication is multiplicative in the multiplier: `(φ ψ) • w = φ • (ψ • w)`. -/
theorem contMDiffSMulL_mul (hφ : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ) ∞ φ)
    (hψ : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ) ∞ ψ) :
    contMDiffSMulL A p k (hφ.mul hψ) =
      (contMDiffSMulL A p k hφ).comp (contMDiffSMulL A p k hψ) :=
  A.halfSectionChartData.contDiffOnSMulL_mul volume p k _ _ _ _ _ _ _

/-- Smooth multiplication commutes with the inclusion `W^{k+1,p}(V) → W^{k,p}(V)`. -/
theorem lowerOrderL_contMDiffSMulL (hφ : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ) ∞ φ)
    (w : BorderedSobolevSection A p (k + 1)) :
    A.halfSectionChartData.lowerOrderL volume p k (contMDiffSMulL A p (k + 1) hφ w) =
      contMDiffSMulL A p k hφ (A.halfSectionChartData.lowerOrderL volume p k w) :=
  A.halfSectionChartData.lowerOrderL_contDiffOnSMulL volume p k _ _ _ _ _ w

end BorderedSobolevSection

end TauCeti
