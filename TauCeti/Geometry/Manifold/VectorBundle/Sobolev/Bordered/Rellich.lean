/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Bordered.Atlas.Equiv
import TauCeti.Analysis.Sobolev.Local.Compactness
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Bordered.Atlas.Transfer
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Rellich

/-!
# Rellich compactness for Sobolev sections over a surface with boundary

Let `M` be a Hausdorff `Cⁿ` manifold modelled on the closed upper half-plane, for instance a
compact surface with boundary, let `V → M` be a `Cⁿ` real vector bundle with finite-dimensional
model fibre `F`, and let `A` be a finite bundle atlas. For `1 ≤ p ≤ ∞` and every order `k` with
`k + 1 ≤ n`, the inclusion `W^{k+1,p}(V) → W^{k,p}(V)` of the bordered Sobolev spaces
`TauCeti.BorderedSobolevSection` is a compact operator
(`TauCeti.BorderedSobolevSection.isCompactOperator_lowerOrderL`).

## The argument

Compactness into the Sobolev sections is componentwise
(`TauCeti.SectionChartData.isCompactOperator_of_forall_apply`). The chart image `A.halfImage j`
need not have its closure inside a set on which the chart data are controlled, so the data are
read in a larger atlas instead. Enlarge the chart domains: an atlas `B` with the same centres as
`A` and domains `U j` containing `closure (A.dom j)` (`TauCeti.FiniteBundleAtlas.enlarge`, with
domains from `TauCeti.FiniteBundleAtlas.exists_open_between_closure_dom_and_isCompact_closure`).
Sections transfer from `A` to `B`
(`TauCeti.BorderedSobolevSection.exists_chartValueL_ae_eq_halfCoord`), so the change of atlas
`TauCeti.BorderedSobolevSection.changeAtlas` is a continuous linear map, and the chart-`j`
components of an element for `A` are the restrictions to `A.halfImage j` of the
chart-`j` components of its image for `B`, since the two atlases read sections in the same charts.
The closure of `A.halfImage j` is compact and lies in the image of chart `j` of `B`, up to the real
axis, so Rellich compactness up to the real axis
(`TauCeti.Wkp.isCompactOperator_restrictL_lowerOrderL_upperHalf`) applies on each component.

Composing, the inclusion `W^{k+d+1,p}(V) → W^{k,p}(V)` is compact for `k + d + 1 ≤ n`
(`TauCeti.BorderedSobolevSection.isCompactOperator_lowerOrdersL`), and with the injectivity of the
chart data this gives **Ehrling's inequality**
(`TauCeti.BorderedSobolevSection.exists_norm_lowerOrdersL_le`), as for bases without boundary
(`TauCeti.SectionChartData.exists_norm_lowerOrdersL_le`).

## Main results

* `TauCeti.BorderedSobolevSection.isCompactOperator_lowerOrderL`: **Rellich's theorem** for
  Sobolev sections over a base with boundary.
* `TauCeti.BorderedSobolevSection.isCompactOperator_lowerOrdersL`: `W^{k+d+1,p}(V) → W^{k,p}(V)`
  is compact.
* `TauCeti.BorderedSobolevSection.exists_norm_lowerOrdersL_le`: **Ehrling's inequality**
  `‖w‖_{W^{k,p}} ≤ ε ‖w‖_{W^{k+d+1,p}} + C_ε ‖w‖_{Lᵖ}`.

## References

* R. S. Palais, *Foundations of Global Non-linear Analysis*, Benjamin (1968), §9.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1.
-/

public section

noncomputable section

open Bundle Filter MeasureTheory Module Set TopologicalSpace
open scoped Manifold Topology ENNReal

namespace TauCeti


namespace BorderedSobolevSection

open FiniteBundleAtlas

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M] [T2Space M]
  {n : ℕ} [IsManifold closedUpperHalfPlaneModel n M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle n F V closedUpperHalfPlaneModel]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {k : ℕ}

/-- **Rellich's theorem over a base with boundary.** For a `Cⁿ` vector bundle over a Hausdorff
`Cⁿ` manifold modelled on the closed upper half-plane, `1 ≤ p ≤ ∞` and `k + 1 ≤ n`, the inclusion
`W^{k+1,p}(V) → W^{k,p}(V)` of Sobolev sections is a compact operator. -/
theorem isCompactOperator_lowerOrderL (hkn : k + 1 ≤ n)
    (A : FiniteBundleAtlas ClosedUpperHalfPlane M F V) :
    IsCompactOperator (A.halfSectionChartData.lowerOrderL volume p k) := by
  have : IsManifold closedUpperHalfPlaneModel 1 M :=
    IsManifold.of_le (n := n) (by exact_mod_cast (Nat.le_add_left 1 k).trans hkn)
  obtain ⟨U, hU, hAU, hUc, hUs⟩ := A.exists_open_between_closure_dom_and_isCompact_closure
  set B := A.enlarge U hU (fun j ↦ subset_closure.trans (hAU j)) hUc hUs
  have htr : TransfersTo A B p (k + 1) := transfersTo_iff.2 fun w _ hs ↦
    exists_chartValueL_ae_eq_halfCoord (le_add_self.trans hkn) hkn w hs B
  refine SectionChartData.isCompactOperator_of_forall_apply A.aeTransition_halfSectionChartData
    fun j m ↦ ?_
  -- Chart `j` of `A` and of `B`, indexed in `Fin A.n` and `Fin B.n`.
  let jA : Fin A.n := Fin.cast rfl j
  let jB : Fin B.n := Fin.cast rfl j
  -- The open set `W` with upper half the interior of the image of chart `j` of `B`.
  set W : Opens ℂ := B.halfOpen jB
  have h1 : W.upperHalf ≤ B.halfImage jB := fun z hz ↦
    B.mem_halfImage.2 ⟨B.mem_halfOpen.1 (Opens.mem_upperHalf.1 hz).1, (Opens.mem_upperHalf.1 hz).2⟩
  have hA : A.halfImage jA ≤ B.halfImage jB := A.halfImage_le_halfImage_enlarge jA
  -- The closure of `A.halfImage jA` is compact and lies in `W`.
  have hVc := A.isCompact_closure_halfImage jA
  have hVW : closure (A.halfImage jA : Set ℂ) ⊆ W := fun z hz ↦ by
    obtain ⟨x, hx, hxz⟩ := A.exists_mem_closure_dom_of_mem_closure_halfImage hz
    exact B.mem_halfOpen.2 (hxz ▸ (B.mem_image (i := jB)).2 ⟨x, hAU jA hx, rfl⟩)
  have h3 : A.halfImage jA ≤ (A.halfImage jA).upperHalf :=
    fun z hz ↦ Opens.mem_upperHalf.2 ⟨hz, (A.mem_halfImage.1 hz).2⟩
  have hle := Opens.upperHalf_mono (SetLike.coe_subset_coe.1 (subset_closure.trans hVW))
  -- The compact operator: change atlas, take the component, restrict and forget a derivative.
  let y : BorderedSobolevSection A p (k + 1) →L[ℝ] Wkp volume (B.halfImage jB) p (k + 1) :=
    (ContinuousLinearMap.proj m).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun i : Fin B.halfSectionChartData.n ↦
        Fin (finrank ℝ F) → Wkp volume (B.halfSectionChartData.image i) p (k + 1)) jB).comp
        ((B.halfSectionChartData.sobolevSections volume p (k + 1)).subtypeL.comp
          (changeAtlas htr)))
  let T : BorderedSobolevSection A p (k + 1) →L[ℝ] Wkp volume (A.halfImage jA) p k :=
    (Wkp.restrictL h3 k).comp (((Wkp.restrictL hle k).comp (Wkp.lowerOrderL k)).comp
      ((Wkp.restrictL h1 (k + 1)).comp y))
  have hT : IsCompactOperator T :=
    ((Wkp.isCompactOperator_restrictL_lowerOrderL_upperHalf (p := p) hVc hVW k).comp_clm
      _).clm_comp _
  -- The component map has codomain `Wkp volume (A.halfSectionChartData.image j) p k`, which is
  -- `Wkp volume (A.halfImage j) p k` since `halfSectionChartData` has image `A.halfImage`.
  have hfun : (fun x ↦ ((A.halfSectionChartData.lowerOrderL volume p k x :
      A.halfSectionChartData.SobolevData volume p k) j m)) = ⇑T := funext fun x ↦ by
    have hx : ((x : A.halfSectionChartData.SobolevData volume p (k + 1)) j m) =
        Wkp.restrictL hA (k + 1) (y x) :=
      component_eq_restrictL_changeAtlas htr (fun s ↦ A.halfCoord_enlarge jA s) hA x m
    rw [SectionChartData.lowerOrderL_apply, hx]
    simp only [T, ContinuousLinearMap.comp_apply, Wkp.restrictL_restrictL]
    rw [Wkp.lowerOrderL_apply, Wkp.lowerOrder_restrictL, Wkp.restrictL_restrictL]
    exact Wkp.lowerOrder_restrictL hA k (y x)
  rw [hfun]
  exact hT

/-- **Rellich's theorem over a base with boundary, for any loss of derivatives.** For
`k + d + 1 ≤ n` and `1 ≤ p ≤ ∞`, the inclusion `W^{k+d+1,p}(V) → W^{k,p}(V)` is a compact
operator. -/
theorem isCompactOperator_lowerOrdersL {d : ℕ} (hkn : k + d + 1 ≤ n)
    (A : FiniteBundleAtlas ClosedUpperHalfPlane M F V) :
    IsCompactOperator (A.halfSectionChartData.lowerOrdersL volume p k (d + 1)) :=
  SectionChartData.isCompactOperator_lowerOrdersL (isCompactOperator_lowerOrderL hkn A)

/-- **Ehrling's inequality over a base with boundary.** For a `Cⁿ` vector bundle over a Hausdorff
`Cⁿ` manifold modelled on the closed upper half-plane, given by a finite bundle atlas, `1 ≤ p ≤ ∞`,
orders with `k + d + 1 ≤ n` and every `ε > 0`, there is `C ≥ 0` with

`‖w‖_{W^{k,p}} ≤ ε ‖w‖_{W^{k+d+1,p}} + C ‖w‖_{Lᵖ}`

for every `w ∈ W^{k+d+1,p}(V)`, where `‖w‖_{Lᵖ}` is the norm of the chart data of `w`
(`TauCeti.SectionChartData.chartValuesL`). -/
theorem exists_norm_lowerOrdersL_le {d : ℕ} (hkn : k + d + 1 ≤ n)
    (A : FiniteBundleAtlas ClosedUpperHalfPlane M F V) {ε : ℝ} (hε : 0 < ε) :
    ∃ C, 0 ≤ C ∧ ∀ w : BorderedSobolevSection A p (k + (d + 1)),
      ‖A.halfSectionChartData.lowerOrdersL volume p k (d + 1) w‖ ≤
        ε * ‖w‖ + C * ‖A.halfSectionChartData.chartValuesL volume p (k + (d + 1)) w‖ :=
  SectionChartData.exists_norm_lowerOrdersL_le (isCompactOperator_lowerOrdersL hkn A) hε

end BorderedSobolevSection

end TauCeti
