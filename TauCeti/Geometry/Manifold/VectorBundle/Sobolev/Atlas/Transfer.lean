/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Atlas.Equiv
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Transfer
import TauCeti.Analysis.Sobolev.Wkp.FiniteCover

/-!
# Transfer of Sobolev sections between finite bundle atlases

Let `M` be a smooth Hausdorff manifold without boundary modelled on a finite-dimensional real
inner product space `E`, and let `V → M` be a smooth real vector bundle with finite-dimensional
model fibre `F`. The Sobolev space `W^{k,p}(V)` of `TauCeti.SobolevSection` is built from a finite
bundle atlas `A`: its elements are the tuples of chartwise `W^{k,p}` components of sections. This
file proves that, for `1 ≤ p ≤ ∞` and every order `k`, a section with `W^{k,p}` components in the
charts of `A` has `W^{k,p}` components in the charts of any second finite bundle atlas `B`
(`TauCeti.SobolevSection.transfersTo_of_contMDiffVectorBundle`). By
`TauCeti.SobolevSection.atlasEquiv` the Sobolev spaces of sections given by `A` and by `B` are then
isomorphic Banach spaces, an element corresponding to the element with the same section, and by
`TauCeti.SobolevSection.exists_norm_changeAtlas_le` the norms of the two atlases are equivalent.
So `W^{k,p}(V)` is a Banach space determined by the bundle up to equivalence of norms.

## Construction

Both atlases are charts of their union `A.append B` (`TauCeti.FiniteBundleAtlas.append`), whose
charts of `A` alone already cover `M`. So the image of each chart `j` of `B` is covered by finitely
many pieces `P i j`, one for each chart `i` of `A`
(`TauCeti.FiniteBundleAtlas.exists_transfer_cover_append`), on which the chart-`j` coordinates of a
section are obtained from its chart-`i` coordinates by a change of variables and the coordinate
change of the bundle (`TauCeti.FiniteBundleAtlas.transferL`), a continuous linear map of Sobolev
spaces. The transferred components glue over the finite cover
(`TauCeti.Wkp.exists_continuousLinearMap_value_ae_eq`) to the chart-`j` components of the section.

## Main results

* `TauCeti.SobolevSection.transfersTo_of_contMDiffVectorBundle`: Sobolev sections transfer between
  any two finite bundle atlases of a smooth vector bundle over a smooth Hausdorff manifold.

## References

* R. S. Palais, *Foundations of Global Non-linear Analysis*, Benjamin (1968), §9.
* T. Aubin, *Some Nonlinear Problems in Riemannian Geometry*, Springer (1998), §2.2.
-/

public section

noncomputable section

open Bundle Filter MeasureTheory Module Set TopologicalSpace
open scoped Manifold ContDiff ENNReal Topology

universe u

namespace TauCeti

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {M : Type*}
  [TopologicalSpace M] [ChartedSpace E M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] (A B : FiniteBundleAtlas E M F V)

variable [IsManifold 𝓘(ℝ, E) ∞ M]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)]

variable (μ : Measure E) [μ.IsAddHaarMeasure] {p : ℝ≥0∞} [Fact (1 ≤ p)] (k : ℕ)

namespace SobolevSection

/-- On a piece `P` of the overlap of chart `i` of `A` and chart `j` of `B`, transferring the
chart-`i` components of an element of `W^{k,p}(V)` for `A` reading a section `s` gives the
components of the chart-`j` coordinates `B.coord j s`. -/
private theorem value_transferL_append_ae {i : Fin A.n} {j : Fin B.n} {P Q : Opens E}
    (hP : (P : Set E) ⊆ (A.append B).overlap (Fin.castAdd B.n i) (Fin.natAdd A.n j))
    (hPc : IsCompact (closure (P : Set E)))
    (hPD : closure (P : Set E) ⊆
      (A.append B).transferDomain (Fin.castAdd B.n i) (Fin.natAdd A.n j))
    (hQ : Q ≤ A.image i)
    (hPQ : MapsTo (((A.append B).chart (Fin.natAdd A.n j)).symm ≫ₕ
      (A.append B).chart (Fin.castAdd B.n i)) P Q)
    {w : SobolevSection A μ p k} {s : ∀ x, V x}
    (hs : ∀ i, A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s)
    (m : Fin (finrank ℝ F)) :
    (Wkp.value k ((A.append B).transferL μ p k (Fin.castAdd B.n i) (Fin.natAdd A.n j) hPc hPD
      hPQ (fun l ↦ Wkp.restrictL hQ k ((w : A.sectionChartData.SobolevData μ p k) i l)) m) :
        E → ℝ) =ᵐ[μ.restrict P] fun y ↦ (finBasis ℝ F).repr (B.coord j s y) m := by
  -- On `Q`, the restricted chart-`i` components assemble to the chart-`i` coordinates of `s`.
  have hQs : ∀ᵐ z ∂μ.restrict Q, ∑ l, Wkp.value k (Wkp.restrictL hQ k
      ((w : A.sectionChartData.SobolevData μ p k) i l)) z • finBasis ℝ F l = A.coord i s z := by
    have hQ' := SetLike.coe_subset_coe.2 hQ
    filter_upwards [ae_all_iff.2 fun l ↦ Wkp.value_restrictL_ae hQ k
        ((w : A.sectionChartData.SobolevData μ p k) i l),
      ae_restrict_of_ae_restrict_of_subset hQ' (A.sectionChartData.chartValueL_apply_ae μ p k i w),
      ae_restrict_of_ae_restrict_of_subset hQ' (hs i)] with z hl hz hsz
    simp only [hl]
    exact hz.symm.trans hsz
  filter_upwards [(A.append B).value_transferL_ae μ p k _ _ hPc hPD hPQ _ m,
    (A.append B).ae_comp_chart_symm_trans hPc hPD hPQ hQs,
    ae_restrict_mem P.isOpen.measurableSet] with y hy₁ hy₂ hy
  -- Pointwise, this is the coordinate change between the two charts of the union atlas.
  rw [hy₁, hy₂, ← FiniteBundleAtlas.coord_append_natAdd A B j,
    (A.append B).coord_eq_coordChange s (hP hy), FiniteBundleAtlas.coord_append_castAdd,
    (A.append B).transition_eq_symm_trans]

/-- The `m`-th component of the chart-`j` coordinates of the sections read by the elements of the
Sobolev sections of `A` depends continuously linearly on them as a `W^{k,p}` function on the
image of chart `j` of `B`. -/
private theorem exists_continuousLinearMap_value_ae [T2Space M] (j : Fin B.n)
    (m : Fin (finrank ℝ F)) :
    ∃ Φ : SobolevSection A μ p k →L[ℝ] Wkp μ (B.image j) p k,
      ∀ (w : SobolevSection A μ p k) (s : ∀ x, V x),
        (∀ i, A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s) →
          (Wkp.value k (Φ w) : E → ℝ) =ᵐ[μ.restrict (B.image j)]
            fun y ↦ (finBasis ℝ F).repr (B.coord j s y) m := by
  obtain ⟨P, Q, hP, hPc, hPD, hQ, hPQ, hPj, hcov⟩ := A.exists_transfer_cover_append B
  -- The chart-`i` components, restricted to `Q i`.
  let D (i : Fin A.n) :
      SobolevSection A μ p k →L[ℝ] (Fin (finrank ℝ F) → Wkp μ (Q i) p k) :=
    ContinuousLinearMap.pi fun l ↦ (Wkp.restrictL (hQ i) k).comp
      ((ContinuousLinearMap.proj l).comp (A.sectionChartData.componentsL μ p k i))
  have hD (w : SobolevSection A μ p k) (i : Fin A.n) :
      D i w = fun l ↦ Wkp.restrictL (hQ i) k ((w : A.sectionChartData.SobolevData μ p k) i l) :=
    funext fun l ↦ congrArg (Wkp.restrictL (hQ i) k)
      (congrFun (A.sectionChartData.componentsL_apply μ p k i w) l)
  -- On the piece `P i j`, the transfer of the chart-`i` components to chart `j` of `B`.
  let f (i : Fin A.n) : SobolevSection A μ p k →L[ℝ] Wkp μ (P i j) p k :=
    (ContinuousLinearMap.proj m).comp (((A.append B).transferL μ p k (Fin.castAdd B.n i)
      (Fin.natAdd A.n j) (hPc i j) (hPD i j) (hPQ i j)).comp (D i))
  have hf (i : Fin A.n) (w : SobolevSection A μ p k) {s : ∀ x, V x}
      (hs : ∀ i, A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)]
        A.coord i s) :
      (Wkp.value k (f i w) : E → ℝ) =ᵐ[μ.restrict (P i j)]
        fun y ↦ (finBasis ℝ F).repr (B.coord j s y) m := by
    simpa only [f, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, hD] using
      value_transferL_append_ae A B μ k (hP i j) (hPc i j) (hPD i j) (hQ i) (hPQ i j) hs m
  -- The transfers glue over the pieces covering the image of chart `j`, to the components of the
  -- coordinates of a chosen section read by `w`, hence of every section read by `w`.
  choose sec hsec using fun w : SobolevSection A μ p k ↦ exists_ae_eq_coord w
  obtain ⟨Φ, hΦ⟩ := Wkp.exists_continuousLinearMap_value_ae_eq (hPj · j) (hcov j) f
    (fun w y ↦ (finBasis ℝ F).repr (B.coord j (sec w) y) m) fun i w ↦ hf i w (hsec w)
  refine ⟨Φ, fun w s hs ↦ ae_restrict_of_ae_restrict_of_subset
    (SetLike.coe_subset_coe.2 (hcov j)) ?_⟩
  rw [Opens.coe_iSup, ae_restrict_iUnion_iff]
  intro i
  filter_upwards [ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.2 (hPj i j))
    (hΦ w), hf i w (hsec w), hf i w hs] with y h₁ h₂ h₃
  rw [h₁, ← h₂, h₃]

variable {A B μ k}

/-- **Transfer of Sobolev sections between atlases of a smooth bundle.** For a smooth vector bundle
over a smooth Hausdorff manifold, `1 ≤ p ≤ ∞` and every order `k`, every section with `W^{k,p}`
components in the charts of a finite bundle atlas `A` has `W^{k,p}` components in the charts of any
finite bundle atlas `B`. So `TauCeti.SobolevSection.atlasEquiv` identifies the Sobolev spaces of
sections of the two atlases, and their norms are equivalent
(`TauCeti.SobolevSection.exists_norm_changeAtlas_le`). -/
theorem transfersTo_of_contMDiffVectorBundle [T2Space M] : TransfersTo A B μ p k := by
  choose Φ hΦ using exists_continuousLinearMap_value_ae (p := p) A B μ k
  refine transfersTo_iff.2 fun w s hs ↦ ?_
  -- The values of `Φ` at `w` are the components of the readings of `s` in the charts of `B`.
  have hB (j : Fin B.n) :
      B.sectionChartData.chartValueL μ p k j (fun j m ↦ Φ j m w) =ᵐ[μ.restrict (B.image j)]
        B.coord j s := by
    refine (B.sectionChartData.chartValueL_ae_eq_coord μ p k fun m ↦ ?_).trans
      (B.sectionChartData_coord_ae_eq μ j s)
    filter_upwards [hΦ j m w s hs, B.sectionChartData_coord_ae_eq μ j s] with y h₁ h₂
    exact h₁.trans (by rw [Basis.coord_apply, h₂])
  exact ⟨⟨fun j m ↦ Φ j m w, (B.sectionChartData.mem_sobolevSections_iff μ p k).2
    ⟨s, fun j ↦ (hB j).trans (B.sectionChartData_coord_ae_eq μ j s).symm⟩⟩, hB⟩

end SobolevSection

end TauCeti
