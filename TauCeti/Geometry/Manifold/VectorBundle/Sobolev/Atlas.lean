/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.FiniteCover
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Transfer

/-!
# Independence of the Sobolev spaces of sections from the atlas

Let `M` be a smooth Hausdorff manifold without boundary modelled on a finite-dimensional real
inner product space `E`, and let `V → M` be a smooth real vector bundle with finite-dimensional
model fibre `F`. The Sobolev space `W^{k,p}(V)` of `TauCeti.SobolevSection` is built from a finite
bundle atlas `A`: its elements are the tuples of chartwise `W^{k,p}` components of sections, with
the maximum of the component norms. This file proves that, for `1 ≤ p < ∞`, it does not depend on
the atlas: for a second finite bundle atlas `B`, the elements of `W^{k,p}(V)` for `A` and for `B`
are the chart data of the same sections, and the identification is a continuous linear
equivalence `TauCeti.SobolevSection.atlasEquiv A B`. In particular the norms given by the two
atlases are equivalent, so `W^{k,p}(V)` is a Banach space determined by the bundle up to
equivalence of norms.

The identification is characterized by keeping the underlying section: if the chart data of `w`
for `A` are the coordinates `A.coord i s` of a section `s`, then the chart data of
`atlasEquiv A B w` for `B` are the coordinates `B.coord j s`
(`TauCeti.SobolevSection.chartValueL_atlasEquiv_ae`). It is compatible with inverses and
composition (`TauCeti.SobolevSection.atlasEquiv_symm`, `TauCeti.SobolevSection.atlasEquiv_trans`)
and with forgetting the highest weak derivative
(`TauCeti.SobolevSection.lowerOrderL_atlasEquiv`).

## Construction

Both atlases are charts of their union `A.append B` (`TauCeti.FiniteBundleAtlas.append`), whose
charts of `A` alone already cover `M`. So the image of each chart `j` of `B` is covered by finitely
many pieces `P i j`, one for each chart `i` of `A`
(`TauCeti.FiniteBundleAtlas.exists_transfer_cover_of_iUnion_dom_eq`), on which the chart-`j`
coordinates of a section are obtained from its chart-`i` coordinates by a change of variables and
the coordinate change of the bundle (`TauCeti.FiniteBundleAtlas.transferL`), a continuous linear
map of Sobolev spaces. The transferred components glue over the finite cover
(`TauCeti.Wkp.exists_continuousLinearMap_value_ae_eq`) to the chart-`j` components of the section.

## Main results

* `TauCeti.SobolevSection.atlasEquiv`: the continuous linear equivalence between the Sobolev
  spaces of sections of two finite bundle atlases, for `1 ≤ p < ∞`.
* `TauCeti.SobolevSection.chartValueL_atlasEquiv_ae`, `TauCeti.SobolevSection.atlasEquiv_eq_iff`:
  it keeps the underlying section, and this characterizes it.

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
private theorem value_transferL_append_ae (hp : p ≠ ⊤) {i : Fin A.n} {j : Fin B.n} {P Q : Opens E}
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
    (Wkp.value k ((A.append B).transferL μ p k hp (Fin.castAdd B.n i) (Fin.natAdd A.n j) hPc hPD
      hPQ (fun l ↦ Wkp.restrictL hQ k ((w : A.sectionChartData.SobolevData μ p k) i l)) m) :
        E → ℝ) =ᵐ[μ.restrict P] fun y ↦ (finBasis ℝ F).repr (B.coord j s y) m := by
  have hcv :=
    ((A.append B).exists_isChangeOfVariables_chart_symm_trans k hPc hPD hPQ).choose_spec.choose_spec
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
  filter_upwards [(A.append B).value_transferL_ae μ p k hp _ _ hPc hPD hPQ _ m, hcv.ae_comp hQs,
    ae_restrict_mem P.isOpen.measurableSet] with y hy₁ hy₂ hy
  -- Pointwise, this is the coordinate change between the two charts of the union atlas.
  obtain ⟨x, hx, rfl⟩ := (A.append B).mem_overlap.1 (hP hy)
  rw [hy₁, hy₂, ← FiniteBundleAtlas.coord_append_natAdd A B j,
    (A.append B).coord_eq_coordChange s (hP hy), FiniteBundleAtlas.coord_append_castAdd,
    (A.append B).transition_chart hx.2, OpenPartialHomeomorph.coe_trans, Function.comp_apply,
    ((A.append B).chart _).left_inv ((A.append B).dom_subset_chart_source _ hx.2)]

/-- The `m`-th component of the chart-`j` coordinates of the sections read by the elements of the
Sobolev sections of `A` depends continuously linearly on them as a `W^{k,p}` function on the
image of chart `j` of `B`. -/
private theorem exists_continuousLinearMap_value_ae (hp : p ≠ ⊤) [T2Space M] (j : Fin B.n)
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
    ContinuousLinearMap.pi fun l ↦ (Wkp.restrictL (hQ i) k).comp ((ContinuousLinearMap.proj l).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun i : Fin A.sectionChartData.n ↦
          ∀ _ : Fin (finrank ℝ F), Wkp μ (A.sectionChartData.image i) p k) i).comp
        (A.sectionChartData.sobolevSections μ p k).subtypeL))
  -- The inclusion followed by the two projections evaluates `w` at `i`. This holds by
  -- definition only, unfolding `pi`, `proj`, `comp` and `subtypeL`, as the index type
  -- `Fin A.sectionChartData.n` of the projection unfolds to `Fin A.n`.
  have hD (w : SobolevSection A μ p k) (i : Fin A.n) :
      D i w = fun l ↦ Wkp.restrictL (hQ i) k ((w : A.sectionChartData.SobolevData μ p k) i l) :=
    (rfl)
  -- On the piece `P i j`, the transfer of the chart-`i` components to chart `j` of `B`.
  let f (i : Fin A.n) : SobolevSection A μ p k →L[ℝ] Wkp μ (P i j) p k :=
    (ContinuousLinearMap.proj m).comp (((A.append B).transferL μ p k hp (Fin.castAdd B.n i)
      (Fin.natAdd A.n j) (hPc i j) (hPD i j) (hPQ i j)).comp (D i))
  have hf (i : Fin A.n) (w : SobolevSection A μ p k) {s : ∀ x, V x}
      (hs : ∀ i, A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)]
        A.coord i s) :
      (Wkp.value k (f i w) : E → ℝ) =ᵐ[μ.restrict (P i j)]
        fun y ↦ (finBasis ℝ F).repr (B.coord j s y) m := by
    simpa only [f, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, hD] using
      value_transferL_append_ae A B μ k hp (hP i j) (hPc i j) (hPD i j) (hQ i) (hPQ i j) hs m
  -- The transfers glue over the pieces covering the image of chart `j`, to the components of the
  -- coordinates of a chosen section read by `w`, hence of every section read by `w`.
  choose sec hsec using SobolevSection.exists_ae_eq_coord A μ p k
  obtain ⟨Φ, hΦ⟩ := Wkp.exists_continuousLinearMap_value_ae_eq (hPj · j) (hcov j) f
    (fun w y ↦ (finBasis ℝ F).repr (B.coord j (sec w) y) m) fun i w ↦ hf i w (hsec w)
  refine ⟨Φ, fun w s hs ↦ ae_restrict_of_ae_restrict_of_subset
    (SetLike.coe_subset_coe.2 (hcov j)) ?_⟩
  rw [Opens.coe_iSup, ae_restrict_iUnion_iff]
  intro i
  filter_upwards [ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.2 (hPj i j))
    (hΦ w), hf i w (hsec w), hf i w hs] with y h₁ h₂ h₃
  rw [h₁, ← h₂, h₃]

/-- A continuous linear map from the Sobolev sections of `A` to those of `B` keeping the underlying
section. -/
private theorem exists_continuousLinearMap_chartValueL_ae (hp : p ≠ ⊤) [T2Space M] :
    ∃ T : SobolevSection A μ p k →L[ℝ] SobolevSection B μ p k,
      ∀ (w : SobolevSection A μ p k) (s : ∀ x, V x),
        (∀ i, A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s) →
          ∀ j, B.sectionChartData.chartValueL μ p k j (T w) =ᵐ[μ.restrict (B.image j)]
            B.coord j s := by
  choose Φ hΦ using exists_continuousLinearMap_value_ae A B μ k hp
  have hchart (w : SobolevSection A μ p k) {s : ∀ x, V x}
      (hs : ∀ i, A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)]
        A.coord i s) (j : Fin B.n) :
      B.sectionChartData.chartValueL μ p k j (fun j m ↦ Φ j m w) =ᵐ[μ.restrict (B.image j)]
        B.sectionChartData.coord j s := by
    refine B.sectionChartData.chartValueL_ae_eq_coord μ p k fun m ↦ ?_
    filter_upwards [hΦ j m w s hs, B.sectionChartData_coord_ae_eq μ j s] with y h₁ h₂
    exact h₁.trans (by rw [h₂, Basis.coord_apply])
  refine ⟨(ContinuousLinearMap.pi fun j ↦ ContinuousLinearMap.pi (Φ j)).codRestrict
    (B.sectionChartData.sobolevSections μ p k) fun w ↦ ?_,
    fun w s hs j ↦ (hchart w hs j).trans (B.sectionChartData_coord_ae_eq μ j s)⟩
  obtain ⟨s, hs⟩ := SobolevSection.exists_ae_eq_coord A μ p k w
  exact (B.sectionChartData.mem_sobolevSections_iff μ p k).2 ⟨s, hchart w hs⟩

variable [T2Space M]

/-- **Independence of the atlas.** For `1 ≤ p < ∞`, the Sobolev spaces `W^{k,p}(V)` of sections
given by two finite bundle atlases `A` and `B` are identified by a continuous linear equivalence,
which keeps the underlying section (`TauCeti.SobolevSection.chartValueL_atlasEquiv_ae`). In
particular the norms of the two atlases are equivalent. -/
def atlasEquiv (hp : p ≠ ⊤) : SobolevSection A μ p k ≃L[ℝ] SobolevSection B μ p k :=
  ContinuousLinearEquiv.equivOfInverse
    (exists_continuousLinearMap_chartValueL_ae A B μ k hp).choose
    (exists_continuousLinearMap_chartValueL_ae B A μ k hp).choose
    (fun w ↦ by
      obtain ⟨s, hs⟩ := exists_ae_eq_coord A μ p k w
      exact eq_of_ae_eq_coord ((exists_continuousLinearMap_chartValueL_ae B A μ k hp).choose_spec
        _ s ((exists_continuousLinearMap_chartValueL_ae A B μ k hp).choose_spec w s hs)) hs)
    (fun w ↦ by
      obtain ⟨s, hs⟩ := exists_ae_eq_coord B μ p k w
      exact eq_of_ae_eq_coord ((exists_continuousLinearMap_chartValueL_ae A B μ k hp).choose_spec
        _ s ((exists_continuousLinearMap_chartValueL_ae B A μ k hp).choose_spec w s hs)) hs)

variable {A B μ k}

/-- **The identification keeps the underlying section.** If the chart data of `w` for `A` are the
coordinates `A.coord i s` of a section `s`, then the chart data of `atlasEquiv A B w` for `B` are
its coordinates `B.coord j s`. -/
theorem chartValueL_atlasEquiv_ae (hp : p ≠ ⊤) {w : SobolevSection A μ p k} {s : ∀ x, V x}
    (hw : ∀ i, A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s)
    (j : Fin B.n) :
    B.sectionChartData.chartValueL μ p k j (atlasEquiv A B μ k hp w) =ᵐ[μ.restrict (B.image j)]
      B.coord j s :=
  (exists_continuousLinearMap_chartValueL_ae A B μ k hp).choose_spec w s hw j

/-- An element `w'` of `W^{k,p}(V)` for `B` is the image of `w` under the identification exactly
when `w` and `w'` are the chart data of a common section. -/
theorem atlasEquiv_eq_iff (hp : p ≠ ⊤) {w : SobolevSection A μ p k}
    {w' : SobolevSection B μ p k} :
    atlasEquiv A B μ k hp w = w' ↔ ∃ s : ∀ x, V x,
      (∀ i, A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s) ∧
        ∀ j, B.sectionChartData.chartValueL μ p k j w' =ᵐ[μ.restrict (B.image j)] B.coord j s := by
  refine ⟨fun h ↦ ?_, fun ⟨s, hs, hs'⟩ ↦ eq_of_ae_eq_coord (chartValueL_atlasEquiv_ae hp hs) hs'⟩
  obtain ⟨s, hs⟩ := exists_ae_eq_coord A μ p k w
  exact ⟨s, hs, h ▸ chartValueL_atlasEquiv_ae hp hs⟩

/-- The inverse of the identification of the Sobolev sections of `A` and `B` is that of `B` and
`A`. -/
@[simp]
theorem atlasEquiv_symm (hp : p ≠ ⊤) :
    (atlasEquiv A B μ k hp).symm = atlasEquiv B A μ k hp := by
  refine ContinuousLinearEquiv.ext <| funext fun w ↦ ?_
  rw [ContinuousLinearEquiv.symm_apply_eq, eq_comm, atlasEquiv_eq_iff]
  obtain ⟨s, hs⟩ := exists_ae_eq_coord B μ p k w
  exact ⟨s, chartValueL_atlasEquiv_ae hp hs, hs⟩

/-- The identification of the Sobolev sections of an atlas with themselves is the identity. -/
@[simp]
theorem atlasEquiv_refl (hp : p ≠ ⊤) :
    atlasEquiv A A μ k hp = ContinuousLinearEquiv.refl ℝ _ := by
  refine ContinuousLinearEquiv.ext <| funext fun w ↦ ?_
  obtain ⟨s, hs⟩ := exists_ae_eq_coord A μ p k w
  exact (atlasEquiv_eq_iff hp).2 ⟨s, hs, hs⟩

/-- The identifications of the Sobolev sections of three atlases compose. -/
@[simp]
theorem atlasEquiv_trans (C : FiniteBundleAtlas E M F V) (hp : p ≠ ⊤) :
    (atlasEquiv A B μ k hp).trans (atlasEquiv B C μ k hp) = atlasEquiv A C μ k hp := by
  refine ContinuousLinearEquiv.ext <| funext fun w ↦ ?_
  obtain ⟨s, hs⟩ := exists_ae_eq_coord A μ p k w
  exact ((atlasEquiv_eq_iff hp).2
    ⟨s, hs, chartValueL_atlasEquiv_ae hp (chartValueL_atlasEquiv_ae hp hs)⟩).symm

/-- The identification commutes with forgetting the highest weak derivative. -/
theorem lowerOrderL_atlasEquiv (hp : p ≠ ⊤) (w : SobolevSection A μ p (k + 1)) :
    B.sectionChartData.lowerOrderL μ p k (atlasEquiv A B μ (k + 1) hp w) =
      atlasEquiv A B μ k hp (A.sectionChartData.lowerOrderL μ p k w) := by
  obtain ⟨s, hs⟩ := exists_ae_eq_coord A μ p (k + 1) w
  refine eq_of_ae_eq_coord (s := s) (fun j ↦ ?_) (chartValueL_atlasEquiv_ae hp fun i ↦ ?_)
  · rw [SectionChartData.chartValueL_coe_lowerOrderL]
    exact chartValueL_atlasEquiv_ae hp hs j
  · rw [SectionChartData.chartValueL_coe_lowerOrderL]
    exact hs i

end SobolevSection

end TauCeti
