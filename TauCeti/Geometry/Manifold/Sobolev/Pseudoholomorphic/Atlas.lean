/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Sobolev.Pseudoholomorphic
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Invariance
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Locality
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.TargetChange
import TauCeti.Geometry.Manifold.ContMDiff.Atlas
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart

/-!
# Chart independence of the weak pseudoholomorphic equation

Let `X` be a Riemann surface and `M` a manifold modelled on a boundaryless model `I` with model
vector space `E`. A map `u : X → M` is weakly pseudoholomorphic on `s` for a domain-dependent
almost complex structure `J` and an inhomogeneous term `ν`
(`TauCeti.IsWeakPseudoholomorphicOn J ν p u s`) when it is continuous and, for every holomorphic
chart `φ` of `X` and every chart `ψ` of the maximal atlas of `M`, its coordinate expression solves
the planar weak equation `∂ₛw + J_φψ(z, w) ∂ₜw = η_φψ(z, w)`. This file shows that it suffices to
test the charts of one family of holomorphic charts covering `s` and one family of charts of `M`
covering `u '' s`, for instance the atlases or the preferred charts. No openness of `s` is needed.

The proof transports the coordinate equation along the two kinds of chart change.

* **Holomorphic chart change.** For holomorphic charts `φ` and `φ'` with transition
  `τ = φ ∘ φ'⁻¹` and `τ' = a + b i`, the coordinate vector `∂ₛ` of `φ'` is `a ∂ₛ + b ∂ₜ` in the
  coordinates of `φ`, and `∂ₜ = j ∂ₛ`. Since `ν` is complex antilinear, the term read in `φ'` is
  `a η_φψ(τ z, ·) - b J_φψ(τ z, ·) η_φψ(τ z, ·)`
  (`TauCeti.InhomogeneousTerm.chartTerm_eq_re_smul_sub_im_smul`), while the structure read in `φ'`
  is `J_φψ(τ z, ·)`. This is exactly how the planar equation transforms under the biholomorphism
  `τ` (`TauCeti.IsWeakCauchyRiemannOn.comp_differentiableOn`).
* **Target chart change.** For charts `ψ₁` and `ψ₂` of `M` with transition `Θ = ψ₂ ∘ ψ₁⁻¹`, the
  derivative of `Θ` intertwines the structures read in the two charts
  (`TauCeti.ContMDiffAlmostComplexStructureFamily.chartField_symm_trans_comp_fderiv`) and carries
  one term to the other (`TauCeti.InhomogeneousTerm.chartTerm_symm_trans_apply`). This is how
  the planar equation transforms under the `C¹` map `Θ`
  (`TauCeti.IsWeakCauchyRiemannOn.contDiffOn_comp_of_intertwine`).

The two steps are glued by the locality of the planar equation,
`TauCeti.isWeakCauchyRiemannOn_iff_locally`.

## Main results

* `TauCeti.isWeakPseudoholomorphicOn_iff_of_subset_maximalAtlas`,
  `TauCeti.isWeakPseudoholomorphic_iff_of_subset_maximalAtlas`: **chart independence**, testing
  families of charts covering `s` and `u '' s`.
* `TauCeti.isWeakPseudoholomorphicOn_iff_atlas`, `TauCeti.isWeakPseudoholomorphic_iff_atlas`:
  it suffices to test the atlases of `X` and `M`.
* `TauCeti.isWeakPseudoholomorphicOn_iff_chartAt`, `TauCeti.isWeakPseudoholomorphic_iff_chartAt`:
  it suffices to test the preferred charts of `X` and `M`.
* `TauCeti.isWeakPseudoholomorphicOn_iff_continuousOn_isWeakCauchyRiemannOn_self`: for maps from
  the plane into a normed space it suffices to test the identity charts, so the predicate is the
  planar weak equation `∂ₛu + J(z, u) ∂ₜu = 2ν(z, u)(1)` together with continuity.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 3.1 and Appendix B.4.
-/

public section

open Set Filter TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology TauCeti.ComplexManifold

noncomputable section

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ∞ X]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {ℓ : ℕ∞}
  {J : ContMDiffAlmostComplexStructureFamily I M 𝓘(ℝ, ℂ) X ℓ}
  {ν : InhomogeneousTerm ((SmoothAlmostComplexStructure.ofComplexManifold ℂ X).toContMDiff ℓ) J}
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-! ### Transporting the coordinate equation -/

section Transport

variable {p : ENNReal} {ψ₁ ψ₂ : OpenPartialHomeomorph M G}

/-- **The coordinate equation under a change of holomorphic chart.** A solution `g` of the
coordinate equation read in the holomorphic chart `φ` and a chart `ψ` of `M` gives, composed with
the transition `φ ∘ φ'⁻¹`, a solution of the coordinate equation read in `φ'` and `ψ`. -/
private theorem IsWeakCauchyRiemannOn.comp_symm_trans_of_mem_maximalAtlas
    {φ φ' : OpenPartialHomeomorph X ℂ}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X) (hφ' : φ' ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    {ψ : OpenPartialHomeomorph M G} (hψ : MDifferentiableOn I 𝓘(ℝ, G) ψ ψ.source)
    (hψs : MDifferentiableOn 𝓘(ℝ, G) I ψ.symm ψ.target) {U U' : Set ℂ} {g : ℂ → G}
    (h : IsWeakCauchyRiemannOn p U' (J.chartField φ ψ) (ν.chartTerm φ ψ) g)
    (hU : U ⊆ (φ'.symm.trans φ).source) (hmaps : MapsTo (φ'.symm.trans φ) U U')
    (hg : MapsTo g U' ψ.target) :
    IsWeakCauchyRiemannOn p U (J.chartField φ' ψ) (ν.chartTerm φ' ψ)
      (fun z ↦ g (φ'.symm.trans φ z)) := by
  have hτ : DifferentiableOn ℂ (φ'.symm.trans φ) (φ'.symm.trans φ).source :=
    (contDiffOn_symm_trans_of_mem_maximalAtlas hφ' hφ).differentiableOn one_ne_zero
  have hderiv : ∀ z ∈ U, deriv (φ'.symm.trans φ) z ≠ 0 := fun z hz ↦ by
    obtain ⟨A, hA⟩ := exists_hasFDerivAt_symm_trans one_ne_zero hφ' hφ (hU hz)
    rw [hA.hasDerivAt.deriv]
    exact A.map_ne_zero_iff.2 one_ne_zero
  -- At a point of the target of `ψ`, both chart derivatives exist.
  have hdiff : ∀ x ∈ ψ.target, MDifferentiableAt I 𝓘(ℝ, G) ψ (ψ.symm x) ∧
      MDifferentiableAt 𝓘(ℝ, G) I ψ.symm x := fun x hx ↦
    ⟨hψ.mdifferentiableAt (ψ.open_source.mem_nhds (ψ.map_target hx)),
      hψs.mdifferentiableAt (ψ.open_target.mem_nhds hx)⟩
  have h' := h.comp_differentiableOn (φ'.symm.trans φ).open_source hτ hU
    ((φ'.symm.trans φ).injOn.mono hU) hderiv hmaps fun z hz ↦ by
      have hx := hg (hmaps (interior_subset hz))
      ext v
      rw [mul_apply_eq_comp, ContMDiffAlmostComplexStructureFamily.chartField_apply,
        (J.freeze _).chartPushforward_apply_chartPushforward_apply ψ hx (hdiff _ hx).1
          (hdiff _ hx).2 v, neg_apply, one_apply_eq_self]
  refine (isWeakCauchyRiemannOn_congr_ae ?_ ?_).1 h' <;>
    refine (ae_restrict_iff' measurableSet_interior).2 (Eventually.of_forall fun z hz ↦ ?_)
  · have hz' : φ'.symm z ∈ φ.source := (by simpa using hU (interior_subset hz) :
      z ∈ φ'.target ∧ φ'.symm z ∈ φ.source).2
    simp [ContMDiffAlmostComplexStructureFamily.chartField_apply, φ.left_inv hz']
  · have hx := hg (hmaps (interior_subset hz))
    exact (ν.chartTerm_eq_re_smul_sub_im_smul hφ hφ' (hU (interior_subset hz)) hx (hdiff _ hx).1
      (hdiff _ hx).2).symm

/-- **The coordinate equation under a change of target chart.** A solution `g` of the coordinate
equation read in the holomorphic chart `φ` and a chart `ψ₁` of `M` gives, after the transition
`ψ₂ ∘ ψ₁⁻¹`, a solution of the coordinate equation read in `φ` and `ψ₂`, when both charts are
`C¹` with `C¹` inverses. -/
private theorem IsWeakCauchyRiemannOn.symm_trans_comp [CompleteSpace G]
    (φ : OpenPartialHomeomorph X ℂ)
    (hψ₁ : ContMDiffOn I 𝓘(ℝ, G) 1 ψ₁ ψ₁.source)
    (hψ₁s : ContMDiffOn 𝓘(ℝ, G) I 1 ψ₁.symm ψ₁.target)
    (hψ₂ : ContMDiffOn I 𝓘(ℝ, G) 1 ψ₂ ψ₂.source)
    (hψ₂s : ContMDiffOn 𝓘(ℝ, G) I 1 ψ₂.symm ψ₂.target) {U : Set ℂ} {g : ℂ → G}
    (h : IsWeakCauchyRiemannOn p U (J.chartField φ ψ₁) (ν.chartTerm φ ψ₁) g)
    (hg : MapsTo g U (ψ₁.symm.trans ψ₂).source) :
    IsWeakCauchyRiemannOn p U (J.chartField φ ψ₂) (ν.chartTerm φ ψ₂)
      (fun z ↦ ψ₁.symm.trans ψ₂ (g z)) := by
  have hsrc : ∀ q ∈ (ψ₁.symm.trans ψ₂).source, q ∈ ψ₁.target ∧ ψ₁.symm q ∈ ψ₂.source :=
    fun q hq ↦ by simpa using hq
  have hΘ : ContDiffOn ℝ 1 (ψ₁.symm.trans ψ₂) (ψ₁.symm.trans ψ₂).source := by
    rw [OpenPartialHomeomorph.coe_trans]
    exact contMDiffOn_iff_contDiffOn.1
      (hψ₂.comp (hψ₁s.mono fun q hq ↦ (hsrc q hq).1) fun q hq ↦ (hsrc q hq).2)
  have hdiff : ∀ q ∈ (ψ₁.symm.trans ψ₂).source,
      MDifferentiableAt I 𝓘(ℝ, G) ψ₁ (ψ₁.symm q) ∧
        MDifferentiableAt 𝓘(ℝ, G) I ψ₂.symm (ψ₁.symm.trans ψ₂ q) ∧
          DifferentiableAt ℝ (ψ₁.symm.trans ψ₂) q := fun q hq ↦
    ⟨(hψ₁.mdifferentiableOn one_ne_zero).mdifferentiableAt
        (ψ₁.open_source.mem_nhds (ψ₁.map_target (hsrc q hq).1)),
      (hψ₂s.mdifferentiableOn one_ne_zero).mdifferentiableAt
        (ψ₂.open_target.mem_nhds ((ψ₁.symm.trans ψ₂).map_source hq).1),
      (hΘ.differentiableOn one_ne_zero).differentiableAt
        ((ψ₁.symm.trans ψ₂).open_source.mem_nhds hq)⟩
  refine h.contDiffOn_comp_of_intertwine (ψ₁.symm.trans ψ₂).open_source hΘ hg ?_ ?_ <;>
    refine (ae_restrict_iff' measurableSet_interior).2 (Eventually.of_forall fun z hz ↦ ?_)
  · obtain ⟨h1, h2, h3⟩ := hdiff _ (hg (interior_subset hz))
    exact J.chartField_symm_trans_comp_fderiv φ z (hg (interior_subset hz)) h1 h2 h3
  · obtain ⟨h1, -, h3⟩ := hdiff _ (hg (interior_subset hz))
    exact ν.chartTerm_symm_trans_apply φ z (hg (interior_subset hz)) h1 h3

end Transport

/-! ### Chart independence -/

section ChartIndependence

variable [I.Boundaryless] [CompleteSpace E] {p : ENNReal} {u : X → M} {s : Set X}

omit [IsManifold I ∞ M] [CompleteSpace E] in
/-- The charts of the maximal atlas of `M`, read in `E`, are `C¹` with `C¹` inverses. -/
private theorem contMDiffOn_extendTrans_refl {ψ : OpenPartialHomeomorph M H}
    (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M) :
    ContMDiffOn I 𝓘(ℝ, E) 1 (ψ.extendTrans I (Homeomorph.refl E))
        (ψ.extendTrans I (Homeomorph.refl E)).source ∧
      ContMDiffOn 𝓘(ℝ, E) I 1 (ψ.extendTrans I (Homeomorph.refl E)).symm
        (ψ.extendTrans I (Homeomorph.refl E)).target :=
  ⟨(ψ.contMDiffOn_extendTrans hψ (Ψ := Homeomorph.refl E) contDiff_id).of_le
      (by exact_mod_cast le_top),
    (ψ.contMDiffOn_extendTrans_symm hψ (Ψ := Homeomorph.refl E) contDiff_id).of_le
      (by exact_mod_cast le_top)⟩

/-- **Chart independence of the weak pseudoholomorphic equation.** A map is weakly
pseudoholomorphic on `s` exactly when it is continuous on `s` and its coordinate expressions solve
the coordinate equation for the charts of a family `A` of holomorphic charts covering `s` and a
family `B` of charts of `M` covering `u '' s`. -/
theorem isWeakPseudoholomorphicOn_iff_of_subset_maximalAtlas
    {A : Set (OpenPartialHomeomorph X ℂ)} (hA : A ⊆ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    (hAs : ∀ x ∈ s, ∃ φ ∈ A, x ∈ φ.source)
    {B : Set (OpenPartialHomeomorph M H)} (hB : B ⊆ IsManifold.maximalAtlas I ∞ M)
    (hBs : ∀ x ∈ s, ∃ ψ ∈ B, u x ∈ ψ.source) :
    IsWeakPseudoholomorphicOn J ν p u s ↔ ContinuousOn u s ∧ ∀ φ ∈ A, ∀ ψ ∈ B,
      IsWeakCauchyRiemannOn p (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source))
        (J.chartField φ (ψ.extendTrans I (Homeomorph.refl E)))
        (ν.chartTerm φ (ψ.extendTrans I (Homeomorph.refl E)))
        (ψ.extendTrans I (Homeomorph.refl E) ∘ u ∘ φ.symm) := by
  refine ⟨fun h ↦ ⟨h.continuousOn, fun φ hφ ψ hψ ↦ h.isWeakCauchyRiemannOn_chart (hA hφ) (hB hψ)⟩,
    fun ⟨hc, h⟩ ↦ isWeakPseudoholomorphicOn_iff_continuousOn_isWeakCauchyRiemannOn.2
      ⟨hc, fun φ' hφ' ψ' hψ' ↦ ?_⟩⟩
  -- Change the holomorphic chart, for each chart of `B`.
  have h1 : ∀ ψ ∈ B, IsWeakCauchyRiemannOn p (φ'.target ∩ φ'.symm ⁻¹' (s ∩ u ⁻¹' ψ.source))
      (J.chartField φ' (ψ.extendTrans I (Homeomorph.refl E)))
      (ν.chartTerm φ' (ψ.extendTrans I (Homeomorph.refl E)))
      (ψ.extendTrans I (Homeomorph.refl E) ∘ u ∘ φ'.symm) := by
    intro ψ hψ
    obtain ⟨hψ₁, hψ₁s⟩ := contMDiffOn_extendTrans_refl (hB hψ)
    refine isWeakCauchyRiemannOn_iff_locally.2 fun z hz ↦ ?_
    obtain ⟨φ, hφA, hxφ⟩ := hAs _ hz.2.1
    have hzτ : z ∈ (φ'.symm.trans φ).source := by simpa using ⟨hz.1, hxφ⟩
    refine ⟨_, inter_mem_nhdsWithin _ ((φ'.symm.trans φ).open_source.mem_nhds hzτ), ?_⟩
    refine ((h φ hφA ψ hψ).comp_symm_trans_of_mem_maximalAtlas (hA hφA) hφ'
      (hψ₁.mdifferentiableOn one_ne_zero) (hψ₁s.mdifferentiableOn one_ne_zero) inter_subset_right
      (fun w hw ↦ ?_) (fun w hw ↦ ?_)).congr fun w hw ↦ ?_
    · have hw' : w ∈ φ'.target ∧ φ'.symm w ∈ φ.source := by simpa using hw.2
      refine ⟨by simpa using φ.map_source hw'.2, ?_⟩
      simpa [φ.left_inv hw'.2] using hw.1.2
    · exact (ψ.extendTrans I (Homeomorph.refl E)).map_source (by simpa using hw.2.2)
    · have hw' : w ∈ φ'.target ∧ φ'.symm w ∈ φ.source := by simpa using hw.2
      simp [φ.left_inv hw'.2]
  -- Change the chart of `M`.
  obtain ⟨hψ₂, hψ₂s⟩ := contMDiffOn_extendTrans_refl hψ'
  have hcont : ContinuousOn (u ∘ φ'.symm) (φ'.target ∩ φ'.symm ⁻¹' (s ∩ u ⁻¹' ψ'.source)) :=
    hc.comp (φ'.continuousOn_symm.mono inter_subset_left) fun _ hw ↦ hw.2.1
  refine isWeakCauchyRiemannOn_iff_locally.2 fun z hz ↦ ?_
  obtain ⟨ψ, hψB, hxψ⟩ := hBs _ hz.2.1
  obtain ⟨hψ₁, hψ₁s⟩ := contMDiffOn_extendTrans_refl (hB hψB)
  have hsub : φ'.target ∩ φ'.symm ⁻¹' (s ∩ u ⁻¹' ψ'.source) ∩ (u ∘ φ'.symm) ⁻¹' ψ.source ⊆
      φ'.target ∩ φ'.symm ⁻¹' (s ∩ u ⁻¹' ψ.source) := fun w hw ↦ ⟨hw.1.1, hw.1.2.1, hw.2⟩
  refine ⟨_, inter_mem self_mem_nhdsWithin
    ((hcont z hz).preimage_mem_nhdsWithin (ψ.open_source.mem_nhds hxψ)), ?_⟩
  refine (((h1 ψ hψB).mono hsub).symm_trans_comp φ' hψ₁ hψ₁s hψ₂ hψ₂s
    fun w hw ↦ ?_).congr fun w hw ↦ ?_
  · have hu : u (φ'.symm w) ∈ ψ.source := hw.2
    simpa [(ψ.extendTrans I (Homeomorph.refl E)).left_inv (by simpa using hu), hu] using hw.1.2.2
  · have hu : u (φ'.symm w) ∈ ψ.source := hw.2
    simp [ψ.left_inv hu]

/-- **Chart independence on the whole surface.** A map is weakly pseudoholomorphic exactly when
it is continuous and its coordinate expressions solve the coordinate equation for the charts of a
family `A` of holomorphic charts covering `X` and a family `B` of charts covering the image of
`u`. -/
theorem isWeakPseudoholomorphic_iff_of_subset_maximalAtlas
    {A : Set (OpenPartialHomeomorph X ℂ)} (hA : A ⊆ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    (hAs : ∀ x, ∃ φ ∈ A, x ∈ φ.source)
    {B : Set (OpenPartialHomeomorph M H)} (hB : B ⊆ IsManifold.maximalAtlas I ∞ M)
    (hBs : ∀ x, ∃ ψ ∈ B, u x ∈ ψ.source) :
    IsWeakPseudoholomorphic J ν p u ↔ Continuous u ∧ ∀ φ ∈ A, ∀ ψ ∈ B,
      IsWeakCauchyRiemannOn p (φ.target ∩ φ.symm ⁻¹' (u ⁻¹' ψ.source))
        (J.chartField φ (ψ.extendTrans I (Homeomorph.refl E)))
        (ν.chartTerm φ (ψ.extendTrans I (Homeomorph.refl E)))
        (ψ.extendTrans I (Homeomorph.refl E) ∘ u ∘ φ.symm) := by
  rw [← isWeakPseudoholomorphicOn_univ, isWeakPseudoholomorphicOn_iff_of_subset_maximalAtlas hA
    (fun x _ ↦ hAs x) hB fun x _ ↦ hBs x]
  simp only [continuousOn_univ, univ_inter]

/-- Chart independence: it suffices to test the charts of the atlases of `X` and `M`. -/
theorem isWeakPseudoholomorphicOn_iff_atlas :
    IsWeakPseudoholomorphicOn J ν p u s ↔ ContinuousOn u s ∧ ∀ φ ∈ atlas ℂ X, ∀ ψ ∈ atlas H M,
      IsWeakCauchyRiemannOn p (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source))
        (J.chartField φ (ψ.extendTrans I (Homeomorph.refl E)))
        (ν.chartTerm φ (ψ.extendTrans I (Homeomorph.refl E)))
        (ψ.extendTrans I (Homeomorph.refl E) ∘ u ∘ φ.symm) :=
  isWeakPseudoholomorphicOn_iff_of_subset_maximalAtlas IsManifold.subset_maximalAtlas
    (fun x _ ↦ ⟨_, chart_mem_atlas ℂ x, mem_chart_source ℂ x⟩) IsManifold.subset_maximalAtlas
    fun x _ ↦ ⟨_, chart_mem_atlas H (u x), mem_chart_source H (u x)⟩

/-- Chart independence on the whole surface: it suffices to test the charts of the atlases of `X`
and `M`. -/
theorem isWeakPseudoholomorphic_iff_atlas :
    IsWeakPseudoholomorphic J ν p u ↔ Continuous u ∧ ∀ φ ∈ atlas ℂ X, ∀ ψ ∈ atlas H M,
      IsWeakCauchyRiemannOn p (φ.target ∩ φ.symm ⁻¹' (u ⁻¹' ψ.source))
        (J.chartField φ (ψ.extendTrans I (Homeomorph.refl E)))
        (ν.chartTerm φ (ψ.extendTrans I (Homeomorph.refl E)))
        (ψ.extendTrans I (Homeomorph.refl E) ∘ u ∘ φ.symm) :=
  isWeakPseudoholomorphic_iff_of_subset_maximalAtlas IsManifold.subset_maximalAtlas
    (fun x ↦ ⟨_, chart_mem_atlas ℂ x, mem_chart_source ℂ x⟩) IsManifold.subset_maximalAtlas
    fun x ↦ ⟨_, chart_mem_atlas H (u x), mem_chart_source H (u x)⟩

/-- Chart independence: it suffices to test the preferred charts of `X` and `M`. -/
theorem isWeakPseudoholomorphicOn_iff_chartAt :
    IsWeakPseudoholomorphicOn J ν p u s ↔ ContinuousOn u s ∧ ∀ (x : X) (y : M),
      IsWeakCauchyRiemannOn p
        ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (s ∩ u ⁻¹' (chartAt H y).source))
        (J.chartField (chartAt ℂ x) ((chartAt H y).extendTrans I (Homeomorph.refl E)))
        (ν.chartTerm (chartAt ℂ x) ((chartAt H y).extendTrans I (Homeomorph.refl E)))
        ((chartAt H y).extendTrans I (Homeomorph.refl E) ∘ u ∘ (chartAt ℂ x).symm) := by
  rw [isWeakPseudoholomorphicOn_iff_of_subset_maximalAtlas (A := range (chartAt ℂ))
    (range_subset_iff.2 IsManifold.chart_mem_maximalAtlas)
    (fun x _ ↦ ⟨_, mem_range_self x, mem_chart_source ℂ x⟩)
    (B := range (chartAt H)) (range_subset_iff.2 IsManifold.chart_mem_maximalAtlas)
    fun x _ ↦ ⟨_, mem_range_self (u x), mem_chart_source H (u x)⟩]
  simp only [forall_mem_range]

/-- Chart independence on the whole surface: it suffices to test the preferred charts of `X` and
`M`. -/
theorem isWeakPseudoholomorphic_iff_chartAt :
    IsWeakPseudoholomorphic J ν p u ↔ Continuous u ∧ ∀ (x : X) (y : M),
      IsWeakCauchyRiemannOn p
        ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (u ⁻¹' (chartAt H y).source))
        (J.chartField (chartAt ℂ x) ((chartAt H y).extendTrans I (Homeomorph.refl E)))
        (ν.chartTerm (chartAt ℂ x) ((chartAt H y).extendTrans I (Homeomorph.refl E)))
        ((chartAt H y).extendTrans I (Homeomorph.refl E) ∘ u ∘ (chartAt ℂ x).symm) := by
  rw [← isWeakPseudoholomorphicOn_univ, isWeakPseudoholomorphicOn_iff_chartAt]
  simp only [continuousOn_univ, univ_inter]

end ChartIndependence

/-! ### Maps from the plane into a normed space -/

section Plane

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {p : ENNReal}
  {J : ContMDiffAlmostComplexStructureFamily 𝓘(ℝ, F) F 𝓘(ℝ, ℂ) ℂ ℓ}
  {ν : InhomogeneousTerm ((SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ).toContMDiff ℓ) J}
  {u : ℂ → F} {s : Set ℂ}

/-- **Maps from the plane into a normed space.** For `X = ℂ` and `M = F`, it suffices to test the
identity charts: a map `u` is weakly pseudoholomorphic on `s` exactly when it is continuous on `s`
and solves the planar weak equation `∂ₛu + J(z, u) ∂ₜu = 2ν(z, u)(1)` on `s`. -/
theorem isWeakPseudoholomorphicOn_iff_continuousOn_isWeakCauchyRiemannOn_self :
    IsWeakPseudoholomorphicOn J ν p u s ↔ ContinuousOn u s ∧
      IsWeakCauchyRiemannOn p s (fun z v ↦ J.toEndomorphism (z, v))
        (fun z v ↦ (2 : ℝ) • (ν.val.tangentHom (z, v) (1 : ℂ) : F)) u := by
  have hA : OpenPartialHomeomorph.refl ℂ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 ℂ :=
    chartAt_self_eq (x := (0 : ℂ)) ▸ IsManifold.chart_mem_maximalAtlas (0 : ℂ)
  have hB : OpenPartialHomeomorph.refl F ∈ IsManifold.maximalAtlas 𝓘(ℝ, F) ∞ F :=
    chartAt_self_eq (x := (0 : F)) ▸ IsManifold.chart_mem_maximalAtlas (0 : F)
  rw [isWeakPseudoholomorphicOn_iff_of_subset_maximalAtlas (A := {OpenPartialHomeomorph.refl ℂ})
    (by simpa using hA) (fun x _ ↦ ⟨_, rfl, mem_univ x⟩) (B := {OpenPartialHomeomorph.refl F})
    (by simpa using hB) fun x _ ↦ ⟨_, rfl, mem_univ (u x)⟩]
  simp only [mem_singleton_iff, forall_eq, OpenPartialHomeomorph.refl_symm,
    OpenPartialHomeomorph.extendTrans_modelWithCornersSelf_refl,
    ContMDiffAlmostComplexStructureFamily.chartField_refl, InhomogeneousTerm.chartTerm_refl]
  refine and_congr_right fun _ ↦ ?_
  have hset : (OpenPartialHomeomorph.refl ℂ).target ∩
      (OpenPartialHomeomorph.refl ℂ) ⁻¹' (s ∩ u ⁻¹' (OpenPartialHomeomorph.refl F).source) = s := by
    simp
  rw [hset]
  -- In the identity chart, `∂ₛ` is the vector `1` at every point. The base point `w` is the
  -- identity chart applied to `z`, which `rw` cannot replace by `z` inside the dependent type
  -- `TangentSpace 𝓘(ℝ, ℂ) w` of the argument; generalizing over `w` and `a` and substituting
  -- the equations transports the argument, after which both sides coincide.
  have hone : ∀ (z : ℂ) (v : F) (w : ℂ), w = z → ∀ a : TangentSpace 𝓘(ℝ, ℂ) w, a = (1 : ℂ) →
      ν.val.tangentHom (w, v) a = ν.val.tangentHom (z, v) (1 : ℂ) := by
    rintro z v w rfl a rfl
    rfl
  refine isWeakCauchyRiemannOn_congr_ae (Eventually.of_forall fun z ↦ ?_)
    (Eventually.of_forall fun z ↦ ?_)
  · ext w
    exact (J.freeze_apply _ _ w).trans (J.tangentEndomorphism_apply _ w)
  · -- The identity chart sends `∂ₛ` to `1`; the tangent space at `z` of `ℂ` is `ℂ`, so the last
    -- step is a definitional unfolding of `TangentSpace`.
    exact congrArg ((2 : ℝ) • ·) (hone z _ _ rfl _
      (by rw [OpenPartialHomeomorph.refl_apply, mfderiv_id]; rfl))

end Plane

end TauCeti
