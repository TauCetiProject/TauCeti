/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume

/-!
# Isometry invariance of the Riemannian volume

A homeomorphism `Φ : M ≃ₜ N` between manifolds with continuous Riemannian metrics whose tangent
maps preserve the Riemannian inner products carries the Riemannian volume of `M` to the
Riemannian volume of `N`; such a map is automatically differentiable. In particular isometric
manifolds have the same Riemannian volume, which is what makes the total volume a Riemannian
invariant.

The isometry condition is stated pointwise, on the tangent maps, and no orientation is used, so
orientation-reversing isometries and manifolds with boundary or corners are covered. The two
manifolds may be modelled on different model spaces `H` and `H'` over the same vector space `E`.

The statement is the invariance of the Riemannian density under isometries, as in
J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
(Riemannian volume forms and densities).

## Main results

* `MeasurableSet.image_of_continuousOn_injOn_extChartAt`: the Lusin–Souslin theorem in charts, a
  map continuous and injective on a measurable subset of a chart source, with image in a chart
  source, has measurable image.
* `MeasurableSet.image_of_continuousOn_injOn_chartedSpace`: the Lusin–Souslin theorem on a
  hereditarily Lindelöf manifold.
* `TauCeti.chartVolumeDensity_eq_abs_det_mul_of_inner_mfderiv`: the chart volume densities of
  two Riemannian manifolds differ by the absolute Jacobian determinant of a map whose tangent map
  preserves the inner products.
* `TauCeti.chartRiemannianVolume_image_of_inner_mfderiv`: such a map, injective on a subset of a
  chart source, carries its chart volume to the chart volume of its image.
* `TauCeti.riemannianVolume_image_of_inner_mfderiv`: such a map, injective on any measurable set,
  carries its Riemannian volume to the Riemannian volume of its image.
* `Homeomorph.measurePreserving_riemannianVolume`: a homeomorphism whose tangent maps preserve
  the inner products preserves the Riemannian volume.
-/

public section

open Bundle FiberBundle MeasureTheory Riemannian.Tensor Set
open scoped InnerProductSpace Manifold Topology

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

section LusinSouslin

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] [BorelSpace N]

attribute [local instance] extChartAtMeasurableSpaceE extChartAtBorelSpaceE

/-- **Lusin–Souslin theorem in charts.** A map which is continuous and injective on a measurable
subset `s` of the extended chart source at `α`, and maps `s` into the extended chart source at
`β`, sends `s` to a measurable set. -/
theorem _root_.MeasurableSet.image_of_continuousOn_injOn_extChartAt {Φ : M → N} {α : M} {β : N}
    {s : Set M} (hs : MeasurableSet s) (hcont : ContinuousOn Φ s) (hinj : InjOn Φ s)
    (hsα : s ⊆ (extChartAt I α).source) (hsβ : MapsTo Φ s (extChartAt I' β).source) :
    MeasurableSet (Φ '' s) := by
  -- Read `Φ` in the two charts: `g` is continuous and injective on the measurable coordinate
  -- image of `s`, so its image is measurable, and that image is the coordinate image of `Φ '' s`.
  let g := extChartAt I' β ∘ Φ ∘ (extChartAt I α).symm
  have hmaps : MapsTo (extChartAt I α).symm (extChartAt I α '' s) s := by
    rintro _ ⟨x, hx, rfl⟩
    rwa [(extChartAt I α).left_inv (hsα hx)]
  have htarget : extChartAt I α '' s ⊆ (extChartAt I α).target :=
    (image_mono hsα).trans (extChartAt I α).image_source_eq_target.subset
  have himage : g '' (extChartAt I α '' s) = extChartAt I' β '' (Φ '' s) := by
    simp only [g, image_image]
    exact image_congr fun x hx ↦ by
      simp only [Function.comp_apply, (extChartAt I α).left_inv (hsα hx)]
  refine (measurableSet_image_extChartAt_iff β hsβ.image_subset).1 (himage ▸ ?_)
  exact (hs.image_extChartAt α hsα).image_of_continuousOn_injOn
    ((continuousOn_extChartAt β).comp
      (hcont.comp ((continuousOn_extChartAt_symm α).mono htarget) hmaps) (hsβ.comp hmaps))
    (((extChartAt I' β).injOn.comp hinj hsβ).comp
      ((extChartAt I α).symm.injOn.mono htarget) hmaps)

variable (I I') in
include I I' in
/-- **Lusin–Souslin theorem on manifolds.** On a hereditarily Lindelöf manifold modelled on a
finite-dimensional space, for instance a Lindelöf one (which is second countable), a map which is
continuous and injective on a measurable set `s` sends `s` to a measurable set. The models only
serve to read the map in charts, so they are explicit arguments. -/
theorem _root_.MeasurableSet.image_of_continuousOn_injOn_chartedSpace
    [HereditarilyLindelofSpace M] {Φ : M → N} {s : Set M} (hs : MeasurableSet s)
    (hcont : ContinuousOn Φ s) (hinj : InjOn Φ s) : MeasurableSet (Φ '' s) := by
  -- Countably many open sets `U x`, each in the chart source at `x ∈ s` and mapped by `Φ` (on
  -- `s`) into the chart source at `Φ x`, cover `s`; apply the theorem in charts on each piece.
  have h (x : M) (hx : x ∈ s) : ∃ u, IsOpen u ∧ x ∈ u ∧ u ∩ s ⊆ Φ ⁻¹' (chartAt H' (Φ x)).source :=
    mem_nhdsWithin.1 ((hcont x hx).preimage_mem_nhdsWithin (chart_source_mem_nhds H' (Φ x)))
  choose! u hu hxu hus using h
  let U (x : M) : Set M := (chartAt H x).source ∩ u x
  obtain ⟨T, hTc, hTs, hcover⟩ := (HereditarilyLindelofSpace.isLindelof s).elim_nhds_subcover U
    fun x hx ↦ ((chartAt H x).open_source.inter (hu x hx)).mem_nhds ⟨mem_chart_source H x, hxu x hx⟩
  rw [← inter_eq_left.2 hcover, inter_iUnion₂, image_iUnion₂]
  refine .biUnion hTc fun x hx ↦ (hs.inter ((chartAt H x).open_source.inter
    (hu x (hTs x hx))).measurableSet).image_of_continuousOn_injOn_extChartAt (I := I) (I' := I')
    (α := x) (β := Φ x) (hcont.mono inter_subset_left) (hinj.mono inter_subset_left) ?_
    fun y hy ↦ ?_
  · rw [extChartAt_source]
    exact inter_subset_right.trans inter_subset_left
  · rw [extChartAt_source]
    exact hus x (hTs x hx) ⟨hy.2.2, hy.1⟩

end LusinSouslin

variable [IsManifold I 1 M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' 1 N]
  [RiemannianBundle (fun y : N ↦ TangentSpace I' y)]

/-- If the tangent map of `Φ` at `x` preserves the Riemannian inner products, then the volume
density of `M` in the chart at `α` is the volume density of `N` in the chart at `β` multiplied by
the absolute Jacobian determinant of `Φ` read in these two charts. -/
theorem chartVolumeDensity_eq_abs_det_mul_of_inner_mfderiv {Φ : M → N} {α x : M} {β : N}
    (hxα : x ∈ (chartAt H α).source) (hxβ : Φ x ∈ (chartAt H' β).source)
    (hinner : ∀ v w : TangentSpace I x,
      ⟪mfderiv I I' Φ x v, mfderiv I I' Φ x w⟫_ℝ = ⟪v, w⟫_ℝ) :
    chartVolumeDensity (I := I) α x =
      |(mfderiv I' 𝓘(ℝ, E) (extChartAt I' β) (Φ x) ∘L mfderiv I I' Φ x ∘L
        mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (range I) (extChartAt I α x) :
          E →L[ℝ] E).det| *
        chartVolumeDensity (I := I') β (Φ x) := by
  have hα : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hxα
  have hβ : Φ x ∈ (trivializationAt E (TangentSpace I') β).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hxβ
  set b := Module.finBasis ℝ E
  set bα := (trivializationAt E (TangentSpace I) α).basisAt b hα
  set bβ := (trivializationAt E (TangentSpace I') β).basisAt b hβ
  set L : E →L[ℝ] E := mfderiv I' 𝓘(ℝ, E) (extChartAt I' β) (Φ x) ∘L mfderiv I I' Φ x ∘L
        mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (range I) (extChartAt I α x)
  -- In the trivialization bases, the tangent map of `Φ` has the Jacobian matrix of `L`.
  have hmat : LinearMap.toMatrix bα bβ (mfderiv I I' Φ x).toLinearMap =
      LinearMap.toMatrix b b L.toLinearMap := by
    ext k i
    simp only [LinearMap.toMatrix_apply, bα, bβ, Trivialization.basisAt, Module.Basis.map_apply,
      Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_symm,
      Trivialization.linearEquivAt_symm_apply, Trivialization.linearEquivAt_apply]
    rw [← Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) _ hβ,
      ← Trivialization.symmL_apply (R := ℝ) _ hα, TangentBundle.symmL_trivializationAt hxα,
      TangentBundle.continuousLinearMapAt_trivializationAt hxβ]
    -- `L` evaluates the composite on `b i`. It is ascribed `E →L[ℝ] E`, while its factors act on
    -- tangent spaces of the model space, which are `E` only by definition, so
    -- `ContinuousLinearMap.comp_apply` does not match syntactically.
    rfl
  -- The inner product at `x` is pulled back from the one at `Φ x`, so the Gram matrices are
  -- congruent by that Jacobian matrix.
  have hform : innerₗ (TangentSpace I x) = LinearMap.BilinForm.comp
      (innerₗ (TangentSpace I' (Φ x))) (mfderiv I I' Φ x).toLinearMap
      (mfderiv I I' Φ x).toLinearMap := by
    ext v w
    simp [hinner]
  have hdet : (chartGramMatrix (I := I) α x).det =
      L.det ^ 2 * (chartGramMatrix (I := I') β (Φ x)).det := by
    rw [chartGramMatrix_eq_toMatrix α hα, chartGramMatrix_eq_toMatrix β hβ, hform,
      LinearMap.BilinForm.toMatrix_comp bβ bα, hmat, Matrix.det_mul, Matrix.det_mul,
      Matrix.det_transpose, LinearMap.det_toMatrix, ContinuousLinearMap.det]
    ring
  rw [chartVolumeDensity_def, hdet, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
    chartVolumeDensity_def]

section Measure

variable [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] [BorelSpace N]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun y : N ↦ TangentSpace I' y)]

attribute [local instance] extChartAtMeasurableSpaceE extChartAtBorelSpaceE

/-- A map which is injective on a measurable subset `s` of the chart source at
`α`, maps `s` into the chart source at `β`, and whose tangent maps at points of `s` preserve the
Riemannian inner products, carries the chart volume of `s` at `α` to the chart volume of its image
at `β`. Differentiability on `s` follows from the inner-product condition
(`TauCeti.mdifferentiableAt_of_inner_mfderiv`). -/
theorem chartRiemannianVolume_image_of_inner_mfderiv {Φ : M → N} {α : M} {β : N} {s : Set M}
    (hs : MeasurableSet s) (hinj : InjOn Φ s)
    (hsα : s ⊆ (chartAt H α).source) (hsβ : MapsTo Φ s (chartAt H' β).source)
    (hinner : ∀ x ∈ s, ∀ v w : TangentSpace I x,
      ⟪mfderiv I I' Φ x v, mfderiv I I' Φ x w⟫_ℝ = ⟪v, w⟫_ℝ) :
    chartRiemannianVolume (I := I') β (Φ '' s) = chartRiemannianVolume (I := I) α s := by
  -- This change-of-variables argument is adapted from the proof of
  -- `TauCeti.chartRiemannianVolume_restrict_overlap`.
  have hΦ (x : M) (hx : x ∈ s) : MDifferentiableAt I I' Φ x :=
    mdifferentiableAt_of_inner_mfderiv fun v ↦ hinner x hx v v
  have hsα' : s ⊆ (extChartAt I α).source := by rwa [extChartAt_source]
  have hsβ' : Φ '' s ⊆ (extChartAt I' β).source := by
    rw [extChartAt_source]; exact hsβ.image_subset
  rw [chartRiemannianVolume_apply α hs, inter_eq_left.2 hsα']
  -- Change variables along `Φ` read in the charts at `α` and `β`.
  let A := extChartAt I α '' s
  let g := extChartAt I' β ∘ Φ ∘ (extChartAt I α).symm
  have hA : MeasurableSet A := hs.image_extChartAt α hsα'
  have hA_range : A ⊆ range I :=
    (image_mono hsα').trans ((extChartAt I α).image_source_eq_target.subset.trans
      (extChartAt_target_subset_range α))
  have himage : g '' A = extChartAt I' β '' (Φ '' s) := by
    simp only [A, g, image_image]
    apply image_congr
    intro x hx
    simp only [Function.comp_apply, (extChartAt I α).left_inv (hsα' hx)]
  have hinjA : InjOn g A := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩ h
    simp only [g, Function.comp_apply, (extChartAt I α).left_inv (hsα' hx),
      (extChartAt I α).left_inv (hsα' hx')] at h
    rw [hinj hx hx' ((extChartAt I' β).injOn (hsβ' (mem_image_of_mem Φ hx))
      (hsβ' (mem_image_of_mem Φ hx')) h)]
  have hderiv (x : M) (hx : x ∈ s) :
      HasFDerivWithinAt g (mfderiv I' 𝓘(ℝ, E) (extChartAt I' β) (Φ x) ∘L mfderiv I I' Φ x ∘L
        mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (range I) (extChartAt I α x) :
          E →L[ℝ] E) (range I) (extChartAt I α x) :=
    (hΦ x hx).hasMFDerivAt.hasFDerivWithinAt_of_mem_source (hsα hx) (hsβ hx)
  have hg' (y : E) (hy : y ∈ A) : HasFDerivWithinAt g (fderivWithin ℝ g (range I) y) A y := by
    obtain ⟨x, hx, rfl⟩ := hy
    exact (hderiv x hx).differentiableWithinAt.hasFDerivWithinAt.mono hA_range
  have hΦs : MeasurableSet (Φ '' s) :=
    hs.image_of_continuousOn_injOn_extChartAt (fun x hx ↦ (hΦ x hx).continuousAt.continuousWithinAt)
      hinj hsα' fun x hx ↦ hsβ' (mem_image_of_mem Φ hx)
  rw [chartRiemannianVolume_apply β hΦs, inter_eq_left.2 hsβ', ← himage,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul (Module.finBasis ℝ E).addHaar hA hg' hinjA]
  apply setLIntegral_congr_fun hA
  rintro _ ⟨x, hx, rfl⟩
  dsimp only
  rw [(hderiv x hx).fderivWithin (I.uniqueDiffOn _ (hA_range (mem_image_of_mem _ hx))),
    (extChartAt I α).left_inv (hsα' hx)]
  simp only [g, Function.comp_apply, (extChartAt I α).left_inv (hsα' hx),
    (extChartAt I' β).left_inv (hsβ' (mem_image_of_mem Φ hx))]
  rw [chartVolumeDensity_eq_abs_det_mul_of_inner_mfderiv (β := β) (hsα hx) (hsβ hx)
    (hinner x hx), ENNReal.ofReal_mul (abs_nonneg _)]

/-- **Volume of an injective isometric image.** If `Φ` is injective on a measurable set `s` and
its tangent maps at points of `s` preserve the Riemannian inner products, then `Φ '' s` has the
Riemannian volume of `s`. The map is only required to be a local isometry along `s`; for instance,
a Riemannian covering map preserves the volume of every measurable set on which it is injective.
Differentiability of `Φ` along `s` follows from the inner-product condition
(`TauCeti.mdifferentiableAt_of_inner_mfderiv`), and measurability of the images of measurable
subsets of `s` from the Lusin–Souslin theorem
(`MeasurableSet.image_of_continuousOn_injOn_chartedSpace`). -/
theorem riemannianVolume_image_of_inner_mfderiv [LindelofSpace M] [LindelofSpace N]
    {Φ : M → N} {s : Set M} (hs : MeasurableSet s) (hinj : InjOn Φ s)
    (hinner : ∀ x ∈ s, ∀ v w : TangentSpace I x,
      ⟪mfderiv I I' Φ x v, mfderiv I I' Φ x w⟫_ℝ = ⟪v, w⟫_ℝ) :
    riemannianVolume I' N (Φ '' s) = riemannianVolume I M s := by
  -- A Lindelöf manifold modelled on a finite-dimensional space is second countable, hence
  -- hereditarily Lindelöf.
  have : SecondCountableTopology H := I.secondCountableTopology
  obtain ⟨c, hc, hcU⟩ := LindelofSpace.elim_nhds_subcover (fun x : M ↦ (chartAt H x).source)
    fun x ↦ chart_source_mem_nhds H x
  have : SecondCountableTopology M := ChartedSpace.secondCountable_of_countable_cover H hcU hc
  have hΦ (x : M) (hx : x ∈ s) : MDifferentiableAt I I' Φ x :=
    mdifferentiableAt_of_inner_mfderiv fun v ↦ hinner x hx v v
  -- Compare the measures `t ↦ vol (Φ '' t)` and `t ↦ vol t` on the subtype `s`. They agree near
  -- each point `x` of `s`, on the open set `V x` which lies in the chart source at `x` and is
  -- mapped by `Φ` into the chart source at `Φ x`.
  let V (x : M) : Set M := (chartAt H x).source ∩ interior (Φ ⁻¹' (chartAt H' (Φ x)).source)
  have hV_open (x : M) : IsOpen (V x) := (chartAt H x).open_source.inter isOpen_interior
  have hV (x : M) (hx : x ∈ s) : V x ∈ 𝓝 x :=
    (hV_open x).mem_nhds ⟨mem_chart_source H x, mem_interior_iff_mem_nhds.2 <|
      (hΦ x hx).continuousAt.preimage_mem_nhds (chart_source_mem_nhds H' (Φ x))⟩
  obtain ⟨T, hTc, -, hcover⟩ := (HereditarilyLindelofSpace.isLindelof s).elim_nhds_subcover V hV
  have hι : MeasurableEmbedding (Subtype.val : s → M) := .subtype_coe hs
  have hf_image (t : Set s) : s.domRestrict Φ '' t = Φ '' (Subtype.val '' t) := by
    rw [Set.domRestrict_eq, image_comp]
  -- Images of measurable subsets of `s` are measurable, by the Lusin–Souslin theorem.
  have hf : ∀ t, MeasurableSet t → MeasurableSet (s.domRestrict Φ '' t) := fun t ht ↦ by
    have hts := Subtype.coe_image_subset s t
    rw [hf_image]
    exact (hι.measurableSet_image' ht).image_of_continuousOn_injOn_chartedSpace I I'
      (fun y hy ↦ (hΦ y (hts hy)).continuousAt.continuousWithinAt) (hinj.mono hts)
  suffices h : (riemannianVolume I' N).comap (s.domRestrict Φ) =
      (riemannianVolume I M).comap Subtype.val by
    have h' := congr($h univ)
    rwa [Measure.comap_apply _ hinj.injective hf _ MeasurableSet.univ, hι.comap_apply,
      image_univ, image_univ, Set.range_domRestrict, Subtype.range_coe] at h'
  refine Measure.ext_of_biUnion_eq_univ (s := fun x ↦ (Subtype.val : s → M) ⁻¹' V x) hTc
    (by rw [← preimage_iUnion₂]; exact eq_univ_of_forall fun y ↦ hcover y.2)
    fun x _ ↦ ?_
  ext t ht
  have htV : MeasurableSet (t ∩ Subtype.val ⁻¹' V x) :=
    ht.inter ((hV_open x).measurableSet.preimage measurable_subtype_coe)
  set u := Subtype.val '' (t ∩ Subtype.val ⁻¹' V x)
  have hus : u ⊆ s := Subtype.coe_image_subset s _
  have huV : u ⊆ V x := by rintro _ ⟨y, hy, rfl⟩; exact hy.2
  have hmaps : MapsTo Φ u (chartAt H' (Φ x)).source := fun y hy ↦
    interior_subset (s := Φ ⁻¹' _) (huV hy).2
  rw [Measure.restrict_apply ht, Measure.restrict_apply ht,
    Measure.comap_apply _ hinj.injective hf _ htV, hι.comap_apply, hf_image,
    riemannianVolume_apply_of_subset (α := Φ x) hmaps.image_subset,
    riemannianVolume_apply_of_subset (α := x) (huV.trans inter_subset_left)]
  exact chartRiemannianVolume_image_of_inner_mfderiv (hι.measurableSet_image' htV)
    (hinj.mono hus) (huV.trans inter_subset_left) hmaps fun y hy ↦ hinner y (hus hy)

/-- **Isometry invariance of the Riemannian volume.** A homeomorphism whose tangent maps preserve
the Riemannian inner products carries the Riemannian volume of `M` to the Riemannian volume of
`N`. Differentiability of the homeomorphism follows from the inner-product condition
(`TauCeti.mdifferentiableAt_of_inner_mfderiv`). -/
theorem _root_.Homeomorph.measurePreserving_riemannianVolume [LindelofSpace M] [LindelofSpace N]
    (Φ : M ≃ₜ N)
    (hinner : ∀ x (v w : TangentSpace I x),
      ⟪mfderiv I I' Φ x v, mfderiv I I' Φ x w⟫_ℝ = ⟪v, w⟫_ℝ) :
    MeasurePreserving Φ (riemannianVolume I M) (riemannianVolume I' N) := by
  refine ⟨Φ.measurable, Measure.ext fun s hs ↦ ?_⟩
  rw [Measure.map_apply Φ.measurable hs, ← riemannianVolume_image_of_inner_mfderiv
    (hs.preimage Φ.measurable) Φ.injective.injOn fun x _ ↦ hinner x, Φ.image_preimage]

end Measure

namespace RiemannianIsometry

variable [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] [BorelSpace N]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun y : N ↦ TangentSpace I' y)]

/-- A Riemannian isometry preserves the Riemannian volume measure.

This packages the general homeomorphism theorem at the canonical `RiemannianIsometry` API. -/
theorem measurePreserving_riemannianVolume [LindelofSpace M] [LindelofSpace N]
    (Φ : RiemannianIsometry I I' M N) :
    MeasurePreserving Φ (riemannianVolume I M) (riemannianVolume I' N) := by
  have h := Φ.toDiffeomorph.toHomeomorph.measurePreserving_riemannianVolume (I := I) (I' := I') ?_
  · rwa [Diffeomorph.coe_toHomeomorph, coe_toDiffeomorph] at h
  · intro x v w
    rw [Diffeomorph.coe_toHomeomorph, coe_toDiffeomorph]
    exact Φ.inner_mfderiv x v w

end RiemannianIsometry

end TauCeti
