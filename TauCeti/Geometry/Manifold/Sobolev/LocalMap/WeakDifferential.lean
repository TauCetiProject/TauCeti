/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Sobolev.LocalMap
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Analysis.Sobolev.W1p.ChangeOfVariables
import TauCeti.Analysis.Sobolev.WeakDeriv.ChainRule
import TauCeti.Analysis.Sobolev.WeakDeriv.Local
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Topology.OpenPartialHomeomorph.Continuity
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.IsManifold.RestrictScalars
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.ExtChartAt

/-!
# The weak differential of a local Sobolev map

Let `X` be a Riemann surface without boundary, given as a charted space modelled on `ℂ` with
holomorphic coordinate changes, and let `M` be a manifold modelled on a boundaryless model `I`
with model vector space `F`. A map `u : X → M` in the local Sobolev class `W^{1,p}_loc` has a
differential defined almost everywhere: a field `du` of real-linear maps `T_x X → T_{u x} M`,
that is a section of `Hom(TX, u*TM)`, whose coordinate expressions are the weak derivatives of the
coordinate expressions of `u`. This file defines this notion and shows that the weak differential
exists, is unique almost everywhere, and is the differential for maps of class `C¹`.

Precisely, `TauCeti.chartDifferential I φ ψ u du` reads the field `du` in a holomorphic chart `φ`
of `X` and a chart `ψ` of `M`: at `z` it is `dψ ∘ du(φ⁻¹ z) ∘ dφ⁻¹`, a real-linear map `ℂ → F`.
The field `du` is a **weak differential** of `u` on `s` (`TauCeti.HasWeakMFDerivOn I u du s`) when
in every such pair of charts the field read in charts is a weak derivative of the coordinate
expression `ψ̂ ∘ u ∘ φ⁻¹` on the part of the target of `φ` over `s` where `u` maps into the source
of `ψ`. The tangent spaces of `X` and `M` are `ℂ` and `F`, and sets of measure zero of `X` are
read in its charts.

## Main results

* `TauCeti.chartDifferential_eq_comp`: under a change of charts, the field read in charts changes
  by the derivatives of the coordinate changes of `X` and of `M`.
* `TauCeti.hasWeakMFDerivOn_iff_of_subset_maximalAtlas` and `TauCeti.hasWeakMFDerivOn_iff_chartAt`:
  for `u` continuous on an open set, it suffices to test charts covering the set and its image,
  for instance the preferred charts.
* `TauCeti.HasWeakMFDerivOn.ae_eq`: two weak differentials agree almost everywhere in every chart.
  Conversely, a field agreeing almost everywhere in every chart with a weak differential is one
  (`TauCeti.HasWeakMFDerivOn.congr_ae_deriv`).
* `TauCeti.MemWkpLocMapOn.exists_hasWeakMFDerivOn`: on an open subset of a second countable Riemann
  surface, every map in `W^{1,p}_loc` has a weak differential, and its coordinate expressions are
  locally `Lᵖ` (`TauCeti.HasWeakMFDerivOn.memLpLoc_chartDifferential`).
* `TauCeti.memWkpLocMapOn_one_iff`: a continuous map is in `W^{1,p}_loc` exactly when it has a
  weak differential and the coordinate expressions of the map and of its weak differential are
  locally `Lᵖ`.
* `ContMDiffOn.hasWeakMFDerivOn_mfderiv`: the differential of a map of class `C¹` on an open set
  is a weak differential there. For example, the weak differential of `z ↦ conj z` on `ℂ` is the
  constant conjugation map (`TauCeti.hasWeakMFDerivOn_conj`).

## Implementation notes

A weak differential is determined only almost everywhere, so the existence theorem chooses one.
It picks a weak derivative of the coordinate expression in each pair of charts, covers `s` by
countably many domains of pairs of preferred charts, and at each point of `s` transports the
weak derivative of one pair of preferred charts containing it. In another pair of charts this
field agrees with the chosen weak derivative almost everywhere on each of the countably many
pieces, by the transformation law and the uniqueness of weak derivatives; second countability of
`X` makes the pieces countable. The model of `M` is boundaryless so that its coordinate changes are
smooth on open sets, where the planar chain rule applies.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1.
-/

public section

open Set TopologicalSpace MeasureTheory
open scoped Manifold ContDiff

noncomputable section

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {p : ENNReal} {u : X → M} {s : Set X}

variable (I) in
/-- A field `du` of real-linear maps `T_x X → T_{u x} M` along `u : X → M`, read in a chart `φ`
of `X` and a chart `ψ` of `M`: at `z`, the composite `dψ ∘ du(φ⁻¹ z) ∘ dφ⁻¹`, a real-linear map
`ℂ → F`. -/
def chartDifferential (φ : OpenPartialHomeomorph X ℂ) (ψ : OpenPartialHomeomorph M H)
    (u : X → M) (du : ∀ x, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace I (u x)) (z : ℂ) :
    ℂ →L[ℝ] F :=
  mvfderiv I (ψ.extend I) (u (φ.symm z)) ∘L du (φ.symm z) ∘L
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) φ.symm z

/-- Unfolding the differential read in charts. -/
theorem chartDifferential_def (φ : OpenPartialHomeomorph X ℂ) (ψ : OpenPartialHomeomorph M H)
    (du : ∀ x, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace I (u x)) (z : ℂ) :
    chartDifferential I φ ψ u du z = mvfderiv I (ψ.extend I) (u (φ.symm z)) ∘L du (φ.symm z) ∘L
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) φ.symm z :=
  (rfl)

variable (I) in
/-- **Weak differentials.** A field `du` of real-linear maps `T_x X → T_{u x} M` along `u : X → M`
is a weak differential of `u` on `s` when, for every holomorphic chart `φ` of `X` and every
smooth chart `ψ` of `M`, the field read in these charts (`TauCeti.chartDifferential`) is a weak
derivative of the coordinate expression `ψ̂ ∘ u ∘ φ⁻¹` on the interior of the part of the target
of `φ` over `s` where `u` maps into the source of `ψ`. The definition is intended for open `s`
and `u` continuous on `s`, where these parts are open. -/
def HasWeakMFDerivOn (u : X → M) (du : ∀ x, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace I (u x))
    (s : Set X) : Prop :=
  ∀ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
    HasWeakFDerivOn volume (Opens.interior (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)))
      (ψ.extend I ∘ u ∘ φ.symm) (chartDifferential I φ ψ u du)

/-- Unfolding the definition of weak differentials. -/
theorem hasWeakMFDerivOn_iff {du : ∀ x, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace I (u x)} :
    HasWeakMFDerivOn I u du s ↔
      ∀ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
        HasWeakFDerivOn volume (Opens.interior (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)))
          (ψ.extend I ∘ u ∘ φ.symm) (chartDifferential I φ ψ u du) :=
  Iff.rfl

/-- A weak differential on `s` is a weak differential on every subset of `s`. -/
theorem HasWeakMFDerivOn.mono {du : ∀ x, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace I (u x)}
    {t : Set X} (h : HasWeakMFDerivOn I u du s) (hts : t ⊆ s) : HasWeakMFDerivOn I u du t :=
  fun φ hφ ψ hψ ↦ (h φ hφ ψ hψ).mono (interior_mono
    (inter_subset_inter_right _ (preimage_mono (inter_subset_inter_left _ hts))))

omit [ChartedSpace ℂ X] [ChartedSpace H M] in
/-- For `u` continuous on an open set `s`, the part of the target of a chart `φ` lying over `s`
where `u` maps into the source of `ψ` is open, hence its own interior. -/
private theorem coe_interior_chartDomain (hs : IsOpen s) (hc : ContinuousOn u s)
    (φ : OpenPartialHomeomorph X ℂ) (ψ : OpenPartialHomeomorph M H) :
    (Opens.interior (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) : Set ℂ) =
      φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source) := by
  rw [Opens.coe_interior,
    (φ.isOpen_inter_preimage_symm_inter_preimage hc hs ψ.open_source).interior_eq]

section ChartChange

variable [I.Boundaryless]

/-- **Change of chart for a differential read in charts.** At a point `z` where two pairs of
charts `(φ, ψ)` and `(φ', ψ')` are both defined along `u`, the differential read in `(φ, ψ)` is
the one read in `(φ', ψ')` at `φ' (φ⁻¹ z)`, composed with the derivatives of the changes of chart
`φ' ∘ φ⁻¹` of `X` and `ψ̂ ∘ ψ̂'⁻¹ = I.extendCoordChange ψ' ψ` of `M`. -/
theorem chartDifferential_eq_comp {φ φ' : OpenPartialHomeomorph X ℂ}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X) (hφ' : φ' ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    {ψ ψ' : OpenPartialHomeomorph M H} (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M)
    (hψ' : ψ' ∈ IsManifold.maximalAtlas I ∞ M)
    (du : ∀ x, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace I (u x)) {z : ℂ} (hz : z ∈ φ.target)
    (hzφ' : φ.symm z ∈ φ'.source) (hzψ : u (φ.symm z) ∈ ψ.source)
    (hzψ' : u (φ.symm z) ∈ ψ'.source) :
    chartDifferential I φ ψ u du z =
      fderiv ℝ (I.extendCoordChange ψ' ψ) (ψ'.extend I (u (φ.symm z))) ∘L
        chartDifferential I φ' ψ' u du (φ' (φ.symm z)) ∘L fderiv ℝ (φ' ∘ φ.symm) z := by
  set x := φ.symm z
  have hφR := IsManifold.maximalAtlas_subset_restrictScalars ℝ (M := X) hφ
  have hφ'R := IsManifold.maximalAtlas_subset_restrictScalars ℝ (M := X) hφ'
  -- The derivative of the chart of `M` factors through the change of chart.
  have h1 : mvfderiv I (ψ.extend I) (u x) =
      fderiv ℝ (I.extendCoordChange ψ' ψ) (ψ'.extend I (u x)) ∘L
        mvfderiv I (ψ'.extend I) (u x) := by
    have hΘ := I.contDiffOn_extendCoordChange hψ' hψ
    have hw : ψ'.extend I (u x) ∈ (I.extendCoordChange ψ' ψ).source :=
      ⟨(ψ'.extend I).map_source (by simpa using hzψ'), by
        simpa [ψ'.left_inv hzψ'] using hzψ⟩
    have hev : ψ.extend I =ᶠ[nhds (u x)] I.extendCoordChange ψ' ψ ∘ ψ'.extend I := by
      filter_upwards [(ψ.open_source.inter ψ'.open_source).mem_nhds ⟨hzψ, hzψ'⟩] with y hy
      simp [ψ'.left_inv hy.2]
    ext v
    rw [hev.mvfderiv_eq, ContinuousLinearMap.comp_apply, mvfderiv_comp_apply_of_differentiableAt
      ((hΘ.contDiffAt (I.isOpen_extendCoordChange_source.mem_nhds hw)).differentiableAt (by simp))
      ((ψ'.contMDiffAt_extend hψ' hzψ').mdifferentiableAt (by simp))]
  -- The derivative of the inverse chart of `X` factors through the change of chart.
  have h2 : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) φ.symm z =
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) φ'.symm (φ' x) ∘L fderiv ℝ (φ' ∘ φ.symm) z := by
    have hzs : z ∈ (φ.symm.trans φ').source := ⟨hz, hzφ'⟩
    have hτ : DifferentiableAt ℝ (φ' ∘ φ.symm) z :=
      (contDiffAt_symm_trans_of_mem_maximalAtlas hφR hφ'R hzs).differentiableAt (by simp)
    have hev : φ.symm =ᶠ[nhds z] φ'.symm ∘ (φ' ∘ φ.symm) := by
      filter_upwards [(φ.symm.trans φ').open_source.mem_nhds hzs] with w hw
      exact (φ'.left_inv hw.2).symm
    rw [hev.mfderiv_eq, mfderiv_comp_of_eq
      (mdifferentiableAt_symm_of_mem_maximalAtlas hφ'R (φ'.map_source hzφ'))
      hτ.mdifferentiableAt rfl, mfderiv_eq_fderiv]
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      NormedSpace.fromTangentSpace_apply, NormedSpace.fromTangentSpace_symm_apply]
    -- `tangentSpaceCast` transports along `φ'.symm (φ' x) = x`.
    exact eq_of_heq (heq_tangentSpaceCast (φ'.left_inv hzφ') _)
  rw [chartDifferential_def, chartDifferential_def, φ'.left_inv hzφ', h1, h2]
  -- Both sides are the same composite, associated differently. `ContinuousLinearMap.comp_assoc`
  -- does not apply: the composite passes between `TangentSpace 𝓘(ℝ, ℂ) _` and `ℂ`, whose
  -- module instances agree only after unfolding `TangentSpace`.
  rfl

/-- **Change of chart for weak derivatives of coordinate expressions.** Let `u` be continuous on
an open set `s`, and let `G` be a weak derivative of the coordinate expression of `u` in charts
`(φ', ψ')` on the interior of its coordinate domain over `s`. Then on every open set `W` lying
over `s` where both pairs of charts are defined along `u`, the coordinate expression in `(φ, ψ)`
has the weak derivative obtained from `G` by composing with the derivatives of the changes of
chart. -/
private theorem HasWeakFDerivOn.comp_chartChange (hs : IsOpen s) (hcu : ContinuousOn u s)
    {φ φ' : OpenPartialHomeomorph X ℂ}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X) (hφ' : φ' ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    {ψ ψ' : OpenPartialHomeomorph M H} (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M)
    (hψ' : ψ' ∈ IsManifold.maximalAtlas I ∞ M) {W : Opens ℂ}
    (hW : (W : Set ℂ) ⊆ φ.target ∩ φ.symm ⁻¹' (φ'.source ∩ (s ∩ u ⁻¹' (ψ.source ∩ ψ'.source))))
    {G : ℂ → ℂ →L[ℝ] F} (hG : HasWeakFDerivOn volume
      (Opens.interior (φ'.target ∩ φ'.symm ⁻¹' (s ∩ u ⁻¹' ψ'.source)))
      (ψ'.extend I ∘ u ∘ φ'.symm) G) :
    HasWeakFDerivOn volume W (ψ.extend I ∘ u ∘ φ.symm) fun z ↦
      fderiv ℝ (I.extendCoordChange ψ' ψ) (ψ'.extend I (u (φ.symm z))) ∘L
        G (φ' (φ.symm z)) ∘L fderiv ℝ (φ' ∘ φ.symm) z := by
  have := hG.completeSpace
  have hφR := IsManifold.maximalAtlas_subset_restrictScalars ℝ (M := X) hφ
  have hφ'R := IsManifold.maximalAtlas_subset_restrictScalars ℝ (M := X) hφ'
  have hΘ := I.contDiffOn_extendCoordChange hψ' hψ
  have hWs : (W : Set ℂ) ⊆ (φ.symm.trans φ').source := fun z hz ↦ ⟨(hW hz).1, (hW hz).2.1⟩
  have hWW' : MapsTo (φ' ∘ φ.symm) W
      (Opens.interior (φ'.target ∩ φ'.symm ⁻¹' (s ∩ u ⁻¹' ψ'.source))) := fun w hw ↦ by
    obtain ⟨-, hwφ', hws, -, hwψ'⟩ := hW hw
    rw [coe_interior_chartDomain hs hcu φ' ψ']
    refine ⟨φ'.map_source hwφ', ?_⟩
    simpa [φ'.left_inv hwφ'] using And.intro hws hwψ'
  have hc : ContinuousOn (ψ'.extend I ∘ u ∘ φ'.symm)
      (Opens.interior (φ'.target ∩ φ'.symm ⁻¹' (s ∩ u ⁻¹' ψ'.source))) := by
    rw [coe_interior_chartDomain hs hcu φ' ψ']
    exact φ'.continuousOn_comp_comp_symm (ψ'.continuousOn_extend.mono ψ'.extend_source.ge) hcu
  have hτ : ContDiffOn ℝ 1 (φ' ∘ φ.symm) W := by
    simpa only [OpenPartialHomeomorph.coe_trans] using
      (contDiffOn_symm_trans_of_mem_maximalAtlas hφR hφ'R).mono hWs
  have hinj : InjOn (φ' ∘ φ.symm) W := by
    simpa only [OpenPartialHomeomorph.coe_trans] using (φ.symm.trans φ').injOn.mono hWs
  have hdet : ∀ z ∈ (W : Set ℂ), (fderiv ℝ (φ' ∘ φ.symm) z).det ≠ 0 := fun z hz ↦ by
    simpa only [OpenPartialHomeomorph.coe_trans] using
      det_fderiv_symm_trans_ne_zero one_ne_zero hφR hφ'R (hWs hz)
  have hmaps : MapsTo ((ψ'.extend I ∘ u ∘ φ'.symm) ∘ (φ' ∘ φ.symm)) W
      (I.extendCoordChange ψ' ψ).source := fun z hz ↦ by
    obtain ⟨-, hzφ', -, hzψ, hzψ'⟩ := hW hz
    simp only [Function.comp_apply, φ'.left_inv hzφ']
    exact ⟨(ψ'.extend I).map_source (by simpa using hzψ'), by simpa [ψ'.left_inv hzψ'] using hzψ⟩
  have h := (hG.comp_contDiffOn_diffeo hτ hinj hdet hWW').contDiffOn_comp
    (hc.comp hτ.continuousOn hWW') I.isOpen_extendCoordChange_source (hΘ.of_le (by simp))
    hmaps
  refine (h.congr_ae (ae_restrict_of_forall_mem W.isOpen.measurableSet fun z hz ↦ ?_))
    |>.congr_ae_deriv (ae_restrict_of_forall_mem W.isOpen.measurableSet fun z hz ↦ ?_)
  · obtain ⟨-, hzφ', -, -, hzψ'⟩ := hW hz
    simp [φ'.left_inv hzφ', ψ'.left_inv hzψ']
  · obtain ⟨-, hzφ', -⟩ := hW hz
    simp only [Function.comp_apply, φ'.left_inv hzφ']

/-- **Chart independence of weak differentials.** For `u` continuous on an open set `s`, it
suffices to test the coordinate expressions in the charts of a family `A` of holomorphic charts
covering `s` and a family `B` of charts of `M` covering `u '' s`. -/
theorem hasWeakMFDerivOn_iff_of_subset_maximalAtlas [CompleteSpace F] (hs : IsOpen s)
    (hc : ContinuousOn u s)
    {A : Set (OpenPartialHomeomorph X ℂ)} (hA : A ⊆ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    (hAs : ∀ x ∈ s, ∃ φ ∈ A, x ∈ φ.source)
    {B : Set (OpenPartialHomeomorph M H)} (hB : B ⊆ IsManifold.maximalAtlas I ∞ M)
    (hBs : ∀ x ∈ s, ∃ ψ ∈ B, u x ∈ ψ.source)
    {du : ∀ x, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace I (u x)} :
    HasWeakMFDerivOn I u du s ↔ ∀ φ ∈ A, ∀ ψ ∈ B,
      HasWeakFDerivOn volume (Opens.interior (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)))
        (ψ.extend I ∘ u ∘ φ.symm) (chartDifferential I φ ψ u du) := by
  refine ⟨fun h φ hφ ψ hψ ↦ h φ (hA hφ) ψ (hB hψ), fun h φ hφ ψ hψ ↦ ?_⟩
  refine hasWeakFDerivOn_iff_locally.2 fun z hz ↦ ?_
  have hz' : z ∈ φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source) := interior_subset hz
  obtain ⟨φ', hφ'A, hxφ'⟩ := hAs _ hz'.2.1
  obtain ⟨ψ', hψ'B, hxψ'⟩ := hBs _ hz'.2.1
  -- Near `z` both pairs of charts are defined along `u`.
  let W : Opens ℂ := ⟨φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' (ψ.source ∩ ψ'.source) ∩ φ'.source),
    φ.isOpen_inter_preimage_symm ((hc.isOpen_inter_preimage hs
      (ψ.open_source.inter ψ'.open_source)).inter φ'.open_source)⟩
  refine ⟨W, ⟨hz'.1, ⟨hz'.2.1, hz'.2.2, hxψ'⟩, hxφ'⟩, ?_⟩
  refine ((h φ' hφ'A ψ' hψ'B).comp_chartChange hs hc hφ (hA hφ'A) hψ (hB hψ'B) (W := W)
    fun w hw ↦ ⟨hw.1, hw.2.2, hw.2.1⟩).congr_ae_deriv
    (ae_restrict_of_forall_mem W.isOpen.measurableSet fun w hw ↦ ?_)
  exact (chartDifferential_eq_comp hφ (hA hφ'A) hψ (hB hψ'B) du hw.1 hw.2.2 hw.2.1.2.1
    hw.2.1.2.2).symm

/-- **Chart independence of weak differentials, in the preferred charts.** For `u` continuous on
an open set `s`, it suffices to test the coordinate expressions in the preferred charts of `X` and
`M`. -/
theorem hasWeakMFDerivOn_iff_chartAt [IsManifold 𝓘(ℂ) 1 X] [IsManifold I ∞ M] [CompleteSpace F]
    (hs : IsOpen s) (hc : ContinuousOn u s)
    {du : ∀ x, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace I (u x)} :
    HasWeakMFDerivOn I u du s ↔ ∀ x : X, ∀ y : M,
      HasWeakFDerivOn volume (Opens.interior ((chartAt ℂ x).target ∩
          (chartAt ℂ x).symm ⁻¹' (s ∩ u ⁻¹' (chartAt H y).source)))
        ((chartAt H y).extend I ∘ u ∘ (chartAt ℂ x).symm)
        (chartDifferential I (chartAt ℂ x) (chartAt H y) u du) := by
  rw [hasWeakMFDerivOn_iff_of_subset_maximalAtlas hs hc (A := range (chartAt ℂ))
    (range_subset_iff.2 IsManifold.chart_mem_maximalAtlas)
    (fun x _ ↦ ⟨_, mem_range_self x, mem_chart_source ℂ x⟩) (B := range (chartAt H))
    (range_subset_iff.2 IsManifold.chart_mem_maximalAtlas)
    fun x _ ↦ ⟨_, mem_range_self (u x), mem_chart_source H (u x)⟩]
  simp only [forall_mem_range]

end ChartChange

section Uniqueness

/-- **Uniqueness of weak differentials.** Two weak differentials of `u` on `s` agree almost
everywhere in every holomorphic chart. -/
theorem HasWeakMFDerivOn.ae_eq {du₁ du₂ : ∀ x, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace I (u x)}
    (h₁ : HasWeakMFDerivOn I u du₁ s) (h₂ : HasWeakMFDerivOn I u du₂ s)
    {φ : OpenPartialHomeomorph X ℂ} (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    {ψ : OpenPartialHomeomorph M H} (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M) :
    ∀ᵐ z ∂volume.restrict (interior (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source))),
      du₁ (φ.symm z) = du₂ (φ.symm z) := by
  filter_upwards [(h₁ φ hφ ψ hψ).ae_eq (h₂ φ hφ ψ hψ), ae_restrict_mem measurableSet_interior]
    with z hz hzU
  have hzU' := interior_subset hzU
  have hA := isInvertible_mvfderiv_extend (IsManifold.maximalAtlas_subset_of_le (by simp) hψ)
    hzU'.2.2
  have hC := isInvertible_mfderiv_chart_symm
    (IsManifold.maximalAtlas_subset_restrictScalars ℝ (M := X) hφ) hzU'.1
  -- Cancel the invertible derivatives of the charts on both sides.
  ext v
  obtain ⟨w, rfl⟩ := hC.surjective v
  exact hA.injective (DFunLike.congr_fun hz w)

/-- A field agreeing almost everywhere in every chart with a weak differential of `u` on `s` is
again a weak differential of `u` on `s`. -/
theorem HasWeakMFDerivOn.congr_ae_deriv
    {du₁ du₂ : ∀ x, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace I (u x)}
    (h : HasWeakMFDerivOn I u du₁ s)
    (hae : ∀ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
      ∀ᵐ z ∂volume.restrict (interior (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source))),
        du₁ (φ.symm z) = du₂ (φ.symm z)) :
    HasWeakMFDerivOn I u du₂ s := fun φ hφ ψ hψ ↦
  (h φ hφ ψ hψ).congr_ae_deriv <| (hae φ hφ ψ hψ).mono fun z hz ↦ by
    rw [chartDifferential_def, chartDifferential_def, hz]

end Uniqueness

/-- The coordinate expressions of a weak differential of a local Sobolev map of order one are
locally `Lᵖ`. -/
theorem HasWeakMFDerivOn.memLpLoc_chartDifferential
    {du : ∀ x, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace I (u x)} (hdu : HasWeakMFDerivOn I u du s)
    (hu : MemWkpLocMapOn I p 1 u s) (hs : IsOpen s) {φ : OpenPartialHomeomorph X ℂ}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X) {ψ : OpenPartialHomeomorph M H}
    (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M) :
    MemLpLoc p (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) (chartDifferential I φ ψ u du) := by
  obtain ⟨D, hD, hDp⟩ := (hu.memWkpLoc_chart hφ hψ).exists_weakFDeriv
  have hae := hD.ae_eq (hdu φ hφ ψ hψ)
  rw [coe_interior_chartDomain hs hu.continuousOn φ ψ] at hae
  exact (memWkpLoc_zero_iff.1 hDp).congr_ae hae

section Existence

variable [IsManifold 𝓘(ℂ) 1 X] [IsManifold I ∞ M] [I.Boundaryless]

omit [I.Boundaryless] in
/-- In the chart pair at which it is built, a field defined from a weak derivative `D` of the
coordinate expression reads as `D`. -/
private theorem chartDifferential_chartAt (t : X)
    {du : ∀ x, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace I (u x)} {D : ℂ → ℂ →L[ℝ] F} {x : X}
    (hx : x ∈ (chartAt ℂ t).source) (hux : u x ∈ (chartAt H (u t)).source)
    (hdu : du x = (mvfderiv I ((chartAt H (u t)).extend I) (u x)).inverse ∘L
      D (chartAt ℂ t x) ∘L
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (chartAt ℂ t).symm (chartAt ℂ t x)).inverse) :
    chartDifferential I (chartAt ℂ t) (chartAt H (u t)) u du (chartAt ℂ t x) =
      D (chartAt ℂ t x) := by
  have hA := isInvertible_mvfderiv_extend (IsManifold.maximalAtlas_subset_of_le (m := 1) (n := ∞)
    (by simp) (IsManifold.chart_mem_maximalAtlas (I := I) (u t))) hux
  have hC := isInvertible_mfderiv_chart_symm
    (IsManifold.maximalAtlas_subset_restrictScalars ℝ (M := X)
      (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ)) (n := 1) t)) ((chartAt ℂ t).map_source hx)
  rw [chartDifferential_def, (chartAt ℂ t).left_inv hx, hdu]
  ext v
  -- The composite unfolds pointwise to `A (A⁻¹ (D (C⁻¹ (C v))))`.
  exact (hA.self_apply_inverse _).trans (congrArg (D _) (hC.inverse_apply_self v))

/-- **Gluing on one preferred chart.** Let `D` be a weak derivative of the coordinate expression
of `u` in `(φ, ψ)`, and `Dₜ` one in the preferred charts at `t`. Let `du` be built from `Dₜ` at the
points satisfying `P`. Then, almost everywhere on the part of the coordinate domain of `(φ, ψ)`
lying over the preferred chart domain at `t`, the differential read in `(φ, ψ)` is `D` at the
points satisfying `P`. -/
private theorem ae_eq_chartDifferential_of_chartAt (hs : IsOpen s) (hc : ContinuousOn u s)
    {φ : OpenPartialHomeomorph X ℂ} (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    {ψ : OpenPartialHomeomorph M H} (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M) (t : X)
    {D Dₜ : ℂ → ℂ →L[ℝ] F}
    (hD : HasWeakFDerivOn volume (Opens.interior (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)))
      (ψ.extend I ∘ u ∘ φ.symm) D)
    (hDₜ : HasWeakFDerivOn volume (Opens.interior ((chartAt ℂ t).target ∩
        (chartAt ℂ t).symm ⁻¹' (s ∩ u ⁻¹' (chartAt H (u t)).source)))
      ((chartAt H (u t)).extend I ∘ u ∘ (chartAt ℂ t).symm) Dₜ)
    {du : ∀ x, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace I (u x)} {P : X → Prop}
    (hdu : ∀ x, P x → du x = (mvfderiv I ((chartAt H (u t)).extend I) (u x)).inverse ∘L
      Dₜ (chartAt ℂ t x) ∘L
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (chartAt ℂ t).symm (chartAt ℂ t x)).inverse) :
    ∀ᵐ z ∂volume, z ∈ φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source ∩
        ((chartAt ℂ t).source ∩ (s ∩ u ⁻¹' (chartAt H (u t)).source))) →
      P (φ.symm z) → D z = chartDifferential I φ ψ u du z := by
  have hφt := IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ)) (n := 1) t
  have hψt := IsManifold.chart_mem_maximalAtlas (I := I) (n := ∞) (u t)
  let W : Opens ℂ := ⟨_, φ.isOpen_inter_preimage_symm
    ((hc.isOpen_inter_preimage hs ψ.open_source).inter ((chartAt ℂ t).open_source.inter
      (hc.isOpen_inter_preimage hs (chartAt H (u t)).open_source)))⟩
  -- On `W`, `D` and the weak derivative transported from `Dₜ` agree almost everywhere.
  have hT := hDₜ.comp_chartChange hs hc hφ hφt hψ hψt (W := W)
    fun w hw ↦ ⟨hw.1, hw.2.2.1, hw.2.1.1, hw.2.1.2, hw.2.2.2.2⟩
  have hDW := hD.mono (Ω' := W) fun w hw ↦ by
    rw [← SetLike.mem_coe, coe_interior_chartDomain hs hc φ ψ]
    exact ⟨hw.1, hw.2.1⟩
  filter_upwards [(ae_restrict_iff' W.isOpen.measurableSet).1 (hDW.ae_eq hT)] with z hz hzW hPz
  obtain ⟨hzφ, ⟨hzs, hzψ⟩, hzt, hzs', hzψt⟩ := hzW
  rw [hz ⟨hzφ, ⟨hzs, hzψ⟩, hzt, hzs', hzψt⟩, chartDifferential_eq_comp hφ hφt hψ hψt _ hzφ hzt
    hzψ hzψt, chartDifferential_chartAt t hzt hzψt (hdu _ hPz)]

/-- **Existence of weak differentials.** On an open subset `s` of a second countable Riemann
surface, every local Sobolev map of order one has a weak differential. -/
theorem MemWkpLocMapOn.exists_hasWeakMFDerivOn [SecondCountableTopology X]
    (hu : MemWkpLocMapOn I p 1 u s) (hs : IsOpen s) :
    ∃ du : ∀ x, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace I (u x), HasWeakMFDerivOn I u du s := by
  classical
  have hc := hu.continuousOn
  -- Choose a weak derivative of the coordinate expression in every pair of charts.
  have hD : ∀ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
      ∃ D : ℂ → ℂ →L[ℝ] F, HasWeakFDerivOn volume
        (Opens.interior (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source))) (ψ.extend I ∘ u ∘ φ.symm) D :=
    fun φ hφ ψ hψ ↦
      let ⟨D, hD, _⟩ := (hu.memWkpLoc_chart hφ hψ).exists_weakFDeriv
      ⟨D, hD⟩
  choose! D hD using hD
  -- Countably many pairs of preferred charts cover `s`; choose one at every point of `s`.
  let V : X → Set X := fun t ↦ (chartAt ℂ t).source ∩ (s ∩ u ⁻¹' (chartAt H (u t)).source)
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable V fun t ↦
    (chartAt ℂ t).open_source.inter (hc.isOpen_inter_preimage hs (chartAt H (u t)).open_source)
  have hcov : ∀ x ∈ s, ∃ t ∈ T, x ∈ V t := fun x hx ↦ by
    have : x ∈ ⋃ t ∈ T, V t :=
      hTU ▸ mem_iUnion.2 ⟨x, mem_chart_source ℂ x, hx, mem_chart_source H (u x)⟩
    simpa only [mem_iUnion, exists_prop] using this
  choose! τ hτT hτV using hcov
  -- At `x`, transport the chosen weak derivative in the charts at `τ x` back to `x`.
  let L : X → ∀ x, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace I (u x) := fun t x ↦
    (mvfderiv I ((chartAt H (u t)).extend I) (u x)).inverse ∘L
      D (chartAt ℂ t) (chartAt H (u t)) (chartAt ℂ t x) ∘L
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (chartAt ℂ t).symm (chartAt ℂ t x)).inverse
  refine ⟨fun x ↦ L (τ x) x, fun φ hφ ψ hψ ↦ (hD φ hφ ψ hψ).congr_ae_deriv ?_⟩
  -- Glue the countably many chart pieces.
  have hloc : ∀ t ∈ T, ∀ᵐ z ∂volume, z ∈ φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source ∩ V t) →
      τ (φ.symm z) = t → D φ ψ z = chartDifferential I φ ψ u (fun x ↦ L (τ x) x) z :=
    fun t _ ↦ ae_eq_chartDifferential_of_chartAt hs hc hφ hψ t (hD φ hφ ψ hψ)
      (hD _ (IsManifold.chart_mem_maximalAtlas t) _ (IsManifold.chart_mem_maximalAtlas (u t)))
      fun x (hx : τ x = t) ↦ by rw [hx]; rfl
  rw [Filter.EventuallyEq, ae_restrict_iff' (Opens.interior _).isOpen.measurableSet]
  filter_upwards [(ae_ball_iff hTc).2 hloc] with z hz hzU
  rw [coe_interior_chartDomain hs hc φ ψ] at hzU
  exact hz _ (hτT _ hzU.2.1) ⟨hzU.1, hzU.2, hτV _ hzU.2.1⟩ rfl

/-- **Local Sobolev maps of order one through their weak differentials.** On an open subset `s`
of a second countable Riemann surface, `u` is in `W^{1,p}_loc` exactly when it is continuous on
`s` and has a weak differential such that the coordinate expressions of `u` and of the weak
differential are locally `Lᵖ`. -/
theorem memWkpLocMapOn_one_iff [SecondCountableTopology X] (hs : IsOpen s) :
    MemWkpLocMapOn I p 1 u s ↔ ContinuousOn u s ∧
      ∃ du : ∀ x, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace I (u x), HasWeakMFDerivOn I u du s ∧
        ∀ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
          MemLpLoc p (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) (ψ.extend I ∘ u ∘ φ.symm) ∧
            MemLpLoc p (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source))
              (chartDifferential I φ ψ u du) := by
  refine ⟨fun hu ↦ ?_, fun ⟨hc, du, hdu, hp⟩ ↦ memWkpLocMapOn_iff.2 ⟨hc, fun φ hφ ψ hψ ↦
    memWkpLoc_succ_iff.2 ⟨(hp φ hφ ψ hψ).1, _, hdu φ hφ ψ hψ,
      memWkpLoc_zero_iff.2 (hp φ hφ ψ hψ).2⟩⟩⟩
  obtain ⟨du, hdu⟩ := hu.exists_hasWeakMFDerivOn hs
  exact ⟨hu.continuousOn, du, hdu, fun φ hφ ψ hψ ↦
    ⟨(hu.memWkpLoc_chart hφ hψ).memLpLoc, hdu.memLpLoc_chartDifferential hu hs hφ hψ⟩⟩

end Existence

section Smooth

variable [CompleteSpace F]

/-- **Weak differentials of `C¹` maps.** On an open set on which `u` is `C¹`, its differential is
a weak differential. -/
theorem _root_.ContMDiffOn.hasWeakMFDerivOn_mfderiv (hs : IsOpen s)
    (hu : ContMDiffOn 𝓘(ℝ, ℂ) I 1 u s) :
    HasWeakMFDerivOn I u (mfderiv 𝓘(ℝ, ℂ) I u) s := by
  intro φ hφ ψ hψ
  have hφR := IsManifold.maximalAtlas_subset_restrictScalars ℝ (M := X) hφ
  have hU := φ.isOpen_inter_preimage_symm_inter_preimage hu.continuousOn hs ψ.open_source
  have hg : ContMDiffOn 𝓘(ℝ, ℂ) I 1 (u ∘ φ.symm) (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) :=
    hu.comp ((contMDiffOn_symm_of_mem_maximalAtlas hφR).mono inter_subset_left)
      fun _ hz ↦ hz.2.1
  have hf : ContDiffOn ℝ 1 (ψ.extend I ∘ u ∘ φ.symm)
      (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) :=
    contMDiffOn_iff_contDiffOn.mp (((ψ.contMDiffOn_extend hψ).of_le (by simp)).comp hg
      fun _ hz ↦ hz.2.2)
  have hf' : ContDiffOn ℝ 1 (ψ.extend I ∘ u ∘ φ.symm)
      (Opens.interior (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source))) := by
    rwa [coe_interior_chartDomain hs hu.continuousOn φ ψ]
  refine hf'.hasWeakFDerivOn_fderiv.congr_ae_deriv
    (ae_restrict_of_forall_mem (Opens.interior _).isOpen.measurableSet fun z hz ↦ ?_)
  rw [coe_interior_chartDomain hs hu.continuousOn φ ψ] at hz
  -- The chain rule for `ψ̂ ∘ u ∘ φ⁻¹` at `z`.
  have key := mvfderiv_comp z ((ψ.contMDiffAt_extend hψ hz.2.2).mdifferentiableAt (by simp))
    ((hg.contMDiffAt (hU.mem_nhds hz)).mdifferentiableAt one_ne_zero)
  rw [mfderiv_comp z ((hu.contMDiffAt (hs.mem_nhds hz.2.1)).mdifferentiableAt one_ne_zero)
    (mdifferentiableAt_symm_of_mem_maximalAtlas hφR hz.1)] at key
  ext v
  refine (mvfderiv_eq_fderiv_apply _ z v).symm.trans ?_
  rw [key, chartDifferential_def]
  -- The two sides agree after unfolding the composition `(u ∘ φ.symm) z = u (φ.symm z)`, which
  -- also occurs inside the tangent-space types, where `rw` cannot rewrite it.
  rfl

/-- On `X = M = ℂ`, the weak differential of the conjugation `z ↦ conj z` is the constant
conjugation map. -/
theorem hasWeakMFDerivOn_conj :
    HasWeakMFDerivOn 𝓘(ℝ, ℂ) (fun z : ℂ ↦ (starRingEnd ℂ) z)
      (fun _ ↦ (Complex.conjCLE : ℂ →L[ℝ] ℂ) :
        ∀ z : ℂ, TangentSpace 𝓘(ℝ, ℂ) z →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) ((starRingEnd ℂ) z)) univ := by
  have hc : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) 1 (fun z : ℂ ↦ (starRingEnd ℂ) z) univ :=
    Complex.conjCLE.contDiff.contMDiff.contMDiffOn
  have heq : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun z : ℂ ↦ (starRingEnd ℂ) z) =
      (fun _ ↦ (Complex.conjCLE : ℂ →L[ℝ] ℂ) :
        ∀ z : ℂ, TangentSpace 𝓘(ℝ, ℂ) z →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) ((starRingEnd ℂ) z)) := by
    funext z
    exact (Complex.conjCLE.hasFDerivAt (x := z)).hasMFDerivAt.mfderiv
  have h := hc.hasWeakMFDerivOn_mfderiv isOpen_univ
  rwa [heq] at h

end Smooth

end TauCeti
