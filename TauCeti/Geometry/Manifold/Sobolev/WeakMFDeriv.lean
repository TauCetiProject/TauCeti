/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Sobolev.LocalMap
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.MeasureTheory.OuterMeasure.Basic
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Topology.Sets.Opens

/-!
# The weak differential of a map from a Riemann surface

Let `X` be a Riemann surface without boundary, given as a charted space modelled on `ℂ` with
holomorphic coordinate changes, and let `M` be a manifold modelled on `I : ModelWithCorners ℝ F H`.
For a map `u : X → M`, a field of real linear maps
`du x : TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace I (u x)` is a *weak differential* of `u` on
`s ⊆ X` with exponent `p` (`TauCeti.HasWeakMFDerivOn I p u du s`) when, for every holomorphic chart
`φ` of `X` and every smooth chart `ψ` of `M`, its coordinate reading
`z ↦ dψ ∘ du (φ.symm z) ∘ d(φ.symm)_z` (`TauCeti.tangentMapReading I u du φ ψ`) is a weak Fréchet
derivative of the coordinate expression `ψ.extend I ∘ u ∘ φ.symm`, and is locally `Lᵖ`, on the part
of the target of `φ` over `s` where `u` maps into the source of `ψ`. The derivatives of the charts
are Mathlib's `mfderiv`, so `du` is a section of `Hom(TX, u*TM)`, defined almost everywhere.

## Main declarations

* `TauCeti.tangentMapReading`: the coordinate reading of a field of tangent maps along `u`.
* `TauCeti.HasWeakMFDerivOn`: weak differentials.
* `TauCeti.HasWeakMFDerivOn.memWkpLocMapOn`: a continuous map with a weak differential is in the
  first-order local Sobolev class `W^{1,p}_loc`.
* `TauCeti.HasWeakMFDerivOn.ae_eq_reading`: two weak differentials have almost everywhere equal
  coordinate readings.
* `TauCeti.HasWeakMFDerivOn.ae_eq`: two weak differentials of a map continuous on an open set
  agree almost everywhere in every holomorphic chart; `TauCeti.HasWeakMFDerivOn.congr_ae`: a
  field of tangent maps agreeing almost everywhere with a weak differential is one.
* `ContMDiffOn.hasWeakMFDerivOn_mfderiv`: for a `C¹` map, `mfderiv` is a weak differential, so
  every weak differential agrees with `mfderiv` almost everywhere
  (`TauCeti.HasWeakMFDerivOn.ae_eq_mfderiv`).
* `TauCeti.hasWeakMFDerivOn_conj`: the weak differential of `conj : ℂ → ℂ` is the constant
  conjugation map, which is `mfderiv` and is not complex linear.

## Implementation notes

The weak derivative of each coordinate expression is tested on the interior of its domain, as in
`TauCeti.MemWkpLoc`, and the local `Lᵖ` bound is required on the domain itself. For an open set
`s` and a map continuous on `s`, the domains are open. The definition does not require the
manifold structures, but it is meant for `IsManifold 𝓘(ℂ) 1 X` and `IsManifold I ∞ M`; the
uniqueness statement in a chart of `X` uses the preferred charts of `M`. Existence of a weak
differential for a member of `TauCeti.MemWkpLocMapOn I p 1 u s`, by gluing the weak derivatives of
the coordinate expressions, is not part of this file.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1.
-/

public section

open Set MeasureTheory TopologicalSpace
open scoped Manifold ContDiff Topology

noncomputable section

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {p q : ENNReal} {u : X → M} {s t : Set X}
  {du du' : (x : X) → TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace I (u x)}

variable (I) in
/-- The coordinate reading `z ↦ dψ ∘ du (φ.symm z) ∘ d(φ.symm)_z` of a field of tangent maps
`du x : T_x X →L[ℝ] T_{u x} M` along `u : X → M`, in a chart `φ` of `X` and a chart `ψ` of `M`. The
derivatives of the charts are their manifold derivatives. -/
def tangentMapReading (u : X → M)
    (du : (x : X) → TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace I (u x))
    (φ : OpenPartialHomeomorph X ℂ) (ψ : OpenPartialHomeomorph M H) (z : ℂ) : ℂ →L[ℝ] F :=
  (mfderiv I 𝓘(ℝ, F) (ψ.extend I) (u (φ.symm z))).comp
    ((du (φ.symm z)).comp (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) φ.symm z))

variable (I) in
/-- A field of tangent maps `du x : T_x X →L[ℝ] T_{u x} M` is a weak differential of
`u : X → M` on `s` with exponent `p` if, for every holomorphic chart `φ` of `X` and every smooth
chart `ψ` of `M`, its coordinate reading is a weak Fréchet derivative of the coordinate expression
`ψ.extend I ∘ u ∘ φ.symm` on the interior of the part of the target of `φ` over `s` where `u` maps
into the source of `ψ`, and is locally `Lᵖ` on that part. -/
def HasWeakMFDerivOn (p : ENNReal) (u : X → M)
    (du : (x : X) → TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace I (u x)) (s : Set X) : Prop :=
  ∀ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
    HasWeakFDerivOn volume (Opens.interior (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)))
        (ψ.extend I ∘ u ∘ φ.symm) (tangentMapReading I u du φ ψ) ∧
      MemLpLoc p (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) (tangentMapReading I u du φ ψ)

/-- Unfolding the definition of a weak differential. -/
theorem hasWeakMFDerivOn_iff : HasWeakMFDerivOn I p u du s ↔
    ∀ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
      HasWeakFDerivOn volume (Opens.interior (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)))
          (ψ.extend I ∘ u ∘ φ.symm) (tangentMapReading I u du φ ψ) ∧
        MemLpLoc p (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) (tangentMapReading I u du φ ψ) :=
  Iff.rfl

section Basic

/-- The coordinate reading of a weak differential is a weak derivative of the coordinate
expression. -/
theorem HasWeakMFDerivOn.hasWeakFDerivOn_chart (h : HasWeakMFDerivOn I p u du s)
    {φ : OpenPartialHomeomorph X ℂ} {ψ : OpenPartialHomeomorph M H}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X) (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M) :
    HasWeakFDerivOn volume (Opens.interior (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)))
      (ψ.extend I ∘ u ∘ φ.symm) (tangentMapReading I u du φ ψ) :=
  (h φ hφ ψ hψ).1

/-- The coordinate reading of a weak differential is locally `Lᵖ`. -/
theorem HasWeakMFDerivOn.memLpLoc_chart (h : HasWeakMFDerivOn I p u du s)
    {φ : OpenPartialHomeomorph X ℂ} {ψ : OpenPartialHomeomorph M H}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X) (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M) :
    MemLpLoc p (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) (tangentMapReading I u du φ ψ) :=
  (h φ hφ ψ hψ).2

/-- A weak differential on `s` is one on every smaller set. -/
theorem HasWeakMFDerivOn.mono (h : HasWeakMFDerivOn I p u du s) (hts : t ⊆ s) :
    HasWeakMFDerivOn I p u du t := by
  intro φ hφ ψ hψ
  have hsub : φ.target ∩ φ.symm ⁻¹' (t ∩ u ⁻¹' ψ.source) ⊆
      φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source) :=
    inter_subset_inter_right _ (preimage_mono (inter_subset_inter_left _ hts))
  exact ⟨(h.hasWeakFDerivOn_chart hφ hψ).mono (interior_mono hsub),
    (h.memLpLoc_chart hφ hψ).mono_set hsub⟩

/-- Decreasing the exponent preserves weak differentials. -/
theorem HasWeakMFDerivOn.mono_exponent (h : HasWeakMFDerivOn I p u du s) (hqp : q ≤ p) :
    HasWeakMFDerivOn I q u du s :=
  fun _ hφ _ hψ ↦ ⟨h.hasWeakFDerivOn_chart hφ hψ, (h.memLpLoc_chart hφ hψ).mono_exponent hqp⟩

/-- A map continuous on `s` with a weak differential on `s` is a first-order local Sobolev map on
`s`: its coordinate expressions are continuous, hence locally `Lᵖ`, and the coordinate readings of
the weak differential are locally `Lᵖ` weak derivatives of them. -/
theorem HasWeakMFDerivOn.memWkpLocMapOn (h : HasWeakMFDerivOn I p u du s)
    (hu : ContinuousOn u s) : MemWkpLocMapOn I p 1 u s := by
  refine memWkpLocMapOn_iff.2 ⟨hu, fun φ hφ ψ hψ ↦ ?_⟩
  obtain ⟨hD, hDp⟩ := h φ hφ ψ hψ
  have h1 : ContinuousOn (u ∘ φ.symm) (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) :=
    hu.comp (φ.continuousOn_symm.mono inter_subset_left) fun _ hz ↦ hz.2.1
  have hc : ContinuousOn (ψ.extend I ∘ u ∘ φ.symm)
      (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) :=
    (ψ.continuousOn_extend (I := I)).comp h1 fun _ hz ↦ by simpa using hz.2.2
  exact memWkpLoc_succ_iff.2 ⟨hc.memLpLoc, _, hD, memWkpLoc_zero_iff.2 hDp⟩

/-- **Uniqueness of the weak differential in coordinates.** Two weak differentials of `u` have
almost everywhere equal coordinate readings. -/
theorem HasWeakMFDerivOn.ae_eq_reading (h : HasWeakMFDerivOn I p u du s)
    (h' : HasWeakMFDerivOn I q u du' s) {φ : OpenPartialHomeomorph X ℂ}
    {ψ : OpenPartialHomeomorph M H} (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M) :
    tangentMapReading I u du φ ψ =ᵐ[volume.restrict
      (Opens.interior (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)))]
      tangentMapReading I u du' φ ψ :=
  (h.hasWeakFDerivOn_chart hφ hψ).ae_eq (h'.hasWeakFDerivOn_chart hφ hψ)

end Basic

/-! ### Uniqueness -/

section Uniqueness

/-- On a point of the domain of a chart pair, the coordinate reading determines the tangent map,
since the derivative of the extended chart of `M` is injective and that of the inverse of the chart
of `X` is surjective. -/
private theorem eq_of_tangentMapReading_eq {φ : OpenPartialHomeomorph X ℂ}
    {ψ : OpenPartialHomeomorph M H} (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M) {z : ℂ} (hz : z ∈ φ.target)
    (hzψ : u (φ.symm z) ∈ ψ.source)
    (heq : tangentMapReading I u du φ ψ z = tangentMapReading I u du' φ ψ z) :
    du (φ.symm z) = du' (φ.symm z) := by
  have hφ' : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) 1 X :=
    IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero 1 one_ne_zero hφ
  have hφd : φ.MDifferentiable 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) :=
    ⟨fun _ hx ↦ (mdifferentiableAt_of_mem_maximalAtlas hφ' hx).mdifferentiableWithinAt,
      fun _ hw ↦ (mdifferentiableAt_symm_of_mem_maximalAtlas hφ' hw).mdifferentiableWithinAt⟩
  obtain ⟨A, hA⟩ := isInvertible_mfderiv_extend
    (IsManifold.maximalAtlas_subset_of_le (by simp) hψ) hzψ
  ext v
  obtain ⟨w, rfl⟩ := hφd.symm.mfderiv_surjective (x := z) hz v
  apply A.injective
  have hv := congrArg (fun L : ℂ →L[ℝ] F ↦ L w) heq
  change (mfderiv I 𝓘(ℝ, F) (ψ.extend I) (u (φ.symm z)))
      (du (φ.symm z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) φ.symm z w)) =
    (mfderiv I 𝓘(ℝ, F) (ψ.extend I) (u (φ.symm z)))
      (du' (φ.symm z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) φ.symm z w)) at hv
  rw [← hA] at hv
  exact hv

/-- **Uniqueness of the weak differential.** Two weak differentials of a map continuous on an open
set `s` agree almost everywhere in every holomorphic chart `φ` of `X`, on the part of the target of
`φ` over `s`. The proof covers that part by the domains of the preferred charts of `M` and applies
`TauCeti.HasWeakMFDerivOn.ae_eq_reading` on each, using that the derivatives of the charts are
invertible. -/
theorem HasWeakMFDerivOn.ae_eq [IsManifold I ∞ M] (h : HasWeakMFDerivOn I p u du s)
    (h' : HasWeakMFDerivOn I q u du' s) (hs : IsOpen s) (hu : ContinuousOn u s)
    {φ : OpenPartialHomeomorph X ℂ} (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X) :
    ∀ᵐ z ∂volume.restrict (φ.target ∩ φ.symm ⁻¹' s), du (φ.symm z) = du' (φ.symm z) := by
  have hW : IsOpen (φ.target ∩ φ.symm ⁻¹' s) := φ.isOpen_inter_preimage_symm hs
  rw [ae_restrict_iff' hW.measurableSet, ae_iff]
  refine measure_null_of_locally_null _ fun z hz ↦ ?_
  obtain ⟨⟨hzt, hzs⟩, -⟩ := not_imp.1 hz
  set ψ := chartAt H (u (φ.symm z))
  have hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M := IsManifold.chart_mem_maximalAtlas _
  have hV : IsOpen (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) :=
    φ.isOpen_inter_preimage_symm (hu.isOpen_inter_preimage hs ψ.open_source)
  have hzV : z ∈ φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source) :=
    ⟨hzt, hzs, mem_chart_source H _⟩
  refine ⟨_, inter_mem_nhdsWithin _ (hV.mem_nhds hzV), ?_⟩
  have hae := h.ae_eq_reading h' hφ hψ
  rw [Opens.coe_interior, hV.interior_eq, Filter.EventuallyEq,
    ae_restrict_iff' hV.measurableSet, ae_iff] at hae
  refine measure_mono_null (fun w ⟨hwB, hwV⟩ ↦ ?_) hae
  exact fun himp ↦ (not_imp.1 hwB).2 (eq_of_tangentMapReading_eq hφ hψ hwV.1 hwV.2.2 (himp hwV))

/-- A field of tangent maps that agrees almost everywhere with a weak differential, in every
holomorphic chart of `X`, is a weak differential. -/
theorem HasWeakMFDerivOn.congr_ae (h : HasWeakMFDerivOn I p u du s)
    (h' : ∀ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X,
      ∀ᵐ z ∂volume.restrict (φ.target ∩ φ.symm ⁻¹' s), du (φ.symm z) = du' (φ.symm z)) :
    HasWeakMFDerivOn I p u du' s := by
  intro φ hφ ψ hψ
  have hsub : φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source) ⊆ φ.target ∩ φ.symm ⁻¹' s :=
    inter_subset_inter_right _ (preimage_mono inter_subset_left)
  have hae : tangentMapReading I u du φ ψ =ᵐ[volume.restrict
      (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source))] tangentMapReading I u du' φ ψ :=
    (ae_restrict_of_ae_restrict_of_subset hsub (h' φ hφ)).mono fun z hz ↦ by
      unfold tangentMapReading
      rw [hz]
  exact ⟨(h.hasWeakFDerivOn_chart hφ hψ).congr_ae_deriv
      (ae_restrict_of_ae_restrict_of_subset interior_subset hae),
    (h.memLpLoc_chart hφ hψ).congr_ae hae⟩

end Uniqueness

/-! ### `C¹` maps -/

section Smooth

variable [CompleteSpace F]

/-- **The differential of a `C¹` map is a weak differential.** For a map `C¹` on an open set `s`,
for the real manifold structure underlying the Riemann surface, `mfderiv` is a weak differential
on `s` for every exponent: by the chain rule its coordinate reading is the derivative of the `C¹`
coordinate expression, which is continuous. -/
theorem _root_.ContMDiffOn.hasWeakMFDerivOn_mfderiv (hu : ContMDiffOn 𝓘(ℝ, ℂ) I 1 u s)
    (hs : IsOpen s) : HasWeakMFDerivOn I p u (fun x ↦ mfderiv 𝓘(ℝ, ℂ) I u x) s := by
  intro φ hφ ψ hψ
  set V := φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)
  have hV : IsOpen V :=
    φ.isOpen_inter_preimage_symm (hu.continuousOn.isOpen_inter_preimage hs ψ.open_source)
  have hφ' : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) 1 X :=
    IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero 1 one_ne_zero hφ
  have hψ' : ψ ∈ IsManifold.maximalAtlas I 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by simp) hψ
  have hcomp : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, F) 1 (ψ.extend I ∘ u ∘ φ.symm) V :=
    (ψ.contMDiffOn_extend hψ').comp (hu.comp ((contMDiffOn_symm_of_mem_maximalAtlas hφ').mono
      inter_subset_left) fun _ hz ↦ hz.2.1) fun _ hz ↦ hz.2.2
  have hcd : ContDiffOn ℝ 1 (ψ.extend I ∘ u ∘ φ.symm) V := contMDiffOn_iff_contDiffOn.mp hcomp
  have hdiff : ∀ z ∈ V, DifferentiableAt ℝ (ψ.extend I ∘ u ∘ φ.symm) z := fun z hz ↦
    (hcd.differentiableOn one_ne_zero).differentiableAt (hV.mem_nhds hz)
  have hfd : ContinuousOn (fderiv ℝ (ψ.extend I ∘ u ∘ φ.symm)) V :=
    (hcd.continuousOn_fderiv_of_isOpen hV le_rfl)
  have heq : ∀ z ∈ V, tangentMapReading I u (fun x ↦ mfderiv 𝓘(ℝ, ℂ) I u x) φ ψ z =
      fderiv ℝ (ψ.extend I ∘ u ∘ φ.symm) z := by
    intro z hz
    have h1 : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) φ.symm z :=
      mdifferentiableAt_symm_of_mem_maximalAtlas hφ' hz.1
    have h2 : MDifferentiableAt 𝓘(ℝ, ℂ) I u (φ.symm z) :=
      (hu.contMDiffAt (hs.mem_nhds hz.2.1)).mdifferentiableAt one_ne_zero
    have h3 : MDifferentiableAt I 𝓘(ℝ, F) (ψ.extend I) (u (φ.symm z)) :=
      ψ.mdifferentiableAt_extend hψ' hz.2.2
    have hm : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, F) (ψ.extend I ∘ u ∘ φ.symm) z =
        fderiv ℝ (ψ.extend I ∘ u ∘ φ.symm) z := by
      rw [mfderiv_eq_fderiv]
      rfl
    rw [← hm, mfderiv_comp z h3 (h2.comp z h1), mfderiv_comp z h2 h1]
    rfl
  refine ⟨?_, ?_⟩
  · have hΩ : Opens.interior V = ⟨V, hV⟩ := Opens.ext hV.interior_eq
    rw [hΩ]
    refine (hasWeakFDerivOn_of_differentiableOn
      (hfd.locallyIntegrableOn hV.measurableSet) hdiff).congr_ae_deriv ?_
    exact ((ae_restrict_iff' hV.measurableSet).2 (Filter.Eventually.of_forall
      fun z hz ↦ (heq z hz).symm))
  · exact (hfd.memLpLoc (p := p)).congr_ae ((ae_restrict_iff' hV.measurableSet).2
      (Filter.Eventually.of_forall fun z hz ↦ (heq z hz).symm))

/-- A `C¹` map has `mfderiv` as a weak differential, for every exponent. -/
theorem _root_.ContMDiff.hasWeakMFDerivOn_mfderiv (hu : ContMDiff 𝓘(ℝ, ℂ) I 1 u) :
    HasWeakMFDerivOn I p u (fun x ↦ mfderiv 𝓘(ℝ, ℂ) I u x) univ :=
  hu.contMDiffOn.hasWeakMFDerivOn_mfderiv isOpen_univ

/-- **The weak differential of a `C¹` map is `mfderiv`.** Every weak differential of a map `C¹` on
an open set `s` agrees almost everywhere with `mfderiv` in every holomorphic chart of `X`. -/
theorem HasWeakMFDerivOn.ae_eq_mfderiv [IsManifold I ∞ M] (h : HasWeakMFDerivOn I p u du s)
    (hu : ContMDiffOn 𝓘(ℝ, ℂ) I 1 u s) (hs : IsOpen s) {φ : OpenPartialHomeomorph X ℂ}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X) :
    ∀ᵐ z ∂volume.restrict (φ.target ∩ φ.symm ⁻¹' s),
      du (φ.symm z) = mfderiv 𝓘(ℝ, ℂ) I u (φ.symm z) :=
  h.ae_eq (hu.hasWeakMFDerivOn_mfderiv (p := p) hs) hs hu.continuousOn hφ

end Smooth

/-! ### Checks on the plane -/

/-- The manifold derivative of the conjugation of `ℂ`, as a real map, is the conjugation map. -/
theorem mfderiv_conj (z : ℂ) :
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun w : ℂ ↦ (starRingEnd ℂ) w) z =
      (Complex.conjCLE : ℂ →L[ℝ] ℂ) := by
  exact (hasMFDerivAt_iff_hasFDerivAt.2 Complex.conjCLE.toContinuousLinearMap.hasFDerivAt).mfderiv

/-- **The weak differential of `conj z`.** For `X = M = ℂ`, the constant conjugation map is a weak
differential of `conj : ℂ → ℂ` for every exponent; it is the manifold derivative
(`TauCeti.mfderiv_conj`), and it is not complex linear, so it is not determined by a complex
linear part alone (`TauCeti.conjCLE_I_ne`). -/
theorem hasWeakMFDerivOn_conj :
    HasWeakMFDerivOn 𝓘(ℝ, ℂ) p (fun w : ℂ ↦ (starRingEnd ℂ) w)
      (fun _ ↦ (Complex.conjCLE : ℂ →L[ℝ] ℂ)) univ := by
  have hc : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) 1 (fun w : ℂ ↦ (starRingEnd ℂ) w) :=
    Complex.conjCLE.contDiff.contMDiff
  simpa only [mfderiv_conj] using hc.hasWeakMFDerivOn_mfderiv (p := p)

/-- The conjugation map is not complex linear: it sends `I` to `-I`, not to `I * conj 1 = I`. -/
theorem conjCLE_I_ne : (Complex.conjCLE : ℂ →L[ℝ] ℂ) Complex.I ≠
    Complex.I * (Complex.conjCLE : ℂ →L[ℝ] ℂ) 1 := by
  norm_num [Complex.ext_iff]

end TauCeti
