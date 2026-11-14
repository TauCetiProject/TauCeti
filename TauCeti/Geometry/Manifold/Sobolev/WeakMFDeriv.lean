/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Sobolev.LocalMap
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.MeasureTheory.OuterMeasure.Basic
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Topology.OpenPartialHomeomorph.Continuity
import TauCeti.Topology.Sets.Opens

/-!
# The weak differential of a map from a Riemann surface

A map `u` in the local Sobolev class `TauCeti.MemWkpLocMapOn I p 1 u s` need not have a classical
derivative `mfderiv`, but first-order equations along `u`, such as the weak Cauchy–Riemann equation,
and `Lᵖ` bounds on its derivative are stated in terms of a differential `du`. This file defines
the weak differential, an intrinsic tangent map along `u` whose expressions in charts are the weak
derivatives of the coordinate expressions of `u`.

Let `X` be a Riemann surface without boundary, given as a charted space modelled on `ℂ` with
holomorphic coordinate changes, and let `M` be a manifold modelled on `I : ModelWithCorners ℝ F H`.
For a map `u : X → M`, a family of real linear maps
`du x : TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace I (u x)` is a *weak differential* of `u` on
`s ⊆ X` with exponent `p` (`TauCeti.HasWeakMFDerivOn I p u du s`) when `u` is continuous on `s`
and, for every holomorphic chart `φ` of `X` and every smooth chart `ψ` of `M`, its expression in
chart coordinates `z ↦ d(ψ.extend I) ∘ du (φ.symm z) ∘ d(φ.symm)_z`
(`TauCeti.inTangentChartCoordinates I u du φ ψ`) is a weak Fréchet derivative of the coordinate
expression `ψ.extend I ∘ u ∘ φ.symm` on the interior of the part of the target of `φ` over `s`
where `u` maps into the source of `ψ`, and is locally `Lᵖ` on that part. The derivatives of the
charts are Mathlib's `mfderiv`. The family `du` is defined at every point, but the definition only
constrains it almost everywhere in holomorphic charts over `s`.

## Main declarations

* `TauCeti.inTangentChartCoordinates`: the expression in chart coordinates of a family of tangent
  maps along `u`.
* `TauCeti.HasWeakMFDerivOn`: weak differentials.
* `TauCeti.HasWeakMFDerivOn.memWkpLocMapOn`: a map with a weak differential is in the first-order
  local Sobolev class `W^{1,p}_loc`.
* `TauCeti.HasWeakMFDerivOn.inTangentChartCoordinates_ae_eq`: two weak differentials have almost
  everywhere equal expressions in chart coordinates, on the interior of the part of the target of
  a chart of `X` over `s` mapping into the source of a chart of `M`.
* `TauCeti.HasWeakMFDerivOn.ae_eq`: two weak differentials on an open set `s` agree almost
  everywhere on the part of the target of every holomorphic chart over `s`;
  `TauCeti.HasWeakMFDerivOn.congr_ae_deriv`: a family of tangent maps agreeing almost everywhere
  with a weak differential is one.
* `ContMDiffOn.hasWeakMFDerivOn_mfderiv`: for a `C¹` map on an open set `s` (with `F` complete),
  `mfderiv` is a weak differential, so every weak differential agrees with `mfderiv` almost
  everywhere on the part of the target of every holomorphic chart over `s`
  (`TauCeti.HasWeakMFDerivOn.ae_eq_mfderiv`, for `IsManifold I ∞ M`).
* `TauCeti.hasWeakMFDerivOn_conj`: the weak differential of `conj : ℂ → ℂ` is the constant
  conjugation map, which is `mfderiv` and is not complex linear.

## Implementation notes

The weak derivative of each coordinate expression is tested on the interior of its domain, as in
`TauCeti.MemWkpLoc`, and the local `Lᵖ` bound is required on the domain itself. Continuity of `u`
on `s` is part of the definition, as in `TauCeti.MemWkpLocMapOn`: for an open set `s` it makes the
domains open, so that discontinuities of `u` cannot hide between the charts of `M`. The definition
does not require the manifold structures, but it is meant for `IsManifold 𝓘(ℂ) 1 X` and
`IsManifold I ∞ M`; the uniqueness statement in a chart of `X` uses the preferred charts of `M`.
As for `TauCeti.HasWeakFDerivOn`, a weak differential forces `F` to be complete, and statements
whose hypotheses include one recover `CompleteSpace F` from it. Existence of a weak differential
for a member of `TauCeti.MemWkpLocMapOn I p 1 u s`, by gluing the weak derivatives of the
coordinate expressions, is not part of this file.

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
/-- The expression `z ↦ d(ψ.extend I) ∘ du (φ.symm z) ∘ d(φ.symm)_z` in chart coordinates of a
family of tangent maps `du x : T_x X →L[ℝ] T_{u x} M` along `u : X → M`, for a chart `φ` of `X` and
a chart `ψ` of `M`. The derivatives of `φ.symm` and of the extended chart `ψ.extend I` are their
manifold derivatives. -/
def inTangentChartCoordinates (u : X → M)
    (du : (x : X) → TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace I (u x))
    (φ : OpenPartialHomeomorph X ℂ) (ψ : OpenPartialHomeomorph M H) (z : ℂ) : ℂ →L[ℝ] F :=
  (mfderiv I 𝓘(ℝ, F) (ψ.extend I) (u (φ.symm z))).comp
    ((du (φ.symm z)).comp (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) φ.symm z))

theorem inTangentChartCoordinates_def (φ : OpenPartialHomeomorph X ℂ)
    (ψ : OpenPartialHomeomorph M H) (z : ℂ) :
    inTangentChartCoordinates I u du φ ψ z =
      (mfderiv I 𝓘(ℝ, F) (ψ.extend I) (u (φ.symm z))).comp
        ((du (φ.symm z)).comp (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) φ.symm z)) :=
  (rfl)

@[simp]
theorem inTangentChartCoordinates_apply (φ : OpenPartialHomeomorph X ℂ)
    (ψ : OpenPartialHomeomorph M H) (z v : ℂ) :
    inTangentChartCoordinates I u du φ ψ z v =
      mfderiv I 𝓘(ℝ, F) (ψ.extend I) (u (φ.symm z))
        (du (φ.symm z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) φ.symm z v)) :=
  (rfl)

variable (I) in
/-- A family of tangent maps `du x : T_x X →L[ℝ] T_{u x} M` is a weak differential of
`u : X → M` on `s` with exponent `p` if `u` is continuous on `s` and, for every holomorphic chart
`φ` of `X` and every smooth chart `ψ` of `M`, its expression in chart coordinates is a weak Fréchet
derivative of the coordinate expression `ψ.extend I ∘ u ∘ φ.symm` on the interior of the part of
the target of `φ` over `s` where `u` maps into the source of `ψ`, and is locally `Lᵖ` on that
part. -/
def HasWeakMFDerivOn (p : ENNReal) (u : X → M)
    (du : (x : X) → TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace I (u x)) (s : Set X) : Prop :=
  ContinuousOn u s ∧ ∀ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
    HasWeakFDerivOn volume (Opens.interior (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)))
        (ψ.extend I ∘ u ∘ φ.symm) (inTangentChartCoordinates I u du φ ψ) ∧
      MemLpLoc p (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source))
        (inTangentChartCoordinates I u du φ ψ)

/-- Unfolding the definition of a weak differential. -/
theorem hasWeakMFDerivOn_iff : HasWeakMFDerivOn I p u du s ↔ ContinuousOn u s ∧
    ∀ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
      HasWeakFDerivOn volume (Opens.interior (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)))
          (ψ.extend I ∘ u ∘ φ.symm) (inTangentChartCoordinates I u du φ ψ) ∧
        MemLpLoc p (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source))
          (inTangentChartCoordinates I u du φ ψ) :=
  Iff.rfl

section Basic

/-- A map with a weak differential on `s` is continuous on `s`. -/
theorem HasWeakMFDerivOn.continuousOn (h : HasWeakMFDerivOn I p u du s) : ContinuousOn u s :=
  h.1

/-- The expression in chart coordinates of a weak differential is a weak derivative of the
coordinate expression, on the interior of the part of the target of `φ` over `s` where `u` maps
into the source of `ψ`. -/
theorem HasWeakMFDerivOn.hasWeakFDerivOn_chart (h : HasWeakMFDerivOn I p u du s)
    {φ : OpenPartialHomeomorph X ℂ} {ψ : OpenPartialHomeomorph M H}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X) (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M) :
    HasWeakFDerivOn volume (Opens.interior (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)))
      (ψ.extend I ∘ u ∘ φ.symm) (inTangentChartCoordinates I u du φ ψ) :=
  (h.2 φ hφ ψ hψ).1

/-- The expression in chart coordinates of a weak differential is locally `Lᵖ` on the part of the
target of `φ` over `s` where `u` maps into the source of `ψ`. -/
theorem HasWeakMFDerivOn.memLpLoc_chart (h : HasWeakMFDerivOn I p u du s)
    {φ : OpenPartialHomeomorph X ℂ} {ψ : OpenPartialHomeomorph M H}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X) (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M) :
    MemLpLoc p (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source))
      (inTangentChartCoordinates I u du φ ψ) :=
  (h.2 φ hφ ψ hψ).2

/-- A weak differential on `s` is one on every smaller set. -/
theorem HasWeakMFDerivOn.mono (h : HasWeakMFDerivOn I p u du s) (hts : t ⊆ s) :
    HasWeakMFDerivOn I p u du t := by
  refine ⟨h.continuousOn.mono hts, fun φ hφ ψ hψ ↦ ?_⟩
  have hsub : φ.target ∩ φ.symm ⁻¹' (t ∩ u ⁻¹' ψ.source) ⊆
      φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source) :=
    inter_subset_inter_right _ (preimage_mono (inter_subset_inter_left _ hts))
  exact ⟨(h.hasWeakFDerivOn_chart hφ hψ).mono (interior_mono hsub),
    (h.memLpLoc_chart hφ hψ).mono_set hsub⟩

/-- Decreasing the exponent preserves weak differentials. -/
theorem HasWeakMFDerivOn.mono_exponent (h : HasWeakMFDerivOn I p u du s) (hqp : q ≤ p) :
    HasWeakMFDerivOn I q u du s :=
  ⟨h.continuousOn, fun _ hφ _ hψ ↦
    ⟨h.hasWeakFDerivOn_chart hφ hψ, (h.memLpLoc_chart hφ hψ).mono_exponent hqp⟩⟩

/-- A map with a weak differential on `s` is a first-order local Sobolev map on `s`. -/
theorem HasWeakMFDerivOn.memWkpLocMapOn (h : HasWeakMFDerivOn I p u du s) :
    MemWkpLocMapOn I p 1 u s := by
  refine memWkpLocMapOn_iff.2 ⟨h.continuousOn, fun φ hφ ψ hψ ↦ ?_⟩
  -- The coordinate expression is continuous, hence locally `Lᵖ`, and the expression of `du` in
  -- chart coordinates is a locally `Lᵖ` weak derivative of it.
  have h1 : ContinuousOn (u ∘ φ.symm) (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) :=
    h.continuousOn.comp (φ.continuousOn_symm.mono inter_subset_left) fun _ hz ↦ hz.2.1
  have hc : ContinuousOn (ψ.extend I ∘ u ∘ φ.symm)
      (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) :=
    (ψ.continuousOn_extend (I := I)).comp h1 fun _ hz ↦ by simpa using hz.2.2
  exact memWkpLoc_succ_iff.2 ⟨hc.memLpLoc, _, h.hasWeakFDerivOn_chart hφ hψ,
    memWkpLoc_zero_iff.2 (h.memLpLoc_chart hφ hψ)⟩

/-- **Uniqueness of the weak differential in coordinates.** Two weak differentials of `u` have
almost everywhere equal expressions in chart coordinates, on the interior of the part of the target
of `φ` over `s` where `u` maps into the source of `ψ`. -/
theorem HasWeakMFDerivOn.inTangentChartCoordinates_ae_eq (h : HasWeakMFDerivOn I p u du s)
    (h' : HasWeakMFDerivOn I q u du' s) {φ : OpenPartialHomeomorph X ℂ}
    {ψ : OpenPartialHomeomorph M H} (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M) :
    inTangentChartCoordinates I u du φ ψ =ᵐ[volume.restrict
      (Opens.interior (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)))]
      inTangentChartCoordinates I u du' φ ψ :=
  (h.hasWeakFDerivOn_chart hφ hψ).ae_eq (h'.hasWeakFDerivOn_chart hφ hψ)

end Basic

/-! ### Uniqueness -/

section Uniqueness

/-- At a point `z` of the target of a chart `φ` of `X` with `u (φ.symm z)` in the source of a chart
`ψ` of `M`, the expression in chart coordinates at `z` determines the tangent map at `φ.symm z`. -/
theorem eq_of_inTangentChartCoordinates_eq {φ : OpenPartialHomeomorph X ℂ}
    {ψ : OpenPartialHomeomorph M H} (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    (hψ : ψ ∈ IsManifold.maximalAtlas I 1 M) {z : ℂ} (hz : z ∈ φ.target)
    (hzψ : u (φ.symm z) ∈ ψ.source)
    (heq : inTangentChartCoordinates I u du φ ψ z = inTangentChartCoordinates I u du' φ ψ z) :
    du (φ.symm z) = du' (φ.symm z) := by
  -- The derivative of `φ.symm` at `z` is surjective and that of `ψ.extend I` is injective.
  have hφ' : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) 1 X :=
    IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero 1 one_ne_zero hφ
  have hφd : φ.MDifferentiable 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) :=
    ⟨fun _ hx ↦ (mdifferentiableAt_of_mem_maximalAtlas hφ' hx).mdifferentiableWithinAt,
      fun _ hw ↦ (mdifferentiableAt_symm_of_mem_maximalAtlas hφ' hw).mdifferentiableWithinAt⟩
  rw [inTangentChartCoordinates_def, inTangentChartCoordinates_def] at heq
  ext v
  obtain ⟨w, rfl⟩ := hφd.symm.mfderiv_surjective (x := z) hz v
  exact (isInvertible_mfderiv_extend hψ hzψ).injective (DFunLike.congr_fun heq w)

/-- **Uniqueness of the weak differential.** Two weak differentials of `u` on an open set `s` agree
almost everywhere in every holomorphic chart `φ` of `X`, on the part of the target of `φ` over
`s`. -/
theorem HasWeakMFDerivOn.ae_eq [IsManifold I ∞ M] (h : HasWeakMFDerivOn I p u du s)
    (h' : HasWeakMFDerivOn I q u du' s) (hs : IsOpen s)
    {φ : OpenPartialHomeomorph X ℂ} (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X) :
    ∀ᵐ z ∂volume.restrict (φ.target ∩ φ.symm ⁻¹' s), du (φ.symm z) = du' (φ.symm z) := by
  -- Cover the part of the target of `φ` over `s` by the domains of the preferred charts of `M`
  -- and compare the expressions in chart coordinates on each.
  have hW : IsOpen (φ.target ∩ φ.symm ⁻¹' s) := φ.isOpen_inter_preimage_symm hs
  rw [ae_restrict_iff' hW.measurableSet, ae_iff]
  refine measure_null_of_locally_null _ fun z hz ↦ ?_
  obtain ⟨⟨hzt, hzs⟩, -⟩ := not_imp.1 hz
  set ψ := chartAt H (u (φ.symm z))
  have hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M := IsManifold.chart_mem_maximalAtlas _
  have hV : IsOpen (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) :=
    φ.isOpen_inter_preimage_symm_inter_preimage h.continuousOn hs ψ.open_source
  have hzV : z ∈ φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source) :=
    ⟨hzt, hzs, mem_chart_source H _⟩
  refine ⟨_, inter_mem_nhdsWithin _ (hV.mem_nhds hzV), ?_⟩
  have hae := h.inTangentChartCoordinates_ae_eq h' hφ hψ
  rw [Opens.coe_interior, hV.interior_eq, Filter.EventuallyEq,
    ae_restrict_iff' hV.measurableSet, ae_iff] at hae
  refine measure_mono_null (fun w ⟨hwB, hwV⟩ ↦ ?_) hae
  exact fun himp ↦ (not_imp.1 hwB).2 (eq_of_inTangentChartCoordinates_eq hφ
    (IsManifold.maximalAtlas_subset_of_le (by simp) hψ) hwV.1 hwV.2.2 (himp hwV))

/-- A family of tangent maps that agrees almost everywhere with a weak differential, in every
holomorphic chart `φ` of `X` on the part of the target of `φ` over `s`, is a weak differential. -/
theorem HasWeakMFDerivOn.congr_ae_deriv (h : HasWeakMFDerivOn I p u du s)
    (h' : ∀ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X,
      ∀ᵐ z ∂volume.restrict (φ.target ∩ φ.symm ⁻¹' s), du (φ.symm z) = du' (φ.symm z)) :
    HasWeakMFDerivOn I p u du' s := by
  refine ⟨h.continuousOn, fun φ hφ ψ hψ ↦ ?_⟩
  have hsub : φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source) ⊆ φ.target ∩ φ.symm ⁻¹' s :=
    inter_subset_inter_right _ (preimage_mono inter_subset_left)
  have hae : inTangentChartCoordinates I u du φ ψ =ᵐ[volume.restrict
      (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source))] inTangentChartCoordinates I u du' φ ψ :=
    (ae_restrict_of_ae_restrict_of_subset hsub (h' φ hφ)).mono fun z hz ↦ by
      rw [inTangentChartCoordinates_def, inTangentChartCoordinates_def, hz]
  exact ⟨(h.hasWeakFDerivOn_chart hφ hψ).congr_ae_deriv
      (ae_restrict_of_ae_restrict_of_subset interior_subset hae),
    (h.memLpLoc_chart hφ hψ).congr_ae hae⟩

end Uniqueness

/-! ### `C¹` maps -/

/-- **Chain rule in chart coordinates.** At a point where `u` is differentiable, the expression of
`mfderiv` in chart coordinates is the Fréchet derivative of the coordinate expression. -/
theorem hasFDerivAt_inTangentChartCoordinates_mfderiv {φ : OpenPartialHomeomorph X ℂ}
    {ψ : OpenPartialHomeomorph M H} (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    (hψ : ψ ∈ IsManifold.maximalAtlas I 1 M) {z : ℂ} (hz : z ∈ φ.target)
    (hzψ : u (φ.symm z) ∈ ψ.source) (hu : MDifferentiableAt 𝓘(ℝ, ℂ) I u (φ.symm z)) :
    HasFDerivAt (ψ.extend I ∘ u ∘ φ.symm)
      (inTangentChartCoordinates I u (fun x ↦ mfderiv 𝓘(ℝ, ℂ) I u x) φ ψ z) z := by
  have hφ' : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) 1 X :=
    IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero 1 one_ne_zero hφ
  rw [inTangentChartCoordinates_def]
  exact hasMFDerivAt_iff_hasFDerivAt.1 <| (ψ.mdifferentiableAt_extend hψ hzψ).hasMFDerivAt.comp z
    (hu.hasMFDerivAt.comp z (mdifferentiableAt_symm_of_mem_maximalAtlas hφ' hz).hasMFDerivAt)

section Smooth

variable [CompleteSpace F]

/-- **The differential of a `C¹` map is a weak differential.** For a map `Cⁿ`, `n ≠ 0`, on an open
set `s`, for the real manifold structure underlying the Riemann surface, `mfderiv` is a weak
differential on `s` for every exponent. -/
theorem _root_.ContMDiffOn.hasWeakMFDerivOn_mfderiv {n : ℕ∞ω} (hu : ContMDiffOn 𝓘(ℝ, ℂ) I n u s)
    (hn : n ≠ 0) (hs : IsOpen s) : HasWeakMFDerivOn I p u (fun x ↦ mfderiv 𝓘(ℝ, ℂ) I u x) s := by
  replace hu := hu.of_le (ENat.one_le_iff_ne_zero_withTop.2 hn)
  refine ⟨hu.continuousOn, fun φ hφ ψ hψ ↦ ?_⟩
  set V := φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)
  have hV : IsOpen V :=
    φ.isOpen_inter_preimage_symm_inter_preimage hu.continuousOn hs ψ.open_source
  have hφ' : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) 1 X :=
    IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero 1 one_ne_zero hφ
  have hψ' : ψ ∈ IsManifold.maximalAtlas I 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by simp) hψ
  have hcomp : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, F) 1 (ψ.extend I ∘ u ∘ φ.symm) V :=
    (ψ.contMDiffOn_extend hψ').comp (hu.comp ((contMDiffOn_symm_of_mem_maximalAtlas hφ').mono
      inter_subset_left) fun _ hz ↦ hz.2.1) fun _ hz ↦ hz.2.2
  have hcd : ContDiffOn ℝ 1 (ψ.extend I ∘ u ∘ φ.symm) V := contMDiffOn_iff_contDiffOn.mp hcomp
  have hfd : ContinuousOn (fderiv ℝ (ψ.extend I ∘ u ∘ φ.symm)) V :=
    hcd.continuousOn_fderiv_of_isOpen hV le_rfl
  have hD : ∀ z ∈ V, HasFDerivAt (ψ.extend I ∘ u ∘ φ.symm)
      (inTangentChartCoordinates I u (fun x ↦ mfderiv 𝓘(ℝ, ℂ) I u x) φ ψ z) z := fun z hz ↦
    hasFDerivAt_inTangentChartCoordinates_mfderiv hφ hψ' hz.1 hz.2.2
      ((hu.contMDiffAt (hs.mem_nhds hz.2.1)).mdifferentiableAt one_ne_zero)
  have hae : fderiv ℝ (ψ.extend I ∘ u ∘ φ.symm) =ᵐ[volume.restrict V]
      inTangentChartCoordinates I u (fun x ↦ mfderiv 𝓘(ℝ, ℂ) I u x) φ ψ :=
    Set.EqOn.aeEq_restrict (fun z hz ↦ (hD z hz).fderiv) hV.measurableSet
  refine ⟨?_, (hfd.memLpLoc (p := p)).congr_ae hae⟩
  rw [show Opens.interior V = ⟨V, hV⟩ from Opens.interior_coe ⟨V, hV⟩]
  exact (hasWeakFDerivOn_of_differentiableOn (hfd.locallyIntegrableOn hV.measurableSet)
    fun z hz ↦ (hD z hz).differentiableAt).congr_ae_deriv hae

/-- A map `Cⁿ`, `n ≠ 0`, on `X` has `mfderiv` as a weak differential, for every exponent. -/
theorem _root_.ContMDiff.hasWeakMFDerivOn_mfderiv {n : ℕ∞ω} (hu : ContMDiff 𝓘(ℝ, ℂ) I n u)
    (hn : n ≠ 0) : HasWeakMFDerivOn I p u (fun x ↦ mfderiv 𝓘(ℝ, ℂ) I u x) univ :=
  hu.contMDiffOn.hasWeakMFDerivOn_mfderiv hn isOpen_univ

end Smooth

/-- **The weak differential of a `C¹` map is `mfderiv`.** Every weak differential of a map `Cⁿ`,
`n ≠ 0`, on an open set `s` agrees almost everywhere with `mfderiv` in every holomorphic chart `φ`
of `X`, on the part of the target of `φ` over `s`. -/
theorem HasWeakMFDerivOn.ae_eq_mfderiv [IsManifold I ∞ M] {n : ℕ∞ω}
    (h : HasWeakMFDerivOn I p u du s) (hu : ContMDiffOn 𝓘(ℝ, ℂ) I n u s) (hn : n ≠ 0)
    (hs : IsOpen s) {φ : OpenPartialHomeomorph X ℂ} (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X) :
    ∀ᵐ z ∂volume.restrict (φ.target ∩ φ.symm ⁻¹' s),
      du (φ.symm z) = mfderiv 𝓘(ℝ, ℂ) I u (φ.symm z) := by
  rcases (φ.target ∩ φ.symm ⁻¹' s).eq_empty_or_nonempty with he | ⟨z, -⟩
  · simp [he]
  -- A weak differential forces the model space `F` to be complete.
  have := (h.hasWeakFDerivOn_chart hφ
    (IsManifold.chart_mem_maximalAtlas (u (φ.symm z)))).completeSpace
  exact h.ae_eq (hu.hasWeakMFDerivOn_mfderiv (p := p) hn hs) hs hφ

/-! ### Checks on the plane -/

/-- **The weak differential of `conj z`.** For `X = M = ℂ`, the constant conjugation map is a weak
differential of `conj : ℂ → ℂ` for every exponent. It is the manifold derivative
(`ContinuousLinearEquiv.mfderiv_eq`), and it sends `I` to `-I` (`Complex.conj_I`): it is complex
antilinear, so it is not complex linear. -/
theorem hasWeakMFDerivOn_conj :
    HasWeakMFDerivOn 𝓘(ℝ, ℂ) p (fun w : ℂ ↦ (starRingEnd ℂ) w)
      (fun _ ↦ (Complex.conjCLE : ℂ →L[ℝ] ℂ)) univ := by
  have h := Complex.conjCLE.contDiff.contMDiff.hasWeakMFDerivOn_mfderiv (p := p) one_ne_zero
  simp only [ContinuousLinearEquiv.mfderiv_eq] at h
  rwa [show ⇑Complex.conjCLE = fun w : ℂ ↦ (starRingEnd ℂ) w from funext Complex.conjCLE_apply]
    at h

end TauCeti
