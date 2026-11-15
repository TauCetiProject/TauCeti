/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.Chart.TangentHom
public import TauCeti.Geometry.Manifold.Measure
public import TauCeti.Geometry.Manifold.Sobolev.LocalMap.Bordered
public import TauCeti.Topology.OpenPartialHomeomorph.Continuity
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import TauCeti.Analysis.Sobolev.WeakDeriv.Local
import TauCeti.Geometry.Manifold.Boundary.Basic
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.ContMDiff.RestrictScalars
import TauCeti.Geometry.Manifold.Measure.Differentiable

/-!
# The weak differential of a local Sobolev map: definitions, locality, and uniqueness

Let `X` be a Riemann surface, possibly with boundary, and let `M` be a smooth manifold modelled on
`I : ModelWithCorners ℝ F H`, where `F` is a real Banach space. A continuous map `u : X → M` of
local Sobolev class `W^{1,p}_loc` need not be classically differentiable at every point, so its
first derivative cannot be written pointwise as `mfderiv`. Instead, a weak differential of `u` is a
family of continuous ℝ-linear maps

`du : ∀ x : X, TangentSpace J x →L[ℝ] TangentSpace I (u x)`

whose coordinate expression `TauCeti.chartTangentHom J I φ ψ u du` (from
`TauCeti.Geometry.Manifold.MFDeriv.Chart.TangentHom`) in every chart `φ` of `X` and every smooth
chart `ψ` of `M` is a weak Fréchet derivative of the coordinate representative
`ψ.extend I ∘ u ∘ (φ.extend J).symm` on the interior of the chart overlap domain.

The definition (`TauCeti.HasWeakMFDerivOnGroupoid`, `TauCeti.HasWeakMFDerivGroupoid`) separates
weak differentiability from the integrability exponent `p`, just as `TauCeti.HasWeakFDerivOn` does
in normed spaces: only local integrability of the coordinate representatives and their weak
derivatives enters `HasWeakMFDerivOnGroupoid`, while local `Lᵖ` bounds up to the boundary are read
off when `u` belongs to `TauCeti.MemWkpLocMapOnGroupoid` at order one. Specializing the structure
groupoid `G` and model `J` gives both:

* `TauCeti.HasWeakMFDerivOn` and `TauCeti.HasWeakMFDeriv` for Riemann surfaces without boundary
  (`G = contDiffGroupoid 1 𝓘(ℂ)`, `J = 𝓘(ℝ, ℂ)`);
* `TauCeti.HasWeakMFDerivOnBordered` and `TauCeti.HasWeakMFDerivBordered` for Riemann surfaces with
  boundary (`G = borderedHolomorphicGroupoid`, `J = closedUpperHalfPlaneModel`), where weak
  derivatives are tested on open interiors in the upper half-plane while local `Lᵖ` integrability
  reaches the real axis.

Because `du x` is the full real-linear map `T_x X →L[ℝ] T_{u x} M` rather than only its
complex-linear part, both `(1, 0)` and `(0, 1)` components are retained: on `ℂ`, the conjugation
map `conj` has weak differential `Complex.conjCLE` rather than `0`, and `0` is not a weak
differential of `id` or `conj` on any nonempty open set. Chart independence, the weak chain rule,
and existence of a global weak differential for `W^{1,p}_loc` maps are proved in
`TauCeti.Geometry.Manifold.Sobolev.LocalMap.WeakDeriv.Calculus`.

## Main declarations

* `TauCeti.HasWeakMFDerivOnGroupoid`, `TauCeti.HasWeakMFDerivGroupoid`,
  `TauCeti.HasWeakMFDerivOn`, `TauCeti.HasWeakMFDeriv`,
  `TauCeti.HasWeakMFDerivOnBordered`, `TauCeti.HasWeakMFDerivBordered`: weak differential
  predicates on open subsets and on the whole surface, with and without boundary (defined as
  `abbrev`s of the groupoid predicates so all groupoid dot-notation projections apply directly).
* `TauCeti.hasWeakMFDerivOnGroupoid_empty`, `TauCeti.hasWeakMFDerivOnGroupoid_const`,
  `TauCeti.hasWeakMFDerivGroupoid_const`, `TauCeti.HasWeakMFDerivOnGroupoid.congr`: empty-set,
  constant-map, and map-congruence lemmas.
* `TauCeti.HasWeakMFDerivOnGroupoid.locallyIntegrableOn_chartTangentHom`,
  `TauCeti.HasWeakMFDerivOnGroupoid.aestronglyMeasurable_chartTangentHom`,
  `TauCeti.HasWeakMFDerivOnGroupoid.memLpLoc_chartTangentHom`,
  `TauCeti.HasWeakMFDerivOnGroupoid.memWkpLocMapOnGroupoid_one_iff`: local integrability,
  measurability, and local `Lᵖ` regularity of `du` in charts, including up to the boundary of `J`.
* `TauCeti.hasWeakMFDerivOnGroupoid_iff_locally`, `TauCeti.hasWeakMFDerivOnGroupoid_iUnion_iff`,
  `TauCeti.HasWeakMFDerivOnGroupoid.union`: locality on open covers.
* `ContMDiffOn.hasWeakMFDerivOnGroupoid`, `ContMDiffOn.hasWeakMFDerivOn`,
  `ContMDiff.hasWeakMFDeriv`, `ContMDiffOn.hasWeakMFDerivOnBordered`,
  `ContMDiff.hasWeakMFDerivBordered`, `MDifferentiableOn.hasWeakMFDerivOn`,
  `MDifferentiable.hasWeakMFDeriv`: classical `C¹` and holomorphic maps have `mfderiv` as weak
  differential.
* `TauCeti.HasWeakMFDerivOnGroupoid.congr_deriv_of_isNullSet`,
  `TauCeti.HasWeakMFDerivOnGroupoid.isNullSet_ne`,
  `TauCeti.HasWeakMFDerivOnGroupoid.isNullSet_ne_mfderiv`: invariance under chartwise null
  modifications and almost-everywhere uniqueness (`TauCeti.IsNullSet`) of the weak differential,
  including on bordered surfaces.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 and Section 3.1.
-/

public section

open Bundle Filter Function MeasureTheory Set TopologicalSpace
open scoped ContDiff Manifold Topology ComplexConjugate

noncomputable section

namespace TauCeti

/-! ### Weak differentials tested in the charts of a structure groupoid -/

section Groupoid

variable {H' : Type*} [TopologicalSpace H'] {X : Type*} [TopologicalSpace X] [ChartedSpace H' X]
  {G : StructureGroupoid H'} {J : ModelWithCorners ℝ ℂ H'}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {p : ENNReal} {u : X → M}
  {du du' : ∀ x : X, TangentSpace J x →L[ℝ] TangentSpace I (u x)} {s t : Set X}

omit [ChartedSpace H' X] in
/-- When `(φ.extend J).target` is a neighborhood of `z` and `U` is a neighborhood of
`(φ.extend J).symm z`, `z` lies in the interior of `(φ.extend J).target ∩ (φ.extend J).symm ⁻¹' U`.
-/
private theorem mem_interior_extend_target_inter_preimage
    {φ : OpenPartialHomeomorph X H'} {U : Set X} {z : ℂ}
    (hzt : (φ.extend J).target ∈ 𝓝 z) (hU : U ∈ 𝓝 ((φ.extend J).symm z)) :
    z ∈ interior ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' U) :=
  mem_interior_iff_mem_nhds.2
    (inter_mem hzt ((φ.continuousOn_extend_symm.continuousAt hzt).preimage_mem_nhds hU))

variable (G J I) in
/-- A family `du : ∀ x, TangentSpace J x →L[ℝ] TangentSpace I (u x)` is a weak differential of
`u : X → M` on `s ⊆ X` for the structure groupoid `G` if `u` is continuous on `s` and, in every
chart `φ` of the maximal atlas of `G` and every smooth chart `ψ` of `M`,
`chartTangentHom J I φ ψ u du` is a weak Fréchet derivative of `ψ.extend I ∘ u ∘ (φ.extend J).symm`
on the interior of the part of `(φ.extend J).target` sent into `s ∩ u ⁻¹' ψ.source`. The definition
is intended for open `s`. -/
def HasWeakMFDerivOnGroupoid (u : X → M)
    (du : ∀ x : X, TangentSpace J x →L[ℝ] TangentSpace I (u x)) (s : Set X) : Prop :=
  ContinuousOn u s ∧
    ∀ φ ∈ G.maximalAtlas X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
      HasWeakFDerivOn volume
        (Opens.interior ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)))
        (ψ.extend I ∘ u ∘ (φ.extend J).symm) (chartTangentHom J I φ ψ u du)

variable (G J I) in
/-- A family `du : ∀ x, TangentSpace J x →L[ℝ] TangentSpace I (u x)` is a weak differential of
`u : X → M` on the whole surface `X` for the structure groupoid `G` if `u` is continuous and, in
every chart `φ` of the maximal atlas of `G` and every smooth chart `ψ` of `M`,
`chartTangentHom J I φ ψ u du` is a weak Fréchet derivative of `ψ.extend I ∘ u ∘ (φ.extend J).symm`
on the interior of `(φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (u ⁻¹' ψ.source)`. -/
def HasWeakMFDerivGroupoid (u : X → M)
    (du : ∀ x : X, TangentSpace J x →L[ℝ] TangentSpace I (u x)) : Prop :=
  Continuous u ∧
    ∀ φ ∈ G.maximalAtlas X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
      HasWeakFDerivOn volume
        (Opens.interior ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (u ⁻¹' ψ.source)))
        (ψ.extend I ∘ u ∘ (φ.extend J).symm) (chartTangentHom J I φ ψ u du)

/-- Unfolding `HasWeakMFDerivOnGroupoid`. -/
theorem hasWeakMFDerivOnGroupoid_iff :
    HasWeakMFDerivOnGroupoid G J I u du s ↔ ContinuousOn u s ∧
      ∀ φ ∈ G.maximalAtlas X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
        HasWeakFDerivOn volume
          (Opens.interior ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)))
          (ψ.extend I ∘ u ∘ (φ.extend J).symm) (chartTangentHom J I φ ψ u du) :=
  Iff.rfl

/-- Unfolding `HasWeakMFDerivGroupoid`. -/
theorem hasWeakMFDerivGroupoid_iff :
    HasWeakMFDerivGroupoid G J I u du ↔ Continuous u ∧
      ∀ φ ∈ G.maximalAtlas X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
        HasWeakFDerivOn volume
          (Opens.interior ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (u ⁻¹' ψ.source)))
          (ψ.extend I ∘ u ∘ (φ.extend J).symm) (chartTangentHom J I φ ψ u du) :=
  Iff.rfl

/-- On `univ`, the relative weak differential predicate agrees with the global one. -/
@[simp]
theorem hasWeakMFDerivOnGroupoid_univ :
    HasWeakMFDerivOnGroupoid G J I u du univ ↔ HasWeakMFDerivGroupoid G J I u du := by
  simp only [HasWeakMFDerivOnGroupoid, HasWeakMFDerivGroupoid, continuousOn_univ, univ_inter]

/-- Every map and tangent-homomorphism family vacuously satisfy `HasWeakMFDerivOnGroupoid` on
`∅`. -/
@[simp]
theorem hasWeakMFDerivOnGroupoid_empty [CompleteSpace F] :
    HasWeakMFDerivOnGroupoid G J I u du ∅ := by
  refine ⟨continuousOn_empty u, fun φ _ ψ _ ↦ ?_⟩
  have hΩ : Opens.interior
      ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (∅ ∩ u ⁻¹' ψ.source)) = ⊥ := by
    ext z; simp
  rw [hΩ]
  exact hasWeakFDerivOn_iff_locally.2 fun _ hz ↦ False.elim hz

/-- A constant map `fun _ ↦ c` has weak differential `0` on any set `s`. -/
theorem hasWeakMFDerivOnGroupoid_const [CompleteSpace F] (c : M) :
    HasWeakMFDerivOnGroupoid G J I (fun _ : X ↦ c) (fun _ ↦ 0) s := by
  refine ⟨continuousOn_const, fun φ _ ψ _ ↦ hasWeakFDerivOn_iff.2 fun v ↦ ?_⟩
  simpa only [Function.comp_def, chartTangentHom_zero, zero_apply] using
    hasWeakLineDerivOn_const (μ := volume) (ψ.extend I c) (v := v)

/-- A constant map `fun _ ↦ c` has global weak differential `0`. -/
theorem hasWeakMFDerivGroupoid_const [CompleteSpace F] (c : M) :
    HasWeakMFDerivGroupoid G J I (fun _ : X ↦ c) (fun _ ↦ 0) :=
  hasWeakMFDerivOnGroupoid_univ.1 (hasWeakMFDerivOnGroupoid_const c)

/-- A map with a weak differential on `s` is continuous on `s`. -/
theorem HasWeakMFDerivOnGroupoid.continuousOn (h : HasWeakMFDerivOnGroupoid G J I u du s) :
    ContinuousOn u s :=
  h.1

/-- A map with a global weak differential is continuous. -/
theorem HasWeakMFDerivGroupoid.continuous (h : HasWeakMFDerivGroupoid G J I u du) :
    Continuous u :=
  h.1

/-- Reading off the planar weak derivative in a chart `φ` of `G` and a smooth chart `ψ` of `M`. -/
theorem HasWeakMFDerivOnGroupoid.hasWeakFDerivOn_chart
    (h : HasWeakMFDerivOnGroupoid G J I u du s) {φ : OpenPartialHomeomorph X H'}
    (hφ : φ ∈ G.maximalAtlas X) {ψ : OpenPartialHomeomorph M H}
    (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M) :
    HasWeakFDerivOn volume
      (Opens.interior ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)))
      (ψ.extend I ∘ u ∘ (φ.extend J).symm) (chartTangentHom J I φ ψ u du) :=
  h.2 φ hφ ψ hψ

/-- Reading off the planar weak derivative of a global weak differential in charts `φ` and `ψ`. -/
theorem HasWeakMFDerivGroupoid.hasWeakFDerivOn_chart
    (h : HasWeakMFDerivGroupoid G J I u du) {φ : OpenPartialHomeomorph X H'}
    (hφ : φ ∈ G.maximalAtlas X) {ψ : OpenPartialHomeomorph M H}
    (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M) :
    HasWeakFDerivOn volume
      (Opens.interior ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (u ⁻¹' ψ.source)))
      (ψ.extend I ∘ u ∘ (φ.extend J).symm) (chartTangentHom J I φ ψ u du) :=
  h.2 φ hφ ψ hψ

/-- Restricting a weak differential to a subset. -/
theorem HasWeakMFDerivOnGroupoid.mono (h : HasWeakMFDerivOnGroupoid G J I u du s) (hts : t ⊆ s) :
    HasWeakMFDerivOnGroupoid G J I u du t :=
  ⟨h.1.mono hts, fun φ hφ ψ hψ ↦ (h.2 φ hφ ψ hψ).mono
    (interior_mono (inter_subset_inter_right _ (preimage_mono (inter_subset_inter_left _ hts))))⟩

/-- A global weak differential restricts to any subset. -/
theorem HasWeakMFDerivGroupoid.hasWeakMFDerivOnGroupoid (h : HasWeakMFDerivGroupoid G J I u du) :
    HasWeakMFDerivOnGroupoid G J I u du s :=
  (hasWeakMFDerivOnGroupoid_univ.2 h).mono (subset_univ s)

/-- Replacing `du` by a section that agrees with it on `s` preserves `HasWeakMFDerivOnGroupoid`. -/
theorem HasWeakMFDerivOnGroupoid.congr_deriv (h : HasWeakMFDerivOnGroupoid G J I u du s)
    (hdu : ∀ x ∈ s, du x = du' x) : HasWeakMFDerivOnGroupoid G J I u du' s := by
  refine ⟨h.1, fun φ hφ ψ hψ ↦ (h.2 φ hφ ψ hψ).congr_ae_deriv ?_⟩
  filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with z hz
  exact chartTangentHom_congr (hdu _ (interior_subset hz).2.1)

/-- Congruence of `HasWeakMFDerivOnGroupoid` under replacing `(u, du)` by `(u', du')` agreeing on
`s` up to `tangentSpaceCast`. -/
theorem HasWeakMFDerivOnGroupoid.congr {u' : X → M}
    {du' : ∀ x : X, TangentSpace J x →L[ℝ] TangentSpace I (u' x)}
    (h : HasWeakMFDerivOnGroupoid G J I u du s) (hu : EqOn u u' s)
    (hdu : ∀ x ∈ s, (tangentSpaceCast I (u x) (u' x)).toContinuousLinearMap.comp (du x) = du' x) :
    HasWeakMFDerivOnGroupoid G J I u' du' s := by
  refine ⟨h.1.congr hu.symm, fun φ hφ ψ hψ ↦ ?_⟩
  have hdom : s ∩ u ⁻¹' ψ.source = s ∩ u' ⁻¹' ψ.source := by
    ext x
    simp only [mem_inter_iff, mem_preimage]
    exact and_congr_right fun hxs ↦ by rw [hu hxs]
  have hchart := h.2 φ hφ ψ hψ
  rw [hdom] at hchart
  refine (hchart.congr_ae ?_).congr_ae_deriv ?_
  · filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with z hz
    simp only [Function.comp_apply, hu (interior_subset hz).2.1]
  · filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with z hz
    exact chartTangentHom_congr_map (hu (interior_subset hz).2.1) (hdu _ (interior_subset hz).2.1)

/-- Global congruence of `HasWeakMFDerivGroupoid` under pointwise equality of maps and tangent
homomorphisms up to `tangentSpaceCast`. -/
theorem HasWeakMFDerivGroupoid.congr {u' : X → M}
    {du' : ∀ x : X, TangentSpace J x →L[ℝ] TangentSpace I (u' x)}
    (h : HasWeakMFDerivGroupoid G J I u du) (hu : ∀ x, u x = u' x)
    (hdu : ∀ x, (tangentSpaceCast I (u x) (u' x)).toContinuousLinearMap.comp (du x) = du' x) :
    HasWeakMFDerivGroupoid G J I u' du' :=
  hasWeakMFDerivOnGroupoid_univ.1
    ((hasWeakMFDerivOnGroupoid_univ.2 h).congr (fun x _ ↦ hu x) (fun x _ ↦ hdu x))

/-- In every chart pair `(φ, ψ)`, `chartTangentHom J I φ ψ u du` is locally integrable on the
interior of the chart overlap domain. -/
theorem HasWeakMFDerivOnGroupoid.locallyIntegrableOn_chartTangentHom
    (h : HasWeakMFDerivOnGroupoid G J I u du s) {φ : OpenPartialHomeomorph X H'}
    (hφ : φ ∈ G.maximalAtlas X) {ψ : OpenPartialHomeomorph M H}
    (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M) :
    LocallyIntegrableOn (chartTangentHom J I φ ψ u du)
      (interior ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (s ∩ u ⁻¹' ψ.source))) volume :=
  (h.hasWeakFDerivOn_chart hφ hψ).locallyIntegrableOn_deriv

/-! ### Measurability and local `Lᵖ` bounds up to the boundary -/

/-- When `s` is open, `chartTangentHom J I φ ψ u du` is a.e. strongly measurable on the full chart
overlap domain, including up to the boundary of `J`. -/
theorem HasWeakMFDerivOnGroupoid.aestronglyMeasurable_chartTangentHom
    (h : HasWeakMFDerivOnGroupoid G J I u du s) (hs : IsOpen s)
    {φ : OpenPartialHomeomorph X H'} (hφ : φ ∈ G.maximalAtlas X)
    {ψ : OpenPartialHomeomorph M H} (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M) :
    AEStronglyMeasurable (chartTangentHom J I φ ψ u du)
      (volume.restrict ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (s ∩ u ⁻¹' ψ.source))) := by
  rw [← φ.measure_restrict_interior_extend_eq (h.1.isOpen_inter_preimage hs ψ.open_source) volume]
  exact (h.locallyIntegrableOn_chartTangentHom hφ hψ).aestronglyMeasurable

/-- When `s` is open and `u` belongs to `MemWkpLocMapOnGroupoid G J I p 1 u s`, any weak
differential `du` of `u` on `s` has locally `Lᵖ` coordinate expressions `chartTangentHom` up to the
boundary of `J`. -/
theorem HasWeakMFDerivOnGroupoid.memLpLoc_chartTangentHom
    (h : HasWeakMFDerivOnGroupoid G J I u du s)
    (hu : MemWkpLocMapOnGroupoid G J I p 1 u s) (hs : IsOpen s)
    {φ : OpenPartialHomeomorph X H'} (hφ : φ ∈ G.maximalAtlas X)
    {ψ : OpenPartialHomeomorph M H} (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M) :
    MemLpLoc p ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (s ∩ u ⁻¹' ψ.source))
      (chartTangentHom J I φ ψ u du) := by
  obtain ⟨D, hD, hDp⟩ := (hu.memWkpLoc_chart hφ hψ).exists_weakFDeriv
  have hae := hD.ae_eq (h.hasWeakFDerivOn_chart hφ hψ)
  rw [Opens.coe_interior,
    φ.measure_restrict_interior_extend_eq (h.1.isOpen_inter_preimage hs ψ.open_source) volume]
      at hae
  exact (memWkpLoc_zero_iff.1 hDp).congr_ae hae

/-- Given a weak differential `du` of `u` on an open set `s`, `u` belongs to `W^{1,p}_loc` on `s`
if and only if every coordinate expression `chartTangentHom` of `du` belongs to `MemLpLoc p` on its
chart overlap domain. -/
theorem HasWeakMFDerivOnGroupoid.memWkpLocMapOnGroupoid_one_iff
    (h : HasWeakMFDerivOnGroupoid G J I u du s) (hs : IsOpen s) :
    MemWkpLocMapOnGroupoid G J I p 1 u s ↔
      ∀ φ ∈ G.maximalAtlas X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
        MemLpLoc p ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (s ∩ u ⁻¹' ψ.source))
          (chartTangentHom J I φ ψ u du) := by
  refine ⟨fun hu φ hφ ψ hψ ↦ h.memLpLoc_chartTangentHom hu hs hφ hψ,
    fun hLp ↦ memWkpLocMapOnGroupoid_iff.2 ⟨h.1, fun φ hφ ψ hψ ↦ ?_⟩⟩
  have huc : ContinuousOn (ψ.extend I ∘ u ∘ (φ.extend J).symm)
      ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) :=
    ((ψ.continuousOn_extend (I := I)).mono ψ.extend_source.ge).comp
      (h.1.comp (φ.continuousOn_extend_symm.mono inter_subset_left) fun _ hz ↦ hz.2.1)
      fun _ hz ↦ hz.2.2
  exact memWkpLoc_succ_iff.2 ⟨huc.memLpLoc, chartTangentHom J I φ ψ u du,
    h.hasWeakFDerivOn_chart hφ hψ, memWkpLoc_zero_iff.2 (hLp φ hφ ψ hψ)⟩

/-! ### Locality on open covers -/

/-- **Neighborhood locality of weak differentials.** On an open set `s`, a candidate `du` is a weak
differential of `u` if and only if every `x ∈ s` has an open neighborhood inside `s` on which `du`
is a weak differential of `u`. -/
theorem hasWeakMFDerivOnGroupoid_iff_locally [CompleteSpace F] (hs : IsOpen s) :
    HasWeakMFDerivOnGroupoid G J I u du s ↔
      ∀ x ∈ s, ∃ U ⊆ s, IsOpen U ∧ x ∈ U ∧ HasWeakMFDerivOnGroupoid G J I u du U := by
  refine ⟨fun h x hx ↦ ⟨s, subset_rfl, hs, hx, h⟩, fun hloc ↦ ?_⟩
  have hc : ContinuousOn u s := by
    intro x hx
    obtain ⟨U, _, hUo, hxU, hU⟩ := hloc x hx
    exact ((hU.continuousOn x hxU).continuousAt (hUo.mem_nhds hxU)).continuousWithinAt
  refine ⟨hc, fun φ hφ ψ hψ ↦ hasWeakFDerivOn_iff_locally.2 fun z hz ↦ ?_⟩
  have hzs : (φ.extend J).symm z ∈ s := (interior_subset hz).2.1
  obtain ⟨U, hUs, hUo, hxU, hU⟩ := hloc _ hzs
  have hzt : (φ.extend J).target ∈ 𝓝 z :=
    mem_of_superset (isOpen_interior.mem_nhds hz) (interior_subset.trans inter_subset_left)
  have hUψ : IsOpen (U ∩ u ⁻¹' ψ.source) :=
    (hc.mono hUs).isOpen_inter_preimage hUo ψ.open_source
  exact ⟨Opens.interior ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (U ∩ u ⁻¹' ψ.source)),
    mem_interior_extend_target_inter_preimage hzt (hUψ.mem_nhds ⟨hxU, (interior_subset hz).2.2⟩),
    hU.hasWeakFDerivOn_chart hφ hψ⟩

/-- **Open-cover locality of weak differentials.** A candidate `du` is a weak differential on a
union `⋃ i, U i` of open sets if and only if it is a weak differential on each `U i`. -/
theorem hasWeakMFDerivOnGroupoid_iUnion_iff [CompleteSpace F] {ι : Sort*} {U : ι → Set X}
    (hU : ∀ i, IsOpen (U i)) :
    HasWeakMFDerivOnGroupoid G J I u du (⋃ i, U i) ↔
      ∀ i, HasWeakMFDerivOnGroupoid G J I u du (U i) := by
  refine ⟨fun h i ↦ h.mono (subset_iUnion U i), fun h ↦ ?_⟩
  rw [hasWeakMFDerivOnGroupoid_iff_locally (isOpen_iUnion hU)]
  rintro x ⟨_, ⟨i, rfl⟩, hxi⟩
  exact ⟨U i, subset_iUnion U i, hU i, hxi, h i⟩

/-- Gluing weak differentials on two open sets. -/
theorem HasWeakMFDerivOnGroupoid.union {s₁ s₂ : Set X}
    (hs₁ : IsOpen s₁) (hs₂ : IsOpen s₂) (h₁ : HasWeakMFDerivOnGroupoid G J I u du s₁)
    (h₂ : HasWeakMFDerivOnGroupoid G J I u du s₂) :
    HasWeakMFDerivOnGroupoid G J I u du (s₁ ∪ s₂) := by
  have hc : ContinuousOn u (s₁ ∪ s₂) := h₁.continuousOn.union_of_isOpen h₂.continuousOn hs₁ hs₂
  refine ⟨hc, fun φ hφ ψ hψ ↦ ?_⟩
  have : CompleteSpace F := (h₁.hasWeakFDerivOn_chart hφ hψ).completeSpace
  refine hasWeakFDerivOn_iff_locally.2 fun z hz ↦ ?_
  have hzt : (φ.extend J).target ∈ 𝓝 z :=
    mem_of_superset (isOpen_interior.mem_nhds hz) (interior_subset.trans inter_subset_left)
  rcases (interior_subset hz).2.1 with hzs₁ | hzs₂
  · refine ⟨Opens.interior ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (s₁ ∩ u ⁻¹' ψ.source)),
      mem_interior_extend_target_inter_preimage hzt
        ((h₁.1.isOpen_inter_preimage hs₁ ψ.open_source).mem_nhds ⟨hzs₁, (interior_subset hz).2.2⟩),
      h₁.hasWeakFDerivOn_chart hφ hψ⟩
  · refine ⟨Opens.interior ((φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (s₂ ∩ u ⁻¹' ψ.source)),
      mem_interior_extend_target_inter_preimage hzt
        ((h₂.1.isOpen_inter_preimage hs₂ ψ.open_source).mem_nhds ⟨hzs₂, (interior_subset hz).2.2⟩),
      h₂.hasWeakFDerivOn_chart hφ hψ⟩

/-! ### Classical consistency -/

/-- **Consistency with `mfderiv`.** A map `u : X → M` that is `C^n` (`1 ≤ n`) on an open set `s`
has `mfderiv J I u` as a weak differential on `s`, provided every chart of `G` belongs to the
`C¹` maximal atlas of `J`. Neither `I` nor `J` need be boundaryless. -/
theorem _root_.ContMDiffOn.hasWeakMFDerivOnGroupoid [CompleteSpace F] {n : ℕ∞ω}
    (hG : G.maximalAtlas X ⊆ IsManifold.maximalAtlas J 1 X)
    (hu : ContMDiffOn J I n u s) (hn : 1 ≤ n) (hs : IsOpen s) :
    HasWeakMFDerivOnGroupoid G J I u (fun x ↦ mfderiv J I u x) s := by
  refine ⟨hu.continuousOn, fun φ hφ ψ hψ ↦ ?_⟩
  set V := (φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)
  have hφc : ContMDiffOn 𝓘(ℝ, ℂ) J 1 (φ.extend J).symm (φ.extend J).target := by
    rw [φ.extend_target']; exact contMDiffOn_extend_symm (hG hφ)
  have hψ1 : ψ ∈ IsManifold.maximalAtlas I 1 M :=
    StructureGroupoid.maximalAtlas_mono (contDiffGroupoid_le (by exact_mod_cast le_top)) hψ
  have hcomp : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, F) 1 (ψ.extend I ∘ u ∘ (φ.extend J).symm) (interior V) :=
    (ψ.contMDiffOn_extend hψ1).comp
      ((hu.of_le hn).comp (hφc.mono (interior_subset.trans inter_subset_left))
        fun _ hz ↦ (interior_subset hz).2.1)
      fun _ hz ↦ (interior_subset hz).2.2
  refine ((contMDiffOn_iff_contDiffOn.1 hcomp).hasWeakFDerivOn_fderiv
    (μ := volume) (Ω := Opens.interior V)).congr_ae_deriv ?_
  filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with z hz
  refine (chartTangentHom_mfderiv (hG hφ) hψ1 (interior_mono inter_subset_left hz)
    (interior_subset hz).2.2 ?_).symm
  exact ((hu.of_le hn _ (interior_subset hz).2.1).contMDiffAt
    (hs.mem_nhds (interior_subset hz).2.1)).mdifferentiableAt one_ne_zero

/-! ### Null-set congruence and almost-everywhere uniqueness -/

/-- If `du` and `du'` agree outside a chartwise null subset of `s`, then `du'` is also a weak
differential of `u` on `s`. -/
theorem HasWeakMFDerivOnGroupoid.congr_deriv_of_isNullSet [IsManifold J 1 X]
    (hG : G.maximalAtlas X ⊆ IsManifold.maximalAtlas J 1 X)
    (h : HasWeakMFDerivOnGroupoid G J I u du s)
    (hnull : IsNullSet J {x ∈ s | du x ≠ du' x}) :
    HasWeakMFDerivOnGroupoid G J I u du' s := by
  refine ⟨h.1, fun φ hφ ψ hψ ↦ (h.2 φ hφ ψ hψ).congr_ae_deriv ?_⟩
  set V := (φ.extend J).target ∩ (φ.extend J).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)
  have hZnull : volume {z ∈ interior V |
      (φ.extend J).symm z ∈ {x ∈ s | du x ≠ du' x}} = 0 :=
    measure_mono_null
      (t := (φ.extend J).target ∩ (φ.extend J).symm ⁻¹' {x ∈ s | du x ≠ du' x})
      (fun _ hz ↦ ⟨(interior_subset hz.1).1, hz.2⟩)
      (hnull.measure_inter_preimage_extend_symm_eq_zero (hG hφ) volume)
  rw [EventuallyEq, Opens.coe_interior, ae_restrict_iff' isOpen_interior.measurableSet]
  filter_upwards [compl_mem_ae_iff.2 hZnull] with z hz hzV
  exact chartTangentHom_congr (not_not.1 fun hne ↦ hz ⟨hzV, (interior_subset hzV).2.1, hne⟩)

/-- For fixed preferred charts at `x₀` and `y₀`, the image under `extChartAt J x₀` of the interior
points of `s` where `du ≠ du'` and `(x, u x)` lies in those charts has Haar measure zero. -/
private theorem measure_image_interior_ne_eq_zero [IsManifold J 1 X] [HasGroupoid X G]
    [IsManifold I ∞ M] (hs : IsOpen s) (h₁ : HasWeakMFDerivOnGroupoid G J I u du s)
    (h₂ : HasWeakMFDerivOnGroupoid G J I u du' s) (x₀ : X) (y₀ : M)
    (μ : Measure ℂ) [μ.IsAddHaarMeasure] :
    μ (extChartAt J x₀ '' {x | x ∈ s ∧ du x ≠ du' x ∧ x ∈ (extChartAt J x₀).source ∧
      u x ∈ (chartAt H y₀).source ∧ J.IsInteriorPoint x}) = 0 := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by exact_mod_cast le_top)
  set V := (extChartAt J x₀).target ∩ (extChartAt J x₀).symm ⁻¹' (s ∩ u ⁻¹' (chartAt H y₀).source)
  have hae := (h₁.hasWeakFDerivOn_chart (StructureGroupoid.chart_mem_maximalAtlas G x₀)
    (IsManifold.chart_mem_maximalAtlas y₀)).ae_eq
      (h₂.hasWeakFDerivOn_chart (StructureGroupoid.chart_mem_maximalAtlas G x₀)
        (IsManifold.chart_mem_maximalAtlas y₀))
  rw [EventuallyEq, Opens.coe_interior, ae_restrict_iff' isOpen_interior.measurableSet,
    eventually_iff_exists_mem] at hae
  obtain ⟨S, hSae, hSeq⟩ := hae
  refine Measure.absolutelyContinuous_isAddHaarMeasure μ volume
    (measure_mono_null (t := Sᶜ) ?_ (mem_ae_iff.1 hSae))
  rintro _ ⟨x, ⟨hxs, hxne, hxsrc, hy, hxint⟩, rfl⟩ hzS
  have hxsrc' : x ∈ (chartAt H' x₀).source := by simpa only [extChartAt_source] using hxsrc
  have hzt : (extChartAt J x₀).target ∈ 𝓝 (extChartAt J x₀ x) :=
    ModelWithCorners.extChartAt_target_mem_nhds_of_isInteriorPoint one_ne_zero x₀ hxsrc hxint
  have hopen : IsOpen (s ∩ u ⁻¹' (chartAt H y₀).source) :=
    h₁.1.isOpen_inter_preimage hs (chartAt H y₀).open_source
  have hzV : extChartAt J x₀ x ∈ interior V :=
    mem_interior_extend_target_inter_preimage hzt
      (by rw [extChartAt, (chartAt H' x₀).extend_left_inv hxsrc']; exact hopen.mem_nhds ⟨hxs, hy⟩)
  exact hxne ((chartTangentHom_chartAt_eq_iff hxsrc' hy).1 (hSeq (extChartAt J x₀ x) hzS hzV))

/-- **Almost-everywhere uniqueness of the weak differential.** On an open set `s`, any two weak
differentials of `u` agree outside a chartwise null set (`TauCeti.IsNullSet J`), including when `X`
or `M` has boundary. -/
theorem HasWeakMFDerivOnGroupoid.isNullSet_ne [IsManifold J 1 X] [HasGroupoid X G]
    [IsManifold I ∞ M] (hs : IsOpen s) (h₁ : HasWeakMFDerivOnGroupoid G J I u du s)
    (h₂ : HasWeakMFDerivOnGroupoid G J I u du' s) :
    IsNullSet J {x ∈ s | du x ≠ du' x} := by
  rw [isNullSet_iff]; intro x₀ μ _
  -- Cover `W ⊆ ℂ` (hence second-countable) by countably many target-chart pullbacks.
  set W := interior ((extChartAt J x₀).target ∩ (extChartAt J x₀).symm ⁻¹' s)
  have hopen : ∀ y₀ : M,
      IsOpen (W ∩ (extChartAt J x₀).symm ⁻¹' (u ⁻¹' (chartAt H y₀).source)) := fun y₀ ↦
    (h₁.1.comp ((continuousOn_extChartAt_symm x₀).mono (interior_subset.trans inter_subset_left))
      fun _ hz ↦ (interior_subset hz).2).isOpen_inter_preimage
        isOpen_interior (chartAt H y₀).open_source
  obtain ⟨T, hTcnt, hTcov⟩ := isOpen_iUnion_countable _ hopen
  -- Split `{du ≠ du'}` into boundary points (`isNullSet_boundary`) and interior points covered by
  -- `T`, where Euclidean uniqueness applies on each `(x₀, y₀)` overlap.
  have hsub : extChartAt J x₀ '' ({x ∈ s | du x ≠ du' x} ∩ (extChartAt J x₀).source) ⊆
      extChartAt J x₀ '' (J.boundary X ∩ (extChartAt J x₀).source) ∪
        ⋃ y₀ ∈ T, extChartAt J x₀ '' {x | x ∈ s ∧ du x ≠ du' x ∧ x ∈ (extChartAt J x₀).source ∧
          u x ∈ (chartAt H y₀).source ∧ J.IsInteriorPoint x} := by
    rintro _ ⟨x, ⟨⟨hxs, hxne⟩, hxsrc⟩, rfl⟩
    have hxsrc' : x ∈ (chartAt H' x₀).source := by simpa only [extChartAt_source] using hxsrc
    by_cases hbd : J.IsInteriorPoint x
    · have hzt := ModelWithCorners.extChartAt_target_mem_nhds_of_isInteriorPoint
        one_ne_zero x₀ hxsrc hbd
      have hzW : extChartAt J x₀ x ∈ W :=
        mem_interior_extend_target_inter_preimage hzt
          (by rw [extChartAt, (chartAt H' x₀).extend_left_inv hxsrc']; exact hs.mem_nhds hxs)
      have hzU : extChartAt J x₀ x ∈
          ⋃ y₀ ∈ T, W ∩ (extChartAt J x₀).symm ⁻¹' (u ⁻¹' (chartAt H y₀).source) :=
        hTcov.symm ▸ mem_iUnion.2
          ⟨u ((extChartAt J x₀).symm (extChartAt J x₀ x)), hzW, mem_chart_source H _⟩
      rcases mem_iUnion₂.1 hzU with ⟨y₀, hy₀T, _, hy₀⟩
      rw [mem_preimage, mem_preimage, (extChartAt J x₀).left_inv hxsrc] at hy₀
      exact Or.inr (mem_iUnion₂.2 ⟨y₀, hy₀T, x, ⟨hxs, hxne, hxsrc, hy₀, hbd⟩, rfl⟩)
    · exact Or.inl ⟨x, ⟨(J.isBoundaryPoint_iff_not_isInteriorPoint x).2 hbd, hxsrc⟩, rfl⟩
  exact measure_mono_null hsub (measure_union_null (isNullSet_boundary.chartwise x₀ μ)
    ((measure_biUnion_null_iff hTcnt).2 fun y₀ _ ↦
      measure_image_interior_ne_eq_zero hs h₁ h₂ x₀ y₀ μ))

/-- On an open set `s` where `u` is `C^n` (`1 ≤ n`), any weak differential of `u` agrees with
`mfderiv J I u` outside a chartwise null set. -/
theorem HasWeakMFDerivOnGroupoid.isNullSet_ne_mfderiv [IsManifold J 1 X] [HasGroupoid X G]
    [IsManifold I ∞ M] {n : ℕ∞ω}
    (h : HasWeakMFDerivOnGroupoid G J I u du s)
    (hu : ContMDiffOn J I n u s) (hn : 1 ≤ n) (hs : IsOpen s) :
    IsNullSet J {x ∈ s | du x ≠ mfderiv J I u x} := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨x₀, _⟩
  · refine (isNullSet_iff J _).2 fun _ _ _ ↦ ?_
    simp
  · have : CompleteSpace F :=
      (h.hasWeakFDerivOn_chart (StructureGroupoid.chart_mem_maximalAtlas G x₀)
        (IsManifold.chart_mem_maximalAtlas (u x₀))).completeSpace
    let G' : StructureGroupoid H' := G ⊓ contDiffGroupoid 1 J
    have : HasGroupoid X G' := hasGroupoid_inf_iff.2 ⟨inferInstance, inferInstance⟩
    have h' : HasWeakMFDerivOnGroupoid G' J I u du s :=
      ⟨h.1, fun φ hφ ψ hψ ↦ h.2 φ (StructureGroupoid.maximalAtlas_mono inf_le_left hφ) ψ hψ⟩
    exact h'.isNullSet_ne hs
      (hu.hasWeakMFDerivOnGroupoid (StructureGroupoid.maximalAtlas_mono inf_le_right) hn hs)

end Groupoid

/-! ### Riemann surfaces without boundary -/

section BoundarylessSurface

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {u : X → M} {du du' : ∀ x : X, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace I (u x)} {s : Set X}

variable (I) in
/-- A family `du : ∀ x, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace I (u x)` is a weak differential
of `u : X → M` on `s ⊆ X`, for a Riemann surface `X` without boundary, if `u` is continuous on `s`
and `chartTangentHom 𝓘(ℝ, ℂ) I φ ψ u du` is a weak Fréchet derivative of `ψ.extend I ∘ u ∘ φ.symm`
in every holomorphic chart `φ` of `X` and every smooth chart `ψ` of `M`. -/
abbrev HasWeakMFDerivOn (u : X → M)
    (du : ∀ x : X, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace I (u x)) (s : Set X) : Prop :=
  HasWeakMFDerivOnGroupoid (contDiffGroupoid 1 𝓘(ℂ)) 𝓘(ℝ, ℂ) I u du s

variable (I) in
/-- A family `du : ∀ x, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace I (u x)` is a global weak
differential of `u : X → M` from a Riemann surface without boundary. -/
abbrev HasWeakMFDeriv (u : X → M)
    (du : ∀ x : X, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace I (u x)) : Prop :=
  HasWeakMFDerivGroupoid (contDiffGroupoid 1 𝓘(ℂ)) 𝓘(ℝ, ℂ) I u du

/-- Unfolding `HasWeakMFDerivOn` on an open set `s` of a Riemann surface without boundary, where
each chart overlap domain `φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)` is already open in `ℂ`. -/
theorem hasWeakMFDerivOn_iff (hs : IsOpen s) :
    HasWeakMFDerivOn I u du s ↔ ∃ hc : ContinuousOn u s,
      ∀ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
        HasWeakFDerivOn volume
          ⟨φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source),
            φ.isOpen_inter_preimage_symm_inter_preimage hc hs ψ.open_source⟩
          (ψ.extend I ∘ u ∘ φ.symm) (chartTangentHom 𝓘(ℝ, ℂ) I φ ψ u du) := by
  have ht (φ : OpenPartialHomeomorph X ℂ) : (φ.extend 𝓘(ℝ, ℂ)).target = φ.target := by
    simp [mfld_simps]
  have hs' (φ : OpenPartialHomeomorph X ℂ) : ⇑(φ.extend 𝓘(ℝ, ℂ)).symm = ⇑φ.symm := by
    ext z; simp [mfld_simps]
  have hEq (hc : ContinuousOn u s) (φ : OpenPartialHomeomorph X ℂ) (ψ : OpenPartialHomeomorph M H) :
      Opens.interior (φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) =
        ⟨φ.target ∩ φ.symm ⁻¹' (s ∩ u ⁻¹' ψ.source),
          φ.isOpen_inter_preimage_symm_inter_preimage hc hs ψ.open_source⟩ :=
    Opens.ext (φ.isOpen_inter_preimage_symm_inter_preimage hc hs ψ.open_source).interior_eq
  refine ⟨fun ⟨hc, h⟩ ↦ ⟨hc, fun φ hφ ψ hψ ↦ ?_⟩, fun ⟨hc, h⟩ ↦ ⟨hc, fun φ hφ ψ hψ ↦ ?_⟩⟩
  · have hchart := h φ hφ ψ hψ; rwa [ht φ, hs' φ, hEq hc φ ψ] at hchart
  · rw [ht φ, hs' φ, hEq hc φ ψ]; exact h φ hφ ψ hψ

/-- Unfolding `HasWeakMFDeriv` on a Riemann surface without boundary. -/
theorem hasWeakMFDeriv_iff :
    HasWeakMFDeriv I u du ↔ ∃ hc : Continuous u,
      ∀ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
        HasWeakFDerivOn volume
          ⟨φ.target ∩ φ.symm ⁻¹' (u ⁻¹' ψ.source),
            φ.isOpen_inter_preimage_symm (ψ.open_source.preimage hc)⟩
          (ψ.extend I ∘ u ∘ φ.symm) (chartTangentHom 𝓘(ℝ, ℂ) I φ ψ u du) := by
  refine hasWeakMFDerivOnGroupoid_univ.symm.trans ((hasWeakMFDerivOn_iff isOpen_univ).trans ?_)
  simp only [continuousOn_univ, univ_inter]

/-- A `C^n` map (`1 ≤ n`) on an open subset of a Riemann surface has `mfderiv 𝓘(ℝ, ℂ) I u` as a
weak differential. -/
theorem _root_.ContMDiffOn.hasWeakMFDerivOn [CompleteSpace F] {n : ℕ∞ω}
    (hu : ContMDiffOn 𝓘(ℝ, ℂ) I n u s) (hn : 1 ≤ n) (hs : IsOpen s) :
    HasWeakMFDerivOn I u (fun x ↦ mfderiv 𝓘(ℝ, ℂ) I u x) s :=
  hu.hasWeakMFDerivOnGroupoid
    (IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero 1 one_ne_zero) hn hs

/-- A `C^n` map (`1 ≤ n`) from a Riemann surface has `mfderiv 𝓘(ℝ, ℂ) I u` as a global weak
differential. -/
theorem _root_.ContMDiff.hasWeakMFDeriv [CompleteSpace F] {n : ℕ∞ω}
    (hu : ContMDiff 𝓘(ℝ, ℂ) I n u) (hn : 1 ≤ n) :
    HasWeakMFDeriv I u (fun x ↦ mfderiv 𝓘(ℝ, ℂ) I u x) :=
  hasWeakMFDerivOnGroupoid_univ.1 (hu.contMDiffOn.hasWeakMFDerivOn hn isOpen_univ)

/-- A map from a Riemann surface into a complex manifold modelled without boundary on a complex
Banach space that is holomorphic on an open set `s` has `mfderiv 𝓘(ℝ, ℂ) (I''.restrictScalars ℝ) f`
as a weak differential on `s`. -/
theorem _root_.MDifferentiableOn.hasWeakMFDerivOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners ℂ E H''} [I''.Boundaryless]
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H'' M']
    [IsManifold 𝓘(ℂ) 1 X] [IsManifold I'' 1 M'] {f : X → M'}
    (hf : MDifferentiableOn 𝓘(ℂ) I'' f s) (hs : IsOpen s) :
    HasWeakMFDerivOn (I''.restrictScalars ℝ) f
      (fun x ↦ mfderiv 𝓘(ℝ, ℂ) (I''.restrictScalars ℝ) f x) s := by
  have hf' := (hf.contMDiffOn (n := 1) hs).restrictScalars ℝ
  rw [modelWithCornersSelf_restrictScalars] at hf'
  exact hf'.hasWeakMFDerivOn le_rfl hs

/-- A holomorphic map from a Riemann surface into a complex manifold modelled without boundary on a
complex Banach space has `mfderiv` as a global weak differential. -/
theorem _root_.MDifferentiable.hasWeakMFDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners ℂ E H''} [I''.Boundaryless]
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H'' M']
    [IsManifold 𝓘(ℂ) 1 X] [IsManifold I'' 1 M'] {f : X → M'}
    (hf : MDifferentiable 𝓘(ℂ) I'' f) :
    HasWeakMFDeriv (I''.restrictScalars ℝ) f
      (fun x ↦ mfderiv 𝓘(ℝ, ℂ) (I''.restrictScalars ℝ) f x) :=
  hasWeakMFDerivOnGroupoid_univ.1 (hf.mdifferentiableOn.hasWeakMFDerivOn isOpen_univ)

/-- Almost-everywhere uniqueness of the weak differential on a Riemann surface without boundary. -/
theorem HasWeakMFDerivOn.isNullSet_ne [IsManifold 𝓘(ℂ) 1 X] [IsManifold I ∞ M] (hs : IsOpen s)
    (h₁ : HasWeakMFDerivOn I u du s) (h₂ : HasWeakMFDerivOn I u du' s) :
    IsNullSet 𝓘(ℝ, ℂ) {x ∈ s | du x ≠ du' x} := by
  have : IsManifold 𝓘(ℝ, ℂ) 1 X :=
    IsManifold.restrictScalars_of_ne_zero 1 one_ne_zero inferInstance
  exact HasWeakMFDerivOnGroupoid.isNullSet_ne hs h₁ h₂

/-- Null-set congruence of the weak differential on a Riemann surface without boundary. -/
theorem HasWeakMFDerivOn.congr_deriv_of_isNullSet [IsManifold 𝓘(ℂ) 1 X]
    (h : HasWeakMFDerivOn I u du s) (hnull : IsNullSet 𝓘(ℝ, ℂ) {x ∈ s | du x ≠ du' x}) :
    HasWeakMFDerivOn I u du' s := by
  have : IsManifold 𝓘(ℝ, ℂ) 1 X :=
    IsManifold.restrictScalars_of_ne_zero 1 one_ne_zero inferInstance
  exact HasWeakMFDerivOnGroupoid.congr_deriv_of_isNullSet
    (IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero 1 one_ne_zero) h hnull

/-- On an open set where `u` is `C^n` (`1 ≤ n`), any weak differential agrees with
`mfderiv 𝓘(ℝ, ℂ) I u` outside a chartwise null set. -/
theorem HasWeakMFDerivOn.isNullSet_ne_mfderiv [IsManifold 𝓘(ℂ) 1 X] [IsManifold I ∞ M] {n : ℕ∞ω}
    (h : HasWeakMFDerivOn I u du s)
    (hu : ContMDiffOn 𝓘(ℝ, ℂ) I n u s) (hn : 1 ≤ n) (hs : IsOpen s) :
    IsNullSet 𝓘(ℝ, ℂ) {x ∈ s | du x ≠ mfderiv 𝓘(ℝ, ℂ) I u x} := by
  have : IsManifold 𝓘(ℝ, ℂ) 1 X :=
    IsManifold.restrictScalars_of_ne_zero 1 one_ne_zero inferInstance
  exact HasWeakMFDerivOnGroupoid.isNullSet_ne_mfderiv h hu hn hs

end BoundarylessSurface

/-! ### Riemann surfaces with boundary -/

section BorderedSurface

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ClosedUpperHalfPlane X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {u : X → M}
  {du du' : ∀ x : X, TangentSpace closedUpperHalfPlaneModel x →L[ℝ] TangentSpace I (u x)}
  {s : Set X}

/-- Every bordered-holomorphic chart belongs to the `C¹` maximal atlas of
`closedUpperHalfPlaneModel`. -/
private theorem borderedHolomorphicGroupoid_maximalAtlas_subset :
    borderedHolomorphicGroupoid.maximalAtlas X ⊆
      IsManifold.maximalAtlas closedUpperHalfPlaneModel 1 X :=
  StructureGroupoid.maximalAtlas_mono
    (borderedHolomorphicGroupoid_le_contDiffGroupoid.trans
      (contDiffGroupoid_le (by exact_mod_cast le_top)))

variable (I) in
/-- A family `du : ∀ x, TangentSpace closedUpperHalfPlaneModel x →L[ℝ] TangentSpace I (u x)` is a
weak differential of `u : X → M` on `s ⊆ X`, for a Riemann surface `X` with boundary, if `u` is
continuous on `s` and `chartTangentHom closedUpperHalfPlaneModel I φ ψ u du` is a weak Fréchet
derivative of `ψ.extend I ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm` on the open interior of
every bordered-holomorphic/smooth chart overlap domain. -/
abbrev HasWeakMFDerivOnBordered (u : X → M)
    (du : ∀ x : X, TangentSpace closedUpperHalfPlaneModel x →L[ℝ] TangentSpace I (u x))
    (s : Set X) : Prop :=
  HasWeakMFDerivOnGroupoid borderedHolomorphicGroupoid closedUpperHalfPlaneModel I u du s

variable (I) in
/-- A family `du` is a global weak differential of `u : X → M` on a Riemann surface with
boundary. -/
abbrev HasWeakMFDerivBordered (u : X → M)
    (du : ∀ x : X, TangentSpace closedUpperHalfPlaneModel x →L[ℝ] TangentSpace I (u x)) : Prop :=
  HasWeakMFDerivGroupoid borderedHolomorphicGroupoid closedUpperHalfPlaneModel I u du

/-- A `C^n` map (`1 ≤ n`) on an open subset of a Riemann surface with boundary has
`mfderiv closedUpperHalfPlaneModel I u` as a weak differential. -/
theorem _root_.ContMDiffOn.hasWeakMFDerivOnBordered [CompleteSpace F] {n : ℕ∞ω}
    (hu : ContMDiffOn closedUpperHalfPlaneModel I n u s) (hn : 1 ≤ n) (hs : IsOpen s) :
    HasWeakMFDerivOnBordered I u (fun x ↦ mfderiv closedUpperHalfPlaneModel I u x) s :=
  hu.hasWeakMFDerivOnGroupoid borderedHolomorphicGroupoid_maximalAtlas_subset hn hs

/-- A `C^n` map (`1 ≤ n`) from a Riemann surface with boundary has
`mfderiv closedUpperHalfPlaneModel I u` as a global weak differential. -/
theorem _root_.ContMDiff.hasWeakMFDerivBordered [CompleteSpace F] {n : ℕ∞ω}
    (hu : ContMDiff closedUpperHalfPlaneModel I n u) (hn : 1 ≤ n) :
    HasWeakMFDerivBordered I u (fun x ↦ mfderiv closedUpperHalfPlaneModel I u x) :=
  hasWeakMFDerivOnGroupoid_univ.1 (hu.contMDiffOn.hasWeakMFDerivOnBordered hn isOpen_univ)

/-- Almost-everywhere uniqueness (`IsNullSet closedUpperHalfPlaneModel`) of the weak differential
on a Riemann surface with boundary. Notice `∂X` is automatically null (`isNullSet_boundary`). -/
theorem HasWeakMFDerivOnBordered.isNullSet_ne
    [HasGroupoid X borderedHolomorphicGroupoid] [IsManifold I ∞ M] (hs : IsOpen s)
    (h₁ : HasWeakMFDerivOnBordered I u du s) (h₂ : HasWeakMFDerivOnBordered I u du' s) :
    IsNullSet closedUpperHalfPlaneModel {x ∈ s | du x ≠ du' x} :=
  HasWeakMFDerivOnGroupoid.isNullSet_ne hs h₁ h₂

/-- Null-set congruence of the weak differential on a Riemann surface with boundary. -/
theorem HasWeakMFDerivOnBordered.congr_deriv_of_isNullSet
    [HasGroupoid X borderedHolomorphicGroupoid]
    (h : HasWeakMFDerivOnBordered I u du s)
    (hnull : IsNullSet closedUpperHalfPlaneModel {x ∈ s | du x ≠ du' x}) :
    HasWeakMFDerivOnBordered I u du' s :=
  HasWeakMFDerivOnGroupoid.congr_deriv_of_isNullSet
    borderedHolomorphicGroupoid_maximalAtlas_subset h hnull

/-- On an open subset of a Riemann surface with boundary where `u` is `C^n` (`1 ≤ n`), any weak
differential agrees with `mfderiv closedUpperHalfPlaneModel I u` outside a chartwise null set. -/
theorem HasWeakMFDerivOnBordered.isNullSet_ne_mfderiv
    [HasGroupoid X borderedHolomorphicGroupoid] [IsManifold I ∞ M] {n : ℕ∞ω}
    (h : HasWeakMFDerivOnBordered I u du s)
    (hu : ContMDiffOn closedUpperHalfPlaneModel I n u s) (hn : 1 ≤ n) (hs : IsOpen s) :
    IsNullSet closedUpperHalfPlaneModel {x ∈ s | du x ≠ mfderiv closedUpperHalfPlaneModel I u x} :=
  HasWeakMFDerivOnGroupoid.isNullSet_ne_mfderiv h hu hn hs

end BorderedSurface

/-! ### Concrete checks on the complex plane -/

section Checks

/-- Complex conjugation `conj : ℂ → ℂ` has weak differential `Complex.conjCLE` (transported to
`TangentSpace 𝓘(ℝ, ℂ)`), agreeing with `mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) conj`. -/
theorem hasWeakMFDeriv_conj :
    HasWeakMFDeriv 𝓘(ℝ, ℂ) (conj : ℂ → ℂ)
      (fun z ↦ (NormedSpace.fromTangentSpace (𝕜 := ℝ) (conj z)).symm.toContinuousLinearMap ∘L
        Complex.conjCLE.toContinuousLinearMap ∘L
        (NormedSpace.fromTangentSpace (𝕜 := ℝ) z).toContinuousLinearMap) := by
  have hcont : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (conj : ℂ → ℂ) :=
    contMDiff_iff_contDiff.2 Complex.conjCLE.contDiff
  have heq : (fun z ↦ mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (conj : ℂ → ℂ) z) =
      fun z ↦ (NormedSpace.fromTangentSpace (𝕜 := ℝ) (conj z)).symm.toContinuousLinearMap ∘L
        Complex.conjCLE.toContinuousLinearMap ∘L
        (NormedSpace.fromTangentSpace (𝕜 := ℝ) z).toContinuousLinearMap := by
    ext z v
    rw [mfderiv_eq_fderiv, ← funext Complex.conjCLE_apply, Complex.conjCLE.fderiv]
  exact heq ▸ hcont.hasWeakMFDeriv (by exact_mod_cast le_top)

/-- On any nonempty open subset `s ⊆ ℂ`, `0` is not a weak differential of `id : ℂ → ℂ`, even
though the `(0, 1)`-part of its differential vanishes identically. -/
theorem not_hasWeakMFDerivOn_id_zero {s : Set ℂ} (hs : IsOpen s) (hne : s.Nonempty) :
    ¬ HasWeakMFDerivOn 𝓘(ℝ, ℂ) (id : ℂ → ℂ) (fun _ ↦ 0) s := by
  intro h0
  have hnull := h0.isNullSet_ne_mfderiv contMDiffOn_id le_top hs
  have hsub : s ⊆ {z ∈ s | (0 : TangentSpace 𝓘(ℝ, ℂ) z →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) z) ≠
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (id : ℂ → ℂ) z} := by
    intro z hzs
    refine ⟨hzs, fun heq ↦ one_ne_zero (α := ℂ) ?_⟩
    rw [mfderiv_id] at heq
    have hv := DFunLike.congr_fun heq ((NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm 1)
    simpa using congrArg (NormedSpace.fromTangentSpace (𝕜 := ℝ) z) hv.symm
  have hint := (hnull.mono hsub).interior_eq_empty
  rw [hs.interior_eq] at hint
  exact hne.ne_empty hint

/-- On any nonempty open subset `s ⊆ ℂ`, `0` is not a weak differential of `conj : ℂ → ℂ`, even
though the `(1, 0)`-part of its differential vanishes identically: `du` retains both `(1, 0)`
and `(0, 1)` components. -/
theorem not_hasWeakMFDerivOn_conj_zero {s : Set ℂ} (hs : IsOpen s) (hne : s.Nonempty) :
    ¬ HasWeakMFDerivOn 𝓘(ℝ, ℂ) (conj : ℂ → ℂ) (fun _ ↦ 0) s := by
  intro h0
  have hnull := h0.isNullSet_ne hs hasWeakMFDeriv_conj.hasWeakMFDerivOnGroupoid
  have hsub : s ⊆ {z ∈ s | (0 : TangentSpace 𝓘(ℝ, ℂ) z →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (conj z)) ≠
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (conj z)).symm.toContinuousLinearMap ∘L
        Complex.conjCLE.toContinuousLinearMap ∘L
        (NormedSpace.fromTangentSpace (𝕜 := ℝ) z).toContinuousLinearMap} := by
    intro z hzs
    refine ⟨hzs, fun heq ↦ one_ne_zero (α := ℂ) ?_⟩
    have hv := DFunLike.congr_fun heq ((NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm 1)
    simpa using congrArg (NormedSpace.fromTangentSpace (𝕜 := ℝ) (conj z)) hv.symm
  have hint := (hnull.mono hsub).interior_eq_empty
  rw [hs.interior_eq] at hint
  exact hne.ne_empty hint

end Checks

end TauCeti
