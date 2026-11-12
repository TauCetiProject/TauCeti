/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.Interior
public import TauCeti.Geometry.Manifold.Sobolev.LocalMap
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Sobolev.Local.Examples
import TauCeti.Analysis.Sobolev.Local.Locality
import TauCeti.Analysis.Sobolev.Trace.Reflection.HalfSpace

/-!
# Local Sobolev maps from a Riemann surface with boundary into a manifold

Let `X` be a Riemann surface with boundary, given as a charted space modelled on the closed upper
half-plane `ClosedUpperHalfPlane` whose chart changes lie in `TauCeti.borderedHolomorphicGroupoid`,
and let `M` be a smooth manifold modelled on `I : ModelWithCorners ℝ F H`. A map `u : X → M` lies
in the local Sobolev class `W^{k,p}_loc(X, M)` up to the boundary
(`TauCeti.MemWkpLocMapBordered I p k u`) when it is continuous and every coordinate expression
`ψ.extend I ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm` belongs to the planar local Sobolev
class `TauCeti.MemWkpLoc p _ k` on the part of the extended target of `φ` where `u` maps into the
source of `ψ`. Here `φ` runs over all bordered holomorphic charts of `X`, the charts of the
maximal atlas of `TauCeti.borderedHolomorphicGroupoid`, and `ψ` over all charts of the maximal
smooth atlas of `M`.

The extended target of a chart of `X` lies in the closed upper half-plane `{z | 0 ≤ z.im}` of
`ℂ`, and the domain of a coordinate expression is relatively open there: it has the form
`Ω ∩ {z | 0 ≤ z.im}` for an open `Ω ⊆ ℂ`. The planar class `TauCeti.MemWkpLoc` on such a
half-disc type set imposes its `Lᵖ` bounds on compact sets reaching the real axis, so the
definition controls the map up to the boundary of `X`. This is the boundary-chart counterpart
of `TauCeti.MemWkpLocMapOn`, which treats Riemann surfaces without boundary.

The relative version `TauCeti.MemWkpLocMapOnBordered I p k u s` asks for continuity on `s` and
tests the coordinate expressions over `s`; it is intended for open subsets `s` of `X`.

## Main declarations

* `TauCeti.MemWkpLocMapOnBordered`, `TauCeti.MemWkpLocMapBordered`: local Sobolev maps on a
  subset and on the whole surface with boundary.
* `TauCeti.memWkpLocMapOnBordered_iff`, `TauCeti.MemWkpLocMapOnBordered.memWkpLoc_chart`:
  unfolding the definition and reading off the coordinate expressions.
* `TauCeti.MemWkpLocMapOnBordered.mono`, `TauCeti.MemWkpLocMapOnBordered.of_le`,
  `TauCeti.MemWkpLocMapOnBordered.mono_exponent`: restriction to a smaller set, decreasing the
  derivative order or the integrability exponent.
* `ContDiffOn.memWkpLoc_inter_setOf_im_nonneg`: a map that is `Cᵏ` on a relatively open subset
  `Ω ∩ {z | 0 ≤ z.im}` of the closed upper half-plane is in the local class `W^{k,p}` there, with
  bounds reaching the real axis. It is extended across the axis near each boundary point by
  `TauCeti.HalfSpaceExtension.exists_local_contDiff_extension_halfSpace`, read in the coordinates
  `(im z, re z)`.
* `ContMDiffOn.memWkpLocMapOnBordered`, `ContMDiff.memWkpLocMapBordered`: `C^n` maps belong to the
  class of every order `k ≤ n`, for every exponent.
* `TauCeti.MemWkpLocMapOn.memWkpLocMapOnBordered_image`: on an open subset of the interior
  `TauCeti.borderedInterior X`, a local Sobolev map for the Riemann surface structure of the
  interior is a local Sobolev map up to the boundary, with the same order and exponent. The
  coordinate expressions in a bordered holomorphic chart are those in its restriction to the
  interior, read in `ℂ` through the open upper half-plane.
* `TauCeti.not_memWkpLocMapOnBordered_sqrt_im`: on the closed upper half-disc, `z ↦ √(Im z)` is
  continuous but is not in the class of order `1` for any `p ≥ 2`, since the boundary chart
  tests its derivative `(2 √(Im z))⁻¹` on compact sets reaching the real axis.

## Implementation notes

As for `TauCeti.MemWkpLocMapOn`, the charts tested are those of the maximal atlases and the
definitions carry no manifold hypotheses; they are meant for
`HasGroupoid X borderedHolomorphicGroupoid` and `IsManifold I ∞ M`. That it suffices to test one
atlas of `X` near the boundary needs the change of variables for the half-disc classes along
bordered holomorphic chart changes, which are smooth only up to the real axis, and is not part of
this file. Neither is the converse of the comparison with the interior class, which tests charts
of the interior with values anywhere in `ℂ`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 and Section 2.4.
-/

public section

open Set Filter MeasureTheory TopologicalSpace
open scoped Manifold ContDiff Topology

noncomputable section

namespace TauCeti

/-! ### Smooth functions on relatively open subsets of the closed upper half-plane -/

section Planar

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ENNReal} {k : ℕ}

/-- The real coordinates `(im z, re z)` of `ℂ`, with the normal coordinate first, as used by the
half-space extension. -/
private def imReEquiv : ℂ ≃L[ℝ] ℝ × ℝ :=
  Complex.equivRealProdCLM.trans (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ)

private theorem imReEquiv_apply (z : ℂ) : imReEquiv z = (z.im, z.re) :=
  rfl

private theorem im_imReEquiv_symm (w : ℝ × ℝ) : (imReEquiv.symm w).im = w.1 := by
  obtain ⟨z, rfl⟩ := imReEquiv.surjective w
  rw [ContinuousLinearEquiv.symm_apply_apply, imReEquiv_apply]

/-- Near every point of a relatively open subset `Ω ∩ {z | 0 ≤ z.im}` of the closed upper
half-plane, a `Cᵏ` map on it agrees with a map that is `Cᵏ` on an open neighbourhood of the
point. At a point of the real axis the extension reflects across the axis. -/
private theorem exists_contDiffOn_eqOn_inter_setOf_im_nonneg {f : ℂ → F} {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ k f (Ω ∩ {z | 0 ≤ z.im})) {x : ℂ}
    (hx : x ∈ Ω ∩ {z | 0 ≤ z.im}) :
    ∃ W : Set ℂ, IsOpen W ∧ x ∈ W ∧ ∃ g : ℂ → F, ContDiffOn ℝ k g W ∧
      EqOn g f ((Ω ∩ {z | 0 ≤ z.im}) ∩ W) := by
  rcases (show 0 ≤ x.im from hx.2).lt_or_eq with hpos | hzero
  · exact ⟨Ω ∩ {z | 0 < z.im}, hΩ.inter (isOpen_lt continuous_const Complex.continuous_im),
      ⟨hx.1, hpos⟩, f, hf.mono fun z hz ↦ ⟨hz.1, show 0 ≤ z.im from le_of_lt hz.2⟩, fun _ _ ↦ rfl⟩
  · have hfe : ContDiffOn ℝ k (f ∘ imReEquiv.symm)
        (HalfSpaceExtension.upperHalfSpace ℝ ∩ imReEquiv.symm ⁻¹' Ω) := by
      refine hf.comp imReEquiv.symm.contDiff.contDiffOn fun w hw ↦ ⟨hw.2, ?_⟩
      have h1 : 0 ≤ w.1 := HalfSpaceExtension.mem_upperHalfSpace.1 hw.1
      simpa only [mem_ofPred_eq, im_imReEquiv_symm] using h1
    have hxΩ : ((0 : ℝ), x.re) ∈ imReEquiv.symm ⁻¹' Ω := by
      rw [mem_preimage, hzero, ← imReEquiv_apply, ContinuousLinearEquiv.symm_apply_apply]
      exact hx.1
    obtain ⟨g, hg, hgf⟩ := HalfSpaceExtension.exists_local_contDiff_extension_halfSpace k
      (f ∘ imReEquiv.symm) (hΩ.preimage imReEquiv.symm.continuous) hfe x.re hxΩ
    obtain ⟨T, hT, hTo, hxT⟩ := eventually_nhds_iff.1 hgf
    refine ⟨imReEquiv ⁻¹' T, hTo.preimage imReEquiv.continuous, ?_, g ∘ imReEquiv,
      (hg.comp imReEquiv.contDiff).contDiffOn, fun z hz ↦ ?_⟩
    · rw [mem_preimage, imReEquiv_apply, ← hzero]
      exact hxT
    · have h := hT _ hz.2 (by simpa only [imReEquiv_apply] using (show 0 ≤ z.im from hz.1.2))
      simpa only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply] using h

/-- A map that is `Cᵏ` on a relatively open subset `Ω ∩ {z | 0 ≤ z.im}` of the closed upper
half-plane, for an open `Ω`, is in the local Sobolev class of order `k` there, for every
exponent. The `Lᵖ` bounds reach the real axis: near a boundary point the map extends to a `Cᵏ`
map across the axis. -/
theorem _root_.ContDiffOn.memWkpLoc_inter_setOf_im_nonneg [CompleteSpace F] {f : ℂ → F}
    {Ω : Set ℂ} (hf : ContDiffOn ℝ k f (Ω ∩ {z | 0 ≤ z.im})) (hΩ : IsOpen Ω) :
    MemWkpLoc p (Ω ∩ {z | 0 ≤ z.im}) k f := by
  have hUm : MeasurableSet (Ω ∩ {z : ℂ | 0 ≤ z.im}) :=
    hΩ.measurableSet.inter (isClosed_le continuous_const Complex.continuous_im).measurableSet
  refine memWkpLoc_iff_locally.2 fun x hx ↦ ?_
  obtain ⟨W, hWo, hxW, g, hg, hgf⟩ := exists_contDiffOn_eqOn_inter_setOf_im_nonneg hΩ hf hx
  refine ⟨_ ∩ W, inter_mem_nhdsWithin _ (hWo.mem_nhds hxW), ?_⟩
  exact (hg.memWkpLoc (Ω := ⟨W, hWo⟩) (p := p) inter_subset_right).congr_ae
    ((ae_restrict_iff' (hUm.inter hWo.measurableSet)).2 (Eventually.of_forall hgf))

end Planar

/-! ### The class of local Sobolev maps up to the boundary -/

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ClosedUpperHalfPlane X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {p q : ENNReal} {k l : ℕ} {u : X → M} {s t : Set X}

variable (I) in
/-- A map `u : X → M` from a Riemann surface with boundary is in the local Sobolev class
`W^{k,p}_loc` on `s ⊆ X` if it is continuous on `s` and, for every bordered holomorphic chart `φ`
of `X` and every smooth chart `ψ` of `M`, the coordinate expression
`ψ.extend I ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm` is in the planar class
`MemWkpLoc p _ k` on the part of the extended target of `φ` over `s` where `u` maps into the
source of `ψ`. That part is relatively open in the closed upper half-plane, and the `Lᵖ` bounds
reach the real axis. The definition is intended for open `s`. -/
def MemWkpLocMapOnBordered (p : ENNReal) (k : ℕ) (u : X → M) (s : Set X) : Prop :=
  ContinuousOn u s ∧
    ∀ φ ∈ borderedHolomorphicGroupoid.maximalAtlas X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
      MemWkpLoc p ((φ.extend closedUpperHalfPlaneModel).target ∩
          (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) k
        (ψ.extend I ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm)

variable (I) in
/-- A map `u : X → M` from a Riemann surface with boundary is in the local Sobolev class
`W^{k,p}_loc(X, M)` if it is continuous and, for every bordered holomorphic chart `φ` of `X` and
every smooth chart `ψ` of `M`, the coordinate expression
`ψ.extend I ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm` is in the planar class
`MemWkpLoc p _ k` on the part of the extended target of `φ` where `u` maps into the source of
`ψ`, with `Lᵖ` bounds reaching the real axis. -/
def MemWkpLocMapBordered (p : ENNReal) (k : ℕ) (u : X → M) : Prop :=
  Continuous u ∧
    ∀ φ ∈ borderedHolomorphicGroupoid.maximalAtlas X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
      MemWkpLoc p ((φ.extend closedUpperHalfPlaneModel).target ∩
          (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (u ⁻¹' ψ.source)) k
        (ψ.extend I ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm)

/-- Unfolding the definition of the relative local Sobolev class up to the boundary. -/
theorem memWkpLocMapOnBordered_iff : MemWkpLocMapOnBordered I p k u s ↔ ContinuousOn u s ∧
    ∀ φ ∈ borderedHolomorphicGroupoid.maximalAtlas X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
      MemWkpLoc p ((φ.extend closedUpperHalfPlaneModel).target ∩
          (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) k
        (ψ.extend I ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm) :=
  Iff.rfl

/-- Unfolding the definition of the local Sobolev class up to the boundary. -/
theorem memWkpLocMapBordered_iff : MemWkpLocMapBordered I p k u ↔ Continuous u ∧
    ∀ φ ∈ borderedHolomorphicGroupoid.maximalAtlas X, ∀ ψ ∈ IsManifold.maximalAtlas I ∞ M,
      MemWkpLoc p ((φ.extend closedUpperHalfPlaneModel).target ∩
          (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (u ⁻¹' ψ.source)) k
        (ψ.extend I ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm) :=
  Iff.rfl

/-- The coordinate expression of a local Sobolev map on `s` in a bordered holomorphic chart `φ`
and a smooth chart `ψ` is in the planar class on the part of the extended target of `φ` over `s`
where `u` maps into the source of `ψ`. -/
theorem MemWkpLocMapOnBordered.memWkpLoc_chart (hu : MemWkpLocMapOnBordered I p k u s)
    {φ : OpenPartialHomeomorph X ClosedUpperHalfPlane}
    (hφ : φ ∈ borderedHolomorphicGroupoid.maximalAtlas X) {ψ : OpenPartialHomeomorph M H}
    (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M) :
    MemWkpLoc p ((φ.extend closedUpperHalfPlaneModel).target ∩
        (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) k
      (ψ.extend I ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm) :=
  hu.2 φ hφ ψ hψ

/-- The coordinate expression of a local Sobolev map in a bordered holomorphic chart `φ` and a
smooth chart `ψ` is in the planar class on the part of the extended target of `φ` where `u` maps
into the source of `ψ`. -/
theorem MemWkpLocMapBordered.memWkpLoc_chart (hu : MemWkpLocMapBordered I p k u)
    {φ : OpenPartialHomeomorph X ClosedUpperHalfPlane}
    (hφ : φ ∈ borderedHolomorphicGroupoid.maximalAtlas X) {ψ : OpenPartialHomeomorph M H}
    (hψ : ψ ∈ IsManifold.maximalAtlas I ∞ M) :
    MemWkpLoc p ((φ.extend closedUpperHalfPlaneModel).target ∩
        (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (u ⁻¹' ψ.source)) k
      (ψ.extend I ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm) :=
  hu.2 φ hφ ψ hψ

/-- On the whole surface, the relative class is the class of maps from the surface. -/
@[simp]
theorem memWkpLocMapOnBordered_univ :
    MemWkpLocMapOnBordered I p k u univ ↔ MemWkpLocMapBordered I p k u := by
  simp only [MemWkpLocMapOnBordered, MemWkpLocMapBordered, continuousOn_univ, univ_inter]

/-- A local Sobolev map on `s` is continuous on `s`. -/
theorem MemWkpLocMapOnBordered.continuousOn (hu : MemWkpLocMapOnBordered I p k u s) :
    ContinuousOn u s :=
  hu.1

/-- A local Sobolev map is continuous. -/
theorem MemWkpLocMapBordered.continuous (hu : MemWkpLocMapBordered I p k u) : Continuous u :=
  hu.1

/-- Restriction to a smaller set, in particular to an open subset, preserves the class. -/
theorem MemWkpLocMapOnBordered.mono (hu : MemWkpLocMapOnBordered I p k u s) (hts : t ⊆ s) :
    MemWkpLocMapOnBordered I p k u t :=
  ⟨hu.1.mono hts, fun φ hφ ψ hψ ↦ (hu.2 φ hφ ψ hψ).mono
    (inter_subset_inter_right _ (preimage_mono (inter_subset_inter_left _ hts)))⟩

/-- A local Sobolev map is a local Sobolev map on every subset. -/
theorem MemWkpLocMapBordered.memWkpLocMapOnBordered (hu : MemWkpLocMapBordered I p k u) :
    MemWkpLocMapOnBordered I p k u s :=
  (memWkpLocMapOnBordered_univ.mpr hu).mono (subset_univ s)

/-- Membership at any smaller derivative order follows from membership at a larger one. -/
theorem MemWkpLocMapOnBordered.of_le (hu : MemWkpLocMapOnBordered I p k u s) (hlk : l ≤ k) :
    MemWkpLocMapOnBordered I p l u s :=
  ⟨hu.1, fun φ hφ ψ hψ ↦ (hu.2 φ hφ ψ hψ).of_le hlk⟩

/-- Membership at any smaller derivative order follows from membership at a larger one. -/
theorem MemWkpLocMapBordered.of_le (hu : MemWkpLocMapBordered I p k u) (hlk : l ≤ k) :
    MemWkpLocMapBordered I p l u :=
  ⟨hu.1, fun φ hφ ψ hψ ↦ (hu.2 φ hφ ψ hψ).of_le hlk⟩

/-- Decreasing the integrability exponent preserves the class. -/
theorem MemWkpLocMapOnBordered.mono_exponent (hu : MemWkpLocMapOnBordered I p k u s)
    (hqp : q ≤ p) : MemWkpLocMapOnBordered I q k u s :=
  ⟨hu.1, fun φ hφ ψ hψ ↦ (hu.2 φ hφ ψ hψ).mono_exponent hqp⟩

/-- Decreasing the integrability exponent preserves the class. -/
theorem MemWkpLocMapBordered.mono_exponent (hu : MemWkpLocMapBordered I p k u) (hqp : q ≤ p) :
    MemWkpLocMapBordered I q k u :=
  ⟨hu.1, fun φ hφ ψ hψ ↦ (hu.2 φ hφ ψ hψ).mono_exponent hqp⟩

/-! ### Smooth maps -/

omit [ChartedSpace ClosedUpperHalfPlane X] in
/-- The part of the extended target of a chart of `X` lying over an open set is relatively open
in the closed upper half-plane. -/
private theorem exists_isOpen_extend_target_inter_preimage
    (φ : OpenPartialHomeomorph X ClosedUpperHalfPlane) {W : Set X} (hW : IsOpen W) :
    ∃ Ω : Set ℂ, IsOpen Ω ∧ (φ.extend closedUpperHalfPlaneModel).target ∩
      (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' W = Ω ∩ {z | 0 ≤ z.im} := by
  have hcont : ContinuousOn (φ.symm ∘ closedUpperHalfPlaneModel.symm)
      (closedUpperHalfPlaneModel.symm ⁻¹' φ.target) :=
    φ.continuousOn_symm.comp closedUpperHalfPlaneModel.continuous_symm.continuousOn
      fun _ hz ↦ hz
  refine ⟨_, hcont.isOpen_inter_preimage
    (φ.open_target.preimage closedUpperHalfPlaneModel.continuous_symm) hW, ?_⟩
  ext z
  simp only [OpenPartialHomeomorph.extend_target, OpenPartialHomeomorph.extend_coe_symm,
    range_closedUpperHalfPlaneModel, mem_inter_iff, mem_preimage, mem_ofPred_eq]
  tauto

/-- A map that is `C^n` on an open set, for the smooth structure of the Riemann surface with
boundary and a manifold `M` modelled on a real Banach space, is a local Sobolev map up to the
boundary on that set, of every order `k ≤ n` and every exponent. -/
theorem _root_.ContMDiffOn.memWkpLocMapOnBordered [CompleteSpace F] {n : ℕ∞ω}
    (hu : ContMDiffOn closedUpperHalfPlaneModel I n u s) (hk : (k : ℕ∞ω) ≤ n) (hs : IsOpen s) :
    MemWkpLocMapOnBordered I p k u s := by
  refine ⟨hu.continuousOn, fun φ hφ ψ hψ ↦ ?_⟩
  have hφ' : φ ∈ IsManifold.maximalAtlas closedUpperHalfPlaneModel k X :=
    StructureGroupoid.maximalAtlas_mono (borderedHolomorphicGroupoid_le_contDiffGroupoid.trans
      (contDiffGroupoid_le (by exact_mod_cast le_top))) hφ
  have hψ' : ContMDiffOn I 𝓘(ℝ, F) k (ψ.extend I) ψ.source :=
    (ψ.contMDiffOn_extend hψ).of_le (by exact_mod_cast le_top)
  have hcomp : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, F) k
      (ψ.extend I ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm)
      ((φ.extend closedUpperHalfPlaneModel).target ∩
        (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' (s ∩ u ⁻¹' ψ.source)) := by
    refine hψ'.comp ((hu.of_le hk).comp ((contMDiffOn_extend_symm hφ').mono ?_)
      fun _ hz ↦ hz.2.1) fun _ hz ↦ hz.2.2
    rw [← OpenPartialHomeomorph.extend_target']
    exact inter_subset_left
  obtain ⟨Ω, hΩ, hV⟩ := exists_isOpen_extend_target_inter_preimage φ
    (hu.continuousOn.isOpen_inter_preimage hs ψ.open_source)
  rw [hV] at hcomp ⊢
  exact (contMDiffOn_iff_contDiffOn.mp hcomp).memWkpLoc_inter_setOf_im_nonneg hΩ

/-- A `C^n` map, for the smooth structure of the Riemann surface with boundary and a manifold `M`
modelled on a real Banach space, is a local Sobolev map up to the boundary of every order
`k ≤ n` and every exponent. -/
theorem _root_.ContMDiff.memWkpLocMapBordered [CompleteSpace F] {n : ℕ∞ω}
    (hu : ContMDiff closedUpperHalfPlaneModel I n u) (hk : (k : ℕ∞ω) ≤ n) :
    MemWkpLocMapBordered I p k u :=
  memWkpLocMapOnBordered_univ.mp (hu.contMDiffOn.memWkpLocMapOnBordered hk isOpen_univ)

/-! ### Comparison with the class on the interior -/

section Interior

variable [IsManifold closedUpperHalfPlaneModel 1 X]

open ClosedUpperHalfPlane in
/-- The restriction of a bordered holomorphic chart of `X` to the interior, read in `ℂ` through
the open upper half-plane, is a holomorphic chart of the interior. -/
private theorem subtypeRestr_trans_mem_maximalAtlas
    {φ : OpenPartialHomeomorph X ClosedUpperHalfPlane}
    (hφ : φ ∈ borderedHolomorphicGroupoid.maximalAtlas X) (hs : Nonempty (borderedInterior X)) :
    φ.subtypeRestr hs ≫ₕ upperHalfPlaneChart ∈
      IsManifold.maximalAtlas 𝓘(ℂ) 1 (borderedInterior X) := by
  have key : ∀ x : borderedInterior X,
      (φ.subtypeRestr hs).symm ≫ₕ chartAt ClosedUpperHalfPlane x ∈ borderedHolomorphicGroupoid ∧
        (chartAt ClosedUpperHalfPlane x).symm ≫ₕ φ.subtypeRestr hs ∈
          borderedHolomorphicGroupoid := fun x ↦
    ⟨borderedHolomorphicGroupoid.mem_of_eqOnSource (closedUnderRestriction'
        (hφ _ (chart_mem_atlas _ (x : X))).1
          (φ.isOpen_inter_preimage_symm (borderedInterior X).2))
        (φ.subtypeRestr_symm_trans_subtypeRestr hs _),
      borderedHolomorphicGroupoid.mem_of_eqOnSource (closedUnderRestriction'
        (hφ _ (chart_mem_atlas _ (x : X))).2
          ((chartAt ClosedUpperHalfPlane (x : X)).isOpen_inter_preimage_symm
            (borderedInterior X).2))
        ((chartAt ClosedUpperHalfPlane (x : X)).subtypeRestr_symm_trans_subtypeRestr hs φ)⟩
  rintro _ ⟨x, rfl⟩
  have h₁ := upperHalfPlaneChart_symm_trans_mem_contDiffGroupoid (key x).1
  have h₂ := upperHalfPlaneChart_symm_trans_mem_contDiffGroupoid (key x).2
  simp only [OpenPartialHomeomorph.trans_assoc] at h₁ h₂
  simp only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.trans_assoc]
  exact ⟨contDiffGroupoid_le (by exact_mod_cast le_top) h₁,
    contDiffGroupoid_le (by exact_mod_cast le_top) h₂⟩

open ClosedUpperHalfPlane in
/-- On an open subset `s` of the interior of a Riemann surface with boundary, a local Sobolev
map for the Riemann surface structure of the interior is a local Sobolev map up to the boundary
on `s`, with the same order and exponent. The coordinate expression in a bordered holomorphic
chart over `s` is its coordinate expression in the restriction of the chart to the interior, read
in `ℂ` through the open upper half-plane. -/
theorem MemWkpLocMapOn.memWkpLocMapOnBordered_image [CompleteSpace F]
    {s : Set (borderedInterior X)} (hu : MemWkpLocMapOn I p k (u ∘ (↑)) s) (hs : IsOpen s) :
    MemWkpLocMapOnBordered I p k u ((↑) '' s) := by
  have hcont : ContinuousOn u ((↑) '' s) :=
    Topology.IsInducing.subtypeVal.continuousOn_image_iff.2 hu.continuousOn
  refine ⟨hcont, fun φ hφ ψ hψ ↦ ?_⟩
  set V := (φ.extend closedUpperHalfPlaneModel).target ∩
    (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' ((↑) '' s ∩ u ⁻¹' ψ.source)
  obtain ⟨Ω, hΩ, hV⟩ := exists_isOpen_extend_target_inter_preimage φ
    (hcont.isOpen_inter_preimage
      ((borderedInterior X).isOpen.isOpenMap_subtype_val s hs) ψ.open_source)
  rcases V.eq_empty_or_nonempty with hV₀ | ⟨z₀, hz₀⟩
  · rw [hV₀]
    exact memWkpLoc_iff_locally.2 fun x hx ↦ hx.elim
  obtain ⟨x₀, -, -⟩ := hz₀.2.1
  have hne : Nonempty (borderedInterior X) := ⟨x₀⟩
  have hφc : φ ∈ IsManifold.maximalAtlas closedUpperHalfPlaneModel ∞ X :=
    StructureGroupoid.maximalAtlas_mono borderedHolomorphicGroupoid_le_contDiffGroupoid hφ
  set φi := φ.subtypeRestr hne ≫ₕ upperHalfPlaneChart
  -- Every point of `V` lies in the test set of `φi`, where the two coordinate expressions agree.
  have hmem : ∀ z ∈ V, z ∈ φi.target ∩ φi.symm ⁻¹' (s ∩ (u ∘ (↑)) ⁻¹' ψ.source) ∧
      (ψ.extend I ∘ (u ∘ (↑)) ∘ φi.symm) z =
        (ψ.extend I ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm) z := by
    rintro z ⟨hzt, ⟨x, hxs, hxz⟩, hzψ⟩
    rw [OpenPartialHomeomorph.extend_target, mem_inter_iff, mem_preimage,
      range_closedUpperHalfPlaneModel] at hzt
    rw [OpenPartialHomeomorph.extend_coe_symm, Function.comp_apply] at hxz hzψ
    have hzim : 0 ≤ z.im := hzt.2
    have hφz : φ (x : X) = closedUpperHalfPlaneModel.symm z := by
      rw [hxz, φ.right_inv hzt.1]
    have hxφ : (x : X) ∈ φ.source := by
      rw [hxz]
      exact φ.map_target hzt.1
    -- The chart sends the interior point `x` to a point of positive imaginary part.
    have hpos : 0 < z.im := by
      have hc := (hφc _ (chart_mem_atlas ClosedUpperHalfPlane (x : X))).2
      have hsrc : chartAt ClosedUpperHalfPlane (x : X) (x : X) ∈
          ((chartAt ClosedUpperHalfPlane (x : X)).symm ≫ₕ φ).source := by
        simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
          mem_inter_iff, mem_preimage, OpenPartialHomeomorph.left_inv _ (mem_chart_source _ _)]
        exact ⟨(chartAt _ _).map_source (mem_chart_source _ _), hxφ⟩
      have h := (im_pos_iff_of_mem_contDiffGroupoid hc (by simp) hsrc).1
        (mem_borderedInterior_iff_im_chartAt_pos.1 x.2)
      rwa [OpenPartialHomeomorph.coe_trans, Function.comp_apply,
        OpenPartialHomeomorph.left_inv _ (mem_chart_source _ _), hφz,
        coe_closedUpperHalfPlaneModel_symm_of_im_nonneg hzim] at h
    have hzi : z ∈ φi.target := by
      simp only [φi, OpenPartialHomeomorph.trans_target, upperHalfPlaneChart_target,
        upperHalfPlaneChart_symm_apply, mem_inter_iff, mem_preimage, mem_ofPred_eq,
        OpenPartialHomeomorph.subtypeRestr_def]
      refine ⟨hpos, hzt.1, ?_⟩
      simp only [Opens.openPartialHomeomorphSubtypeCoe_target, ← hxz, SetLike.mem_coe]
      exact x.2
    have hsymm : φi.symm z = x := by
      apply Subtype.ext
      have h := φ.subtypeRestr_symm_apply hne hzi.2
      rw [upperHalfPlaneChart_symm_apply] at h
      replace h := h.trans hxz.symm
      simpa only [φi, OpenPartialHomeomorph.coe_trans_symm, Function.comp_apply,
        upperHalfPlaneChart_symm_apply] using h
    refine ⟨⟨hzi, ?_, ?_⟩, ?_⟩
    · rw [hsymm]
      exact hxs
    · rw [mem_preimage, hsymm, Function.comp_apply, hxz]
      exact hzψ
    · simp only [Function.comp_apply, hsymm, OpenPartialHomeomorph.extend_coe_symm, ← hxz]
  have hVm : MeasurableSet V := by
    rw [show V = Ω ∩ {z | 0 ≤ z.im} from hV]
    exact hΩ.measurableSet.inter
      (isClosed_le continuous_const Complex.continuous_im).measurableSet
  exact ((hu.memWkpLoc_chart (subtypeRestr_trans_mem_maximalAtlas hφ hne) hψ).mono
    fun z hz ↦ (hmem z hz).1).congr_ae
      ((ae_restrict_iff' hVm).2 (Eventually.of_forall fun z hz ↦ (hmem z hz).2))

end Interior

/-! ### A square-root profile on the closed upper half-disc -/

/-- On the closed upper half-disc `{z | ‖z‖ < 1}` of `ClosedUpperHalfPlane`, the map
`z ↦ √(Im z)` is continuous, but it is not a local Sobolev map up to the boundary of order `1`
for any exponent `p ≥ 2`: in the identity chart its coordinate expression is `z ↦ √(Im z)` on
`ball 0 1 ∩ {z | 0 ≤ z.im}`, whose derivative `(2 √(Im z))⁻¹` is not square integrable near the
real axis (`TauCeti.memWkpLoc_sqrt_im_iff`). On the open half-disc it is smooth. -/
theorem not_memWkpLocMapOnBordered_sqrt_im (hp : 2 ≤ p) :
    ¬ MemWkpLocMapOnBordered 𝓘(ℝ) p 1 (fun z : ClosedUpperHalfPlane ↦ √(z : ℂ).im)
      {z | ‖(z : ℂ)‖ < 1} := by
  intro h
  have hφ := borderedHolomorphicGroupoid.chart_mem_maximalAtlas (ClosedUpperHalfPlane.ofReal 0)
  have hψ := (contDiffGroupoid ∞ 𝓘(ℝ)).chart_mem_maximalAtlas (0 : ℝ)
  have hc := h.memWkpLoc_chart hφ hψ
  have hset : ((chartAt ClosedUpperHalfPlane (ClosedUpperHalfPlane.ofReal 0)).extend
      closedUpperHalfPlaneModel).target ∩
      ((chartAt ClosedUpperHalfPlane (ClosedUpperHalfPlane.ofReal 0)).extend
        closedUpperHalfPlaneModel).symm ⁻¹' ({z : ClosedUpperHalfPlane | ‖(z : ℂ)‖ < 1} ∩
        (fun z : ClosedUpperHalfPlane ↦ √(z : ℂ).im) ⁻¹' (chartAt ℝ (0 : ℝ)).source) =
      Metric.ball (0 : ℂ) 1 ∩ {z | 0 ≤ z.im} := by
    ext z
    simp only [chartAt_self_eq, OpenPartialHomeomorph.extend_target,
      OpenPartialHomeomorph.extend_coe_symm, OpenPartialHomeomorph.refl_target,
      OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_source,
      OpenPartialHomeomorph.refl_apply, range_closedUpperHalfPlaneModel, preimage_univ,
      inter_univ, mem_inter_iff, mem_preimage, mem_ofPred_eq, Function.comp_apply, id_eq,
      Metric.mem_ball, dist_zero_right, mem_univ, true_and]
    constructor
    · rintro ⟨hz, hzn⟩
      rw [coe_closedUpperHalfPlaneModel_symm_of_im_nonneg hz] at hzn
      exact ⟨hzn, hz⟩
    · rintro ⟨hzn, hz⟩
      rw [coe_closedUpperHalfPlaneModel_symm_of_im_nonneg hz]
      exact ⟨hz, hzn⟩
  rw [hset] at hc
  have hm : MeasurableSet (Metric.ball (0 : ℂ) 1 ∩ {z : ℂ | 0 ≤ z.im}) :=
    Metric.isOpen_ball.measurableSet.inter
      (isClosed_le continuous_const Complex.continuous_im).measurableSet
  have hc' : MemWkpLoc p (Metric.ball (0 : ℂ) 1 ∩ {z | 0 ≤ z.im}) 1 (fun z : ℂ ↦ √z.im) := by
    refine hc.congr_ae ((ae_restrict_iff' hm).2 (Eventually.of_forall fun z hz ↦ ?_))
    simp [chartAt_self_eq, coe_closedUpperHalfPlaneModel_symm_of_im_nonneg hz.2]
  exact absurd (memWkpLoc_sqrt_im_iff.1 hc') (not_lt.2 hp)

end TauCeti
