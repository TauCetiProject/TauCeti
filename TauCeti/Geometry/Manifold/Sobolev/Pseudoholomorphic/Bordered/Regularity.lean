/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Sobolev.Pseudoholomorphic.Bordered
public import TauCeti.Geometry.Manifold.Complex.TotallyReal.Basic
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Bootstrap
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Bootstrap.Boundary
import TauCeti.Analysis.Sobolev.Local.ChainRule.HalfDisc
import TauCeti.Geometry.Manifold.Complex.ClosedUpperHalfPlane.Boundary
import TauCeti.Geometry.Manifold.ContMDiff.Atlas
import TauCeti.Geometry.Manifold.Complex.TotallyReal.AdaptedChart
import TauCeti.Geometry.Manifold.Complex.TotallyReal.Examples
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.Sobolev.Pseudoholomorphic.Atlas
import TauCeti.Geometry.Manifold.Sobolev.LocalMap.Bordered.Atlas.Higher
import TauCeti.Geometry.Manifold.Sobolev.LocalMap.Bordered.Morrey
import TauCeti.Geometry.Manifold.Sobolev.LocalMap.Locality
import TauCeti.Geometry.Manifold.Sobolev.Pseudoholomorphic.Bordered.Comparison
import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Chart

/-!
# Regularity up to a totally real boundary of weak pseudoholomorphic maps

Let `X` be a Riemann surface with boundary, `M` a manifold modelled on a boundaryless model `I`
with finite-dimensional model vector space, `J₀` an almost complex structure on `M` of class
`C^ℓ`, and `ι : N → M` a `C^k` totally real embedding for `J₀` with `ℓ + 1 ≤ k`. A weak
pseudoholomorphic map
`u : X → M` up to the boundary on an open set `s`
(`TauCeti.IsWeakPseudoholomorphicOnBordered`), for `J₀` regarded as a family independent of the
domain point and the zero inhomogeneous term, which maps the boundary points of `s` into `ι (N)`,
lies in `W^{m,p}_loc` up to the boundary for every `m ≤ ℓ` and finite `p > 2`. For `ℓ ≥ 2` this is
the conclusion `W^{ℓ,p}` of McDuff–Salamon, Theorem B.4.1. By Morrey's embedding up to the boundary
(`TauCeti.MemWkpLocMapOnBordered.contMDiffOn`) such a map is of class `C^(ℓ-1)` up to the
boundary, and smooth up to the boundary when `J₀` and `ι` are smooth; these conclusions hold for
`p = ∞` as well, since a weak solution for `p` is one for every finite exponent in `(2, p]`.

The proof is local. Near an interior point of `X` the coordinate expression of `u` solves the
planar equation for the structure `J₀` read in a chart of `M`, which is `C^ℓ`, and the interior
bootstrap `TauCeti.memWkpLoc_of_isWeakCauchyRiemannOn` gives `W^{ℓ+1,p}`. Near a boundary point
`x₀`, write `u x₀ = ι y₀` and take an adapted chart `ψ` of `M` at `ι y₀`
(`TauCeti.IsTotallyRealEmbedding.exists_adaptedChart`): a `C^ℓ` chart into `F × F` flattening
`ι (N)` onto the zero section, in which `J₀` reads as a `C^(ℓ-1)` structure equal to the standard
one `(v, w) ↦ (-w, v)` along the zero section. Moving the coordinate expression into `ψ` along
the `C^ℓ` transition (`TauCeti.IsWeakCauchyRiemannOn.contDiffOn_comp_of_intertwine`), the boundary
condition puts it on the zero section along the real axis, and the planar boundary bootstrap in
adapted coordinates (`TauCeti.memWkpLoc_of_isWeakCauchyRiemannOn_halfPlane_prod`) gives
`W^{ℓ,p}` up to the axis. The loss of one derivative compared with the interior is the chart: the
pushed-forward structure is only `C^(ℓ-1)`. Moving back along the inverse transition, which is
`C^ℓ`, keeps `W^{ℓ,p}`.

## Main results

* `TauCeti.IsWeakPseudoholomorphicOnBordered.memWkpLocMapOnBordered_of_mapsTo`,
  `TauCeti.IsWeakPseudoholomorphicBordered.memWkpLocMapBordered_of_mapsBoundaryInto`:
  **regularity up to a totally real boundary**, `W^{m,p}_loc` up to the boundary for `m ≤ ℓ`.
* `TauCeti.IsWeakPseudoholomorphicOnBordered.contMDiffOn_of_mapsTo`,
  `TauCeti.IsWeakPseudoholomorphicBordered.contMDiff_of_mapsBoundaryInto`: `C^(ℓ-1)` up to the
  boundary.
* `TauCeti.IsWeakPseudoholomorphicOnBordered.contMDiffOn_infty_of_mapsTo`,
  `TauCeti.IsWeakPseudoholomorphicBordered.contMDiff_infty_of_mapsBoundaryInto`: smoothness up to
  the boundary for a smooth structure and a smooth totally real embedding.
* `TauCeti.IsPseudoholomorphicOn.contMDiffOn_of_mapsTo`,
  `TauCeti.IsPseudoholomorphic.contMDiff_of_mapsBoundaryInto`: a pseudoholomorphic map of class
  `C¹` for a smooth structure, sending the boundary into the image of a smooth totally real
  embedding, is smooth up to the boundary. This is the smooth case read through the comparison
  `TauCeti.isWeakPseudoholomorphicOnBordered_iff_isPseudoholomorphicOn`.
* Check: the inclusion of the closed upper half-plane into `ℂ`, with boundary in the totally real
  line `ℝ`, satisfies the hypotheses for every `ℓ`, and the smooth case and the `C¹` criterion
  apply to it.

## Implementation notes

The structure is independent of the domain point and the inhomogeneous term vanishes, as in
McDuff–Salamon, Theorem B.4.1. Domain-dependent structures and inhomogeneous terms would need the
joint regularity up to the boundary of the structure and the term read in bordered charts, and
adapted charts depending on the domain point; neither is treated here.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4 (Theorem B.4.1).
-/

public section

open Set Filter TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal

noncomputable section

namespace TauCeti

open ClosedUpperHalfPlane

/-! ### Regularity up to the boundary -/

section Regularity

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ClosedUpperHalfPlane X]
  [HasGroupoid X borderedHolomorphicGroupoid]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ F H'} [I'.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {ℓ : ℕ∞} {k : ℕ∞ω} {J₀ : ContMDiffAlmostComplexStructure I ℓ M} {ι : N → M}
  {p : ENNReal} {u : X → M} {s : Set X}

omit [FiniteDimensional ℝ E] in
/-- In a bordered holomorphic chart `φ` and a chart `χ` of `M`, over a set `t ⊆ s` mapped
into the source of `χ`, the coordinate expression of a weak pseudoholomorphic map for a structure
`J₀` independent of the domain point and the zero term solves `∂ₛw + χ_* J₀(w) ∂ₜw = 0`. -/
private theorem IsWeakPseudoholomorphicOnBordered.isWeakCauchyRiemannOn_chart_const
    (h : IsWeakPseudoholomorphicOnBordered (ContMDiffAlmostComplexStructureFamily.const J₀) 0 p u
      s)
    {t : Set X} (hts : t ⊆ s) {φ : OpenPartialHomeomorph X ClosedUpperHalfPlane}
    (hφ : φ ∈ borderedHolomorphicGroupoid.maximalAtlas X) {χ : OpenPartialHomeomorph M H}
    (hχ : χ ∈ IsManifold.maximalAtlas I ∞ M) (htχ : MapsTo u t χ.source) :
    IsWeakCauchyRiemannOn p ((φ.extend closedUpperHalfPlaneModel).target ∩
        (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' t)
      (fun _ v ↦ J₀.chartPushforward (χ.extendTrans I (Homeomorph.refl E)) v) (fun _ _ ↦ 0)
      (χ.extendTrans I (Homeomorph.refl E) ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm) := by
  have hw := h.isWeakCauchyRiemannOn_chart hφ hχ
  rw [ContMDiffAlmostComplexStructureFamily.chartField_const,
    InhomogeneousTerm.chartTermExtend_zero] at hw
  exact hw.mono (inter_subset_inter_right _ (preimage_mono fun x hx ↦ ⟨hts hx, htχ hx⟩))

/-- **Regularity near an interior point.** For `2 < p < ∞` and `m ≤ ℓ`, near a point of `s` that
is not a boundary point of `X`, a weak pseudoholomorphic map for a `C^ℓ` structure independent of
the domain point and the zero term is in `W^{m+1,p}_loc`. -/
private theorem IsWeakPseudoholomorphicOnBordered.exists_memWkpLocMapOnBordered_of_not_mem
    (h : IsWeakPseudoholomorphicOnBordered (ContMDiffAlmostComplexStructureFamily.const J₀) 0 p u
      s)
    (hs : IsOpen s) (hp : 2 < p) (hp' : p ≠ ⊤) {m : ℕ} (hm : (m : ℕ∞) ≤ ℓ) {x₀ : X}
    (hx₀ : x₀ ∈ s) (hb : x₀ ∉ closedUpperHalfPlaneModel.boundary X) :
    ∃ t ∈ 𝓝[s] x₀, MemWkpLocMapOnBordered I p (m + 1) u t := by
  set φ := chartAt ClosedUpperHalfPlane x₀
  set χ := chartAt H (u x₀)
  set χ' := χ.extendTrans I (Homeomorph.refl E)
  have hφ : φ ∈ borderedHolomorphicGroupoid.maximalAtlas X :=
    StructureGroupoid.chart_mem_maximalAtlas _ x₀
  have hχ : χ ∈ IsManifold.maximalAtlas I ∞ M := IsManifold.chart_mem_maximalAtlas _
  set t := (s ∩ φ.source ∩ (closedUpperHalfPlaneModel.boundary X)ᶜ) ∩ u ⁻¹' χ.source
  have hts : t ⊆ s := fun x hx ↦ hx.1.1.1
  have hs' : s ∩ φ.source ∩ (closedUpperHalfPlaneModel.boundary X)ᶜ ⊆ s := fun x hx ↦ hx.1.1
  have ht : IsOpen t := (h.continuousOn.mono hs').isOpen_inter_preimage
    ((hs.inter φ.open_source).inter
      (closedUpperHalfPlaneModel.isClosed_boundary_of_finiteDimensional X).isOpen_compl)
    χ.open_source
  have hx₀t : x₀ ∈ t :=
    ⟨⟨⟨hx₀, mem_chart_source _ x₀⟩, mem_compl hb⟩, mem_preimage.2 (mem_chart_source H (u x₀))⟩
  refine ⟨t, mem_nhdsWithin_of_mem_nhds (ht.mem_nhds hx₀t), ?_⟩
  have htχ : MapsTo u t χ.source := fun x hx ↦ mem_preimage.1 hx.2
  -- The coordinate domain avoids the real axis, so it is open.
  set D := (φ.extend closedUpperHalfPlaneModel).target ∩
    (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' t
  have hDo : IsOpen D :=
    φ.isOpen_extend_target_inter_preimage_of_subset_compl ht fun x hx ↦ hx.1.2
  have hχ'1 : ContMDiffOn I 𝓘(ℝ, E) ∞ χ' χ'.source :=
    χ.contMDiffOn_extendTrans hχ contDiff_id
  have hχ's : ContMDiffOn 𝓘(ℝ, E) I ∞ χ'.symm χ'.target :=
    χ.contMDiffOn_extendTrans_symm hχ contDiff_id
  have hw := h.isWeakCauchyRiemannOn_chart_const hts hφ hχ htχ
  have hwt : ∀ z ∈ D, (χ' ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm) z ∈ χ'.target :=
    fun z hz ↦ χ'.map_source (by simpa [χ'] using hz.2.2)
  have hreg := memWkpLoc_of_isWeakCauchyRiemannOn (Ω := ⟨D, hDo⟩) (W := univ ×ˢ χ'.target)
    (ℓ := m) hp hp' (isOpen_univ.prod χ'.open_target)
    (((J₀.contDiffOn_chartPushforward hχ'1 hχ's le_top).of_le (by exact_mod_cast hm)).comp
      contDiffOn_snd fun x (hx : x ∈ univ ×ˢ χ'.target) ↦ (mem_prod.1 hx).2)
    contDiffOn_const (fun z hz ↦ mem_prod.2 ⟨mem_univ _, hwt z hz⟩)
    (ae_restrict_of_forall_mem hDo.measurableSet fun z hz ↦
      J₀.chartPushforward_mul_self_of_contMDiffOn χ' hχ'1 hχ's (by simp) (hwt z hz))
    hw
  have htφ : t ⊆ φ.source := fun x hx ↦ hx.1.1.2
  refine memWkpLocMapOnBordered_of_memWkpLoc_chart hp hp' ht hφ htφ hχ htχ
    (h.continuousOn.mono hts) ?_
  rw [← χ.coe_extendTrans_refl I]
  exact hreg

omit [I.Boundaryless] in
/-- **Regularity in an adapted chart.** Let `ψ` be an adapted chart of `M` for a subset `S` and a
`C^ℓ` structure `J₀` (`TauCeti.IsAdaptedChart`), and `χ` a chart of `M` into `E` that is `C^ℓ` with
`C^ℓ` inverse, with `1 ≤ ℓ`. For `2 < p < ∞` and `m + 1 ≤ ℓ`, let `w` solve
`∂ₛw + χ_* J₀(w) ∂ₜw = 0` weakly on `H = Ω ∩ {0 ≤ im}`, with values in the source of the transition
`Θ = ψ ∘ χ⁻¹`, and with `χ⁻¹ (w s) ∈ S` for real `s ∈ Ω`. Then `w ∈ W^{m+1,p}_loc(H)`: the
expression `Θ ∘ w` solves the equation for `ψ_* J₀`, which is `C^(ℓ-1)` and standard on the zero
section where `Θ ∘ w` takes its boundary values, and `Θ⁻¹` is `C^ℓ`. -/
private theorem memWkpLoc_of_isAdaptedChart {S : Set M} {ψ : OpenPartialHomeomorph M (F × F)}
    (hψ : IsAdaptedChart J₀ S ψ) {χ : OpenPartialHomeomorph M E}
    (hχ : ContMDiffOn I 𝓘(ℝ, E) ℓ χ χ.source) (hχs : ContMDiffOn 𝓘(ℝ, E) I ℓ χ.symm χ.target)
    (hℓ : 1 ≤ ℓ) (hp : 2 < p) (hp' : p ≠ ⊤) {m : ℕ} (hm : ((m + 1 : ℕ) : ℕ∞) ≤ ℓ)
    {Ω : Opens ℂ} {w : ℂ → E}
    (h : IsWeakCauchyRiemannOn p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})
      (fun _ v ↦ J₀.chartPushforward χ v) (fun _ _ ↦ 0) w)
    (hwΘ : MapsTo w ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (χ.symm.trans ψ).source)
    (hS : ∀ s : ℝ, (s : ℂ) ∈ Ω → χ.symm (w s) ∈ S) :
    MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (m + 1) w := by
  have hℓ1 : (1 : ℕ∞ω) ≤ ℓ := by exact_mod_cast hℓ
  have hℓ0 : (ℓ : ℕ∞ω) ≠ 0 := (zero_lt_one.trans_le hℓ1).ne'
  -- The source of the transition `Θ = ψ ∘ χ⁻¹` is `χ.target ∩ χ⁻¹ ⁻¹' ψ.source`.
  have hwΘ' : MapsTo w ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (χ.target ∩ χ.symm ⁻¹' ψ.source) :=
    fun z hz ↦ by
      have h := hwΘ hz
      rwa [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at h
  -- The target of `Θ` is `ψ.target ∩ ψ⁻¹ ⁻¹' χ.source`.
  have hΘt : ∀ z ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, χ.symm.trans ψ (w z) ∈ ψ.target := fun z hz ↦ by
    have h := (χ.symm.trans ψ).map_source (hwΘ hz)
    rw [OpenPartialHomeomorph.trans_target, mem_inter_iff] at h
    exact h.1
  have hreal : ∀ s : ℝ, (s : ℂ) ∈ Ω → (s : ℂ) ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} :=
    fun s hs ↦ ⟨hs, by simp⟩
  -- Along the real axis `Θ ∘ w` lies on the zero section, where `ψ_* J₀` is standard.
  have hzero : ∀ s : ℝ, (s : ℂ) ∈ Ω → (χ.symm.trans ψ (w s)).2 = 0 := fun s hs ↦ by
    have h := (hψ.isImage (mem_preimage.1 (hwΘ' (hreal s hs)).2)).2 (hS s hs)
    rw [mem_ofPred_eq] at h
    rwa [OpenPartialHomeomorph.coe_trans, Function.comp_apply]
  set Θ := χ.symm.trans ψ
  obtain ⟨-, hΘs⟩ := OpenPartialHomeomorph.contDiffOn_symm_trans_and_symm_of_contMDiffOn hχ hχs
    hψ.contMDiffOn hψ.contMDiffOn_symm
  have hw := h.chartPushforward_symm_trans_comp (hχ.of_le hℓ1) (hχs.of_le hℓ1)
    (hψ.contMDiffOn.of_le hℓ1) (hψ.contMDiffOn_symm.of_le hℓ1) hwΘ
  have hreg := memWkpLoc_of_isWeakCauchyRiemannOn_halfPlane_prod (W' := univ ×ˢ ψ.target)
    (ℓ := m) hp hp' (isOpen_univ.prod ψ.open_target)
    ((hψ.contDiffOn_chartPushforward.of_le ?_).comp contDiffOn_snd
      fun (x : ℂ × (F × F)) (hx : x ∈ univ ×ˢ ψ.target ∩ {x : ℂ × (F × F) | 0 ≤ x.1.im}) ↦
        (mem_prod.1 hx.1).2)
    contDiffOn_const (fun z hz ↦ mem_prod.2 ⟨mem_univ _, hΘt z hz⟩)
    (ae_restrict_of_forall_mem (Ω.isOpen.measurableSet.inter (measurableSet_le measurable_const
      Complex.measurable_im)) fun z hz ↦ J₀.chartPushforward_mul_self_of_contMDiffOn ψ
        hψ.contMDiffOn hψ.contMDiffOn_symm hℓ0 (hΘt z hz))
    hzero (fun s hs ↦ hψ.chartPushforward_of_snd_eq_zero _ (hΘt _ (hreal s hs)) (hzero s hs)) hw
  · -- Move back along the inverse transition, which is `C^ℓ`.
    lift p to ℝ≥0 using hp'
    exact (MemWkpLoc.contDiffOn_comp_succ_halfPlane (g := Θ.symm) (by exact_mod_cast hp) hreg
      hw.continuousOn Θ.open_target (hΘs.of_le (by exact_mod_cast hm))
      fun z hz ↦ Θ.map_source (hwΘ hz)).congr fun z hz ↦ (Θ.left_inv (hwΘ hz)).symm
  · -- The pushed-forward structure is `C^(ℓ-1)` and `m + 1 ≤ ℓ`.
    have hm' : (m : ℕ∞) ≤ ℓ - 1 :=
      ENat.le_sub_of_add_le_right ENat.one_ne_top (by exact_mod_cast hm)
    exact_mod_cast hm'

/-- **Regularity near a point mapped into a totally real submanifold.** For `2 < p < ∞` and
`m + 1 ≤ ℓ`, near a point `x₀ ∈ s` with `u x₀ ∈ ι (N)`, a weak pseudoholomorphic map for a `C^ℓ`
structure `J₀` independent of the domain point and the zero term, mapping the boundary points of
`s` into the image of a totally real embedding `ι` for `J₀`, is in `W^{m+1,p}_loc` up to the
boundary. Its coordinate expression in the chart at `u x₀` is regular by
`memWkpLoc_of_isAdaptedChart`, for an adapted chart at `u x₀`. -/
private theorem IsWeakPseudoholomorphicOnBordered.exists_memWkpLocMapOnBordered_of_mem_range
    [IsManifold I' k N]
    (h : IsWeakPseudoholomorphicOnBordered (ContMDiffAlmostComplexStructureFamily.const J₀) 0 p u
      s)
    (hs : IsOpen s) (hp : 2 < p) (hp' : p ≠ ⊤)
    (hι : IsTotallyRealEmbedding I' I k J₀.almostComplexStructureAt ι) (hk : (ℓ : ℕ∞ω) + 1 ≤ k)
    (hb : MapsTo u (s ∩ closedUpperHalfPlaneModel.boundary X) (range ι)) {m : ℕ}
    (hm : ((m + 1 : ℕ) : ℕ∞) ≤ ℓ) {x₀ : X} (hx₀ : x₀ ∈ s) {y₀ : N} (hy₀ : u x₀ = ι y₀) :
    ∃ t ∈ 𝓝[s] x₀, MemWkpLocMapOnBordered I p (m + 1) u t := by
  have hℓ : 1 ≤ ℓ := le_trans (by exact_mod_cast Nat.le_add_left 1 m) hm
  obtain ⟨ψ, -, -, -, -, hy₀ψ, hψχ, hψ⟩ := hι.exists_adaptedChart hℓ hk y₀
  set φ := chartAt ClosedUpperHalfPlane x₀
  set χ := chartAt H (ι y₀)
  set χ' := χ.extendTrans I (Homeomorph.refl E)
  have hφ : φ ∈ borderedHolomorphicGroupoid.maximalAtlas X :=
    StructureGroupoid.chart_mem_maximalAtlas _ x₀
  have hχ : χ ∈ IsManifold.maximalAtlas I ∞ M := IsManifold.chart_mem_maximalAtlas _
  set t := s ∩ φ.source ∩ u ⁻¹' ψ.source
  have hts : t ⊆ s := fun x hx ↦ hx.1.1
  have ht : IsOpen t := (h.continuousOn.mono
    (fun x (hx : x ∈ s ∩ φ.source) ↦ hx.1)).isOpen_inter_preimage
    (hs.inter φ.open_source) ψ.open_source
  have hx₀t : x₀ ∈ t := ⟨⟨hx₀, mem_chart_source _ x₀⟩, by rw [mem_preimage, hy₀]; exact hy₀ψ⟩
  refine ⟨t, mem_nhdsWithin_of_mem_nhds (ht.mem_nhds hx₀t), ?_⟩
  have htχ : MapsTo u t χ.source := fun x hx ↦ by
    simpa [χ, extChartAt_source] using hψχ hx.2
  obtain ⟨Ω, hΩ, hD⟩ := φ.exists_isOpen_extend_target_inter_preimage ht
  have hleft : ∀ z ∈ (φ.extend closedUpperHalfPlaneModel).target ∩
      (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' t,
      χ'.symm ((χ' ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm) z) =
        u ((φ.extend closedUpperHalfPlaneModel).symm z) :=
    fun z hz ↦ χ'.left_inv (by simpa [χ'] using htχ hz.2)
  have hw := h.isWeakCauchyRiemannOn_chart_const hts hφ hχ htχ
  rw [hD] at hw hleft
  refine memWkpLocMapOnBordered_of_memWkpLoc_chart hp hp' ht hφ (fun x hx ↦ hx.1.2) hχ htχ
    (h.continuousOn.mono hts) ?_
  rw [← χ.coe_extendTrans_refl I, hD]
  refine memWkpLoc_of_isAdaptedChart (Ω := ⟨Ω, hΩ⟩) hψ
    ((χ.contMDiffOn_extendTrans hχ contDiff_id).of_le (by exact_mod_cast le_top))
    ((χ.contMDiffOn_extendTrans_symm hχ contDiff_id).of_le (by exact_mod_cast le_top)) hℓ hp hp'
    hm hw (fun z hz ↦ ?_) fun s' hs' ↦ ?_
  · -- Membership in the source of the transition `ψ ∘ χ'⁻¹`, by `trans_source`.
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source, mem_inter_iff,
      mem_preimage, hleft z hz]
    have hz' := hD ▸ hz
    rw [mem_inter_iff, mem_preimage] at hz'
    exact ⟨χ'.map_source (by simpa [χ'] using htχ hz'.2), mem_preimage.1 hz'.2.2⟩
  · -- A real point of the coordinate domain reads a boundary point of `X`.
    have hz : (s' : ℂ) ∈ Ω ∩ {z | 0 ≤ z.im} := ⟨hs', by simp⟩
    rw [hleft _ hz]
    have hz' := hD ▸ hz
    rw [mem_inter_iff, mem_preimage] at hz'
    -- `closedUpperHalfPlaneModel.boundary X` is by definition the set of boundary points.
    exact hb ⟨hz'.2.1.1, (φ.isBoundaryPoint_extend_symm_iff hz'.1).2 (Complex.ofReal_im s')⟩

/-- **Regularity up to a totally real boundary** (McDuff–Salamon, Theorem B.4.1). Let `2 < p < ∞`,
let `J₀` be an almost complex structure on `M` of class `C^ℓ`, regarded as a family independent of
the domain point, and let `ι : N → M` be a `C^k` totally real embedding for `J₀` with
`ℓ + 1 ≤ k`. A weak pseudoholomorphic map up to the boundary on an open set `s`, for `J₀` and the
zero inhomogeneous term, which maps the boundary points of `X` in `s` into `ι (N)`, lies in
`W^{m,p}_loc` up to the boundary on `s` for every `m ≤ ℓ`. -/
theorem IsWeakPseudoholomorphicOnBordered.memWkpLocMapOnBordered_of_mapsTo [IsManifold I' k N]
    (h : IsWeakPseudoholomorphicOnBordered (ContMDiffAlmostComplexStructureFamily.const J₀) 0 p u
      s)
    (hs : IsOpen s) (hp : 2 < p) (hp' : p ≠ ⊤)
    (hι : IsTotallyRealEmbedding I' I k J₀.almostComplexStructureAt ι) (hk : (ℓ : ℕ∞ω) + 1 ≤ k)
    (hb : MapsTo u (s ∩ closedUpperHalfPlaneModel.boundary X) (range ι)) {m : ℕ}
    (hm : (m : ℕ∞) ≤ ℓ) : MemWkpLocMapOnBordered I p m u s := by
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · exact h.memWkpLocMapOnBordered.of_le (by omega)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' (show 1 ≤ m by omega)
  refine memWkpLocMapOnGroupoid_iff_locally.2 fun x₀ hx₀ ↦ ?_
  by_cases hx₀b : x₀ ∈ closedUpperHalfPlaneModel.boundary X
  · obtain ⟨y₀, hy₀⟩ := hb ⟨hx₀, hx₀b⟩
    exact h.exists_memWkpLocMapOnBordered_of_mem_range hs hp hp' hι hk hb hm hx₀ hy₀.symm
  · exact h.exists_memWkpLocMapOnBordered_of_not_mem hs hp hp'
      (le_trans (by exact_mod_cast Nat.le_succ m) hm) hx₀ hx₀b

/-- **Regularity up to a totally real boundary on the whole surface** (McDuff–Salamon,
Theorem B.4.1). For `2 < p < ∞`, a weak pseudoholomorphic map up to the boundary for a `C^ℓ`
almost complex structure `J₀` independent of the domain point and the zero inhomogeneous term,
mapping the boundary of `X` into the image of a `C^k` totally real embedding for `J₀` with
`ℓ + 1 ≤ k`, lies in `W^{m,p}_loc` up to the boundary for every `m ≤ ℓ`. -/
theorem IsWeakPseudoholomorphicBordered.memWkpLocMapBordered_of_mapsBoundaryInto
    [IsManifold I' k N]
    (h : IsWeakPseudoholomorphicBordered (ContMDiffAlmostComplexStructureFamily.const J₀) 0 p u)
    (hp : 2 < p) (hp' : p ≠ ⊤)
    (hι : IsTotallyRealEmbedding I' I k J₀.almostComplexStructureAt ι) (hk : (ℓ : ℕ∞ω) + 1 ≤ k)
    (hb : MapsBoundaryInto closedUpperHalfPlaneModel u ι) {m : ℕ} (hm : (m : ℕ∞) ≤ ℓ) :
    MemWkpLocMapBordered I p m u :=
  memWkpLocMapOnGroupoid_univ.1
    ((isWeakPseudoholomorphicOnBordered_univ.2 h).memWkpLocMapOnBordered_of_mapsTo isOpen_univ hp
      hp' hι hk (hb.mapsTo.mono_left inter_subset_right) hm)

/-- **`C^(ℓ-1)` up to a totally real boundary** (McDuff–Salamon, Theorem B.4.1). Let `2 < p`,
possibly `p = ∞`, let `J₀` be an almost complex structure on `M` of class `C^ℓ`, regarded as a
family independent of the domain point, and let `ι : N → M` be a `C^k` totally real embedding for
`J₀` with `ℓ + 1 ≤ k`. A weak pseudoholomorphic map up to the boundary on an open set `s`, for `J₀`
and the zero inhomogeneous term, which maps the boundary points of `X` in `s` into `ι (N)`, is of
class `C^(ℓ-1)` on `s` up to the boundary; for `ℓ = ∞` it is smooth there. For a finite exponent
`q ∈ (2, p]` it is `W^{m+1,q}_loc` up to the boundary for `m + 1 ≤ ℓ`, hence `Cᵐ` by Morrey's
embedding up to the boundary (`TauCeti.MemWkpLocMapOnBordered.contMDiffOn`). -/
theorem IsWeakPseudoholomorphicOnBordered.contMDiffOn_of_mapsTo [IsManifold I' k N]
    (h : IsWeakPseudoholomorphicOnBordered (ContMDiffAlmostComplexStructureFamily.const J₀) 0 p u
      s)
    (hs : IsOpen s) (hp : 2 < p)
    (hι : IsTotallyRealEmbedding I' I k J₀.almostComplexStructureAt ι) (hk : (ℓ : ℕ∞ω) + 1 ≤ k)
    (hb : MapsTo u (s ∩ closedUpperHalfPlaneModel.boundary X) (range ι)) :
    ContMDiffOn closedUpperHalfPlaneModel I (ℓ - 1 : ℕ∞) u s := by
  -- A weak solution for `p` is one for the finite exponent `min p 3 > 2`.
  have hq : 2 < min p 3 := lt_min hp (by norm_num)
  have hq' : min p 3 ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) (min_le_right p 3)
  replace h := h.mono_exponent (min_le_left p 3)
  have hm : ∀ m : ℕ, (m : ℕ∞) ≤ ℓ - 1 → ContMDiffOn closedUpperHalfPlaneModel I m u s := by
    rintro (_ | m) hm
    · exact contMDiffOn_zero_iff.2 h.continuousOn
    -- From `1 ≤ m + 1 ≤ ℓ - 1` we get `1 ≤ ℓ`, so `m + 2 ≤ ℓ`.
    have hℓ : (1 : ℕ∞) ≤ ℓ := le_trans (by exact_mod_cast Nat.le_add_left 1 m)
      (hm.trans tsub_le_self)
    refine (h.memWkpLocMapOnBordered_of_mapsTo hs hq hq' hι hk hb (m := m + 1 + 1) ?_).contMDiffOn
      hq hs
    exact_mod_cast add_le_of_le_tsub_right_of_le hℓ hm
  by_cases htop : ℓ - 1 = ⊤
  · rw [htop]
    exact contMDiffOn_infty.2 fun m ↦ hm m (htop ▸ le_top)
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 htop
    rw [← hn]
    exact hm n hn.le

/-- **`C^(ℓ-1)` up to a totally real boundary on the whole surface** (McDuff–Salamon,
Theorem B.4.1). For `2 < p`, possibly `p = ∞`, a weak pseudoholomorphic map up to the boundary
for a `C^ℓ` almost complex structure `J₀` independent of the domain point and the zero
inhomogeneous term, mapping the boundary of `X` into the image of a `C^k` totally real embedding
for `J₀` with `ℓ + 1 ≤ k`, is of class `C^(ℓ-1)` up to the boundary; for `ℓ = ∞` it is smooth. -/
theorem IsWeakPseudoholomorphicBordered.contMDiff_of_mapsBoundaryInto [IsManifold I' k N]
    (h : IsWeakPseudoholomorphicBordered (ContMDiffAlmostComplexStructureFamily.const J₀) 0 p u)
    (hp : 2 < p) (hι : IsTotallyRealEmbedding I' I k J₀.almostComplexStructureAt ι)
    (hk : (ℓ : ℕ∞ω) + 1 ≤ k) (hb : MapsBoundaryInto closedUpperHalfPlaneModel u ι) :
    ContMDiff closedUpperHalfPlaneModel I (ℓ - 1 : ℕ∞) u :=
  contMDiffOn_univ.1
    ((isWeakPseudoholomorphicOnBordered_univ.2 h).contMDiffOn_of_mapsTo isOpen_univ hp hι hk
      (hb.mapsTo.mono_left inter_subset_right))

/-- **Smoothness up to a totally real boundary** (McDuff–Salamon, Theorem B.4.1, smooth case). For
`2 < p`, possibly `p = ∞`, a weak pseudoholomorphic map up to the boundary on an open set `s`, for
a smooth almost complex structure `J` independent of the domain point and the zero inhomogeneous
term, mapping the boundary points of `X` in `s` into the image of a `C^k` totally real embedding
for `J` with `k ≥ ∞`, is smooth on `s` up to the boundary. -/
theorem IsWeakPseudoholomorphicOnBordered.contMDiffOn_infty_of_mapsTo [IsManifold I' k N]
    {J : ContMDiffAlmostComplexStructure I ⊤ M}
    (h : IsWeakPseudoholomorphicOnBordered (ContMDiffAlmostComplexStructureFamily.const J) 0 p u
      s)
    (hs : IsOpen s) (hp : 2 < p)
    (hι : IsTotallyRealEmbedding I' I k J.almostComplexStructureAt ι) (hk : ∞ ≤ k)
    (hb : MapsTo u (s ∩ closedUpperHalfPlaneModel.boundary X) (range ι)) :
    ContMDiffOn closedUpperHalfPlaneModel I ∞ u s := by
  simpa using h.contMDiffOn_of_mapsTo hs hp hι (by simpa using hk) hb

/-- **Smoothness up to a totally real boundary on the whole surface** (McDuff–Salamon,
Theorem B.4.1, smooth case). For `2 < p`, possibly `p = ∞`, a weak pseudoholomorphic map up to
the boundary for a smooth almost complex structure `J` independent of the domain point and the
zero inhomogeneous term, mapping the boundary of `X` into the image of a `C^k` totally real
embedding for `J` with `k ≥ ∞`, is smooth up to the boundary. -/
theorem IsWeakPseudoholomorphicBordered.contMDiff_infty_of_mapsBoundaryInto [IsManifold I' k N]
    {J : ContMDiffAlmostComplexStructure I ⊤ M}
    (h : IsWeakPseudoholomorphicBordered (ContMDiffAlmostComplexStructureFamily.const J) 0 p u)
    (hp : 2 < p) (hι : IsTotallyRealEmbedding I' I k J.almostComplexStructureAt ι)
    (hk : ∞ ≤ k) (hb : MapsBoundaryInto closedUpperHalfPlaneModel u ι) :
    ContMDiff closedUpperHalfPlaneModel I ∞ u := by
  simpa using h.contMDiff_of_mapsBoundaryInto hp hι (by simpa using hk) hb

/-- **`C¹` pseudoholomorphic maps are smooth up to a totally real boundary** (McDuff–Salamon,
Theorem B.4.1 and Remark B.4.3, smooth case). Let `J` be a smooth almost complex structure on `M`
and `ι : N → M` a `C^k` totally real embedding for `J` with `k ≥ ∞`. A map `u` of class `C¹` on an
open set `s` of a Riemann surface with boundary `X`, pseudoholomorphic on `s` for the structure of
`X` and `J`, which maps the boundary points of `X` in `s` into `ι (N)`, is smooth on `s` up to the
boundary. -/
theorem IsPseudoholomorphicOn.contMDiffOn_of_mapsTo [IsManifold I' k N]
    {J : SmoothAlmostComplexStructure I M}
    (h : IsPseudoholomorphicOn (SmoothAlmostComplexStructure.ofBorderedHolomorphic X) J u s)
    (hs : IsOpen s) (hu : ContMDiffOn closedUpperHalfPlaneModel I 1 u s)
    (hι : IsTotallyRealEmbedding I' I k J.almostComplexStructureAt ι) (hk : ∞ ≤ k)
    (hb : MapsTo u (s ∩ closedUpperHalfPlaneModel.boundary X) (range ι)) :
    ContMDiffOn closedUpperHalfPlaneModel I ∞ u s :=
  ((isWeakPseudoholomorphicOnBordered_iff_isPseudoholomorphicOn (ℓ := ⊤) (p := 3) J hs hu).2
    h).contMDiffOn_infty_of_mapsTo hs (by norm_num)
      (by rwa [SmoothAlmostComplexStructure.toContMDiff_almostComplexStructureAt]) hk hb

/-- **`C¹` pseudoholomorphic maps are smooth up to a totally real boundary, on the whole
surface** (McDuff–Salamon, Theorem B.4.1 and Remark B.4.3, smooth case). A map of class `C¹` from
a Riemann surface with boundary `X`, pseudoholomorphic for the structure of `X` and a smooth
almost complex structure `J` on `M`, which maps the boundary of `X` into the image of a `C^k`
totally real embedding for `J` with `k ≥ ∞`, is smooth up to the boundary. -/
theorem IsPseudoholomorphic.contMDiff_of_mapsBoundaryInto [IsManifold I' k N]
    {J : SmoothAlmostComplexStructure I M}
    (h : IsPseudoholomorphic (SmoothAlmostComplexStructure.ofBorderedHolomorphic X) J u)
    (hu : ContMDiff closedUpperHalfPlaneModel I 1 u)
    (hι : IsTotallyRealEmbedding I' I k J.almostComplexStructureAt ι) (hk : ∞ ≤ k)
    (hb : MapsBoundaryInto closedUpperHalfPlaneModel u ι) :
    ContMDiff closedUpperHalfPlaneModel I ∞ u :=
  contMDiffOn_univ.1 ((isPseudoholomorphicOn_univ.2 h).contMDiffOn_of_mapsTo isOpen_univ
    hu.contMDiffOn hι hk (hb.mapsTo.mono_left inter_subset_right))

end Regularity

/-! ### Checks -/

/-- The inclusion of the closed upper half-plane into `ℂ` is weakly pseudoholomorphic up to the
boundary for the complex structure of `ℂ`, and maps the boundary into the real line, which is
totally real for it; so it lies in `W^{k,3}_loc` up to the boundary for every `k`, and is smooth
up to the boundary. Being `C¹` and pseudoholomorphic, it is also smooth by the `C¹` criterion. -/
example : (∀ k : ℕ, MemWkpLocMapBordered 𝓘(ℝ, ℂ) 3 k ((↑) : ClosedUpperHalfPlane → ℂ)) ∧
    ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ, ℂ) ∞ ((↑) : ClosedUpperHalfPlane → ℂ) ∧
    ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ, ℂ) ∞ ((↑) : ClosedUpperHalfPlane → ℂ) := by
  have hι : IsTotallyRealEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ⊤
      ((SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ).toContMDiff ⊤).almostComplexStructureAt
      ((↑) : ℝ → ℂ) := by
    refine (isTotallyRealEmbedding_congr fun x ↦ ?_).1 (isTotallyRealEmbedding_ofRealCLM ⊤)
    ext (v : ℂ)
    simp only [ContMDiffAlmostComplexStructure.almostComplexStructureAt_toLinearMap,
      AlmostComplexStructure.constSmooth_almostComplexStructureAt,
      SmoothAlmostComplexStructure.toContMDiff_toEndomorphism_apply]
    exact (AlmostComplexStructure.ofComplexModule_apply v).trans
      (SmoothAlmostComplexStructure.ofComplexManifold_apply (M := ℂ) (x : ℂ) v).symm
  have h := isWeakPseudoholomorphicBordered_coe (ℓ := ⊤) (p := 3)
  exact ⟨fun k ↦ h.memWkpLocMapBordered_of_mapsBoundaryInto (by norm_num) (by norm_num) hι le_top
    mapsBoundaryInto_coe_ofReal le_top, h.contMDiff_infty_of_mapsBoundaryInto (by norm_num) hι
      le_top mapsBoundaryInto_coe_ofReal,
    IsPseudoholomorphic.contMDiff_of_mapsBoundaryInto
      SmoothAlmostComplexStructure.isPseudoholomorphic_coe_ofBorderedHolomorphic
        ClosedUpperHalfPlane.contMDiff_coe
        (by rwa [SmoothAlmostComplexStructure.toContMDiff_almostComplexStructureAt] at hι) le_top
        mapsBoundaryInto_coe_ofReal⟩

end TauCeti
