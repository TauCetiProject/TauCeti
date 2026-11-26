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
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.TargetChange
import TauCeti.Analysis.Sobolev.Local.ChainRule.HalfDisc
import TauCeti.Geometry.Manifold.Boundary.Invariance
import TauCeti.Geometry.Manifold.ContMDiff.Atlas
import TauCeti.Geometry.Manifold.Complex.TotallyReal.AdaptedChart
import TauCeti.Geometry.Manifold.Complex.TotallyReal.Examples
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.Sobolev.LocalMap.Bordered.Atlas.Higher
import TauCeti.Geometry.Manifold.Sobolev.LocalMap.Locality
import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Chart

/-!
# Regularity up to a totally real boundary of weak pseudoholomorphic maps

Let `X` be a Riemann surface with boundary, `M` a manifold modelled on a boundaryless model `I`
with finite-dimensional model vector space, `J₀` an almost complex structure on `M` of class
`C^ℓ`, and `ι : N → M` a totally real embedding for `J₀`. A weak pseudoholomorphic map
`u : X → M` up to the boundary on an open set `s`
(`TauCeti.IsWeakPseudoholomorphicOnBordered`), for `J₀` regarded as a family independent of the
domain point and the zero inhomogeneous term, which maps the boundary points of `s` into `ι (N)`,
lies in `W^{k,p}_loc` up to the boundary for every `k ≤ ℓ` and finite `p > 2`. For `ℓ ≥ 2` this is
the conclusion `W^{ℓ,p}` of McDuff–Salamon, Theorem B.4.1, so `u` is `C^{ℓ-1}` up to the boundary.

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

* `TauCeti.IsWeakCauchyRiemannOn.chartPushforward_symm_trans_comp`: the homogeneous coordinate
  equation for a structure independent of the domain point, under a change of target chart, and
  `TauCeti.ContMDiffAlmostComplexStructure.chartPushforward_mul_self`: a structure read in a `C¹`
  chart squares to `-1`.
* `TauCeti.IsWeakPseudoholomorphicOnBordered.memWkpLocMapOnBordered_of_mapsTo`,
  `TauCeti.IsWeakPseudoholomorphicBordered.memWkpLocMapBordered_of_mapsBoundaryInto`:
  **regularity up to a totally real boundary**, `W^{k,p}_loc` up to the boundary for `k ≤ ℓ`.
* Check: the inclusion of the closed upper half-plane into `ℂ`, with boundary in the totally real
  line `ℝ`, satisfies the hypotheses for every `ℓ`.

## Implementation notes

The structure is independent of the domain point and the inhomogeneous term vanishes, as in
McDuff–Salamon, Theorem B.4.1. Domain-dependent structures and inhomogeneous terms need the joint
regularity of the structure and the term read in bordered charts, and a structure that is standard
along the zero section of one adapted chart at every boundary point, which are not treated here.

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

/-! ### Changing the target chart -/

section TargetChart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {n : ℕ∞}
  {G G' : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup G']
  [NormedSpace ℝ G'] [CompleteSpace G']

/-- **The homogeneous coordinate equation under a change of target chart.** Let `J₀` be an almost
complex structure on `M`, and `ψ₁`, `ψ₂` charts of `M` into normed spaces, both `C¹` with `C¹`
inverses. A weak solution `g` of `∂ₛg + ψ₁_* J₀(g) ∂ₜg = 0` on `U`, with values in the source of the
transition `Θ = ψ₂ ∘ ψ₁⁻¹`, gives the weak solution `Θ ∘ g` of `∂ₛg + ψ₂_* J₀(g) ∂ₜg = 0`: the
derivative of `Θ` intertwines the two pushed-forward structures
(`TauCeti.ContMDiffAlmostComplexStructure.chartPushforward_symm_trans_comp_fderiv`). -/
theorem IsWeakCauchyRiemannOn.chartPushforward_symm_trans_comp
    {J₀ : ContMDiffAlmostComplexStructure I n M} {ψ₁ : OpenPartialHomeomorph M G}
    {ψ₂ : OpenPartialHomeomorph M G'} (hψ₁ : ContMDiffOn I 𝓘(ℝ, G) 1 ψ₁ ψ₁.source)
    (hψ₁s : ContMDiffOn 𝓘(ℝ, G) I 1 ψ₁.symm ψ₁.target)
    (hψ₂ : ContMDiffOn I 𝓘(ℝ, G') 1 ψ₂ ψ₂.source)
    (hψ₂s : ContMDiffOn 𝓘(ℝ, G') I 1 ψ₂.symm ψ₂.target) {p : ENNReal} {U : Set ℂ} {g : ℂ → G}
    (h : IsWeakCauchyRiemannOn p U (fun _ v ↦ J₀.chartPushforward ψ₁ v) (fun _ _ ↦ 0) g)
    (hg : MapsTo g U (ψ₁.symm.trans ψ₂).source) :
    IsWeakCauchyRiemannOn p U (fun _ v ↦ J₀.chartPushforward ψ₂ v) (fun _ _ ↦ 0)
      (fun z ↦ ψ₁.symm.trans ψ₂ (g z)) := by
  obtain ⟨hΘ, -⟩ := OpenPartialHomeomorph.contDiffOn_symm_trans_and_symm_of_contMDiffOn hψ₁ hψ₁s
    hψ₂ hψ₂s
  refine h.contDiffOn_comp_of_intertwine (ψ₁.symm.trans ψ₂).open_source hΘ hg ?_ ?_ <;>
    refine (ae_restrict_iff' measurableSet_interior).2 (Eventually.of_forall fun z hz ↦ ?_)
  · have hq := hg (interior_subset hz)
    have hq' : g z ∈ ψ₁.target ∧ ψ₁.symm (g z) ∈ ψ₂.source := by simpa using hq
    exact J₀.chartPushforward_symm_trans_comp_fderiv hq
      ((hψ₁.mdifferentiableOn one_ne_zero).mdifferentiableAt
        (ψ₁.open_source.mem_nhds (ψ₁.map_target hq'.1)))
      ((hψ₂s.mdifferentiableOn one_ne_zero).mdifferentiableAt
        (ψ₂.open_target.mem_nhds ((ψ₁.symm.trans ψ₂).map_source hq).1))
      ((hΘ.differentiableOn one_ne_zero).differentiableAt
        ((ψ₁.symm.trans ψ₂).open_source.mem_nhds hq))
  · simp

/-- A structure pushed forward along a chart of `M` that is `C¹` with `C¹` inverse squares to `-1`
on the target of the chart. -/
theorem ContMDiffAlmostComplexStructure.chartPushforward_mul_self
    (J₀ : ContMDiffAlmostComplexStructure I n M) {ψ : OpenPartialHomeomorph M G}
    (hψ : ContMDiffOn I 𝓘(ℝ, G) 1 ψ ψ.source) (hψs : ContMDiffOn 𝓘(ℝ, G) I 1 ψ.symm ψ.target)
    {q : G} (hq : q ∈ ψ.target) : J₀.chartPushforward ψ q * J₀.chartPushforward ψ q = -1 := by
  ext v
  rw [mul_apply_eq_comp,
    J₀.chartPushforward_apply_chartPushforward_apply ψ hq
      ((hψ.mdifferentiableOn one_ne_zero).mdifferentiableAt
        (ψ.open_source.mem_nhds (ψ.map_target hq)))
      ((hψs.mdifferentiableOn one_ne_zero).mdifferentiableAt (ψ.open_target.mem_nhds hq)) v]
  simp

end TargetChart

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

omit [HasGroupoid X borderedHolomorphicGroupoid] in
/-- A real point of the extended target of a chart of `X` reads a boundary point of `X`. -/
private theorem isBoundaryPoint_extend_symm {φ : OpenPartialHomeomorph X ClosedUpperHalfPlane}
    {z : ℂ} (hz : z ∈ (φ.extend closedUpperHalfPlaneModel).target) (him : z.im = 0) :
    closedUpperHalfPlaneModel.IsBoundaryPoint ((φ.extend closedUpperHalfPlaneModel).symm z) := by
  have hz' : closedUpperHalfPlaneModel.symm z ∈ φ.target := by
    rw [OpenPartialHomeomorph.extend_target] at hz
    exact hz.1
  rw [OpenPartialHomeomorph.extend_coe_symm, Function.comp_apply,
    φ.isBoundaryPoint_iff closedUpperHalfPlaneModel closedUpperHalfPlaneModel rfl
      (φ.map_target hz'), φ.right_inv hz', closedUpperHalfPlaneModel_isBoundaryPoint_iff,
    coe_closedUpperHalfPlaneModel_symm_of_im_nonneg him.ge]
  exact him

omit [HasGroupoid X borderedHolomorphicGroupoid] [IsManifold I ∞ M] in
/-- **Testing one pair of charts.** For `2 < p < ∞`, a map continuous on an open set `t` inside
the source of a bordered holomorphic chart `φ`, mapping `t` into the source of a chart `χ` of `M`,
is a local Sobolev map up to the boundary on `t` as soon as its coordinate expression in `φ` and
`χ` is in the planar class over `t`. -/
private theorem memWkpLocMapOnBordered_of_memWkpLoc_chart (hp : 2 < p)
    (hp' : p ≠ ⊤) {m : ℕ} {t : Set X} (ht : IsOpen t)
    {φ : OpenPartialHomeomorph X ClosedUpperHalfPlane}
    (hφ : φ ∈ borderedHolomorphicGroupoid.maximalAtlas X) (htφ : t ⊆ φ.source)
    {χ : OpenPartialHomeomorph M H} (hχ : χ ∈ IsManifold.maximalAtlas I ∞ M)
    (htχ : MapsTo u t χ.source) (hu : ContinuousOn u t)
    (h : MemWkpLoc p ((φ.extend closedUpperHalfPlaneModel).target ∩
      (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' t) m
        (χ.extend I ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm)) :
    MemWkpLocMapOnBordered I p m u t := by
  refine (memWkpLocMapOnBordered_iff_of_subset_maximalAtlas_of_two_lt hp hp' ht (A := {φ})
    (singleton_subset_iff.2 hφ) (fun x hx ↦ ⟨φ, rfl, htφ hx⟩) (B := {χ})
    (singleton_subset_iff.2 hχ) fun x hx ↦ ⟨χ, rfl, htχ hx⟩).2 ⟨hu, ?_⟩
  rintro _ rfl _ rfl
  rwa [inter_eq_left.2 fun x hx ↦ htχ hx]

omit [FiniteDimensional ℝ E] in
/-- In a bordered holomorphic chart `φ` and a chart `χ` of `M`, over an open set `t ⊆ s` mapped
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

/-- **Regularity near an interior point.** For `2 < p < ∞` and `k ≤ ℓ`, near a point of `s` that
is not a boundary point of `X`, a weak pseudoholomorphic map for a `C^ℓ` structure independent of
the domain point and the zero term is in `W^{k+1,p}_loc`. -/
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
  have hx₀t : x₀ ∈ t := ⟨⟨⟨hx₀, mem_chart_source _ x₀⟩, hb⟩, mem_chart_source H (u x₀)⟩
  refine ⟨t, mem_nhdsWithin_of_mem_nhds (ht.mem_nhds hx₀t), ?_⟩
  have htχ : MapsTo u t χ.source := fun x hx ↦ hx.2
  -- The coordinate domain avoids the real axis, so it is open.
  obtain ⟨Ω, hΩ, hD⟩ := φ.exists_isOpen_extend_target_inter_preimage ht
  set D := (φ.extend closedUpperHalfPlaneModel).target ∩
    (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' t
  have hpos : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hDo : IsOpen D := by
    convert hΩ.inter hpos using 1
    rw [hD]
    refine Set.ext fun z ↦ ⟨fun hz ↦ ⟨hz.1, show 0 < z.im from lt_of_le_of_ne hz.2 fun h0 ↦ ?_⟩,
      fun hz ↦ ⟨hz.1, show 0 ≤ z.im from le_of_lt hz.2⟩⟩
    have hzD : z ∈ D := hD ▸ hz
    exact hzD.2.1.2 (isBoundaryPoint_extend_symm hzD.1 h0.symm)
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
      contDiffOn_snd fun x (hx : x ∈ univ ×ˢ χ'.target) ↦ hx.2)
    contDiffOn_const (fun z hz ↦ ⟨trivial, hwt z hz⟩)
    (ae_restrict_of_forall_mem hDo.measurableSet fun z hz ↦
      J₀.chartPushforward_mul_self (hχ'1.of_le (by simp)) (hχ's.of_le (by simp)) (hwt z hz))
    hw
  have htφ : t ⊆ φ.source := fun x hx ↦ hx.1.1.2
  refine memWkpLocMapOnBordered_of_memWkpLoc_chart hp hp' ht hφ htφ hχ htχ
    (h.continuousOn.mono hts) ?_
  rw [← χ.coe_extendTrans_refl I]
  exact hreg

/-- **Regularity near a point mapped into a totally real submanifold.** For `2 < p < ∞` and
`k + 1 ≤ ℓ`, near a point `x₀ ∈ s` with `u x₀ ∈ ι (N)`, a weak pseudoholomorphic map for a `C^ℓ`
structure `J₀` independent of the domain point and the zero term, mapping the boundary points of
`s` into the image of a totally real embedding `ι` for `J₀`, is in `W^{k+1,p}_loc` up to the
boundary. The coordinate expression is moved into an adapted chart at `u x₀`, where the planar
boundary bootstrap applies. -/
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
  set D := (φ.extend closedUpperHalfPlaneModel).target ∩
    (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' t
  set w := χ' ∘ u ∘ (φ.extend closedUpperHalfPlaneModel).symm
  set Θ := χ'.symm.trans ψ
  -- The charts and the transition are `C^ℓ`.
  have hχ'1 : ContMDiffOn I 𝓘(ℝ, E) ℓ χ' χ'.source :=
    (χ.contMDiffOn_extendTrans hχ contDiff_id).of_le (by exact_mod_cast le_top)
  have hχ's : ContMDiffOn 𝓘(ℝ, E) I ℓ χ'.symm χ'.target :=
    (χ.contMDiffOn_extendTrans_symm hχ contDiff_id).of_le (by exact_mod_cast le_top)
  have hℓ1 : (1 : ℕ∞ω) ≤ ℓ := by exact_mod_cast hℓ
  obtain ⟨-, hΘs⟩ := OpenPartialHomeomorph.contDiffOn_symm_trans_and_symm_of_contMDiffOn hχ'1
    hχ's hψ.contMDiffOn hψ.contMDiffOn_symm
  have hwΘ : MapsTo w D Θ.source := fun z hz ↦ by
    have hu : u ((φ.extend closedUpperHalfPlaneModel).symm z) ∈ χ'.source := by
      simpa [χ'] using htχ hz.2
    refine ⟨χ'.map_source hu, ?_⟩
    change χ'.symm (χ' (u _)) ∈ ψ.source
    rw [χ'.left_inv hu]
    exact hz.2.2
  -- In the adapted chart, the equation is the homogeneous one for `ψ_* J₀`.
  have hw := (h.isWeakCauchyRiemannOn_chart_const hts hφ hχ
    htχ).chartPushforward_symm_trans_comp (hχ'1.of_le hℓ1) (hχ's.of_le hℓ1)
    (hψ.contMDiffOn.of_le hℓ1) (hψ.contMDiffOn_symm.of_le hℓ1) hwΘ
  have hΘt : ∀ z ∈ D, Θ (w z) ∈ ψ.target := fun z hz ↦ (Θ.map_source (hwΘ hz)).1
  have hΘw : ∀ z ∈ D, Θ (w z) = ψ (u ((φ.extend closedUpperHalfPlaneModel).symm z)) :=
    fun z hz ↦ by
      have hu : u ((φ.extend closedUpperHalfPlaneModel).symm z) ∈ χ'.source := by
        simpa [χ'] using htχ hz.2
      change ψ (χ'.symm (χ' (u _))) = _
      rw [χ'.left_inv hu]
  -- Along the real axis the adapted expression lies on the zero section.
  have hzero : ∀ s' : ℝ, (s' : ℂ) ∈ Ω → (Θ (w s')).2 = 0 := fun s' hs' ↦ by
    have hz : (s' : ℂ) ∈ D := hD ▸ ⟨hs', by simp⟩
    have hbd := isBoundaryPoint_extend_symm hz.1 (Complex.ofReal_im s')
    rw [hΘw _ hz]
    exact (hψ.isImage hz.2.2).2 (hb ⟨hz.2.1.1, hbd⟩)
  have hwD : IsWeakCauchyRiemannOn p (Ω ∩ {z | 0 ≤ z.im}) (fun _ v ↦ J₀.chartPushforward ψ v)
      (fun _ _ ↦ 0) (fun z ↦ Θ (w z)) := by
    rw [← hD]
    exact hw
  have hreg := memWkpLoc_of_isWeakCauchyRiemannOn_halfPlane_prod (Ω := ⟨Ω, hΩ⟩)
    (W' := univ ×ˢ ψ.target) (ℓ := m) hp hp' (isOpen_univ.prod ψ.open_target)
    ((hψ.contDiffOn_chartPushforward.of_le ?_).comp contDiffOn_snd
      fun (x : ℂ × (F × F)) (hx : x ∈ univ ×ˢ ψ.target ∩ {x : ℂ × (F × F) | 0 ≤ x.1.im}) ↦
        hx.1.2)
    contDiffOn_const (fun z hz ↦ ⟨trivial, hΘt z (hD ▸ hz)⟩)
    (ae_restrict_of_forall_mem (hΩ.measurableSet.inter (measurableSet_le measurable_const
      Complex.measurable_im)) fun z hz ↦ J₀.chartPushforward_mul_self
        (hψ.contMDiffOn.of_le hℓ1) (hψ.contMDiffOn_symm.of_le hℓ1) (hΘt z (hD ▸ hz)))
    hzero (fun s' hs' ↦ hψ.chartPushforward_of_snd_eq_zero _
      (hΘt _ (hD ▸ ⟨hs', by simp⟩)) (hzero s' hs'))
    hwD
  · -- Move back along the inverse transition, which is `C^ℓ`.
    lift p to ℝ≥0 using hp'
    have hback := MemWkpLoc.contDiffOn_comp_succ_halfPlane (Ω := ⟨Ω, hΩ⟩) (g := Θ.symm)
      (by exact_mod_cast hp) hreg hwD.continuousOn
      Θ.open_target (hΘs.of_le (by exact_mod_cast hm)) fun z hz ↦ Θ.map_source (hwΘ (hD ▸ hz))
    have htφ : t ⊆ φ.source := fun x hx ↦ hx.1.2
    refine memWkpLocMapOnBordered_of_memWkpLoc_chart (by exact_mod_cast hp) ENNReal.coe_ne_top
      ht hφ htφ hχ htχ (h.continuousOn.mono hts) ?_
    rw [← χ.coe_extendTrans_refl I]
    change MemWkpLoc _ D _ _
    rw [hD]
    exact hback.congr fun z hz ↦ (Θ.left_inv (hwΘ (hD ▸ hz))).symm
  · -- The pushed-forward structure is `C^(ℓ-1)` and `m + 1 ≤ ℓ`.
    have hm' : (m : ℕ∞) ≤ ℓ - 1 :=
      ENat.le_sub_of_add_le_right ENat.one_ne_top (by exact_mod_cast hm)
    exact_mod_cast hm'

/-- **Regularity up to a totally real boundary** (McDuff–Salamon, Theorem B.4.1). Let `2 < p < ∞`,
let `J₀` be an almost complex structure on `M` of class `C^ℓ`, regarded as a family independent of
the domain point, and let `ι : N → M` be a `C^(ℓ+1)` totally real embedding for `J₀`. A weak
pseudoholomorphic map up to the boundary on an open set `s`, for `J₀` and the zero inhomogeneous
term, which maps the boundary points of `X` in `s` into `ι (N)`, lies in `W^{k,p}_loc` up to the
boundary on `s` for every `k ≤ ℓ`. For `ℓ ≥ 2` it is therefore `C^{ℓ-1}` up to the boundary. -/
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
mapping the boundary of `X` into the image of a `C^(ℓ+1)` totally real embedding for `J₀`, lies in
`W^{k,p}_loc` up to the boundary for every `k ≤ ℓ`. -/
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

end Regularity

/-! ### Checks -/

/-- The inclusion of the closed upper half-plane into `ℂ` is weakly pseudoholomorphic up to the
boundary for the complex structure of `ℂ`, and maps the boundary into the real line, which is
totally real for it; so it lies in `W^{k,3}_loc` up to the boundary for every `k`. -/
example (k : ℕ) : MemWkpLocMapBordered 𝓘(ℝ, ℂ) 3 k ((↑) : ClosedUpperHalfPlane → ℂ) := by
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
  exact (isWeakPseudoholomorphicBordered_coe (ℓ := ⊤)).memWkpLocMapBordered_of_mapsBoundaryInto
    (by norm_num) (by norm_num) hι le_top mapsBoundaryInto_coe_ofReal le_top

end TauCeti
