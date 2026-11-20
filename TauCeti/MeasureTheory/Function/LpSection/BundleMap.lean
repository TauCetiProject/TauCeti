/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.LpSection.Chart

/-!
# Transport of `Lᵖ` sections along bundle maps

Let `E → M` and `E' → N` be vector bundles, let `ψ : N → M` be a map of the bases and let
`A y : E (ψ y) →L[𝕜] E' y` be a family of continuous linear maps, a *bundle map covering `ψ`*.
It transports a section `s` of `E` to the section

`(A^* s)(y) = A y (s (ψ y))`

of `E'`. If `ψ` is measure preserving from `ν` to `μ` and `‖A y‖ ≤ C` for almost every `y`, this
is a bounded operator `Lᵖ(E, μ) → Lᵖ(E', ν)` of norm at most `C`, for every `1 ≤ p ≤ ∞`
(`TauCeti.LpSection.compBundleMap`). When every `A y` is a linear isometry it is a linear isometry
(`TauCeti.LpSection.compBundleMapₗᵢ`), and when `ψ` and the fibre maps are invertible, with inverse
data covering a measure-preserving inverse map, it is a linear isometric equivalence
(`TauCeti.LpSection.compBundleMapEquiv`), a unitary operator on `L²`.

For a unitary bundle isomorphism `Φ` covering a measure-preserving homeomorphism `φ : M → N` this
is the unitary `L²(E, μ) → L²(E', ν)` given by `s ↦ (y ↦ Φ (s (φ⁻¹ y)))`: take `ψ = φ⁻¹` and let
`A y` be the restriction of `Φ` to the fibre over `φ⁻¹ y`. With `E = E'` and a measure-preserving
group action on a bundle, these operators form the induced unitary action on `L²` sections, and for
a trivial line bundle they are the Koopman operators `f ↦ f ∘ φ⁻¹`. Mathlib's
`MeasureTheory.Lp.compMeasurePreservingₗᵢ` is the special case of the trivial bundle with identity
fibre maps.

The only regularity asked of the bundle map is that it is continuous in charts
(`TauCeti.IsContinuousBundleMap`): for every vector `v` of the model fibre and every pair of atlas
charts, the coordinates of `A y` applied to the chart section through `v` depend continuously on
`y`. This makes transported sections measurable
(`TauCeti.AEStronglyMeasurableSection.comp_bundleMap`): the coordinates of `A^* s` are obtained from
the coordinates of `s ∘ ψ` by applying a family of linear maps that is continuous in the vector and
measurable in the base point. The map `ψ` itself need not be continuous; it is only required to be
measure preserving.

## Main definitions

* `TauCeti.IsContinuousBundleMap`: a bundle map covering `ψ` is continuous in charts.
* `TauCeti.LpSection.compBundleMap`: the bounded operator `Lᵖ(E, μ) → Lᵖ(E', ν)` induced by an
  essentially bounded bundle map covering a measure-preserving map.
* `TauCeti.LpSection.compBundleMapₗᵢ`: the linear isometry induced by a fibrewise isometric bundle
  map.
* `TauCeti.LpSection.compBundleMapEquiv`: the linear isometric equivalence induced by a fibrewise
  isometric bundle map with an inverse.

## Main results

* `TauCeti.isContinuousBundleMap_id`: the identity bundle map is continuous in charts.
* `TauCeti.isContinuousBundleMap_trivial_iff`: for trivial bundles, continuity in charts is
  continuity of `y ↦ A y v` for every vector `v`.
* `TauCeti.AEStronglyMeasurableSection.comp_bundleMap`: transported measurable sections are
  measurable.
* `TauCeti.LpSection.coeFn_compBundleMap`: the operator is `s ↦ (y ↦ A y (s (ψ y)))`.
* `TauCeti.LpSection.norm_compBundleMap_le`: its norm is at most an essential bound of `‖A y‖`.
* `TauCeti.LpSection.compBundleMap_comp`, `TauCeti.LpSection.compBundleMap_id`: transport is
  compatible with composition of bundle maps and is the identity for the identity bundle map.
* `TauCeti.LpSection.trivialEquiv_compBundleMapₗᵢ_id`: for trivial bundles and identity fibre
  maps, transport is Mathlib's composition with a measure-preserving map.

## References

* L. I. Nicolaescu, *Lectures on the Geometry of Manifolds*, 3rd ed., §10.2.3, for the `L²` spaces
  of sections.
-/

public section

noncomputable section

open Bundle MeasureTheory Set Filter
open scoped ENNReal

namespace TauCeti

variable {𝕜 M N P F F' F'' : Type*} [RCLike 𝕜]
  [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  [NormedAddCommGroup F''] [NormedSpace 𝕜 F'']
  {E : M → Type*} [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace 𝕜 (E x)] [FiberBundle F E] [VectorBundle 𝕜 F E]
  {E' : N → Type*} [TopologicalSpace (TotalSpace F' E')] [∀ y, NormedAddCommGroup (E' y)]
  [∀ y, NormedSpace 𝕜 (E' y)] [FiberBundle F' E'] [VectorBundle 𝕜 F' E']
  {E'' : P → Type*} [TopologicalSpace (TotalSpace F'' E'')] [∀ z, NormedAddCommGroup (E'' z)]
  [∀ z, NormedSpace 𝕜 (E'' z)] [FiberBundle F'' E''] [VectorBundle 𝕜 F'' E'']
  {ψ : N → M}

/-! ### Continuity in charts -/

variable (𝕜 F F') in
/-- A family of continuous linear maps `A y : E (ψ y) →L[𝕜] E' y`, a bundle map covering
`ψ : N → M`, is *continuous in charts* when, for every atlas chart `e` of `E`, every atlas chart
`e'` of `E'` and every vector `v` of the model fibre of `E`, the coordinates in `e'` of `A y`
applied to the vector of `E (ψ y)` with coordinates `v` in `e` depend continuously on `y` wherever
both charts are defined. -/
def IsContinuousBundleMap (ψ : N → M) (A : ∀ y, E (ψ y) →L[𝕜] E' y) : Prop :=
  ∀ (e : Trivialization F (π F E)) [MemTrivializationAtlas e]
    (e' : Trivialization F' (π F' E')) [MemTrivializationAtlas e'] (v : F),
    ContinuousOn (fun y ↦ e'.continuousLinearMapAt 𝕜 y (A y (e.symmL 𝕜 (ψ y) v)))
      (ψ ⁻¹' e.baseSet ∩ e'.baseSet)

theorem isContinuousBundleMap_iff {A : ∀ y, E (ψ y) →L[𝕜] E' y} :
    IsContinuousBundleMap 𝕜 F F' ψ A ↔
      ∀ (e : Trivialization F (π F E)) [MemTrivializationAtlas e]
        (e' : Trivialization F' (π F' E')) [MemTrivializationAtlas e'] (v : F),
        ContinuousOn (fun y ↦ e'.continuousLinearMapAt 𝕜 y (A y (e.symmL 𝕜 (ψ y) v)))
          (ψ ⁻¹' e.baseSet ∩ e'.baseSet) :=
  Iff.rfl

variable (𝕜 F E) in
/-- The identity bundle map is continuous in charts: its chart expressions are the coordinate
changes of the bundle. -/
theorem isContinuousBundleMap_id :
    IsContinuousBundleMap 𝕜 F F id (fun x ↦ ContinuousLinearMap.id 𝕜 (E x)) := by
  intro e _ e' _ v
  refine ((continuousOn_coordChange 𝕜 e e').clm_apply (continuousOn_const (c := v))).congr
    fun x hx ↦ ?_
  simp only [ContinuousLinearMap.id_apply, id, e.symmL_apply hx.1,
    e'.continuousLinearMapAt_apply_of_mem (R := 𝕜) hx.2, ContinuousLinearEquiv.coe_coe,
    e.coordChangeL_apply e' hx]

variable (𝕜 F F' ψ) in
/-- For trivial bundles, a bundle map is continuous in charts exactly when it is strongly
continuous: `y ↦ A y v` is continuous for every vector `v`. -/
theorem isContinuousBundleMap_trivial_iff {A : ∀ y, Trivial M F (ψ y) →L[𝕜] Trivial N F' y} :
    IsContinuousBundleMap 𝕜 F F' ψ A ↔ ∀ v : F, Continuous fun y ↦ A y v := by
  have : MemTrivializationAtlas (Trivial.trivialization M F) := ⟨mem_singleton _⟩
  have : MemTrivializationAtlas (Trivial.trivialization N F') := ⟨mem_singleton _⟩
  refine ⟨fun h v ↦ ?_, fun h e _ e' _ v ↦ ?_⟩
  · simpa only [Trivial.trivialization_baseSet, preimage_univ, inter_self,
      continuousOn_univ, Trivial.continuousLinearMapAt_trivialization, Trivial.symmL_trivialization,
      ContinuousLinearMap.id_apply] using
      h (Trivial.trivialization M F) (Trivial.trivialization N F') v
  · obtain rfl := Trivial.eq_trivialization M F e
    obtain rfl := Trivial.eq_trivialization N F' e'
    simpa only [Trivial.trivialization_baseSet, preimage_univ, inter_self,
      continuousOn_univ, Trivial.continuousLinearMapAt_trivialization, Trivial.symmL_trivialization,
      ContinuousLinearMap.id_apply] using h v

variable (𝕜 F ψ) in
/-- The identity fibre maps of a trivial bundle, covering any map of the bases, are continuous in
charts. -/
theorem isContinuousBundleMap_trivial_id :
    IsContinuousBundleMap 𝕜 F F ψ (E := Trivial M F) (E' := Trivial N F)
      fun _ ↦ (LinearIsometry.id : F →ₗᵢ[𝕜] F).toContinuousLinearMap :=
  (isContinuousBundleMap_trivial_iff 𝕜 F F ψ).2 fun _ ↦ continuous_const

/-! ### Measurability of transported sections -/

section Measurable

variable [MeasurableSpace M] [MeasurableSpace N] [OpensMeasurableSpace M]
  [SecondCountableTopology M] [OpensMeasurableSpace N] [SecondCountableTopology N]
  {μ : Measure M} {ν : Measure N}

/-- A bundle map continuous in charts, covering a measure-preserving map, transports
a.e.-strongly measurable sections to a.e.-strongly measurable sections. -/
theorem AEStronglyMeasurableSection.comp_bundleMap {A : ∀ y, E (ψ y) →L[𝕜] E' y}
    (hA : IsContinuousBundleMap 𝕜 F F' ψ A) (hψ : MeasurePreserving ψ ν μ) {s : ∀ x, E x}
    (hs : AEStronglyMeasurableSection 𝕜 F μ s) :
    AEStronglyMeasurableSection 𝕜 F' ν (fun y ↦ A y (s (ψ y))) := by
  cases isEmpty_or_nonempty M
  · have : IsEmpty N := Function.isEmpty ψ
    exact .of_isEmpty _
  obtain ⟨p, hp⟩ := FiberBundle.exists_iUnion_baseSet_trivializationAt_eq_univ F E (B := M)
  refine .mk fun e' _ ↦ ?_
  have hcover : e'.baseSet = ⋃ n, ψ ⁻¹' (trivializationAt F E (p n)).baseSet ∩ e'.baseSet := by
    rw [← iUnion_inter, ← preimage_iUnion, hp, preimage_univ, univ_inter]
  rw [hcover, aestronglyMeasurable_iUnion_iff]
  intro n
  -- On the part of the base set of `e'` lying over the base set of `e`, the coordinates of the
  -- transported section in `e'` are the coordinates of `s ∘ ψ` in `e` followed by the chart
  -- expression of the bundle map, which is continuous in the vector and measurable in the point.
  set e := trivializationAt F E (p n)
  have hS : MeasurableSet (ψ ⁻¹' e.baseSet ∩ e'.baseSet) :=
    (hψ.measurable e.open_baseSet.measurableSet).inter e'.open_baseSet.measurableSet
  -- The coordinates of `s ∘ ψ` in `e`, on the preimage of the base set of `e`.
  have hc : AEStronglyMeasurable (fun y ↦ e.continuousLinearMapAt 𝕜 (ψ y) (s (ψ y)))
      (ν.restrict (ψ ⁻¹' e.baseSet ∩ e'.baseSet)) :=
    ((hs.aestronglyMeasurable_continuousLinearMapAt e).comp_quasiMeasurePreserving
      (hψ.restrict_preimage e.open_baseSet.measurableSet).quasiMeasurePreserving).mono_measure
      (Measure.restrict_mono inter_subset_left le_rfl)
  refine (hc.apply_of_forall_of_continuousAt
    (g := fun y w ↦ e'.continuousLinearMapAt 𝕜 y (A y (e.symmL 𝕜 (ψ y) w)))
    (fun w ↦ (hA e e' w).aestronglyMeasurable hS)
    (ae_of_all _ fun y ↦ ((e'.continuousLinearMapAt 𝕜 y).continuous.comp
      ((A y).continuous.comp (e.symmL 𝕜 (ψ y)).continuous)).continuousAt)).congr ?_
  filter_upwards [ae_restrict_mem hS] with y hy
  rw [e.symmL_continuousLinearMapAt hy.1]

end Measurable

section Bounded

variable [MeasurableSpace N] [MeasurableSpace P] {ν : Measure N} {ρ : Measure P}
  {A : ∀ y, E (ψ y) →L[𝕜] E' y}

omit [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P] in
/-- Composing an essentially bounded bundle map covering `ψ` with an essentially bounded bundle map
covering a quasi-measure-preserving map `ψ₂` gives an essentially bounded bundle map. -/
theorem exists_ae_norm_comp_le {ψ₂ : P → N} (hψ₂ : QuasiMeasurePreserving ψ₂ ρ ν)
    {A₂ : ∀ z, E' (ψ₂ z) →L[𝕜] E'' z} (hAC : ∃ C, ∀ᵐ y ∂ν, ‖A y‖ ≤ C)
    (hA₂C : ∃ C, ∀ᵐ z ∂ρ, ‖A₂ z‖ ≤ C) :
    ∃ C, ∀ᵐ z ∂ρ, ‖(A₂ z).comp (A (ψ₂ z))‖ ≤ C := by
  obtain ⟨C₁, hC₁⟩ := hAC
  obtain ⟨C₂, hC₂⟩ := hA₂C
  refine ⟨C₂ * max C₁ 0, ?_⟩
  filter_upwards [hC₂, hψ₂.ae hC₁] with z h₂ h₁
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul h₂ (h₁.trans (le_max_left _ _))
    (norm_nonneg _) ((norm_nonneg _).trans h₂))

omit [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P] in
/-- A bundle map of linear isometries is essentially bounded, by `1`. -/
theorem exists_ae_norm_toContinuousLinearMap_le (A : ∀ y, E (ψ y) →ₗᵢ[𝕜] E' y) :
    ∃ C, ∀ᵐ y ∂ν, ‖(A y).toContinuousLinearMap‖ ≤ C :=
  ⟨1, ae_of_all _ fun y ↦ (A y).norm_toContinuousLinearMap_le⟩

end Bounded

/-! ### Transport of `Lᵖ` sections -/

section LpSection

variable [MeasurableSpace M] [MeasurableSpace N] [MeasurableSpace P] {μ : Measure M}
  {ν : Measure N} {ρ : Measure P} [OpensMeasurableSpace M] [SecondCountableTopology M]
  [OpensMeasurableSpace N] [SecondCountableTopology N] [OpensMeasurableSpace P]
  [SecondCountableTopology P]
  [ContinuousFiberNorm F E] [ContinuousFiberNorm F' E'] [ContinuousFiberNorm F'' E'']
  {p : ℝ≥0∞} {A : ∀ y, E (ψ y) →L[𝕜] E' y} {C : ℝ}

omit [ContinuousFiberNorm F E] in
/-- A bundle map whose fibre maps have essentially bounded norm, covering a measure-preserving map,
transports sections with `p`-integrable fibre norm to sections with `p`-integrable fibre norm. -/
theorem memLp_norm_comp_bundleMap (hA : IsContinuousBundleMap 𝕜 F F' ψ A)
    (hψ : MeasurePreserving ψ ν μ) (hAC : ∀ᵐ y ∂ν, ‖A y‖ ≤ C) {s : ∀ x, E x}
    (hs : AEStronglyMeasurableSection 𝕜 F μ s) (hsp : MemLp (fun x ↦ ‖s x‖) p μ) :
    MemLp (fun y ↦ ‖A y (s (ψ y))‖) p ν := by
  refine ((hsp.comp_measurePreserving hψ).const_mul C).of_le
    (hs.comp_bundleMap hA hψ).aestronglyMeasurable_norm ?_
  filter_upwards [hAC] with y hy
  rw [norm_norm, Function.comp_apply, Real.norm_eq_abs, abs_mul, abs_norm]
  exact ((A y).le_of_opNorm_le hy _).trans
    (mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _))

namespace LpSection

/-- The transport `s ↦ (y ↦ A y (s (ψ y)))` of `Lᵖ` sections along a bundle map continuous in
charts with essentially bounded fibre maps, covering a measure-preserving map, as a linear map. -/
private def compBundleMapₗ (hψ : MeasurePreserving ψ ν μ) (A : ∀ y, E (ψ y) →L[𝕜] E' y)
    (hA : IsContinuousBundleMap 𝕜 F F' ψ A) (hAC : ∃ C, ∀ᵐ y ∂ν, ‖A y‖ ≤ C) :
    LpSection 𝕜 F E p μ →ₗ[𝕜] LpSection 𝕜 F' E' p ν where
  toFun f := mk (fun y ↦ A y (f (ψ y))) (f.aestronglyMeasurableSection.comp_bundleMap hA hψ)
    (memLp_norm_comp_bundleMap hA hψ hAC.choose_spec f.aestronglyMeasurableSection f.memLp_norm)
  map_add' f g := by
    rw [mk_add, mk_eq_mk_iff]
    filter_upwards [hψ.quasiMeasurePreserving.ae (coeFn_add f g)] with y hy
    rw [hy, map_add]
  map_smul' c f := by
    rw [RingHom.id_apply, mk_smul, mk_eq_mk_iff]
    filter_upwards [hψ.quasiMeasurePreserving.ae (coeFn_smul f c)] with y hy
    rw [hy, map_smul]

/-- If the fibre maps have norm at most `C` almost everywhere, the transport of `f` has norm at most
`max C 0` times the norm of `f`. -/
private theorem norm_compBundleMapₗ_le (hψ : MeasurePreserving ψ ν μ)
    (hA : IsContinuousBundleMap 𝕜 F F' ψ A) (hAC : ∃ C, ∀ᵐ y ∂ν, ‖A y‖ ≤ C)
    (hC : ∀ᵐ y ∂ν, ‖A y‖ ≤ C) (f : LpSection 𝕜 F E p μ) :
    ‖compBundleMapₗ hψ A hA hAC f‖ ≤ max C 0 * ‖f‖ := by
  rw [compBundleMapₗ, LinearMap.coe_mk, AddHom.coe_mk, norm_mk, norm_def,
    ← ENNReal.toReal_ofReal (le_max_right C 0), ← ENNReal.toReal_mul,
    ← eLpNorm_comp_measurePreserving f.aestronglyMeasurable_norm hψ]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (f.memLp_norm.comp_measurePreserving hψ).eLpNorm_ne_top) ?_
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    (f.aestronglyMeasurableSection.comp_bundleMap hA hψ).aestronglyMeasurable_norm ?_ p
  filter_upwards [hC] with y hy
  rw [norm_norm, Function.comp_apply, norm_norm]
  exact ((A y).le_of_opNorm_le hy _).trans
    (mul_le_mul_of_nonneg_right (le_max_left C 0) (norm_nonneg _))

variable [Fact (1 ≤ p)]

variable (p) in
/-- **Transport along a bundle map.** A bundle map `A y : E (ψ y) →L[𝕜] E' y` continuous in charts,
covering a measure-preserving map `ψ` from `ν` to `μ`, whose fibre maps have essentially bounded
norm, induces the bounded operator `s ↦ (y ↦ A y (s (ψ y)))` from `Lᵖ(E, μ)` to `Lᵖ(E', ν)`. -/
def compBundleMap (hψ : MeasurePreserving ψ ν μ) (A : ∀ y, E (ψ y) →L[𝕜] E' y)
    (hA : IsContinuousBundleMap 𝕜 F F' ψ A) (hAC : ∃ C, ∀ᵐ y ∂ν, ‖A y‖ ≤ C) :
    LpSection 𝕜 F E p μ →L[𝕜] LpSection 𝕜 F' E' p ν :=
  -- The bound is supplied by a tactic: elaborating it as a term makes unification unfold the
  -- normed group structure of `LpSection` and time out.
  (compBundleMapₗ hψ A hA hAC).mkContinuous (max hAC.choose 0) fun f ↦ by
    exact norm_compBundleMapₗ_le hψ hA hAC hAC.choose_spec f

theorem compBundleMap_mk (hψ : MeasurePreserving ψ ν μ) (hA : IsContinuousBundleMap 𝕜 F F' ψ A)
    (hAC : ∃ C, ∀ᵐ y ∂ν, ‖A y‖ ≤ C) {s : ∀ x, E x} (hs : AEStronglyMeasurableSection 𝕜 F μ s)
    (hsp : MemLp (fun x ↦ ‖s x‖) p μ) :
    compBundleMap p hψ A hA hAC (mk s hs hsp) =
      mk (fun y ↦ A y (s (ψ y))) (hs.comp_bundleMap hA hψ)
        (memLp_norm_comp_bundleMap hA hψ hAC.choose_spec hs hsp) := by
  rw [compBundleMap, LinearMap.mkContinuous_apply, compBundleMapₗ, LinearMap.coe_mk,
    AddHom.coe_mk, mk_eq_mk_iff]
  filter_upwards [hψ.quasiMeasurePreserving.ae (coeFn_mk hs hsp)] with y hy
  rw [hy]

theorem coeFn_compBundleMap (hψ : MeasurePreserving ψ ν μ) (hA : IsContinuousBundleMap 𝕜 F F' ψ A)
    (hAC : ∃ C, ∀ᵐ y ∂ν, ‖A y‖ ≤ C) (f : LpSection 𝕜 F E p μ) :
    ∀ᵐ y ∂ν, compBundleMap p hψ A hA hAC f y = A y (f (ψ y)) := by
  have h := compBundleMap_mk hψ hA hAC f.aestronglyMeasurableSection f.memLp_norm
  rw [mk_coeFn] at h
  rw [h]
  exact coeFn_mk _ _

/-- The norm of the transport of `f` is the `Lᵖ(ν)` norm of the fibre norm of
`y ↦ A y (f (ψ y))`. -/
theorem norm_compBundleMap_apply (hψ : MeasurePreserving ψ ν μ)
    (hA : IsContinuousBundleMap 𝕜 F F' ψ A) (hAC : ∃ C, ∀ᵐ y ∂ν, ‖A y‖ ≤ C)
    (f : LpSection 𝕜 F E p μ) :
    ‖compBundleMap p hψ A hA hAC f‖ = (eLpNorm (fun y ↦ ‖A y (f (ψ y))‖) p ν).toReal := by
  have h := compBundleMap_mk hψ hA hAC f.aestronglyMeasurableSection f.memLp_norm
  rw [mk_coeFn] at h
  rw [h]
  exact norm_mk _ _

/-- The transport along a bundle map whose fibre maps have norm at most `C` almost everywhere has
norm at most `C`. -/
theorem norm_compBundleMap_le (hψ : MeasurePreserving ψ ν μ)
    (hA : IsContinuousBundleMap 𝕜 F F' ψ A) (hAC : ∃ C, ∀ᵐ y ∂ν, ‖A y‖ ≤ C) (hC₀ : 0 ≤ C)
    (hC : ∀ᵐ y ∂ν, ‖A y‖ ≤ C) : ‖compBundleMap p hψ A hA hAC‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC₀ fun f ↦ by
    have h := norm_compBundleMapₗ_le hψ hA hAC hC f
    rw [max_eq_left hC₀] at h
    exact h

/-- **Functoriality.** Transport along `A₁` covering `ψ₁` followed by transport along `A₂` covering
`ψ₂` is transport along the composite bundle map `z ↦ A₂ z ∘ A₁ (ψ₂ z)` covering `ψ₁ ∘ ψ₂`. -/
theorem compBundleMap_comp {ψ₂ : P → N} (hψ : MeasurePreserving ψ ν μ)
    (hψ₂ : MeasurePreserving ψ₂ ρ ν) (hA : IsContinuousBundleMap 𝕜 F F' ψ A)
    (hAC : ∃ C, ∀ᵐ y ∂ν, ‖A y‖ ≤ C) {A₂ : ∀ z, E' (ψ₂ z) →L[𝕜] E'' z}
    (hA₂ : IsContinuousBundleMap 𝕜 F' F'' ψ₂ A₂) (hA₂C : ∃ C, ∀ᵐ z ∂ρ, ‖A₂ z‖ ≤ C)
    (hA₁₂ : IsContinuousBundleMap 𝕜 F F'' (ψ ∘ ψ₂) fun z ↦ (A₂ z).comp (A (ψ₂ z))) :
    (compBundleMap p hψ₂ A₂ hA₂ hA₂C).comp (compBundleMap p hψ A hA hAC) =
      compBundleMap p (hψ.comp hψ₂) (fun z ↦ (A₂ z).comp (A (ψ₂ z))) hA₁₂
        (exists_ae_norm_comp_le hψ₂.quasiMeasurePreserving hAC hA₂C) := by
  refine ContinuousLinearMap.ext fun f ↦ (ext_iff _ _).2 ?_
  filter_upwards [coeFn_compBundleMap hψ₂ hA₂ hA₂C (compBundleMap p hψ A hA hAC f),
    hψ₂.quasiMeasurePreserving.ae (coeFn_compBundleMap hψ hA hAC f),
    coeFn_compBundleMap (hψ.comp hψ₂) hA₁₂ _ f] with z h₁ h₂ h₃
  -- The two sides differ by unfolding `ψ ∘ ψ₂` inside the fibre, which `rw` cannot reach.
  rw [ContinuousLinearMap.comp_apply, h₁, h₂, h₃]
  rfl

/-- Transport along the identity bundle map is the identity. -/
theorem compBundleMap_id :
    compBundleMap p (MeasurePreserving.id μ) (fun x ↦ ContinuousLinearMap.id 𝕜 (E x))
      (isContinuousBundleMap_id 𝕜 F E) ⟨1, ae_of_all _ fun _ ↦ ContinuousLinearMap.norm_id_le⟩ =
      ContinuousLinearMap.id 𝕜 (LpSection 𝕜 F E p μ) := by
  refine ContinuousLinearMap.ext fun f ↦ (ext_iff _ _).2 ?_
  filter_upwards [coeFn_compBundleMap (MeasurePreserving.id μ) (isContinuousBundleMap_id 𝕜 F E)
    ⟨1, ae_of_all _ fun _ ↦ ContinuousLinearMap.norm_id_le⟩ f] with x hx
  rw [hx]
  rfl

/-! ### Isometric bundle maps -/

variable {A : ∀ y, E (ψ y) →ₗᵢ[𝕜] E' y}

variable (p) in
/-- **Transport along an isometric bundle map.** A bundle map of linear isometries
`A y : E (ψ y) →ₗᵢ[𝕜] E' y` continuous in charts, covering a measure-preserving map `ψ` from `ν` to
`μ`, induces the linear isometry `s ↦ (y ↦ A y (s (ψ y)))` from `Lᵖ(E, μ)` to `Lᵖ(E', ν)`. -/
def compBundleMapₗᵢ (hψ : MeasurePreserving ψ ν μ) (A : ∀ y, E (ψ y) →ₗᵢ[𝕜] E' y)
    (hA : IsContinuousBundleMap 𝕜 F F' ψ fun y ↦ (A y).toContinuousLinearMap) :
    LpSection 𝕜 F E p μ →ₗᵢ[𝕜] LpSection 𝕜 F' E' p ν where
  toLinearMap := (compBundleMap p hψ _ hA (exists_ae_norm_toContinuousLinearMap_le A)).toLinearMap
  norm_map' f := by
    rw [ContinuousLinearMap.coe_coe, norm_compBundleMap_apply, norm_def,
      ← eLpNorm_comp_measurePreserving f.aestronglyMeasurable_norm hψ]
    simp only [LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map,
      Function.comp_def]

theorem coe_compBundleMapₗᵢ (hψ : MeasurePreserving ψ ν μ)
    (hA : IsContinuousBundleMap 𝕜 F F' ψ fun y ↦ (A y).toContinuousLinearMap) :
    ⇑(compBundleMapₗᵢ p hψ A hA) =
      compBundleMap p hψ _ hA (exists_ae_norm_toContinuousLinearMap_le A) :=
  (rfl)

theorem coeFn_compBundleMapₗᵢ (hψ : MeasurePreserving ψ ν μ)
    (hA : IsContinuousBundleMap 𝕜 F F' ψ fun y ↦ (A y).toContinuousLinearMap)
    (f : LpSection 𝕜 F E p μ) :
    ∀ᵐ y ∂ν, compBundleMapₗᵢ p hψ A hA f y = A y (f (ψ y)) :=
  coeFn_compBundleMap hψ hA (exists_ae_norm_toContinuousLinearMap_le A) f

variable {ψ' : M → N} {B : ∀ x, E' (ψ' x) →ₗᵢ[𝕜] E x}

variable (p) in
/-- **The unitary of a bundle isomorphism.** Let `A y : E (ψ y) →ₗᵢ[𝕜] E' y` cover a
measure-preserving map `ψ` from `ν` to `μ` and `B x : E' (ψ' x) →ₗᵢ[𝕜] E x` cover a
measure-preserving map `ψ'` from `μ` to `ν`, both continuous in charts, such that transporting any
section along `A` and then along `B`, or along `B` and then along `A`, gives it back. Then
transport along `A` is a linear isometric equivalence `Lᵖ(E, μ) ≃ₗᵢ[𝕜] Lᵖ(E', ν)` with inverse
transport along `B`; for `p = 2` it is a unitary operator. -/
def compBundleMapEquiv (hψ : MeasurePreserving ψ ν μ) (hψ' : MeasurePreserving ψ' μ ν)
    (A : ∀ y, E (ψ y) →ₗᵢ[𝕜] E' y) (B : ∀ x, E' (ψ' x) →ₗᵢ[𝕜] E x)
    (hA : IsContinuousBundleMap 𝕜 F F' ψ fun y ↦ (A y).toContinuousLinearMap)
    (hB : IsContinuousBundleMap 𝕜 F' F ψ' fun x ↦ (B x).toContinuousLinearMap)
    (hBA : ∀ (s : ∀ x, E x) x, B x (A (ψ' x) (s (ψ (ψ' x)))) = s x)
    (hAB : ∀ (t : ∀ y, E' y) y, A y (B (ψ y) (t (ψ' (ψ y)))) = t y) :
    LpSection 𝕜 F E p μ ≃ₗᵢ[𝕜] LpSection 𝕜 F' E' p ν where
  toLinearEquiv := LinearEquiv.ofLinearMap (compBundleMapₗᵢ p hψ A hA).toLinearMap
    (compBundleMapₗᵢ p hψ' B hB).toLinearMap
    (LinearMap.ext fun t ↦ (ext_iff _ _).2 <| by
      filter_upwards [coeFn_compBundleMapₗᵢ hψ hA (compBundleMapₗᵢ p hψ' B hB t),
        hψ.quasiMeasurePreserving.ae (coeFn_compBundleMapₗᵢ hψ' hB t)] with y h₁ h₂
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearIsometry.coe_toLinearMap,
        LinearMap.id_coe, id_eq, h₁, h₂]
      exact hAB t y)
    (LinearMap.ext fun f ↦ (ext_iff _ _).2 <| by
      filter_upwards [coeFn_compBundleMapₗᵢ hψ' hB (compBundleMapₗᵢ p hψ A hA f),
        hψ'.quasiMeasurePreserving.ae (coeFn_compBundleMapₗᵢ hψ hA f)] with x h₁ h₂
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearIsometry.coe_toLinearMap,
        LinearMap.id_coe, id_eq, h₁, h₂]
      exact hBA f x)
  norm_map' := (compBundleMapₗᵢ p hψ A hA).norm_map

variable (hψ : MeasurePreserving ψ ν μ) (hψ' : MeasurePreserving ψ' μ ν)
  (hA : IsContinuousBundleMap 𝕜 F F' ψ fun y ↦ (A y).toContinuousLinearMap)
  (hB : IsContinuousBundleMap 𝕜 F' F ψ' fun x ↦ (B x).toContinuousLinearMap)
  (hBA : ∀ (s : ∀ x, E x) x, B x (A (ψ' x) (s (ψ (ψ' x)))) = s x)
  (hAB : ∀ (t : ∀ y, E' y) y, A y (B (ψ y) (t (ψ' (ψ y)))) = t y)

@[simp]
theorem coe_compBundleMapEquiv :
    ⇑(compBundleMapEquiv p hψ hψ' A B hA hB hBA hAB) = compBundleMapₗᵢ p hψ A hA :=
  (rfl)

@[simp]
theorem coe_compBundleMapEquiv_symm :
    ⇑(compBundleMapEquiv p hψ hψ' A B hA hB hBA hAB).symm = compBundleMapₗᵢ p hψ' B hB :=
  (rfl)

theorem coeFn_compBundleMapEquiv (f : LpSection 𝕜 F E p μ) :
    ∀ᵐ y ∂ν, compBundleMapEquiv p hψ hψ' A B hA hB hBA hAB f y = A y (f (ψ y)) :=
  coeFn_compBundleMapₗᵢ hψ hA f

theorem coeFn_compBundleMapEquiv_symm (t : LpSection 𝕜 F' E' p ν) :
    ∀ᵐ x ∂μ, (compBundleMapEquiv p hψ hψ' A B hA hB hBA hAB).symm t x = B x (t (ψ' x)) :=
  coeFn_compBundleMapₗᵢ hψ' hB t

/-! ### Trivial bundles -/

variable (p) in
/-- For trivial bundles and identity fibre maps, transport along a measure-preserving map `ψ` is
composition with `ψ`: under the identification `TauCeti.LpSection.trivialEquiv` of `Lᵖ` sections
of a trivial bundle with `Lp`, it is Mathlib's `MeasureTheory.Lp.compMeasurePreservingₗᵢ`. -/
theorem trivialEquiv_compBundleMapₗᵢ_id (hψ : MeasurePreserving ψ ν μ)
    (f : LpSection 𝕜 F (Trivial M F) p μ) :
    trivialEquiv 𝕜 p ν (compBundleMapₗᵢ p hψ (fun _ ↦ LinearIsometry.id)
      (isContinuousBundleMap_trivial_id 𝕜 F ψ) f) =
      Lp.compMeasurePreservingₗᵢ 𝕜 ψ hψ (trivialEquiv 𝕜 p μ f) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_trivialEquiv (compBundleMapₗᵢ p hψ (fun _ ↦ LinearIsometry.id)
      (isContinuousBundleMap_trivial_id 𝕜 F ψ) f),
    coeFn_compBundleMapₗᵢ hψ (isContinuousBundleMap_trivial_id 𝕜 F ψ) f,
    Lp.coeFn_compMeasurePreserving (trivialEquiv 𝕜 p μ f) hψ,
    hψ.quasiMeasurePreserving.ae (coeFn_trivialEquiv f)] with y h₁ h₂ h₃ h₄
  rw [h₁, h₂, LinearIsometry.id_apply, ← h₄]
  exact h₃.symm

end LpSection

end LpSection

end TauCeti
