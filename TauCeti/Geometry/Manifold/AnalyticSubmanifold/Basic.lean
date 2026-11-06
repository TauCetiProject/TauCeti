/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Analysis.Analytic.Submanifold.Transport
public import TauCeti.Analysis.Analytic.Submanifold.ZeroDimensional
public import TauCeti.Geometry.Manifold.ContMDiff.Analytic
import TauCeti.Topology.OpenPartialHomeomorph.Composition

/-!
# Analytic submanifolds of analytic manifolds

A nonempty subset `s` of a manifold `M` modelled on `(E, H)` via `I : ModelWithCorners 𝕜 E H` is a
`d`-dimensional *analytic submanifold* (`TauCeti.IsMAnalyticSubmanifold I e d s`), relative to a
continuous linear coordinate equivalence `e : E ≃L[𝕜] Fin n → 𝕜`, if around every `x ∈ s` the image
of `s ∩ (extChartAt I x).source` in `Fin n → 𝕜` under `e ∘ extChartAt I x` is a `d`-dimensional
analytic submanifold in the sense of `TauCeti.IsAnalyticSubmanifold`.

When `I` is boundaryless and `M` is an analytic manifold (`IsManifold I ω M`), transition maps
between extended charts of the maximal `C^ω` atlas are analytic open partial homeomorphisms on
their open domains. Consequently:

* `IsMAnalyticSubmanifold I e d s` is independent of the choice of continuous linear equivalence
  `e : E ≃L[𝕜] Fin n → 𝕜` and invariant under `ModelWithCorners.transContinuousLinearEquiv`
  (even without boundarylessness or `IsManifold`);
* `IsMAnalyticSubmanifold I e d s` is independent of the choice of charts in `maximalAtlas I ω M`
  or `atlas H M`, and is equivalent to local straightening on an open neighborhood of the image of
  each `x ∈ s` in *some* maximal-atlas chart;
* open subsets, singletons, nonempty discrete subsets (in dimension `0`), and nonempty relatively
  open subsets of analytic submanifolds are analytic submanifolds, and the property is local in the
  ambient topology of `M`.

## Main declarations

* `TauCeti.IsMAnalyticSubmanifold I e d s`: `s ⊆ M` is a `d`-dimensional analytic submanifold.
* `TauCeti.isMAnalyticSubmanifold_iff_of_continuousLinearEquiv`,
  `TauCeti.isMAnalyticSubmanifold_transContinuousLinearEquiv_iff`: independence of `e` and
  invariance under linear model reparametrizations.
* `TauCeti.isMAnalyticSubmanifold_model_iff`, `TauCeti.isMAnalyticSubmanifold_model_refl_iff`:
  agreement with `TauCeti.IsAnalyticSubmanifold` on normed model spaces.
* `TauCeti.IsMAnalyticSubmanifold.image_extend_of_mem_maximalAtlas`,
  `TauCeti.isMAnalyticSubmanifold_iff_forall_mem_maximalAtlas`,
  `TauCeti.isMAnalyticSubmanifold_iff_forall_mem_atlas`,
  `TauCeti.isMAnalyticSubmanifold_iff_exists_mem_maximalAtlas`,
  `TauCeti.isMAnalyticSubmanifold_iff_exists_isOpen_extChartAt`: chart-independence and local
  open-neighborhood characterizations.
* `TauCeti.IsMAnalyticSubmanifold.inter`, `TauCeti.IsMAnalyticSubmanifold.of_isOpen_preimage_val`,
  `TauCeti.isMAnalyticSubmanifold_iff_exists_isOpen`: restriction to relatively open subsets and
  ambient locality.
* `IsOpen.isMAnalyticSubmanifold`, `TauCeti.isMAnalyticSubmanifold_univ`,
  `TauCeti.isMAnalyticSubmanifold_singleton`, `TauCeti.isMAnalyticSubmanifold_zero_iff`: open
  subsets, the whole manifold, points, and `0`-dimensional submanifolds.

## References

* S. G. Krantz and H. R. Parks, *A Primer of Real Analytic Functions*, second edition,
  Birkhäuser, 2002, Chapter 2 and §6.4.
* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore
  di Pisa (3) 18 (1964), 449–474, §1.
-/

public section

open Filter Function IsManifold Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n n' d : ℕ} {s t u : Set M}

/-! ### Definition and coordinate-equivalence independence -/

/-- A subset `s` of a charted space `M` is a `d`-dimensional *analytic submanifold* with respect to
`I : ModelWithCorners 𝕜 E H` and `e : E ≃L[𝕜] Fin n → 𝕜` if `s` is nonempty and, around every
`x ∈ s`, the image of `s ∩ (extChartAt I x).source` under `e ∘ extChartAt I x` is a `d`-dimensional
analytic submanifold of `Fin n → 𝕜`. -/
def IsMAnalyticSubmanifold (I : ModelWithCorners 𝕜 E H) (e : E ≃L[𝕜] Fin n → 𝕜)
    (d : ℕ) (s : Set M) : Prop :=
  s.Nonempty ∧ ∀ x ∈ s,
    IsAnalyticSubmanifold d ((e ∘ extChartAt I x) '' (s ∩ (extChartAt I x).source))

/-- Definitional characterization of `TauCeti.IsMAnalyticSubmanifold` in preferred extended
charts. -/
theorem isMAnalyticSubmanifold_iff {e : E ≃L[𝕜] Fin n → 𝕜} :
    IsMAnalyticSubmanifold I e d s ↔ s.Nonempty ∧ ∀ x ∈ s,
      IsAnalyticSubmanifold d ((e ∘ extChartAt I x) '' (s ∩ (extChartAt I x).source)) :=
  Iff.rfl

namespace IsMAnalyticSubmanifold

/-- An analytic submanifold is nonempty. -/
theorem nonempty {e : E ≃L[𝕜] Fin n → 𝕜} (hs : IsMAnalyticSubmanifold I e d s) : s.Nonempty :=
  hs.1

/-- An analytic submanifold has dimension at most that of the ambient model space. -/
theorem le {e : E ≃L[𝕜] Fin n → 𝕜} (hs : IsMAnalyticSubmanifold I e d s) : d ≤ n := by
  obtain ⟨x, hx⟩ := hs.1
  exact (hs.2 x hx).le

/-- The image of `s ∩ (extChartAt I x).source` in `Fin n → 𝕜` around any `x ∈ s` is an analytic
submanifold of dimension `d`. -/
theorem image_extChartAt {e : E ≃L[𝕜] Fin n → 𝕜} (hs : IsMAnalyticSubmanifold I e d s)
    {x : M} (hx : x ∈ s) :
    IsAnalyticSubmanifold d ((e ∘ extChartAt I x) '' (s ∩ (extChartAt I x).source)) :=
  hs.2 x hx

/-- **Coordinate-equivalence independence.** Replacing `e : E ≃L[𝕜] Fin n → 𝕜` by another
continuous linear equivalence `e' : E ≃L[𝕜] Fin n' → 𝕜` preserves `IsMAnalyticSubmanifold`. -/
theorem of_continuousLinearEquiv {e : E ≃L[𝕜] Fin n → 𝕜} (hs : IsMAnalyticSubmanifold I e d s)
    (e' : E ≃L[𝕜] Fin n' → 𝕜) :
    IsMAnalyticSubmanifold I e' d s := by
  refine ⟨hs.1, fun x hx ↦ ?_⟩
  have heq : (e' ∘ extChartAt I x) '' (s ∩ (extChartAt I x).source) =
      (e.symm.trans e') '' ((e ∘ extChartAt I x) '' (s ∩ (extChartAt I x).source)) := by
    rw [← image_comp]
    congr 1
    ext y
    simp
  rw [heq]
  exact (hs.2 x hx).image_continuousLinearEquiv (e.symm.trans e')

end IsMAnalyticSubmanifold

/-- **Coordinate-equivalence independence.** `IsMAnalyticSubmanifold` does not depend on the choice
of continuous linear equivalence identifying the model space `E` with `Fin n → 𝕜`. -/
theorem isMAnalyticSubmanifold_iff_of_continuousLinearEquiv (e : E ≃L[𝕜] Fin n → 𝕜)
    (e' : E ≃L[𝕜] Fin n' → 𝕜) :
    IsMAnalyticSubmanifold I e d s ↔ IsMAnalyticSubmanifold I e' d s :=
  ⟨fun h ↦ h.of_continuousLinearEquiv e', fun h ↦ h.of_continuousLinearEquiv e⟩

/-- Transporting the model vector space along a continuous linear equivalence `L : E ≃L[𝕜] E'`
composes the coordinate equivalence with `L`. -/
@[simp]
theorem isMAnalyticSubmanifold_transContinuousLinearEquiv_iff
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    (L : E ≃L[𝕜] E') (e' : E' ≃L[𝕜] Fin n' → 𝕜) :
    IsMAnalyticSubmanifold (I.transContinuousLinearEquiv L) e' d s ↔
      IsMAnalyticSubmanifold I (L.trans e') d s := by
  simp only [isMAnalyticSubmanifold_iff, I.coe_extChartAt_transContinuousLinearEquiv,
    extChartAt_source, Function.comp_def, ContinuousLinearEquiv.trans_apply]

/-- On a normed space modelled on itself, `IsMAnalyticSubmanifold` is `IsAnalyticSubmanifold` of
the coordinate image `e '' s`. -/
@[simp]
theorem isMAnalyticSubmanifold_model_iff (e : E ≃L[𝕜] Fin n → 𝕜) {s : Set E} :
    IsMAnalyticSubmanifold 𝓘(𝕜, E) e d s ↔ IsAnalyticSubmanifold d (e '' s) := by
  refine ⟨fun ⟨⟨x, hx⟩, h⟩ ↦ by simpa using h x hx, fun hs ↦ ⟨?_, fun x _ ↦ by simpa using hs⟩⟩
  rcases hs.nonempty with ⟨_, x, hx, rfl⟩
  exact ⟨x, hx⟩

/-- On `Fin n → 𝕜` with the identity coordinate equivalence, `IsMAnalyticSubmanifold` agrees with
`TauCeti.IsAnalyticSubmanifold`. -/
theorem isMAnalyticSubmanifold_model_refl_iff {s : Set (Fin n → 𝕜)} :
    IsMAnalyticSubmanifold 𝓘(𝕜, Fin n → 𝕜) (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) d s ↔
      IsAnalyticSubmanifold d s := by
  simp

/-- Any singleton in a charted space is a `0`-dimensional analytic submanifold. -/
theorem isMAnalyticSubmanifold_singleton {e : E ≃L[𝕜] Fin n → 𝕜} (a : M) :
    IsMAnalyticSubmanifold I e 0 {a} := by
  refine ⟨singleton_nonempty a, ?_⟩
  rintro a rfl
  have hmem : {a} ∩ (extChartAt I a).source = {a} :=
    inter_eq_left.2 (singleton_subset_iff.2 (mem_extChartAt_source a))
  rw [hmem, image_singleton]
  exact isAnalyticSubmanifold_singleton _

/-! ### Open subsets, zero-dimensional submanifolds, restrictions, and chart transitions -/

section Boundaryless

variable [I.Boundaryless]

/-- A `0`-dimensional analytic submanifold of a boundaryless charted space is discrete in its
subspace topology. -/
theorem IsMAnalyticSubmanifold.isDiscrete {e : E ≃L[𝕜] Fin n → 𝕜}
    (hs : IsMAnalyticSubmanifold I e 0 s) : IsDiscrete s := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro x hxs
  set C := (chartAt H x).extendTrans I e.toHomeomorph
  have hC_coe : ⇑C = e ∘ extChartAt I x := by
    ext y
    simp [C, extChartAt]
  have hxC : x ∈ C.source := by simp [C]
  have hdisc : IsDiscrete (C '' (s ∩ C.source)) := by
    simpa [hC_coe, C, extChartAt] using (hs.image_extChartAt hxs).isDiscrete
  obtain ⟨U, hU, hUC⟩ :=
    isDiscrete_iff_forall_mem_exists_isOpen.1 hdisc (C x) ⟨x, ⟨hxs, hxC⟩, rfl⟩
  refine ⟨C.source ∩ C ⁻¹' U, C.continuousOn.isOpen_inter_preimage C.open_source hU, ?_⟩
  ext y
  constructor
  · rintro ⟨⟨hyC, hyU⟩, hys⟩
    have hCy : C y = C x := mem_singleton_iff.1 (hUC ▸ ⟨hyU, y, ⟨hys, hyC⟩, rfl⟩)
    exact mem_singleton_iff.2 (C.injOn hyC hxC hCy)
  · rintro rfl
    have hyU : C y ∈ U := (hUC.symm ▸ mem_singleton (C y)).1
    exact ⟨⟨hxC, hyU⟩, hxs⟩

/-- Every nonempty discrete subset of a boundaryless charted space is a `0`-dimensional analytic
submanifold. -/
theorem _root_.IsDiscrete.isMAnalyticSubmanifold_zero {e : E ≃L[𝕜] Fin n → 𝕜}
    (hs : IsDiscrete s) (hne : s.Nonempty) : IsMAnalyticSubmanifold I e 0 s := by
  refine ⟨hne, fun x hxs ↦ ?_⟩
  set C := (chartAt H x).extendTrans I e.toHomeomorph
  have hC_coe : ⇑C = e ∘ extChartAt I x := by
    ext y
    simp [C, extChartAt]
  have hneC : ((e ∘ extChartAt I x) '' (s ∩ (extChartAt I x).source)).Nonempty :=
    ⟨e (extChartAt I x x), x, ⟨hxs, mem_extChartAt_source x⟩, rfl⟩
  refine IsDiscrete.isAnalyticSubmanifold_zero ?_ hneC
  rw [← hC_coe, isDiscrete_iff_forall_mem_exists_isOpen]
  rintro _ ⟨y, ⟨hys, hyext⟩, rfl⟩
  have hyC : y ∈ C.source := by simpa [C, extChartAt] using hyext
  obtain ⟨W, hW, hWs⟩ := isDiscrete_iff_forall_mem_exists_isOpen.1 hs y hys
  refine ⟨C.target ∩ C.symm ⁻¹' W, C.continuousOn_symm.isOpen_inter_preimage C.open_target hW, ?_⟩
  ext w
  constructor
  · rintro ⟨⟨_, hwW⟩, z, ⟨hzs, hzext⟩, rfl⟩
    have hzC : z ∈ C.source := by simpa [C, extChartAt] using hzext
    rw [mem_preimage, C.left_inv hzC] at hwW
    have hzy : z = y := mem_singleton_iff.1 (hWs ▸ ⟨hwW, hzs⟩)
    exact mem_singleton_iff.2 (congrArg C hzy)
  · rintro rfl
    have hyW : y ∈ W := (hWs.symm ▸ mem_singleton y).1
    exact ⟨⟨C.map_source hyC, by simpa [C.left_inv hyC] using hyW⟩, y, ⟨hys, hyext⟩, rfl⟩

/-- On a boundaryless charted space, `0`-dimensional analytic submanifolds are precisely the
nonempty discrete subsets. -/
@[simp]
theorem isMAnalyticSubmanifold_zero_iff {e : E ≃L[𝕜] Fin n → 𝕜} :
    IsMAnalyticSubmanifold I e 0 s ↔ s.Nonempty ∧ IsDiscrete s :=
  ⟨fun hs ↦ ⟨hs.nonempty, hs.isDiscrete⟩,
    fun ⟨hne, hs⟩ ↦ hs.isMAnalyticSubmanifold_zero hne⟩

/-- Intersecting a `d`-dimensional analytic submanifold with an open set of `M` that meets it gives
a `d`-dimensional analytic submanifold. -/
theorem IsMAnalyticSubmanifold.inter {e : E ≃L[𝕜] Fin n → 𝕜}
    (hs : IsMAnalyticSubmanifold I e d s) (hu : IsOpen u) (hne : (s ∩ u).Nonempty) :
    IsMAnalyticSubmanifold I e d (s ∩ u) := by
  refine ⟨hne, fun x ⟨hxs, hxu⟩ ↦ ?_⟩
  set C := (chartAt H x).extendTrans I e.toHomeomorph
  have hC_coe : ⇑C = e ∘ extChartAt I x := by
    ext y
    simp [C, extChartAt]
  have hC_src : (extChartAt I x).source = C.source := by simp [C]
  let V := C.target ∩ C.symm ⁻¹' u
  have hV : IsOpen V := C.continuousOn_symm.isOpen_inter_preimage C.open_target hu
  have heq : (e ∘ extChartAt I x) '' ((s ∩ u) ∩ (extChartAt I x).source) =
      ((e ∘ extChartAt I x) '' (s ∩ (extChartAt I x).source)) ∩ V := by
    rw [← hC_coe, hC_src, inter_comm (s ∩ u), C.image_source_inter_eq',
      inter_comm s C.source, C.image_source_inter_eq', preimage_inter, inter_inter_distrib_left]
  rw [heq]
  have hxC : x ∈ C.source := by simp [C]
  exact (hs.image_extChartAt hxs).inter hV
    ⟨C x, ⟨x, ⟨hxs, mem_extChartAt_source x⟩, by rw [← hC_coe]⟩,
      C.map_source hxC, by simpa [C.left_inv hxC] using hxu⟩

/-- A nonempty relatively open subset of a `d`-dimensional analytic submanifold is a
`d`-dimensional analytic submanifold. -/
theorem IsMAnalyticSubmanifold.of_isOpen_preimage_val {e : E ≃L[𝕜] Fin n → 𝕜}
    (hs : IsMAnalyticSubmanifold I e d s) (hts : t ⊆ s)
    (ht : IsOpen (Subtype.val ⁻¹' t : Set s)) (hne : t.Nonempty) :
    IsMAnalyticSubmanifold I e d t := by
  obtain ⟨u, hu, hut⟩ := isOpen_induced_iff.mp ht
  have heq : s ∩ u = t := by
    ext x
    exact ⟨fun ⟨hxs, hxu⟩ ↦ (Set.ext_iff.mp hut ⟨x, hxs⟩).mp hxu,
      fun hxt ↦ ⟨hts hxt, (Set.ext_iff.mp hut ⟨x, hts hxt⟩).mpr hxt⟩⟩
  simpa only [heq] using hs.inter hu (heq.symm ▸ hne)

/-- Any nonempty open subset of a boundaryless charted space with `n`-dimensional model is an
`n`-dimensional analytic submanifold. -/
theorem _root_.IsOpen.isMAnalyticSubmanifold {e : E ≃L[𝕜] Fin n → 𝕜}
    (hu : IsOpen u) (hne : u.Nonempty) :
    IsMAnalyticSubmanifold I e n u := by
  refine ⟨hne, fun x hxu ↦ ?_⟩
  set C := (chartAt H x).extendTrans I e.toHomeomorph
  have hC_coe : ⇑C = e ∘ extChartAt I x := by
    ext y
    simp [C, extChartAt]
  have hC_src : (extChartAt I x).source = C.source := by simp [C]
  have heq : (e ∘ extChartAt I x) '' (u ∩ (extChartAt I x).source) = C.target ∩ C.symm ⁻¹' u := by
    rw [← hC_coe, hC_src, inter_comm, C.image_source_inter_eq']
  rw [heq]
  have hxC : x ∈ C.source := by simp [C]
  exact (C.continuousOn_symm.isOpen_inter_preimage C.open_target hu).isAnalyticSubmanifold
    ⟨C x, C.map_source hxC, by simpa [C.left_inv hxC] using hxu⟩

/-- A nonempty boundaryless charted space with `n`-dimensional model is an `n`-dimensional
analytic submanifold of itself. -/
theorem isMAnalyticSubmanifold_univ [Nonempty M] (e : E ≃L[𝕜] Fin n → 𝕜) :
    IsMAnalyticSubmanifold I e n (univ : Set M) :=
  isOpen_univ.isMAnalyticSubmanifold univ_nonempty

/-- Core chart-gluing lemma: if around each `x ∈ s ∩ c.source` there is a maximal-atlas chart `φ`
and an open neighborhood `U` of `e (φ.extend I x)` in which `s` is a `d`-dimensional analytic
submanifold, then `(e ∘ c.extend I) '' (s ∩ c.source)` is a `d`-dimensional analytic submanifold
whenever `s ∩ c.source` is nonempty. -/
private theorem isAnalyticSubmanifold_image_extend_of_local {e : E ≃L[𝕜] Fin n → 𝕜}
    {c : OpenPartialHomeomorph M H} (hc : c ∈ maximalAtlas I ω M)
    (hne : (s ∩ c.source).Nonempty)
    (hloc : ∀ x ∈ s ∩ c.source, ∃ φ ∈ maximalAtlas I ω M, x ∈ φ.source ∧
      ∃ U : Set (Fin n → 𝕜), IsOpen U ∧ e (φ.extend I x) ∈ U ∧
        IsAnalyticSubmanifold d (U ∩ (e ∘ φ.extend I) '' (s ∩ φ.source))) :
    IsAnalyticSubmanifold d ((e ∘ c.extend I) '' (s ∩ c.source)) := by
  set C := c.extendTrans I e.toHomeomorph
  have hC_coe : ⇑C = e ∘ c.extend I := by
    ext y
    simp [C]
  rw [← hC_coe]
  refine isAnalyticSubmanifold_of_locally_isAnalyticSubmanifold (hne.image C) ?_
  rintro _ ⟨x, ⟨hxs, hxc⟩, rfl⟩
  obtain ⟨φ, hφ, hxφ, U, hU, hxU, hSU⟩ := hloc x ⟨hxs, hxc⟩
  set Φ := φ.extendTrans I e.toHomeomorph
  have hΦ_coe : ⇑Φ = e ∘ φ.extend I := by
    ext y
    simp [Φ]
  let Ψ := (Φ.symm.trans C).restrOpen U hU
  have hΨ_an : AnalyticOnNhd 𝕜 Ψ Ψ.source :=
    (OpenPartialHomeomorph.analyticOnNhd_extendTrans_symm_trans hφ hc e.symm.contDiff
      e.contDiff).mono inter_subset_left
  have htarget : Ψ.target ⊆ (C.symm.trans Φ).source := by
    intro w hw
    have hsub : Ψ.target ⊆ (Φ.symm.trans C).target := by
      simp only [Ψ, OpenPartialHomeomorph.restrOpen_toPartialEquiv, PartialEquiv.restr_target]
      exact inter_subset_left
    exact hsub hw
  have hΨ_symm_an : AnalyticOnNhd 𝕜 Ψ.symm Ψ.target :=
    ((OpenPartialHomeomorph.analyticOnNhd_extendTrans_symm_trans hc hφ e.symm.contDiff
      e.contDiff).mono htarget).congr Ψ.open_target fun _ _ ↦ rfl
  have hxΦ : x ∈ Φ.source := by simpa [Φ] using hxφ
  have hxC : x ∈ C.source := by simpa [C] using hxc
  have hxΨ : Φ x ∈ Ψ.source := by
    refine ⟨⟨Φ.map_source hxΦ, ?_⟩, by simpa [hΦ_coe] using hxU⟩
    rw [OpenPartialHomeomorph.symm_symm, mem_preimage, Φ.left_inv hxΦ]
    exact hxC
  have hSU' : IsAnalyticSubmanifold d (U ∩ Φ '' (s ∩ φ.source)) := by rwa [hΦ_coe]
  have himg : Ψ '' ((U ∩ Φ '' (s ∩ φ.source)) ∩ Ψ.source) = (C '' (s ∩ c.source)) ∩ Ψ.target := by
    have hsrc : (U ∩ Φ '' (s ∩ φ.source)) ∩ Ψ.source = Ψ.source ∩ Φ '' (Φ.source ∩ s) := by
      simp only [Ψ, OpenPartialHomeomorph.restrOpen_source, Φ,
        OpenPartialHomeomorph.extendTrans_source]
      rw [inter_comm s, inter_comm (U ∩ _), inter_assoc, ← inter_assoc U, inter_self, ← inter_assoc]
    have hC_src : C.source = c.source := by simp [C]
    rw [hsrc, Φ.image_restrOpen_symm_trans_source_inter C hU s, hC_src,
      inter_comm c.source, inter_comm]
  refine ⟨Ψ.target, Ψ.open_target, ?_, ?_⟩
  · have hval : Ψ (Φ x) = C x := by simp [Ψ, Φ.left_inv hxΦ]
    exact hval ▸ Ψ.map_source hxΨ
  · rw [← himg]
    exact hSU'.image_openPartialHomeomorph hΨ_an hΨ_symm_an
      ⟨Φ x, ⟨by simpa [hΦ_coe] using hxU, x, ⟨hxs, hxφ⟩, rfl⟩, hxΨ⟩

/-! ### Maximal-atlas independence and ambient locality -/

variable [IsManifold I ω M]

/-- **Maximal-atlas chart independence.** On a boundaryless `C^ω` manifold, the image of a
`d`-dimensional analytic submanifold in *every* chart `φ ∈ maximalAtlas I ω M` meeting `s` is a
`d`-dimensional analytic submanifold of `Fin n → 𝕜`. -/
theorem IsMAnalyticSubmanifold.image_extend_of_mem_maximalAtlas {e : E ≃L[𝕜] Fin n → 𝕜}
    (hs : IsMAnalyticSubmanifold I e d s) {φ : OpenPartialHomeomorph M H}
    (hφ : φ ∈ maximalAtlas I ω M) (hne : (s ∩ φ.source).Nonempty) :
    IsAnalyticSubmanifold d ((e ∘ φ.extend I) '' (s ∩ φ.source)) := by
  refine isAnalyticSubmanifold_image_extend_of_local hφ hne fun x ⟨hxs, _⟩ ↦
    ⟨chartAt H x, chart_mem_maximalAtlas x, mem_chart_source H x, univ, isOpen_univ, mem_univ _, ?_⟩
  simpa [extChartAt] using hs.image_extChartAt hxs

/-- **Maximal-atlas characterization.** On a boundaryless `C^ω` manifold, `s` is a `d`-dimensional
analytic submanifold if and only if it is nonempty and its image in every chart of
`maximalAtlas I ω M` meeting `s` is a `d`-dimensional analytic submanifold. -/
theorem isMAnalyticSubmanifold_iff_forall_mem_maximalAtlas {e : E ≃L[𝕜] Fin n → 𝕜} :
    IsMAnalyticSubmanifold I e d s ↔
      s.Nonempty ∧ ∀ φ ∈ maximalAtlas I ω M, (s ∩ φ.source).Nonempty →
        IsAnalyticSubmanifold d ((e ∘ φ.extend I) '' (s ∩ φ.source)) := by
  refine ⟨fun hs ↦ ⟨hs.nonempty, fun φ hφ hne ↦ hs.image_extend_of_mem_maximalAtlas hφ hne⟩,
    fun ⟨hne, h⟩ ↦ ⟨hne, fun x hxs ↦ ?_⟩⟩
  simpa [extChartAt] using
    h (chartAt H x) (chart_mem_maximalAtlas x) ⟨x, hxs, mem_chart_source H x⟩

/-- **Atlas characterization.** On a boundaryless `C^ω` manifold, `s` is a `d`-dimensional analytic
submanifold if and only if it is nonempty and its image in every chart of `atlas H M` meeting `s`
is a `d`-dimensional analytic submanifold. -/
theorem isMAnalyticSubmanifold_iff_forall_mem_atlas {e : E ≃L[𝕜] Fin n → 𝕜} :
    IsMAnalyticSubmanifold I e d s ↔
      s.Nonempty ∧ ∀ φ ∈ atlas H M, (s ∩ φ.source).Nonempty →
        IsAnalyticSubmanifold d ((e ∘ φ.extend I) '' (s ∩ φ.source)) := by
  refine ⟨fun hs ↦ ⟨hs.nonempty, fun φ hφ hne ↦
    hs.image_extend_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hφ) hne⟩,
    fun ⟨hne, h⟩ ↦ ⟨hne, fun x hxs ↦ ?_⟩⟩
  simpa [extChartAt] using h (chartAt H x) (chart_mem_atlas H x) ⟨x, hxs, mem_chart_source H x⟩

/-- **Local maximal-atlas characterization.** On a boundaryless `C^ω` manifold, `s` is a
`d`-dimensional analytic submanifold if and only if it is nonempty and around each `x ∈ s` there
exist a chart `φ ∈ maximalAtlas I ω M` containing `x` and an open neighborhood `U` of
`e (φ.extend I x)` in `Fin n → 𝕜` on which the coordinate image of `s` is a `d`-dimensional
analytic submanifold. -/
theorem isMAnalyticSubmanifold_iff_exists_mem_maximalAtlas {e : E ≃L[𝕜] Fin n → 𝕜} :
    IsMAnalyticSubmanifold I e d s ↔
      s.Nonempty ∧ ∀ x ∈ s, ∃ φ ∈ maximalAtlas I ω M, x ∈ φ.source ∧
        ∃ U : Set (Fin n → 𝕜), IsOpen U ∧ e (φ.extend I x) ∈ U ∧
          IsAnalyticSubmanifold d (U ∩ (e ∘ φ.extend I) '' (s ∩ φ.source)) := by
  refine ⟨fun hs ↦ ⟨hs.nonempty, fun x hxs ↦
    ⟨chartAt H x, chart_mem_maximalAtlas x, mem_chart_source H x, univ, isOpen_univ, mem_univ _,
      by simpa [extChartAt] using hs.image_extChartAt hxs⟩⟩,
    fun ⟨hne, h⟩ ↦ ⟨hne, fun x hxs ↦ ?_⟩⟩
  simpa [extChartAt] using
    isAnalyticSubmanifold_image_extend_of_local (chart_mem_maximalAtlas x)
      ⟨x, hxs, mem_chart_source H x⟩ fun y ⟨hys, _⟩ ↦ h y hys

/-- **Local open-neighborhood characterization in preferred charts.** On a boundaryless `C^ω`
manifold, `s` is a `d`-dimensional analytic submanifold if and only if it is nonempty and around
each `x ∈ s` there is an open neighborhood `U ⊆ e '' (extChartAt I x).target` of
`e (extChartAt I x x)` whose intersection with
`(e ∘ extChartAt I x) '' (s ∩ (extChartAt I x).source)` is a `d`-dimensional analytic
submanifold. -/
theorem isMAnalyticSubmanifold_iff_exists_isOpen_extChartAt {e : E ≃L[𝕜] Fin n → 𝕜} :
    IsMAnalyticSubmanifold I e d s ↔
      s.Nonempty ∧ ∀ x ∈ s, ∃ U : Set (Fin n → 𝕜), IsOpen U ∧ e (extChartAt I x x) ∈ U ∧
        U ⊆ e '' (extChartAt I x).target ∧
          IsAnalyticSubmanifold d
            (U ∩ (e ∘ extChartAt I x) '' (s ∩ (extChartAt I x).source)) := by
  refine ⟨fun hs ↦ ⟨hs.nonempty, fun x hxs ↦ ?_⟩, fun ⟨hne, h⟩ ↦ ?_⟩
  · let U := e '' (extChartAt I x).target
    have hU : IsOpen U := e.toHomeomorph.isOpenMap _ (isOpen_extChartAt_target x)
    have hxU : e (extChartAt I x x) ∈ U := mem_image_of_mem e (mem_extChartAt_target x)
    have hinter : U ∩ (e ∘ extChartAt I x) '' (s ∩ (extChartAt I x).source) =
        (e ∘ extChartAt I x) '' (s ∩ (extChartAt I x).source) := by
      refine inter_eq_right.2 ?_
      rintro _ ⟨y, ⟨_, hy⟩, rfl⟩
      exact mem_image_of_mem e ((extChartAt I x).map_source hy)
    exact ⟨U, hU, hxU, Subset.rfl, hinter.symm ▸ hs.image_extChartAt hxs⟩
  · refine isMAnalyticSubmanifold_iff_exists_mem_maximalAtlas.2 ⟨hne, fun x hxs ↦ ?_⟩
    obtain ⟨U, hU, hxU, _, hSU⟩ := h x hxs
    exact ⟨chartAt H x, chart_mem_maximalAtlas x, mem_chart_source H x, U, hU,
      by simpa [extChartAt] using hxU, by simpa [extChartAt] using hSU⟩

/-- **Ambient locality.** A nonempty subset of a boundaryless `C^ω` manifold that is locally a
`d`-dimensional analytic submanifold around each of its points is a `d`-dimensional analytic
submanifold. -/
theorem isMAnalyticSubmanifold_of_locally_isMAnalyticSubmanifold {e : E ≃L[𝕜] Fin n → 𝕜}
    (hne : s.Nonempty)
    (h : ∀ x ∈ s, ∃ u : Set M, IsOpen u ∧ x ∈ u ∧ IsMAnalyticSubmanifold I e d (s ∩ u)) :
    IsMAnalyticSubmanifold I e d s := by
  refine isMAnalyticSubmanifold_iff_exists_isOpen_extChartAt.2 ⟨hne, fun x hxs ↦ ?_⟩
  obtain ⟨u, hu, hxu, hsu⟩ := h x hxs
  set C := (chartAt H x).extendTrans I e.toHomeomorph
  have hC_coe : ⇑C = e ∘ extChartAt I x := by
    ext y
    simp [C, extChartAt]
  have hC_src : (extChartAt I x).source = C.source := by simp [C]
  let U := C.target ∩ C.symm ⁻¹' u
  have hU : IsOpen U := C.continuousOn_symm.isOpen_inter_preimage C.open_target hu
  have hxC : x ∈ C.source := by simp [C]
  have hxU : e (extChartAt I x x) ∈ U := by
    rw [← Function.comp_apply (f := e), ← hC_coe]
    exact ⟨C.map_source hxC, by simpa [C.left_inv hxC] using hxu⟩
  have hUsub : U ⊆ e '' (extChartAt I x).target := by
    rintro w ⟨hwt, _⟩
    have hwsrc : C.symm w ∈ C.source := C.map_target hwt
    have hwext : C.symm w ∈ (extChartAt I x).source := by simpa [C, extChartAt] using hwsrc
    refine ⟨extChartAt I x (C.symm w), (extChartAt I x).map_source hwext, ?_⟩
    rw [← Function.comp_apply (f := e), ← hC_coe, C.right_inv hwt]
  have hinter : U ∩ (e ∘ extChartAt I x) '' (s ∩ (extChartAt I x).source) =
      (e ∘ extChartAt I x) '' ((s ∩ u) ∩ (extChartAt I x).source) := by
    rw [← hC_coe, hC_src, inter_comm s, C.image_source_inter_eq',
      inter_comm (s ∩ u), C.image_source_inter_eq', preimage_inter, inter_comm U,
      ← inter_inter_distrib_left]
  exact ⟨U, hU, hxU, hUsub, hinter.symm ▸ hsu.image_extChartAt ⟨hxs, hxu⟩⟩

/-- A subset of a boundaryless `C^ω` manifold is a `d`-dimensional analytic submanifold if and only
if it is nonempty and locally a `d`-dimensional analytic submanifold around each of its points. -/
theorem isMAnalyticSubmanifold_iff_exists_isOpen {e : E ≃L[𝕜] Fin n → 𝕜} :
    IsMAnalyticSubmanifold I e d s ↔
      s.Nonempty ∧ ∀ x ∈ s, ∃ u : Set M, IsOpen u ∧ x ∈ u ∧ IsMAnalyticSubmanifold I e d (s ∩ u) :=
  ⟨fun hs ↦ ⟨hs.nonempty, fun x _ ↦ ⟨univ, isOpen_univ, mem_univ x, by simpa using hs⟩⟩,
    fun ⟨hne, h⟩ ↦ isMAnalyticSubmanifold_of_locally_isMAnalyticSubmanifold hne h⟩

end Boundaryless

end TauCeti
