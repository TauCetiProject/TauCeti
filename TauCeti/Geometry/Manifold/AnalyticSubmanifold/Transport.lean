/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import TauCeti.Geometry.Manifold.AnalyticSubmanifold.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import TauCeti.Analysis.Analytic.Submanifold.Image
import TauCeti.Analysis.Analytic.Submanifold.Product
import TauCeti.Geometry.Manifold.ContMDiff.Atlas
import TauCeti.Geometry.Manifold.LinearSlice
import TauCeti.Topology.Algebra.Module.Equiv.Fin
import TauCeti.Topology.OpenPartialHomeomorph.Composition

/-!
# Products, analytic isomorphisms, embeddings, and induced atlases for analytic submanifolds

This file relates `TauCeti.IsMAnalyticSubmanifold` to products of manifolds, local and global
analytic isomorphisms, analytic smooth embeddings (`Manifold.IsSmoothEmbedding`), and induced `C^ω`
manifold structures (`TauCeti.linearSliceChartedSpace`).

* **Products** (`TauCeti.IsMAnalyticSubmanifold.prod`): the Cartesian product `s ×ˢ t` of
  `d₁`- and `d₂`-dimensional analytic submanifolds is a `(d₁ + d₂)`-dimensional analytic
  submanifold of `M × N` for any continuous linear coordinate equivalence on `E × E'`.
* **Local and global analytic isomorphisms**
  (`OpenPartialHomeomorph.isMAnalyticSubmanifold_image`,
  `Diffeomorph.isMAnalyticSubmanifold_image`, `Diffeomorph.isMAnalyticSubmanifold_preimage`, and
  their `_iff` companions): an analytic open partial homeomorphism with analytic inverse
  (and in particular any analytic diffeomorphism `Φ : M ≃ₘ^ω⟮I, J⟯ N`) between boundaryless `C^ω`
  manifolds preserves `IsMAnalyticSubmanifold` without requiring completeness of `𝕜`.
* **Induced `C^ω` manifold structure** (`TauCeti.IsMAnalyticSubmanifold.exists_isManifold`,
  `TauCeti.IsMAnalyticSubmanifold.exists_isSmoothEmbedding`): every `d`-dimensional analytic
  submanifold `s ⊆ M` carries a `ChartedSpace (Fin d → 𝕜) s` making `s` a `C^ω` manifold with
  `C^ω` inclusion `(Subtype.val : s → M)`, and when `M` is modelled on `𝓘(𝕜, E)` this inclusion
  is a `C^ω` smooth embedding (`Manifold.IsSmoothEmbedding`).
* **Images of `C^ω` smooth embeddings**
  (`TauCeti.IsMAnalyticSubmanifold.image_of_isSmoothEmbedding`,
  `Manifold.IsSmoothEmbedding.isMAnalyticSubmanifold_range`): over a complete field `𝕜`, a `C^ω`
  smooth embedding transports analytic submanifolds of its domain to analytic submanifolds of its
  codomain; in particular, the range of a nonempty `C^ω` smooth embedding is an analytic
  submanifold.

## References

* S. G. Krantz and H. R. Parks, *A Primer of Real Analytic Functions*, second edition,
  Birkhäuser, 2002, Chapter 2 and §6.4.
* H. Whitney and F. Bruhat, *Quelques propriétés fondamentales des ensembles analytiques-réels*,
  Commentarii Mathematici Helvetici 33 (1959), 132–160.
-/

public section

noncomputable section

open Set Function Filter Topology IsManifold
open scoped Manifold ContDiff

namespace TauCeti

section Prod

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {n m l d₁ d₂ : ℕ} {s : Set M} {t : Set N}

/-! ### Products of analytic submanifolds -/

/-- The Cartesian product of a `d₁`-dimensional analytic submanifold of `M` and a `d₂`-dimensional
analytic submanifold of `N` is a `(d₁ + d₂)`-dimensional analytic submanifold of `M × N` for any
continuous linear coordinate equivalence on `E × E'`. -/
theorem IsMAnalyticSubmanifold.prod {e₁ : E ≃L[𝕜] Fin n → 𝕜} {e₂ : E' ≃L[𝕜] Fin m → 𝕜}
    (hs : IsMAnalyticSubmanifold I e₁ d₁ s) (ht : IsMAnalyticSubmanifold J e₂ d₂ t)
    (e_prod : (E × E') ≃L[𝕜] Fin l → 𝕜) :
    IsMAnalyticSubmanifold (I.prod J) e_prod (d₁ + d₂) (s ×ˢ t) := by
  let e₀ : (E × E') ≃L[𝕜] Fin (n + m) → 𝕜 :=
    (e₁.prodCongr e₂).trans (splitCoords (𝕜 := 𝕜) n m).symm
  suffices h₀ : IsMAnalyticSubmanifold (I.prod J) e₀ (d₁ + d₂) (s ×ˢ t) from
    h₀.of_continuousLinearEquiv e_prod
  rw [isMAnalyticSubmanifold_iff]
  refine ⟨hs.nonempty.prod ht.nonempty, ?_⟩
  rintro ⟨x, y⟩ ⟨hxs, hyt⟩
  have hprod := (hs.image_extChartAt hxs).prod (ht.image_extChartAt hyt)
  have heq :
      {z : Fin (n + m) → 𝕜 |
        (fun i ↦ z (Fin.castAdd m i)) ∈ (e₁ ∘ extChartAt I x) '' (s ∩ (extChartAt I x).source) ∧
        (fun i ↦ z (Fin.natAdd n i)) ∈ (e₂ ∘ extChartAt J y) '' (t ∩ (extChartAt J y).source)} =
      (e₀ ∘ extChartAt (I.prod J) (x, y)) ''
        ((s ×ˢ t) ∩ (extChartAt (I.prod J) (x, y)).source) := by
    rw [extChartAt_prod]
    ext z
    simp only [mem_ofPred_eq]
    have h1 : (fun i ↦ z (Fin.castAdd m i)) = (splitCoords (𝕜 := 𝕜) n m z).1 :=
      (congrArg Prod.fst (splitCoords_apply (𝕜 := 𝕜) z)).symm
    have h2 : (fun i ↦ z (Fin.natAdd n i)) = (splitCoords (𝕜 := 𝕜) n m z).2 :=
      (congrArg Prod.snd (splitCoords_apply (𝕜 := 𝕜) z)).symm
    rw [h1, h2]
    constructor
    · rintro ⟨⟨x', ⟨hx's, hx'src⟩, hx'eq⟩, ⟨y', ⟨hy't, hy'src⟩, hy'eq⟩⟩
      refine ⟨(x', y'), ⟨⟨hx's, hy't⟩, hx'src, hy'src⟩, ?_⟩
      apply (splitCoords (𝕜 := 𝕜) n m).injective
      apply Prod.ext
      · simpa [e₀] using hx'eq
      · simpa [e₀] using hy'eq
    · rintro ⟨⟨x', y'⟩, ⟨⟨hx's, hy't⟩, hx'src, hy'src⟩, rfl⟩
      exact ⟨⟨x', ⟨hx's, hx'src⟩, by simp [e₀]⟩, ⟨y', ⟨hy't, hy'src⟩, by simp [e₀]⟩⟩
  rwa [← heq]

end Prod

end TauCeti

/-! ### Transport along local and global analytic isomorphisms -/

namespace OpenPartialHomeomorph

open TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' H'}
  [I.Boundaryless] [J.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ω N]
  {n m d : ℕ}

/-- An open partial homeomorphism `Φ : OpenPartialHomeomorph M N` that is `C^ω` on its source with
`C^ω` inverse on its target maps the part of a `d`-dimensional analytic submanifold `s` in
`Φ.source` to a `d`-dimensional analytic submanifold of `N`, provided `s ∩ Φ.source` is
nonempty. -/
theorem isMAnalyticSubmanifold_image (Φ : OpenPartialHomeomorph M N)
    (hΦ : ContMDiffOn I J ω Φ Φ.source) (hΦs : ContMDiffOn J I ω Φ.symm Φ.target)
    {e : E ≃L[𝕜] Fin n → 𝕜} {e' : E' ≃L[𝕜] Fin m → 𝕜} {s : Set M}
    (hs : IsMAnalyticSubmanifold I e d s) (hne : (s ∩ Φ.source).Nonempty) :
    IsMAnalyticSubmanifold J e' d (Φ '' (s ∩ Φ.source)) := by
  rw [isMAnalyticSubmanifold_iff_exists_isOpen_extChartAt]
  refine ⟨hne.image Φ, ?_⟩
  rintro _ ⟨x, ⟨hxs, hxΦ⟩, rfl⟩
  let C_I := (chartAt H x).extendTrans I e.toHomeomorph
  let C_J := (chartAt H' (Φ x)).extendTrans J e'.toHomeomorph
  let Ψ := C_I.symm.trans (Φ.trans C_J)
  have hΨ_cd : ContDiffOn 𝕜 ω Ψ Ψ.source := by
    rw [← contMDiffOn_iff_contDiffOn]
    have hstep0 : ContMDiffOn 𝓘(𝕜, Fin n → 𝕜) I ω C_I.symm Ψ.source :=
      ((chartAt H x).contMDiffOn_extendTrans_symm (chart_mem_maximalAtlas x)
        e.symm.contDiff).mono fun _ hv ↦ hv.1
    have hstep1 : ContMDiffOn 𝓘(𝕜, Fin n → 𝕜) J ω (Φ ∘ C_I.symm) Ψ.source :=
      hΦ.comp hstep0 fun _ hv ↦ hv.2.1
    exact (((chartAt H' (Φ x)).contMDiffOn_extendTrans (chart_mem_maximalAtlas (Φ x))
      e'.contDiff).comp hstep1 fun _ hv ↦ hv.2.2).congr fun _ _ ↦ rfl
  have hΨ_symm_cd : ContDiffOn 𝕜 ω Ψ.symm Ψ.target := by
    rw [← contMDiffOn_iff_contDiffOn]
    have hstep0 : ContMDiffOn 𝓘(𝕜, Fin m → 𝕜) J ω C_J.symm Ψ.target :=
      ((chartAt H' (Φ x)).contMDiffOn_extendTrans_symm (chart_mem_maximalAtlas (Φ x))
        e'.symm.contDiff).mono fun _ hv ↦ hv.1.1
    have hstep1 : ContMDiffOn 𝓘(𝕜, Fin m → 𝕜) I ω (Φ.symm ∘ C_J.symm) Ψ.target :=
      hΦs.comp hstep0 fun _ hv ↦ hv.1.2
    exact (((chartAt H x).contMDiffOn_extendTrans (chart_mem_maximalAtlas x)
      e.contDiff).comp hstep1 fun _ hv ↦ hv.2).congr fun v _ ↦ by simp [Ψ, C_I]
  have hΨ : AnalyticOnNhd 𝕜 Ψ Ψ.source :=
    Ψ.open_source.analyticOn_iff_analyticOnNhd.1
      ((contDiffOn_omega_iff_analyticOn Ψ.open_source.uniqueDiffOn).1 hΨ_cd)
  have hΨ_symm : AnalyticOnNhd 𝕜 Ψ.symm Ψ.target :=
    Ψ.open_target.analyticOn_iff_analyticOnNhd.1
      ((contDiffOn_omega_iff_analyticOn Ψ.open_target.uniqueDiffOn).1 hΨ_symm_cd)
  have hxCI : x ∈ C_I.source := by simp [C_I]
  have hxΨ : C_I x ∈ Ψ.source :=
    ⟨C_I.map_source hxCI, by simpa [C_I.left_inv hxCI] using hxΦ,
      by simp [C_J, C_I.left_inv hxCI]⟩
  have hS_I : IsAnalyticSubmanifold d ((e ∘ extChartAt I x) '' (s ∩ (extChartAt I x).source)) :=
    hs.image_extChartAt hxs
  have hC_I_eq : ⇑C_I = e ∘ extChartAt I x := by ext y; simp [C_I, extChartAt]
  have hC_J_eq : ⇑C_J = e' ∘ extChartAt J (Φ x) := by ext y; simp [C_J, extChartAt]
  have hC_I_src : (extChartAt I x).source = C_I.source := by simp [C_I]
  have hC_J_src : (extChartAt J (Φ x)).source = C_J.source := by simp [C_J]
  have hopen_S : (((e ∘ extChartAt I x) '' (s ∩ (extChartAt I x).source)) ∩ Ψ.source).Nonempty :=
    ⟨C_I x, ⟨x, ⟨hxs, mem_extChartAt_source x⟩, by rw [← hC_I_eq]⟩, hxΨ⟩
  have himg := hS_I.image_openPartialHomeomorph hΨ hΨ_symm hopen_S
  have htarget_sub : Ψ.target ⊆ e' '' (extChartAt J (Φ x)).target := by
    intro w hw
    have hwCJ : w ∈ C_J.target := hw.1.1
    have hyCJ : C_J.symm w ∈ C_J.source := C_J.map_target hwCJ
    refine ⟨extChartAt J (Φ x) (C_J.symm w), ?_, ?_⟩
    · exact (extChartAt J (Φ x)).map_source (by simpa [C_J, extChartAt] using hyCJ)
    · simpa [hC_J_eq] using C_J.right_inv hwCJ
  refine ⟨Ψ.target, Ψ.open_target, ?_, htarget_sub, ?_⟩
  · have h1 : Ψ (C_I x) ∈ Ψ.target := Ψ.map_source hxΨ
    simpa [Ψ, C_I.left_inv hxCI, hC_J_eq] using h1
  · have heq : Ψ '' (((e ∘ extChartAt I x) '' (s ∩ (extChartAt I x).source)) ∩ Ψ.source) =
        Ψ.target ∩ (e' ∘ extChartAt J (Φ x)) ''
          ((Φ '' (s ∩ Φ.source)) ∩ (extChartAt J (Φ x)).source) := by
      rw [← hC_I_eq, ← hC_J_eq, hC_I_src, hC_J_src, inter_comm _ Ψ.source, inter_comm s,
        C_I.image_symm_trans_source_inter (Φ.trans C_J) s, Φ.image_trans_source_inter C_J s,
        inter_comm C_J.source, inter_comm Φ.source]
    rwa [heq] at himg

end OpenPartialHomeomorph

namespace Diffeomorph

open TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' H'}
  [I.Boundaryless] [J.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ω N]
  {n m d : ℕ}

/-- An analytic diffeomorphism `Φ : M ≃ₘ^ω⟮I, J⟯ N` maps a `d`-dimensional analytic submanifold of
`M` to a `d`-dimensional analytic submanifold of `N`. -/
theorem isMAnalyticSubmanifold_image (Φ : M ≃ₘ^ω⟮I, J⟯ N)
    {e : E ≃L[𝕜] Fin n → 𝕜} {e' : E' ≃L[𝕜] Fin m → 𝕜} {s : Set M}
    (hs : IsMAnalyticSubmanifold I e d s) :
    IsMAnalyticSubmanifold J e' d (Φ '' s) := by
  simpa using Φ.toHomeomorph.toOpenPartialHomeomorph.isMAnalyticSubmanifold_image
    Φ.contMDiff.contMDiffOn Φ.symm.contMDiff.contMDiffOn hs (by simpa using hs.nonempty)

/-- Pulling back a `d`-dimensional analytic submanifold along an analytic diffeomorphism gives a
`d`-dimensional analytic submanifold. -/
theorem isMAnalyticSubmanifold_preimage (Φ : M ≃ₘ^ω⟮I, J⟯ N)
    {e : E ≃L[𝕜] Fin n → 𝕜} {e' : E' ≃L[𝕜] Fin m → 𝕜} {t : Set N}
    (ht : IsMAnalyticSubmanifold J e' d t) :
    IsMAnalyticSubmanifold I e d (Φ ⁻¹' t) := by
  rw [← Φ.symm_image_eq_preimage]
  exact Φ.symm.isMAnalyticSubmanifold_image ht

/-- An analytic diffeomorphism preserves `IsMAnalyticSubmanifold` on images. -/
theorem isMAnalyticSubmanifold_image_iff (Φ : M ≃ₘ^ω⟮I, J⟯ N)
    (e : E ≃L[𝕜] Fin n → 𝕜) {e' : E' ≃L[𝕜] Fin m → 𝕜} {s : Set M} :
    IsMAnalyticSubmanifold J e' d (Φ '' s) ↔ IsMAnalyticSubmanifold I e d s := by
  refine ⟨fun h ↦ ?_, Φ.isMAnalyticSubmanifold_image⟩
  simpa only [Φ.symm_image_image] using Φ.symm.isMAnalyticSubmanifold_image h

/-- An analytic diffeomorphism preserves `IsMAnalyticSubmanifold` on preimages. -/
theorem isMAnalyticSubmanifold_preimage_iff (Φ : M ≃ₘ^ω⟮I, J⟯ N)
    {e : E ≃L[𝕜] Fin n → 𝕜} (e' : E' ≃L[𝕜] Fin m → 𝕜) {t : Set N} :
    IsMAnalyticSubmanifold I e d (Φ ⁻¹' t) ↔ IsMAnalyticSubmanifold J e' d t := by
  rw [← Φ.symm_image_eq_preimage, Φ.symm.isMAnalyticSubmanifold_image_iff e']

end Diffeomorph

/-! ### Induced `C^ω` manifold structure and smooth embeddings -/

namespace TauCeti

section InducedManifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  {n d : ℕ} {s : Set M}

/-- Private linear-slice chart package induced by `IsMAnalyticSubmanifold I e d s`. -/
private theorem IsMAnalyticSubmanifold.exists_linearSliceCharts {e : E ≃L[𝕜] Fin n → 𝕜}
    (hs : IsMAnalyticSubmanifold I e d s) :
    ∃ (c : s → OpenPartialHomeomorph M ((Fin d → 𝕜) × (Fin (n - d) → 𝕜)))
      (_ : ∀ x, IsSliceChart (c x) ((univ : Set (Fin d → 𝕜)) ×ˢ ({0} : Set (Fin (n - d) → 𝕜))) s),
      (∀ x : s, (x : M) ∈ (c x).source) ∧
      (∀ x, ContMDiffOn I 𝓘(𝕜, (Fin d → 𝕜) × (Fin (n - d) → 𝕜)) ω (c x) (c x).source) ∧
      (∀ x, ContMDiffOn 𝓘(𝕜, (Fin d → 𝕜) × (Fin (n - d) → 𝕜)) I ω (c x).symm (c x).target) := by
  classical
  have hd : d ≤ n := hs.le
  have hchart : ∀ x : s, ∃ φ : OpenPartialHomeomorph (Fin n → 𝕜) (Fin n → 𝕜),
      ((chartAt H (x : M)).extendTrans I e.toHomeomorph) x ∈ φ.source ∧
      IsAnalyticChart d
        (((chartAt H (x : M)).extendTrans I e.toHomeomorph) ''
          (s ∩ ((chartAt H (x : M)).extendTrans I e.toHomeomorph).source)) φ := by
    intro x
    set C := (chartAt H (x : M)).extendTrans I e.toHomeomorph
    have hC_eq : ⇑C = e ∘ extChartAt I (x : M) := by ext y; simp [C, extChartAt]
    have hS : IsAnalyticSubmanifold d (C '' (s ∩ C.source)) := by
      simpa [hC_eq, C, extChartAt] using hs.image_extChartAt x.2
    exact hS.exists_isAnalyticChart (C x) ⟨x, ⟨x.2, by simp [C]⟩, rfl⟩
  choose φ hφx hφ using hchart
  let A := splitAt (𝕜 := 𝕜) (M := 𝕜) hd
  let c (x : s) : OpenPartialHomeomorph M ((Fin d → 𝕜) × (Fin (n - d) → 𝕜)) :=
    (((chartAt H (x : M)).extendTrans I e.toHomeomorph).trans (φ x)).transHomeomorph A.toHomeomorph
  have hc (x : s) :
      IsSliceChart (c x) ((univ : Set (Fin d → 𝕜)) ×ˢ ({0} : Set (Fin (n - d) → 𝕜))) s := by
    refine isSliceChart_iff.2 fun z hz ↦ ?_
    set C := (chartAt H (x : M)).extendTrans I e.toHomeomorph
    have hzC : z ∈ C.source := hz.1
    have hzφ : C z ∈ (φ x).source := hz.2
    have hmem_img : C z ∈ C '' (s ∩ C.source) ↔ z ∈ s := by
      refine ⟨?_, fun hzs ↦ ⟨z, ⟨hzs, hzC⟩, rfl⟩⟩
      rintro ⟨y, ⟨hys, hyC⟩, hyz⟩
      rwa [← C.injOn hyC hzC hyz]
    rw [← hmem_img, (hφ x).mem_iff hzφ]
    simp [c, C, A, splitAt_snd_eq_zero_iff]
  have hcover (x : s) : (x : M) ∈ (c x).source := ⟨by simp, hφx x⟩
  have hcs (x : s) : ContMDiffOn I 𝓘(𝕜, (Fin d → 𝕜) × (Fin (n - d) → 𝕜)) ω (c x) (c x).source := by
    have hφ_cd : ContMDiffOn 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω (φ x) (φ x).source := by
      rw [contMDiffOn_iff_contDiffOn]
      exact (contDiffOn_omega_iff_analyticOn (φ x).open_source.uniqueDiffOn).2
        ((φ x).open_source.analyticOn_iff_analyticOnNhd.2 (hφ x).analyticOnNhd)
    have hsub : (c x).source ⊆ ((chartAt H (x : M)).extendTrans I e.toHomeomorph).source :=
      fun _ hz ↦ hz.1
    have hstep : ContMDiffOn I 𝓘(𝕜, Fin n → 𝕜) ω
        (φ x ∘ (chartAt H (x : M)).extendTrans I e.toHomeomorph) (c x).source :=
      hφ_cd.comp (((chartAt H (x : M)).contMDiffOn_extendTrans
        (chart_mem_maximalAtlas (x : M)) e.contDiff).mono hsub) fun _ hz ↦ hz.2
    exact (A.contDiff.contMDiff.comp_contMDiffOn hstep).congr fun _ _ ↦ rfl
  have hci (x : s) :
      ContMDiffOn 𝓘(𝕜, (Fin d → 𝕜) × (Fin (n - d) → 𝕜)) I ω (c x).symm (c x).target := by
    have hφ_symm : ContMDiffOn 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω (φ x).symm (φ x).target := by
      rw [contMDiffOn_iff_contDiffOn]
      exact (contDiffOn_omega_iff_analyticOn (φ x).open_target.uniqueDiffOn).2
        ((φ x).open_target.analyticOn_iff_analyticOnNhd.2 (hφ x).analyticOnNhd_symm)
    have hstep : ContMDiffOn 𝓘(𝕜, (Fin d → 𝕜) × (Fin (n - d) → 𝕜)) 𝓘(𝕜, Fin n → 𝕜) ω
        ((φ x).symm ∘ A.symm) (c x).target :=
      hφ_symm.comp A.symm.contDiff.contMDiff.contMDiffOn (s := (c x).target)
        fun v hv ↦ by simpa [c] using hv.1
    exact (((chartAt H (x : M)).contMDiffOn_extendTrans_symm
      (chart_mem_maximalAtlas (x : M)) e.symm.contDiff).comp hstep
      fun v hv ↦ by simpa [c] using hv.2).congr fun _ _ ↦ rfl
  exact ⟨c, hc, hcover, hcs, hci⟩

/-- Every `d`-dimensional analytic submanifold `s` of a boundaryless `C^ω` manifold `M` admits a
charted-space structure modelled on `Fin d → 𝕜` making `s` a `C^ω` manifold with `C^ω` inclusion
`Subtype.val : s → M`. -/
theorem IsMAnalyticSubmanifold.exists_isManifold {e : E ≃L[𝕜] Fin n → 𝕜}
    (hs : IsMAnalyticSubmanifold I e d s) :
    ∃ C : ChartedSpace (Fin d → 𝕜) s, letI := C
      IsManifold 𝓘(𝕜, Fin d → 𝕜) ω s ∧ ContMDiff 𝓘(𝕜, Fin d → 𝕜) I ω (Subtype.val : s → M) := by
  obtain ⟨c, hc, hcover, hcs, hci⟩ := hs.exists_linearSliceCharts
  exact ⟨linearSliceChartedSpace c hc hcover,
    isManifold_linearSliceChartedSpace c hc
      (fun x z hz ↦ (hcs x).contMDiffAt ((c x).open_source.mem_nhds hz))
      (fun x z hz ↦ (hci x).contMDiffAt ((c x).open_target.mem_nhds hz)) hcover,
    contMDiff_subtypeVal_linearSliceChartedSpace c hc
      (fun x z hz ↦ (hci x).contMDiffAt ((c x).open_target.mem_nhds hz)) hcover⟩

/-- When the ambient `C^ω` manifold `M` is modelled on `𝓘(𝕜, E)`, every `d`-dimensional analytic
submanifold `s ⊆ M` admits a `C^ω` manifold structure modelled on `Fin d → 𝕜` for which
`Subtype.val : s → M` is a `C^ω` smooth embedding (`Manifold.IsSmoothEmbedding`). -/
theorem IsMAnalyticSubmanifold.exists_isSmoothEmbedding
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(𝕜, E) ω M]
    {s : Set M} {e : E ≃L[𝕜] Fin n → 𝕜} (hs : IsMAnalyticSubmanifold 𝓘(𝕜, E) e d s) :
    ∃ C : ChartedSpace (Fin d → 𝕜) s, letI := C
      IsManifold 𝓘(𝕜, Fin d → 𝕜) ω s ∧
        Manifold.IsSmoothEmbedding 𝓘(𝕜, Fin d → 𝕜) 𝓘(𝕜, E) ω (Subtype.val : s → M) := by
  obtain ⟨c, hc, hcover, hcs, hci⟩ := hs.exists_linearSliceCharts
  let A : s → ((Fin d → 𝕜) × (Fin (n - d) → 𝕜)) ≃L[𝕜] E :=
    fun _ ↦ (splitAt (𝕜 := 𝕜) (M := 𝕜) hs.le).symm.trans e.symm
  exact ⟨linearSliceChartedSpace c hc hcover,
    isManifold_linearSliceChartedSpace c hc
      (fun x z hz ↦ (hcs x).contMDiffAt ((c x).open_source.mem_nhds hz))
      (fun x z hz ↦ (hci x).contMDiffAt ((c x).open_target.mem_nhds hz)) hcover,
    isSmoothEmbedding_subtypeVal_linearSliceChartedSpace c hc A hcs hci hcover⟩

end InducedManifold

section SmoothEmbeddingImage

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' H'}
  [I.Boundaryless] [J.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ω N]
  {n m k : ℕ}

/-- Over a complete field `𝕜`, a `C^ω` smooth embedding `f : M → N` maps any `k`-dimensional
analytic submanifold of `M` to a `k`-dimensional analytic submanifold of `N`. -/
theorem IsMAnalyticSubmanifold.image_of_isSmoothEmbedding
    {e : E ≃L[𝕜] Fin m → 𝕜} {e' : E' ≃L[𝕜] Fin n → 𝕜} {s : Set M} {f : M → N}
    (hs : IsMAnalyticSubmanifold I e k s) (hf : Manifold.IsSmoothEmbedding I J ω f) :
    IsMAnalyticSubmanifold J e' k (f '' s) := by
  rw [isMAnalyticSubmanifold_iff_exists_mem_maximalAtlas]
  refine ⟨hs.nonempty.image f, ?_⟩
  rintro _ ⟨x, hxs, rfl⟩
  let h := hf.isImmersion.isImmersionOfComplement_complement x
  let φ := h.domChart
  let ψ := h.codChart
  have hxφ : x ∈ φ.source := h.mem_domChart_source
  have hfxψ : f x ∈ ψ.source := h.mem_codChart_source
  have hS₀ : IsAnalyticSubmanifold k ((e ∘ φ.extend I) '' (s ∩ φ.source)) :=
    hs.image_extend_of_mem_maximalAtlas h.domChart_mem_maximalAtlas ⟨x, hxs, hxφ⟩
  obtain ⟨W, hW, hfW⟩ := hf.isEmbedding.isInducing.isOpen_iff.1 φ.open_source
  set Ψ := ψ.extendTrans J e'.toHomeomorph
  have hΨ_apply (y : N) : Ψ y = e' (ψ.extend J y) := by simp [Ψ]
  let U := Ψ.target ∩ Ψ.symm ⁻¹' W
  have hU : IsOpen U := Ψ.continuousOn_symm.isOpen_inter_preimage Ψ.open_target hW
  have hfxΨ : f x ∈ Ψ.source := by simpa [Ψ] using hfxψ
  have hfxU : e' (ψ.extend J (f x)) ∈ U := by
    have hfxW : f x ∈ W := by rwa [← mem_preimage, hfW]
    rw [← hΨ_apply]
    exact ⟨Ψ.map_source hfxΨ, by simpa [Ψ.left_inv hfxΨ] using hfxW⟩
  let ι : (Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜) :=
    e'.toContinuousLinearMap.comp
      (h.equiv.toContinuousLinearMap.comp
        ((ContinuousLinearMap.inl 𝕜 E _).comp e.symm.toContinuousLinearMap))
  let π : (Fin n → 𝕜) →L[𝕜] (Fin m → 𝕜) :=
    e.toContinuousLinearMap.comp
      ((ContinuousLinearMap.fst 𝕜 E _).comp
        (h.equiv.symm.toContinuousLinearMap.comp e'.symm.toContinuousLinearMap))
  have hleft : LeftInvOn π ι ((e ∘ φ.extend I) '' (s ∩ φ.source)) := fun u _ ↦ by
    simp [ι, π]
  have hι_nhd : AnalyticOnNhd 𝕜 ι ((e ∘ φ.extend I) '' (s ∩ φ.source)) := fun u _ ↦ ι.analyticAt u
  have hπ_nhd : AnalyticOnNhd 𝕜 π univ := fun w _ ↦ π.analyticAt w
  have himg_S₀ : IsAnalyticSubmanifold k (ι '' ((e ∘ φ.extend I) '' (s ∩ φ.source))) :=
    hS₀.image_of_leftInvOn (hι_nhd.analyticOnSubmanifold hS₀)
      (hπ_nhd.analyticOnSubmanifold (isOpen_univ.isAnalyticSubmanifold univ_nonempty))
      (mapsTo_univ _ _) hleft
  have hform : ∀ z ∈ φ.source, e' (ψ.extend J (f z)) = ι (e (φ.extend I z)) := by
    intro z hzφ
    have hze : z ∈ (φ.extend I).source := by simpa [OpenPartialHomeomorph.extend_source] using hzφ
    have hzt : φ.extend I z ∈ (φ.extend I).target := (φ.extend I).map_source hze
    have hwr : ψ.extend J (f ((φ.extend I).symm (φ.extend I z))) = h.equiv (φ.extend I z, 0) :=
      h.writtenInCharts hzt
    rw [(φ.extend I).left_inv hze] at hwr
    simp only [ι, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearMap.inl_apply, ContinuousLinearEquiv.symm_apply_apply, hwr]
  refine ⟨ψ, h.codChart_mem_maximalAtlas, hfxψ, U, hU, hfxU, ?_⟩
  have heq : ι '' ((e ∘ φ.extend I) '' (s ∩ φ.source)) =
      U ∩ (e' ∘ ψ.extend J) '' ((f '' s) ∩ ψ.source) := by
    ext w
    constructor
    · rintro ⟨_, ⟨z, ⟨hzs, hzφ⟩, rfl⟩, rfl⟩
      have hfzψ : f z ∈ ψ.source := h.source_subset_preimage_source hzφ
      have hfzΨ : f z ∈ Ψ.source := by simpa [Ψ] using hfzψ
      have hfzW : f z ∈ W := by rwa [← mem_preimage, hfW]
      have hw_eq : ι ((e ∘ φ.extend I) z) = (e' ∘ ψ.extend J) (f z) := (hform z hzφ).symm
      rw [hw_eq]
      refine ⟨?_, f z, ⟨⟨z, hzs, rfl⟩, hfzψ⟩, rfl⟩
      simp only [Function.comp_apply, ← hΨ_apply]
      exact ⟨Ψ.map_source hfzΨ, by simpa [Ψ.left_inv hfzΨ] using hfzW⟩
    · rintro ⟨hwU, _, ⟨⟨z, hzs, rfl⟩, hfzψ⟩, rfl⟩
      have hfzΨ : f z ∈ Ψ.source := by simpa [Ψ] using hfzψ
      have hwW : Ψ.symm (Ψ (f z)) ∈ W := by
        simpa [hΨ_apply] using hwU.2
      rw [Ψ.left_inv hfzΨ] at hwW
      have hzφ : z ∈ φ.source := by rwa [← hfW]
      exact ⟨(e ∘ φ.extend I) z, ⟨z, ⟨hzs, hzφ⟩, rfl⟩, (hform z hzφ).symm⟩
  rwa [heq] at himg_S₀

/-- Over a complete field `𝕜`, the range of a `C^ω` smooth embedding of a nonempty boundaryless
`C^ω` manifold with `d`-dimensional model into a boundaryless `C^ω` manifold is a `d`-dimensional
analytic submanifold. -/
theorem _root_.Manifold.IsSmoothEmbedding.isMAnalyticSubmanifold_range [Nonempty M]
    {d : ℕ} (e : E ≃L[𝕜] Fin d → 𝕜) (e' : E' ≃L[𝕜] Fin n → 𝕜) {f : M → N}
    (hf : Manifold.IsSmoothEmbedding I J ω f) :
    IsMAnalyticSubmanifold J e' d (range f) := by
  rw [← image_univ]
  exact (isMAnalyticSubmanifold_univ e).image_of_isSmoothEmbedding hf

end SmoothEmbeddingImage

end TauCeti
