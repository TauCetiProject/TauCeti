/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.Submanifold.Immersion
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import TauCeti.Topology.LocallyClosed

/-!
# Dimension comparison for analytic submanifolds

An immersion taking values locally in a `d`-dimensional analytic submanifold has source
dimension at most `d`. Applying this to chart parametrizations shows that local inclusion of
analytic submanifolds implies the corresponding dimension inequality. In particular, the
dimension of a nonempty analytic submanifold is unique, and depends only on its germ at any
of its points.

A lower-dimensional analytic submanifold has empty interior relative to a higher-dimensional
one. Since analytic submanifolds are locally closed, a finite family of them covering a
`d`-dimensional analytic submanifold must contain one of dimension at least `d`. Consequently,
two finite analytic-submanifold decompositions of the same set have the same maximum dimension,
with maximum `⊥` for an empty family. Disjointness and frontier conditions are not needed.
This comparison makes dimension independent of the chosen finite local decomposition.
No claim about the dimension of closures or frontiers is made here.

## References

* S. G. Krantz and H. R. Parks, *A Primer of Real Analytic Functions*, second edition,
  Birkhäuser, 2002, Chapter 2 (real analytic submanifolds).
-/

public section

open Set Filter Topology

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {n d e : ℕ} {S T : Set (Fin n → 𝕜)} {x : Fin n → 𝕜}

/-- An immersion whose image lies locally in an analytic chart of dimension `d` has source
dimension at most `d`. Only differentiability of the immersion at the point is required. -/
theorem IsAnalyticChart.finrank_le_of_injective_fderiv
    {c : OpenPartialHomeomorph (Fin n → 𝕜) (Fin n → 𝕜)}
    (hc : IsAnalyticChart d T c) {φ : E → Fin n → 𝕜} {u : E}
    (hφ : DifferentiableAt 𝕜 φ u) (hinj : Function.Injective (fderiv 𝕜 φ u))
    (hu : φ u ∈ c.source) (hT : ∀ᶠ v in 𝓝 u, φ v ∈ T) : Module.finrank 𝕜 E ≤ d := by
  let q := fun v ↦ firstCoords 𝕜 n d (c (φ v))
  let ψ := fun w ↦ c.symm (firstCoords 𝕜 d n w)
  have hq : DifferentiableAt 𝕜 q u :=
    (firstCoords 𝕜 n d).differentiableAt.comp u
      ((hc.analyticOnNhd _ hu).differentiableAt.comp u hφ)
  have hψ : DifferentiableAt 𝕜 ψ (q u) :=
    (hc.analyticAt_symm_firstCoords hu hT.self_of_nhds).differentiableAt
  have hcomp : ψ ∘ q =ᶠ[𝓝 u] φ := by
    filter_upwards [hT, hφ.continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hu)] with v hv hv'
    exact hc.symm_firstCoords_firstCoords_apply hv' hv
  have hD : (fderiv 𝕜 ψ (q u)).comp (fderiv 𝕜 q u) = fderiv 𝕜 φ u := by
    rw [← fderiv_comp u hψ hq]
    exact hcomp.fderiv_eq
  have hi : Function.Injective (fderiv 𝕜 q u) := by
    intro v w hvw
    apply hinj
    simpa only [← ContinuousLinearMap.comp_apply, hD] using
      congrArg (fderiv 𝕜 ψ (q u)) hvw
  simpa using LinearMap.finrank_le_finrank_of_injective
    (f := (fderiv 𝕜 q u).toLinearMap) hi

/-- Local inclusion at a point of an analytic submanifold implies a dimension inequality.
The inclusion is only required within the smaller submanifold near that point. -/
theorem IsAnalyticSubmanifold.dim_le_of_eventually_mem (hS : IsAnalyticSubmanifold d S)
    (hT : IsAnalyticSubmanifold e T) (hx : x ∈ S)
    (hST : ∀ᶠ y in 𝓝[S] x, y ∈ T) : d ≤ e := by
  obtain ⟨c, hxc, hc⟩ := hS.exists_isAnalyticChart x hx
  let u := firstCoords 𝕜 n d (c x)
  let φ := fun v ↦ c.symm (firstCoords 𝕜 d n v)
  have hφ₀ : φ u = x := hc.symm_firstCoords_firstCoords_apply hxc hx
  have hφ : AnalyticAt 𝕜 φ u := hc.analyticAt_symm_firstCoords hxc hx
  have hφS : ∀ᶠ v in 𝓝 u, φ v ∈ S :=
    (hc.eventually_symm_firstCoords_mem hxc hx).mono fun _ hv ↦ hv.2
  have htend : Tendsto φ (𝓝 u) (𝓝[S] x) :=
    tendsto_nhdsWithin_iff.2 ⟨hφ₀ ▸ hφ.continuousAt.tendsto, hφS⟩
  have hxT : x ∈ T := mem_of_mem_nhdsWithin hx hST
  obtain ⟨c', hxc', hc'⟩ := hT.exists_isAnalyticChart x hxT
  simpa using hc'.finrank_le_of_injective_fderiv hφ.differentiableAt
    (hc.injective_fderiv_symm_firstCoords hxc hx hS.le) (by rw [hφ₀]; exact hxc')
    (htend.eventually hST)

/-- Inclusion of nonempty analytic submanifolds implies a dimension inequality. -/
theorem IsAnalyticSubmanifold.dim_le_of_subset (hS : IsAnalyticSubmanifold d S)
    (hT : IsAnalyticSubmanifold e T) (hST : S ⊆ T) : d ≤ e := by
  obtain ⟨x, hx⟩ := hS.nonempty
  apply hS.dim_le_of_eventually_mem hT hx
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact hST hy

/-- The dimension of a nonempty analytic submanifold is unique. -/
theorem IsAnalyticSubmanifold.dim_eq (hS : IsAnalyticSubmanifold d S)
    (hS' : IsAnalyticSubmanifold e S) : d = e :=
  le_antisymm (hS.dim_le_of_subset hS' subset_rfl) (hS'.dim_le_of_subset hS subset_rfl)

/-- Analytic submanifolds with the same germ at a point of either one have equal dimensions. -/
theorem IsAnalyticSubmanifold.dim_eq_of_eventuallyEq (hS : IsAnalyticSubmanifold d S)
    (hT : IsAnalyticSubmanifold e T) (hx : x ∈ S) (hST : S =ᶠ[𝓝 x] T) : d = e := by
  have heq := eventuallyEqSet_iff.1 hST
  have hxT : x ∈ T := (heq.self_of_nhds).1 hx
  exact le_antisymm
    (hS.dim_le_of_eventually_mem hT hx (by
      filter_upwards [heq.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with y hy hyS
      exact hy.1 hyS))
    (hT.dim_le_of_eventually_mem hS hxT (by
      filter_upwards [heq.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with y hy hyT
      exact hy.2 hyT))

/-- If an analytic submanifold contains a nonempty relatively open part of another analytic
submanifold, its dimension is at least that of the latter. Global inclusion is not required. -/
theorem IsAnalyticSubmanifold.dim_le_of_nonempty_interior_preimage_val
    (hS : IsAnalyticSubmanifold d S) (hT : IsAnalyticSubmanifold e T)
    (hne : (interior (Subtype.val ⁻¹' S : Set T)).Nonempty) : e ≤ d := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨U, hU, hUT⟩ := isOpen_induced_iff.1
    (isOpen_interior : IsOpen (interior (Subtype.val ⁻¹' S : Set T)))
  have hxU : x.val ∈ U := (Set.ext_iff.1 hUT x).2 hx
  have hTS : T ∩ U ⊆ S := by
    rintro y ⟨hyT, hyU⟩
    exact (interior_subset (s := (Subtype.val ⁻¹' S : Set T)))
      ((Set.ext_iff.1 hUT ⟨y, hyT⟩).1 hyU)
  exact (hT.inter hU ⟨x.val, x.property, hxU⟩).dim_le_of_subset hS hTS

/-- A lower-dimensional analytic submanifold has empty interior relative to any
higher-dimensional analytic submanifold, whether or not the sets are globally nested. -/
theorem IsAnalyticSubmanifold.interior_preimage_val_eq_empty_of_dim_lt
    (hS : IsAnalyticSubmanifold d S) (hT : IsAnalyticSubmanifold e T) (hde : d < e) :
    interior (Subtype.val ⁻¹' S : Set T) = ∅ := by
  by_contra hne
  exact (not_le_of_gt hde)
    (hS.dim_le_of_nonempty_interior_preimage_val hT (Set.nonempty_iff_ne_empty.2 hne))

/-- A finite family of analytic submanifolds covering a nonempty analytic submanifold contains
one whose dimension is at least that of the covered submanifold. No disjointness or frontier
condition on the cover is required. -/
theorem IsAnalyticSubmanifold.exists_dim_le_of_subset_iUnion
    {ι : Type*} [Finite ι] {T : ι → Set (Fin n → 𝕜)} {e : ι → ℕ}
    (hS : IsAnalyticSubmanifold d S) (hT : ∀ i, IsAnalyticSubmanifold (e i) (T i))
    (hcover : S ⊆ ⋃ i, T i) : ∃ i, d ≤ e i := by
  have : Nonempty S := hS.nonempty.to_subtype
  have hU : ⋃ i, (Subtype.val ⁻¹' T i : Set S) = univ := by
    ext x
    simpa only [mem_iUnion, mem_preimage, mem_univ, iff_true] using hcover x.property
  obtain ⟨i, hi⟩ := nonempty_interior_of_iUnion_of_isLocallyClosed
    (fun i ↦ (hT i).isLocallyClosed.preimage continuous_subtype_val) hU
  exact ⟨i, (hT i).dim_le_of_nonempty_interior_preimage_val hS hi⟩

/-- Inclusion between two finite unions of analytic submanifolds implies the corresponding
inequality between their maximum dimensions, with `⊥` for an empty family. -/
theorem sup_dim_le_of_iUnion_subset {ι κ : Type*} [Fintype ι] [Fintype κ]
    {S : ι → Set (Fin n → 𝕜)} {T : κ → Set (Fin n → 𝕜)} {d : ι → ℕ} {e : κ → ℕ}
    (hS : ∀ i, IsAnalyticSubmanifold (d i) (S i))
    (hT : ∀ j, IsAnalyticSubmanifold (e j) (T j)) (hcover : ⋃ i, S i ⊆ ⋃ j, T j) :
    Finset.univ.sup (fun i ↦ (d i : WithBot ℕ)) ≤
      Finset.univ.sup (fun j ↦ (e j : WithBot ℕ)) := by
  refine Finset.sup_le fun i _ ↦ ?_
  obtain ⟨j, hj⟩ := (hS i).exists_dim_le_of_subset_iUnion hT
    ((subset_iUnion S i).trans hcover)
  exact (WithBot.coe_le_coe.2 hj).trans (Finset.le_sup (f := fun j ↦ (e j : WithBot ℕ))
    (Finset.mem_univ j))

/-- Two finite covers of the same set by analytic submanifolds have the same maximum dimension.
The maximum is taken in `WithBot ℕ`, so an empty cover has dimension `⊥`, including when the
ambient space has dimension zero. The covers need not be partitions. -/
theorem sup_dim_eq_of_iUnion_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    {S : ι → Set (Fin n → 𝕜)} {T : κ → Set (Fin n → 𝕜)} {d : ι → ℕ} {e : κ → ℕ}
    (hS : ∀ i, IsAnalyticSubmanifold (d i) (S i))
    (hT : ∀ j, IsAnalyticSubmanifold (e j) (T j)) (hcover : ⋃ i, S i = ⋃ j, T j) :
    Finset.univ.sup (fun i ↦ (d i : WithBot ℕ)) =
      Finset.univ.sup (fun j ↦ (e j : WithBot ℕ)) :=
  le_antisymm (sup_dim_le_of_iUnion_subset hS hT hcover.subset)
    (sup_dim_le_of_iUnion_subset hT hS hcover.symm.subset)

end TauCeti
