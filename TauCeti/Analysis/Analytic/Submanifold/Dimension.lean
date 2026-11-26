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
# Dimension of analytic submanifolds and analytic dimension of sets

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

The analytic dimension `TauCeti.analyticDim s` of an arbitrary subset `s` of `𝕜ⁿ` is the supremum
of the dimensions of the analytic submanifolds contained in `s`, with `⊥` for the empty set, and
its local analytic dimension `TauCeti.analyticDimAt s x` at `x` is the smallest analytic
dimension of a trace of `s` on a neighbourhood of `x`. The analytic dimension of a finite union of
analytic submanifolds is the largest of their dimensions (`TauCeti.analyticDim_sUnion`), the
analytic dimension is the supremum of the local ones (`TauCeti.iSup_analyticDimAt`), and the local
analytic dimension at `x` is the largest dimension of the pieces of any finite cover of `s` near
`x` by analytic submanifolds contained in `s` that have `x` in their closures
(`TauCeti.analyticDimAt_eq_iSup_of_subset_iUnion`). No claim about the dimension of closures or
frontiers is made here; for semianalytic sets these follow from the frontier condition of the
local normal decomposition.

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
    (hS.dim_le_of_nonempty_interior_preimage_val hT (Set.ne_empty_iff_nonempty.1 hne))

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
    (fun i ↦ (hT i).isLocallyClosed.preimage continuous_subtypeVal) hU
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

/-! ### The analytic dimension of a set -/

section AnalyticDim

variable {s t U : Set (Fin n → 𝕜)}

/-- The **analytic dimension** of a subset `s` of `𝕜ⁿ`: the supremum of the dimensions of the
analytic submanifolds contained in `s`. The empty set has dimension `⊥`, and every other set has a
natural number dimension at most `n` (`TauCeti.analyticDim_le`,
`TauCeti.exists_isAnalyticSubmanifold_analyticDim_eq`). A finite union of analytic submanifolds
has the largest of their dimensions (`TauCeti.analyticDim_sUnion`), so for a set decomposed into
finitely many analytic submanifolds this is the largest dimension of a piece, whichever
decomposition is used. -/
noncomputable def analyticDim (s : Set (Fin n → 𝕜)) : WithBot ℕ∞ :=
  ⨆ (S : Set (Fin n → 𝕜)) (_ : S ⊆ s) (d : ℕ) (_ : IsAnalyticSubmanifold d S), (d : WithBot ℕ∞)

/-- An upper bound for the analytic dimension is a bound on the dimensions of the analytic
submanifolds contained in the set. -/
theorem analyticDim_le_iff {k : WithBot ℕ∞} :
    analyticDim s ≤ k ↔ ∀ S ⊆ s, ∀ d, IsAnalyticSubmanifold d S → (d : WithBot ℕ∞) ≤ k := by
  simp only [analyticDim, iSup_le_iff]

/-- A set containing a `d`-dimensional analytic submanifold has analytic dimension at least
`d`. -/
theorem IsAnalyticSubmanifold.le_analyticDim (hS : IsAnalyticSubmanifold d S) (hSs : S ⊆ s) :
    (d : WithBot ℕ∞) ≤ analyticDim s :=
  le_iSup₂_of_le S hSs <| le_iSup₂_of_le d hS le_rfl

/-- The analytic dimension is monotone. -/
@[gcongr]
theorem analyticDim_mono (h : s ⊆ t) : analyticDim s ≤ analyticDim t :=
  analyticDim_le_iff.2 fun _ hS _ hd ↦ hd.le_analyticDim (hS.trans h)

/-- A subset of `𝕜ⁿ` has analytic dimension at most `n`. -/
theorem analyticDim_le (s : Set (Fin n → 𝕜)) : analyticDim s ≤ n :=
  analyticDim_le_iff.2 fun _ _ _ hd ↦ by exact_mod_cast hd.le

/-- The analytic dimension of a set is `⊥` exactly when the set is empty: a point is a
zero-dimensional analytic submanifold. -/
@[simp]
theorem analyticDim_eq_bot_iff : analyticDim s = ⊥ ↔ s = ∅ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · by_contra hs
    obtain ⟨x, hx⟩ := ne_empty_iff_nonempty.1 hs
    have h0 := (isAnalyticSubmanifold_singleton x).le_analyticDim (singleton_subset_iff.2 hx)
    simp [h] at h0
  · subst h
    exact le_bot_iff.1 <| analyticDim_le_iff.2 fun _ hS _ hd ↦
      absurd (subset_empty_iff.1 hS) hd.nonempty.ne_empty

/-- The empty set has analytic dimension `⊥`. -/
@[simp]
theorem analyticDim_empty : analyticDim (∅ : Set (Fin n → 𝕜)) = ⊥ :=
  analyticDim_eq_bot_iff.2 rfl

/-- A `d`-dimensional analytic submanifold has analytic dimension `d`. -/
theorem IsAnalyticSubmanifold.analyticDim_eq (hS : IsAnalyticSubmanifold d S) :
    analyticDim S = d :=
  le_antisymm (analyticDim_le_iff.2 fun _ hT _ hd ↦ by exact_mod_cast hd.dim_le_of_subset hS hT)
    (hS.le_analyticDim subset_rfl)

/-- The analytic dimension of a nonempty set is a natural number, attained by an analytic
submanifold contained in it. -/
theorem exists_isAnalyticSubmanifold_analyticDim_eq (hs : s.Nonempty) :
    ∃ S ⊆ s, ∃ d : ℕ, analyticDim s = d ∧ IsAnalyticSubmanifold d S := by
  classical
  -- The dimensions of the analytic submanifolds of `s` are bounded by `n`, so one is largest.
  let P : ℕ → Prop := fun d ↦ ∃ S ⊆ s, IsAnalyticSubmanifold d S
  obtain ⟨x, hx⟩ := hs
  have hP : P (Nat.findGreatest P n) :=
    Nat.findGreatest_spec (m := 0) (Nat.zero_le n) ⟨{x}, singleton_subset_iff.2 hx,
      isAnalyticSubmanifold_singleton x⟩
  obtain ⟨S, hSs, hS⟩ := hP
  refine ⟨S, hSs, _, le_antisymm (analyticDim_le_iff.2 fun T hTs e he ↦ ?_)
    (hS.le_analyticDim hSs), hS⟩
  exact_mod_cast Nat.le_findGreatest he.le (show P e from ⟨T, hTs, he⟩)

/-- If a `d`-dimensional analytic submanifold is covered by finitely many analytic submanifolds,
one of them has analytic dimension at least `d`. No disjointness or frontier condition on the
cover is required. -/
theorem IsAnalyticSubmanifold.exists_le_analyticDim_of_subset_sUnion
    {𝒞 : Set (Set (Fin n → 𝕜))} (hS : IsAnalyticSubmanifold d S) (h𝒞 : 𝒞.Finite)
    (hC : ∀ C ∈ 𝒞, ∃ e, IsAnalyticSubmanifold e C) (hS𝒞 : S ⊆ ⋃₀ 𝒞) :
    ∃ C ∈ 𝒞, (d : WithBot ℕ∞) ≤ analyticDim C := by
  have := h𝒞.to_subtype
  choose e he using fun C : 𝒞 ↦ hC C C.property
  obtain ⟨C, hCd⟩ := hS.exists_dim_le_of_subset_iUnion he (by rwa [← sUnion_eq_iUnion])
  exact ⟨C, C.property, (he C).analyticDim_eq ▸ by exact_mod_cast hCd⟩

/-- If a `d`-dimensional analytic submanifold `S ⊆ T ∩ ⋃₀ 𝒞` is covered by finitely many analytic
submanifolds, one of them meeting `T` has analytic dimension at least `d`. -/
theorem IsAnalyticSubmanifold.exists_le_analyticDim_of_subset_inter_sUnion
    {𝒞 : Set (Set (Fin n → 𝕜))} (hS : IsAnalyticSubmanifold d S) (h𝒞 : 𝒞.Finite)
    (hC : ∀ C ∈ 𝒞, ∃ e, IsAnalyticSubmanifold e C) (hST : S ⊆ T ∩ ⋃₀ 𝒞) :
    ∃ C ∈ 𝒞, (C ∩ T).Nonempty ∧ (d : WithBot ℕ∞) ≤ analyticDim C := by
  obtain ⟨C, ⟨hC𝒞, hCT⟩, hdC⟩ := hS.exists_le_analyticDim_of_subset_sUnion
    (𝒞 := {C ∈ 𝒞 | (C ∩ T).Nonempty}) (h𝒞.subset (sep_subset _ _))
    (fun C hC' ↦ hC C hC'.1) fun y hy ↦ by
      obtain ⟨C, hC𝒞, hyC⟩ := mem_sUnion.1 (hST hy).2
      exact ⟨C, ⟨hC𝒞, y, hyC, (hST hy).1⟩, hyC⟩
  exact ⟨C, hC𝒞, hCT, hdC⟩

/-- **Dimension of a finite union of analytic submanifolds.** The analytic dimension of the union
of finitely many analytic submanifolds is the largest of their dimensions. Disjointness is not
required. -/
theorem analyticDim_sUnion {𝒞 : Set (Set (Fin n → 𝕜))} (h𝒞 : 𝒞.Finite)
    (hC : ∀ C ∈ 𝒞, ∃ e, IsAnalyticSubmanifold e C) :
    analyticDim (⋃₀ 𝒞) = ⨆ C ∈ 𝒞, analyticDim C := by
  refine le_antisymm (analyticDim_le_iff.2 fun S hS d hd ↦ ?_)
    (iSup₂_le fun C hC ↦ analyticDim_mono (subset_sUnion_of_mem hC))
  obtain ⟨C, hC𝒞, hdC⟩ := hd.exists_le_analyticDim_of_subset_sUnion h𝒞 hC hS
  exact hdC.trans (le_iSup₂_of_le C hC𝒞 le_rfl)

/-- The **local analytic dimension** of `s` at `x`: the smallest analytic dimension of the traces
`s ∩ U` of `s` on neighbourhoods `U` of `x`. It is `⊥` exactly away from the closure of `s`
(`TauCeti.analyticDimAt_eq_bot_iff`), its supremum over all points is `TauCeti.analyticDim s`
(`TauCeti.iSup_analyticDimAt`), and it is the largest dimension of a piece contained in `s` of
any finite decomposition of `s` near `x` into analytic submanifolds having `x` in their closures
(`TauCeti.analyticDimAt_eq_iSup_of_subset_iUnion`). -/
noncomputable def analyticDimAt (s : Set (Fin n → 𝕜)) (x : Fin n → 𝕜) : WithBot ℕ∞ :=
  ⨅ U ∈ 𝓝 x, analyticDim (s ∩ U)

/-- The local analytic dimension at `x` is at most the analytic dimension of the trace of the set
on any neighbourhood of `x`. -/
theorem analyticDimAt_le_analyticDim_inter (hU : U ∈ 𝓝 x) :
    analyticDimAt s x ≤ analyticDim (s ∩ U) :=
  iInf₂_le U hU

/-- A lower bound for the local analytic dimension at `x` is a lower bound for the analytic
dimension of the trace of the set on every neighbourhood of `x`. -/
theorem le_analyticDimAt_iff {k : WithBot ℕ∞} :
    k ≤ analyticDimAt s x ↔ ∀ U ∈ 𝓝 x, k ≤ analyticDim (s ∩ U) := by
  simp only [analyticDimAt, le_iInf_iff]

/-- The local analytic dimension is at most the analytic dimension. -/
theorem analyticDimAt_le_analyticDim : analyticDimAt s x ≤ analyticDim s :=
  (analyticDimAt_le_analyticDim_inter univ_mem).trans (analyticDim_mono inter_subset_left)

/-- The local analytic dimension is monotone in the set. -/
@[gcongr]
theorem analyticDimAt_mono (h : s ⊆ t) : analyticDimAt s x ≤ analyticDimAt t x :=
  iInf₂_mono fun _ _ ↦ analyticDim_mono (inter_subset_inter_left _ h)

/-- The local analytic dimension at `x` is attained on some neighbourhood of `x`, and then on
every smaller neighbourhood. -/
theorem exists_mem_nhds_analyticDim_inter_eq (s : Set (Fin n → 𝕜)) (x : Fin n → 𝕜) :
    ∃ U ∈ 𝓝 x, ∀ V ∈ 𝓝 x, V ⊆ U → analyticDim (s ∩ V) = analyticDimAt s x := by
  -- `WithBot ℕ∞` is well-founded, so the infimum is a minimum.
  have : Nonempty {U // U ∈ 𝓝 x} := ⟨⟨univ, univ_mem⟩⟩
  obtain ⟨⟨U, hU⟩, hUeq⟩ := ciInf_mem fun U : {U // U ∈ 𝓝 x} ↦ analyticDim (s ∩ U)
  have hinf : analyticDimAt s x = ⨅ U : {U // U ∈ 𝓝 x}, analyticDim (s ∩ U) := by
    rw [analyticDimAt, iInf_subtype']
  refine ⟨U, hU, fun V hV hVU ↦ le_antisymm ?_ (analyticDimAt_le_analyticDim_inter hV)⟩
  rw [hinf, ← hUeq]
  exact analyticDim_mono (inter_subset_inter_right _ hVU)

/-- If `x` lies in the closure of a `d`-dimensional analytic submanifold `S ⊆ s`, then the local
analytic dimension of `s` at `x` is at least `d`. -/
theorem IsAnalyticSubmanifold.le_analyticDimAt (hS : IsAnalyticSubmanifold d S) (hSs : S ⊆ s)
    (hx : x ∈ closure S) : (d : WithBot ℕ∞) ≤ analyticDimAt s x := by
  refine le_analyticDimAt_iff.2 fun U hU ↦ ?_
  have hne : (S ∩ interior U).Nonempty :=
    inter_comm (interior U) S ▸ mem_closure_iff_nhds.1 hx _ (interior_mem_nhds.2 hU)
  exact (hS.inter isOpen_interior hne).le_analyticDim
    (inter_subset_inter hSs interior_subset)

/-- The local analytic dimension of `s` at `x` is `⊥` exactly when `x` is not in the closure
of `s`. -/
@[simp]
theorem analyticDimAt_eq_bot_iff : analyticDimAt s x = ⊥ ↔ x ∉ closure s := by
  refine ⟨fun h hx ↦ ?_, fun hx ↦ le_bot_iff.1 ?_⟩
  · -- Near a point of the closure, every trace of `s` contains a point.
    have h0 : ((0 : ℕ) : WithBot ℕ∞) ≤ analyticDimAt s x :=
      le_analyticDimAt_iff.2 fun U hU ↦ by
        obtain ⟨y, hy⟩ := mem_closure_iff_nhds.1 hx U hU
        exact (isAnalyticSubmanifold_singleton y).le_analyticDim
          (singleton_subset_iff.2 ⟨hy.2, hy.1⟩)
    simp [h] at h0
  · refine (analyticDimAt_le_analyticDim_inter (isClosed_closure.isOpen_compl.mem_nhds hx)).trans_eq
      (analyticDim_eq_bot_iff.2 ?_)
    exact subset_empty_iff.1 fun y hy ↦ hy.2 (subset_closure hy.1)

/-- The analytic dimension of a set is the supremum of its local analytic dimensions. -/
theorem iSup_analyticDimAt (s : Set (Fin n → 𝕜)) : ⨆ x, analyticDimAt s x = analyticDim s := by
  refine le_antisymm (iSup_le fun _ ↦ analyticDimAt_le_analyticDim)
    (analyticDim_le_iff.2 fun S hSs d hd ↦ ?_)
  obtain ⟨x, hx⟩ := hd.nonempty
  exact (hd.le_analyticDimAt hSs (subset_closure hx)).trans (le_iSup _ x)

/-- **Independence of the local dimension from the decomposition.** Suppose that, on a
neighbourhood `U` of `x`, the set `s` is covered by finitely many analytic submanifolds `C i`
contained in `s`, each having `x` in its closure. Then the local analytic dimension of `s` at `x`
is the largest dimension of the `C i`; in particular it is the same for every such decomposition.
The pieces need not be disjoint. -/
theorem analyticDimAt_eq_iSup_of_subset_iUnion {ι : Type*} [Finite ι]
    {C : ι → Set (Fin n → 𝕜)} {e : ι → ℕ} (hC : ∀ i, IsAnalyticSubmanifold (e i) (C i))
    (hCs : ∀ i, C i ⊆ s) (hx : ∀ i, x ∈ closure (C i)) (hU : U ∈ 𝓝 x)
    (hsU : s ∩ U ⊆ ⋃ i, C i) : analyticDimAt s x = ⨆ i, (e i : WithBot ℕ∞) := by
  refine le_antisymm ?_ (iSup_le fun i ↦ (hC i).le_analyticDimAt (hCs i) (hx i))
  refine (analyticDimAt_le_analyticDim_inter hU).trans <| (analyticDim_mono hsU).trans <|
    analyticDim_le_iff.2 fun S hS d hd ↦ ?_
  obtain ⟨i, hi⟩ := hd.exists_dim_le_of_subset_iUnion hC hS
  exact (show (d : WithBot ℕ∞) ≤ e i by exact_mod_cast hi).trans (le_iSup_of_le i le_rfl)

end AnalyticDim

end TauCeti
