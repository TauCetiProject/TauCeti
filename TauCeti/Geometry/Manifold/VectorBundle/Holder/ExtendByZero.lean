/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Holder.Atlas

/-!
# Hölder sections supported in one chart

Let `V → M` be a `Cⁿ` real vector bundle with Banach model fibre `F` over a `Cⁿ` manifold without
boundary, let `A` be a finite bundle atlas, and let `L` be a closed subset of the domain of
chart `i`. An element of the Hölder space `C^{k,α}(V)` of `TauCeti.HolderSection A k α` whose
underlying section vanishes off `L` is determined by its chart-`i` component
(`TauCeti.HolderSection.eq_of_component_eq`). Conversely, for `k + 1 ≤ n` and `α ≤ 1`, every
function of `C^{k,α}(A.image i)` vanishing at the points of the chart image outside the image of
`L` is the chart-`i` component of such an element: the section reading as this function in
chart `i` and vanishing off the domain of chart `i` has `C^{k,α}` readings in every chart
(`TauCeti.FiniteBundleAtlas.memHolderSection_of_forall_notMem_eq_zero`).

This **extension by zero** `TauCeti.HolderSection.extendByZeroL` is a continuous linear map from
the closed subspace `TauCeti.HolderSection.chartZeroOff A k α i L` of such functions into
`C^{k,α}(V)`, by the closed graph theorem. So the `C^{k,α}(V)` norm of a section supported in `L`
is controlled by the `C^{k,α}` norm of its reading in chart `i` alone. This localizes questions
about `C^{k,α}(V)` to a single chart, as for the little Hölder space of sections
(`TauCeti.HolderSection.mem_littleHolder_iff_forall_mem_littleHolder_component`).

## Main definitions

* `TauCeti.HolderSection.chartZeroOff A k α i L`: the elements of `C^{k,α}(A.image i)` vanishing
  at the points whose preimage under chart `i` lies outside `L`.
* `TauCeti.HolderSection.extendByZeroL`: the element of `C^{k,α}(V)` vanishing off `L` with given
  chart-`i` component, as a continuous linear map.

## Main results

* `TauCeti.HolderSection.eq_of_component_eq`: elements vanishing off a subset of the domain of
  chart `i` are determined by their chart-`i` components.
* `TauCeti.HolderSection.restrictOnL_mem_chartZeroOff`: restrictions to the chart image of
  functions on `E` supported in a set `K` lie in `chartZeroOff A k α i ((A.chart i).symm '' K)`.
* `TauCeti.HolderSection.toSection_extendByZeroL_eq`: the extension by zero of the chart-`i`
  reading of a section vanishing off the domain of chart `i` is that section.

## References

* M. E. Taylor, *Partial Differential Equations III*, Chapter 13, for Hölder spaces on compact
  manifolds defined through finitely many charts.
-/

public section

noncomputable section

open Bundle Filter Set
open scoped Manifold NNReal Topology

universe u

namespace TauCeti

namespace HolderSection

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
  {A : FiniteBundleAtlas E M F V} {k : ℕ} {α : ℝ≥0} {i : Fin A.n} {L : Set M}

variable (A k α) in
/-- The elements of `C^{k,α}(A.image i)` vanishing at every point of the chart image whose
preimage under chart `i` lies outside `L`. This subspace contains the chart-`i` components of the
elements of `C^{k,α}(V)` vanishing off `L`; for closed `L ⊆ A.dom i`, `α ≤ 1` and `k + 1 ≤ n`,
every element of it is such a component, of its extension by zero `extendByZeroL`. -/
def chartZeroOff (i : Fin A.n) (L : Set M) : Submodule ℝ (CkHolderSpaceOn k α (A.image i) F) where
  carrier := {f | ∀ y : A.image i, (A.chart i).symm y ∉ L → f y = 0}
  add_mem' {f g} hf hg y hy := by
    rw [CkHolderSpaceOn.coe_add, Pi.add_apply, hf y hy, hg y hy, add_zero]
  zero_mem' y _ := by rw [CkHolderSpaceOn.coe_zero, Pi.zero_apply]
  smul_mem' c f hf y hy := by rw [CkHolderSpaceOn.coe_smul, Pi.smul_apply, hf y hy, smul_zero]

@[simp]
theorem mem_chartZeroOff {f : CkHolderSpaceOn k α (A.image i) F} :
    f ∈ chartZeroOff A k α i L ↔ ∀ y : A.image i, (A.chart i).symm y ∉ L → f y = 0 :=
  Iff.rfl

variable (A k α i L) in
/-- The subspace `chartZeroOff A k α i L` is closed, since evaluation at a point of the chart image
is continuous on `C^{k,α}(A.image i)`. -/
theorem isClosed_chartZeroOff :
    IsClosed (chartZeroOff A k α i L : Set (CkHolderSpaceOn k α (A.image i) F)) := by
  have hset : (chartZeroOff A k α i L : Set (CkHolderSpaceOn k α (A.image i) F)) =
      ⋂ y : A.image i, ⋂ (_ : (A.chart i).symm y ∉ L),
        {f : CkHolderSpaceOn k α (A.image i) F | f.extend y = 0} := by
    ext f
    simp only [SetLike.mem_coe, mem_chartZeroOff, mem_iInter, mem_ofPred_eq,
      CkHolderSpaceOn.extend_apply]
  rw [hset]
  exact isClosed_iInter fun y ↦ isClosed_iInter fun _ ↦
    isClosed_eq (CkHolderSpaceOn.continuous_extend_apply y.property) continuous_const

/-- The restriction to the image of chart `i` of a function on `E` supported in a set `K` lies in
`chartZeroOff A k α i ((A.chart i).symm '' K)`. -/
theorem restrictOnL_mem_chartZeroOff {K : Set E} {g : CkHolderSpace k α E F}
    (hgK : tsupport g ⊆ K) :
    CkHolderSpace.restrictOnL (A.image i) g ∈ chartZeroOff A k α i ((A.chart i).symm '' K) :=
  mem_chartZeroOff.2 fun y hy ↦ by
    rw [CkHolderSpace.restrictOnL_apply]
    exact image_eq_zero_of_notMem_tsupport fun h ↦ hy ⟨y, hgK h, rfl⟩

instance [CompleteSpace F] : CompleteSpace (chartZeroOff A k α i L) :=
  (isClosed_chartZeroOff A k α i L).completeSpace_coe

variable [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [VectorBundle ℝ F V]

/-- **Uniqueness from one chart.** Two elements of `C^{k,α}(V)` whose underlying sections vanish
off a subset `L` of the domain of chart `i`, and whose chart-`i` components agree, are equal. -/
theorem eq_of_component_eq {v v' : HolderSection A k α} (hLi : L ⊆ A.dom i)
    (hv : ∀ x ∉ L, toSection v x = 0) (hv' : ∀ x ∉ L, toSection v' x = 0)
    (h : (v : ∀ i : Fin A.n, CkHolderSpaceOn k α (A.image i) F) i =
      (v' : ∀ i : Fin A.n, CkHolderSpaceOn k α (A.image i) F) i) : v = v' := by
  refine ext (funext fun x ↦ ?_)
  by_cases hx : x ∈ A.dom i
  · refine A.eq_of_coord_chart_eq hx ?_
    have hy : A.chart i x ∈ A.image i := A.mem_image.2 ⟨x, hx, rfl⟩
    exact ((coord_toSection v i ⟨_, hy⟩).trans (by rw [h])).trans
      (coord_toSection v' i ⟨_, hy⟩).symm
  · rw [hv x fun h ↦ hx (hLi h), hv' x fun h ↦ hx (hLi h)]

/-- The section reading as an element of `chartZeroOff A k α i L` in chart `i` and vanishing off
the domain of chart `i` vanishes off `L`. -/
private theorem chartSection_eq_zero_of_notMem (f : chartZeroOff A k α i L) {x : M} (hx : x ∉ L) :
    A.chartSection i (f : CkHolderSpaceOn k α (A.image i) F).extend x = 0 := by
  refine FiniteBundleAtlas.chartSection_eq_zero fun hxi ↦ ?_
  have hy : A.chart i x ∈ A.image i := A.mem_image.2 ⟨x, hxi, rfl⟩
  rw [CkHolderSpaceOn.extend_apply_of_mem _ hy]
  refine f.property ⟨_, hy⟩ ?_
  rwa [(A.chart i).left_inv (A.dom_subset_chart_source i hxi)]

variable {n : WithTop ℕ∞} [IsManifold 𝓘(ℝ, E) n M] [ContMDiffVectorBundle n F V 𝓘(ℝ, E)]

/-- The section reading as an element of `chartZeroOff A k α i L` in chart `i` and vanishing off
the domain of chart `i` is of class `C^{k,α}`. -/
private theorem memHolderSection_chartSection (hα : α ≤ 1) (hn : (k : WithTop ℕ∞) + 1 ≤ n)
    (hL : IsClosed L) (hLi : L ⊆ A.dom i) (f : chartZeroOff A k α i L) :
    A.MemHolderSection k α (A.chartSection i (f : CkHolderSpaceOn k α (A.image i) F).extend) :=
  FiniteBundleAtlas.memHolderSection_of_forall_notMem_eq_zero A hα hn hL hLi
    (fun _ hx ↦ chartSection_eq_zero_of_notMem f hx)
    ⟨f, fun y ↦ by
      rw [FiniteBundleAtlas.coord_chartSection _ y.property, CkHolderSpaceOn.extend_apply]⟩

omit [IsManifold 𝓘(ℝ, E) n M] [ContMDiffVectorBundle n F V 𝓘(ℝ, E)] in
/-- The chart-`i` component of the element of `C^{k,α}(V)` defined by the section reading as `G`
in chart `i` and vanishing off the domain of chart `i` is `G`. -/
private theorem ofSection_chartSection_component (G : CkHolderSpaceOn k α (A.image i) F)
    (hs : A.MemHolderSection k α (A.chartSection i G.extend)) :
    (ofSection _ hs : ∀ i : Fin A.n, CkHolderSpaceOn k α (A.image i) F) i = G :=
  CkHolderSpaceOn.ext fun y ↦ by
    rw [ofSection_apply, FiniteBundleAtlas.coord_chartSection _ y.property,
      CkHolderSpaceOn.extend_apply]

/-- Extension by zero from chart `i`, as a linear map. -/
private def extendByZeroₗ (hα : α ≤ 1) (hn : (k : WithTop ℕ∞) + 1 ≤ n) (hL : IsClosed L)
    (hLi : L ⊆ A.dom i) : chartZeroOff A k α i L →ₗ[ℝ] HolderSection A k α where
  toFun f := ofSection _ (memHolderSection_chartSection hα hn hL hLi f)
  map_add' f g := by
    refine eq_of_component_eq hLi (fun x hx ↦ ?_) (fun x hx ↦ ?_) ?_
    · rw [toSection_ofSection]
      exact chartSection_eq_zero_of_notMem _ hx
    · rw [map_add, Pi.add_apply, toSection_ofSection, toSection_ofSection,
        chartSection_eq_zero_of_notMem _ hx, chartSection_eq_zero_of_notMem _ hx, add_zero]
    · simp only [Submodule.coe_add, Pi.add_apply, ofSection_chartSection_component]
  map_smul' c f := by
    refine eq_of_component_eq hLi (fun x hx ↦ ?_) (fun x hx ↦ ?_) ?_
    · rw [toSection_ofSection]
      exact chartSection_eq_zero_of_notMem _ hx
    · rw [RingHom.id_apply, map_smul, Pi.smul_apply, toSection_ofSection,
        chartSection_eq_zero_of_notMem _ hx, smul_zero]
    · simp only [RingHom.id_apply, Submodule.coe_smul, Pi.smul_apply,
        ofSection_chartSection_component]

private theorem extendByZeroₗ_apply_self (hα : α ≤ 1) (hn : (k : WithTop ℕ∞) + 1 ≤ n)
    (hL : IsClosed L) (hLi : L ⊆ A.dom i) (f : chartZeroOff A k α i L) :
    (extendByZeroₗ hα hn hL hLi f : ∀ i : Fin A.n, CkHolderSpaceOn k α (A.image i) F) i = f :=
  ofSection_chartSection_component _ _

private theorem toSection_extendByZeroₗ (hα : α ≤ 1) (hn : (k : WithTop ℕ∞) + 1 ≤ n)
    (hL : IsClosed L) (hLi : L ⊆ A.dom i) (f : chartZeroOff A k α i L) :
    toSection (extendByZeroₗ hα hn hL hLi f) =
      A.chartSection i (f : CkHolderSpaceOn k α (A.image i) F).extend :=
  toSection_ofSection _ _

variable [CompleteSpace F]

/-- **Extension by zero from one chart.** Let `L` be a closed subset of the domain of chart `i`,
`k + 1 ≤ n` and `α ≤ 1`. A function of `C^{k,α}(A.image i)` vanishing at the points of the chart
image outside the image of `L` is the chart-`i` component of a unique element of `C^{k,α}(V)`
vanishing off `L`. This is a continuous linear map from `chartZeroOff A k α i L` into
`C^{k,α}(V)`, by the closed graph theorem. -/
def extendByZeroL (hα : α ≤ 1) (hn : (k : WithTop ℕ∞) + 1 ≤ n) (hL : IsClosed L)
    (hLi : L ⊆ A.dom i) : chartZeroOff A k α i L →L[ℝ] HolderSection A k α :=
  ContinuousLinearMap.ofSeqClosedGraph (g := extendByZeroₗ hα hn hL hLi) fun u f v hu hv ↦ by
    -- The limit `v` has chart-`i` component `f`, since components depend continuously on `v`.
    have hcomp : Tendsto (fun m ↦ (extendByZeroₗ hα hn hL hLi (u m) :
        ∀ i : Fin A.n, CkHolderSpaceOn k α (A.image i) F) i) atTop
        (𝓝 ((v : ∀ i : Fin A.n, CkHolderSpaceOn k α (A.image i) F) i)) :=
      ((continuous_apply i).comp continuous_subtypeVal).continuousAt.tendsto.comp hv
    simp only [extendByZeroₗ_apply_self] at hcomp
    have hvi : (v : ∀ i : Fin A.n, CkHolderSpaceOn k α (A.image i) F) i = f :=
      tendsto_nhds_unique hcomp (continuous_subtypeVal.continuousAt.tendsto.comp hu)
    -- The limit `v` vanishes off `L`, reading it in a chart through each point.
    have hvL (x : M) (hx : x ∉ L) : toSection v x = 0 := by
      obtain ⟨j, hj⟩ := A.exists_mem_dom x
      have hy : A.chart j x ∈ A.image j := A.mem_image.2 ⟨x, hj, rfl⟩
      have hxs := A.dom_subset_chart_source j hj
      suffices h : A.coord j (toSection v) (A.chart j x) = 0 by
        rwa [A.coord_eq_zero_iff hy, (A.chart j).left_inv hxs] at h
      have hlim := ((continuous_coord_toSection (k := k) (α := α) hy).tendsto v).comp hv
      refine tendsto_nhds_unique hlim (tendsto_const_nhds.congr fun m ↦ ?_)
      simp only [Function.comp_apply]
      rw [toSection_extendByZeroₗ]
      refine (A.coord_eq_zero hy ?_).symm
      rw [(A.chart j).left_inv hxs]
      exact chartSection_eq_zero_of_notMem _ hx
    refine eq_of_component_eq hLi hvL (fun x hx ↦ ?_) ?_
    · rw [toSection_extendByZeroₗ]
      exact chartSection_eq_zero_of_notMem _ hx
    · rw [hvi, extendByZeroₗ_apply_self]

/-- The underlying section of the extension by zero of `f` reads as `f` in chart `i` and vanishes
off the domain of chart `i`. -/
theorem toSection_extendByZeroL (hα : α ≤ 1) (hn : (k : WithTop ℕ∞) + 1 ≤ n) (hL : IsClosed L)
    (hLi : L ⊆ A.dom i) (f : chartZeroOff A k α i L) :
    toSection (extendByZeroL hα hn hL hLi f) =
      A.chartSection i (f : CkHolderSpaceOn k α (A.image i) F).extend := by
  rw [extendByZeroL, ContinuousLinearMap.coeFn_ofSeqClosedGraph, toSection_extendByZeroₗ]

/-- The chart-`i` component of the extension by zero of `f` is `f`. -/
@[simp]
theorem extendByZeroL_apply_self (hα : α ≤ 1) (hn : (k : WithTop ℕ∞) + 1 ≤ n) (hL : IsClosed L)
    (hLi : L ⊆ A.dom i) (f : chartZeroOff A k α i L) :
    (extendByZeroL hα hn hL hLi f : ∀ i : Fin A.n, CkHolderSpaceOn k α (A.image i) F) i = f := by
  rw [extendByZeroL, ContinuousLinearMap.coeFn_ofSeqClosedGraph, extendByZeroₗ_apply_self]

/-- The underlying section of the extension by zero vanishes off `L`. -/
theorem toSection_extendByZeroL_eq_zero (hα : α ≤ 1) (hn : (k : WithTop ℕ∞) + 1 ≤ n)
    (hL : IsClosed L) (hLi : L ⊆ A.dom i) (f : chartZeroOff A k α i L) {x : M} (hx : x ∉ L) :
    toSection (extendByZeroL hα hn hL hLi f) x = 0 := by
  rw [toSection_extendByZeroL]
  exact chartSection_eq_zero_of_notMem f hx

/-- **The extension by zero recovers sections supported in one chart.** If a section `s` vanishes
off the domain of chart `i` and its reading in chart `i` is `f`, then `s` is the underlying section
of the extension by zero of `f`. -/
theorem toSection_extendByZeroL_eq (hα : α ≤ 1) (hn : (k : WithTop ℕ∞) + 1 ≤ n) (hL : IsClosed L)
    (hLi : L ⊆ A.dom i) {f : chartZeroOff A k α i L} {s : ∀ x, V x}
    (hs : ∀ x ∉ A.dom i, s x = 0)
    (hfs : ∀ y : A.image i, (f : CkHolderSpaceOn k α (A.image i) F) y = A.coord i s y) :
    toSection (extendByZeroL hα hn hL hLi f) = s := by
  refine funext fun x ↦ ?_
  rw [toSection_extendByZeroL]
  by_cases hx : x ∈ A.dom i
  · refine A.eq_of_coord_chart_eq hx ?_
    have hy : A.chart i x ∈ A.image i := A.mem_image.2 ⟨x, hx, rfl⟩
    rw [FiniteBundleAtlas.coord_chartSection _ hy, CkHolderSpaceOn.extend_apply_of_mem _ hy]
    exact hfs ⟨_, hy⟩
  · rw [FiniteBundleAtlas.chartSection_eq_zero fun h ↦ absurd h hx, hs x hx]

end HolderSection

end TauCeti
