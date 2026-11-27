/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Holder.Basic
import TauCeti.Analysis.Holder.OpenSet.Comp.Basic
import TauCeti.Topology.MetricSpace.Holder
import TauCeti.Topology.VectorBundle.Trivialization

/-!
# Independence of the Hölder space of sections from the atlas and the frames

Let `V → M` be a `Cⁿ` real vector bundle with normed model fibre `F` over a `Cⁿ` manifold without
boundary modelled on a real normed space `E`, and let `A` and `B` be two finite bundle atlases.
A finite bundle atlas fixes both the manifold charts and the local frames (bundle charts) in
which sections are read, so `A` and `B` may differ in both. This file shows that for `k + 1 ≤ n`
and `α ≤ 1` the Hölder spaces `C^{k,α}(V)` of `TauCeti.HolderSection A k α` and
`TauCeti.HolderSection B k α` consist of the same sections
(`TauCeti.FiniteBundleAtlas.memHolderSection_iff_of_atlas`), and that the identity on underlying
sections is an isomorphism of Banach spaces when `F` is complete
(`TauCeti.HolderSection.atlasEquiv`). Hence the two `C^{k,α}` norms are equivalent
(`TauCeti.HolderSection.exists_norm_atlasEquiv_le`).

## The argument

Let `s` have `C^{k,α}` readings in the charts of `A`, and fix a chart `j` of `B`. Every point `y`
of the compact closure of the image of chart `j` is the image of a point `x` of the closure of the
chart domain, and `x` lies in the domain of some chart `i` of `A`. On an open neighbourhood of `y`
the reading of `s` in chart `j` is `Φ(z) (wᵢ (τ z))`
(`TauCeti.FiniteBundleAtlas.coord_eq_coordChangeL_coord`), where `wᵢ` is the reading in
chart `i`, `τ` is the chart transition and `Φ` is the coordinate change of the bundle (the change
of frame) read in chart `j`. Both `τ` and `Φ` are `Cⁿ`, so the `k`-th derivative of this reading
is `α`-Hölder near `y` by
`TauCeti.CkHolderSpaceOn.exists_holderOnWith_iteratedFDeriv_clm_apply_comp`. These local Hölder
bounds combine over the compact closure of the chart image by a Lebesgue number argument
(`IsCompact.exists_holderOnWith_thickening_and_norm_le`), and the derivatives of lower order are
continuous near the compact closure, hence bounded on it.

The same local argument applies to a section vanishing off a closed subset `L` of the domain of
a single chart `i` of `A`, whose reading in chart `i` alone is `C^{k,α}`: near a point `x` of the
domain of chart `i` it is the argument above, and near a point outside that domain, hence outside
`L`, the reading in chart `j` vanishes.

The identity on underlying sections has closed graph, since the readings of an element at a point
depend continuously on it, and two readings of the same point in charts of `A` and `B` differ by
an invertible linear map. Both spaces are complete, so the closed graph theorem makes it
continuous.

## Main results

* `TauCeti.FiniteBundleAtlas.MemHolderSection.of_atlas` and
  `TauCeti.FiniteBundleAtlas.memHolderSection_iff_of_atlas`: having `C^{k,α}` readings does not
  depend on the atlas.
* `TauCeti.FiniteBundleAtlas.memHolderSection_of_forall_notMem_eq_zero`: a section vanishing off
  a closed subset of the domain of one chart, with `C^{k,α}` reading in that chart, has `C^{k,α}`
  readings in the charts of every atlas.
* `TauCeti.HolderSection.atlasLinearEquiv` and `TauCeti.HolderSection.atlasEquiv`: the identity on
  underlying sections, as a linear equivalence and as an isomorphism of Banach spaces, compatible
  with inversion and composition (`TauCeti.HolderSection.atlasEquiv_symm`,
  `TauCeti.HolderSection.atlasEquiv_trans`).
* `TauCeti.HolderSection.exists_norm_atlasEquiv_le`: the norms of the two atlases are equivalent.

## References

* M. E. Taylor, *Partial Differential Equations III*, Chapter 13, for Hölder spaces on compact
  manifolds defined through finitely many charts.
-/

public section

noncomputable section

open Bundle Filter Set TopologicalSpace
open scoped NNReal Manifold ContDiff Topology

universe u

namespace TauCeti

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  (A B : FiniteBundleAtlas E M F V)

namespace FiniteBundleAtlas

variable {A B} {n : WithTop ℕ∞} [IsManifold 𝓘(ℝ, E) n M] [ContMDiffVectorBundle n F V 𝓘(ℝ, E)]
  {k : ℕ} {α : ℝ≥0}

/-- Near a point `x` of the closure of the domain of chart `j` of `B` lying in the domain of
chart `i` of `A`, the reading in chart `j` of a section with `C^{k,α}` reading in chart `i` is
`C^k` on an open neighbourhood of `B.chart j x`, and its `k`-th derivative is `α`-Hölder on a
ball around it. -/
private theorem exists_contDiffOn_and_holderOnWith (hα : α ≤ 1) (hn : (k : WithTop ℕ∞) + 1 ≤ n)
    {s : ∀ x, V x} {i : Fin A.n}
    (hs : ∃ f : CkHolderSpaceOn k α (A.image i) F, ∀ y : A.image i, f y = A.coord i s y)
    (j : Fin B.n) {x : M} (hxcl : x ∈ closure (B.dom j)) (hi : x ∈ A.dom i) :
    ∃ N : Set E, IsOpen N ∧ B.chart j x ∈ N ∧ ContDiffOn ℝ k (B.coord j s) N ∧
      ∃ r > 0, ∃ L : ℝ≥0,
        HolderOnWith L α (iteratedFDeriv ℝ k (B.coord j s)) (Metric.ball (B.chart j x) r) := by
  obtain ⟨f, hf⟩ := hs
  have hxs : x ∈ (B.chart j).source := B.closure_dom_subset_source j hxcl
  set N : Set E := (B.chart j).target ∩ (B.chart j).symm ⁻¹' (A.dom i ∩ (B.triv j).baseSet)
  have hNo : IsOpen N := (B.chart j).isOpen_inter_preimage_symm
    ((A.isOpen_dom i).inter (B.triv j).open_baseSet)
  have hyN : B.chart j x ∈ N := ⟨(B.chart j).map_source hxs, by
    rw [mem_preimage, (B.chart j).left_inv hxs]
    exact ⟨hi, B.closure_dom_subset_baseSet j hxcl⟩⟩
  -- The chart transition `τ` and the change of frame `Φ`, both `Cⁿ` on `N`.
  set τ : E → E := fun z ↦ A.chart i ((B.chart j).symm z) with hτdef
  set Φ : E → F →L[ℝ] F := fun z ↦ (A.triv i).coordChangeL ℝ (B.triv j) ((B.chart j).symm z)
    with hΦdef
  have hτN : MapsTo τ N (A.image i) := fun z hz ↦ A.mem_image.2 ⟨_, hz.2.1, rfl⟩
  have hτ : ContDiffOn ℝ n τ N := by
    rw [← contMDiffOn_iff_contDiffOn]
    exact (contMDiffOn_chart (x := A.center i)).comp
      (contMDiffOn_chart_symm.mono inter_subset_left) fun z hz ↦
        A.dom_subset_chart_source i hz.2.1
  have hΦ : ContDiffOn ℝ n Φ N := by
    rw [← contMDiffOn_iff_contDiffOn]
    exact (contMDiffOn_coordChangeL (IB := 𝓘(ℝ, E)) (A.triv i) (B.triv j)).comp
      (contMDiffOn_chart_symm.mono inter_subset_left) fun z hz ↦
        ⟨A.dom_subset_baseSet i hz.2.1, hz.2.2⟩
  -- The reading in chart `j` is `Φ (wᵢ ∘ τ)` on `N`.
  have heq : EqOn (B.coord j s) (fun z ↦ Φ z (f.extend (τ z))) N := fun z hz ↦ by
    rw [A.coord_eq_coordChangeL_coord B s hz.2.2 hz.2.1]
    simp only [hΦdef, hτdef]
    rw [← hf ⟨_, hτN hz⟩, ← CkHolderSpaceOn.extend_apply]
    rfl
  obtain ⟨r, hr, hrN, L, hL⟩ := f.exists_holderOnWith_iteratedFDeriv_clm_apply_comp hNo
    (hτ.of_le hn) (hΦ.of_le hn) hτN hα hyN
  refine ⟨N, hNo, hyN, (((hΦ.of_le hn).of_le (by exact_mod_cast le_self_add)).clm_apply
    (f.contDiffOn_extend.comp ((hτ.of_le hn).of_le (by exact_mod_cast le_self_add))
      hτN)).congr heq, r, hr, L, fun a ha b hb ↦ ?_⟩
  have hev (c : E) (hc : c ∈ Metric.ball (B.chart j x) r) :
      iteratedFDeriv ℝ k (B.coord j s) c =
        iteratedFDeriv ℝ k (fun z ↦ Φ z (f.extend (τ z))) c :=
    ((heq.eventuallyEq_of_mem (hNo.mem_nhds (hrN hc))).iteratedFDeriv ℝ k).eq_of_nhds
  rw [hev a ha, hev b hb]
  exact hL a ha b hb

omit [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [VectorBundle ℝ F V] in
/-- **Gluing local Hölder bounds.** If near every point of the compact closure of the image of
chart `j` the reading of a section is `C^k` on an open neighbourhood with `k`-th derivative
`α`-Hölder on a ball, then this reading is `C^{k,α}` on the image of chart `j`. -/
private theorem exists_eq_coord_of_forall_mem_closure {s : ∀ x, V x} (j : Fin B.n)
    (h : ∀ y ∈ closure (B.image j : Set E), ∃ N : Set E, IsOpen N ∧ y ∈ N ∧
      ContDiffOn ℝ k (B.coord j s) N ∧ ∃ r > 0, ∃ L : ℝ≥0,
        HolderOnWith L α (iteratedFDeriv ℝ k (B.coord j s)) (Metric.ball y r)) :
    ∃ f : CkHolderSpaceOn k α (B.image j) F, ∀ y : B.image j, f y = B.coord j s y := by
  set K := closure (B.image j : Set E)
  have hK : IsCompact K := B.isCompact_closure_image j
  choose! N hNo hyN hcd r hr L hL using h
  have hU : IsOpen (⋃ y ∈ K, N y) := isOpen_biUnion fun y hy ↦ hNo y hy
  have hKU : K ⊆ ⋃ y ∈ K, N y := fun y hy ↦ mem_biUnion hy (hyN y hy)
  have hcdU : ContDiffOn ℝ k (B.coord j s) (⋃ y ∈ K, N y) :=
    contDiffOn_of_locally_contDiffOn fun z hz ↦ by
      obtain ⟨y, hy, hz⟩ := mem_iUnion₂.1 hz
      exact ⟨N y, hNo y hy, hz, (hcd y hy).mono inter_subset_right⟩
  have hΩK : (B.image j : Set E) ⊆ K := subset_closure
  have hbdd : ∀ m ≤ k, ∃ C, ∀ x : B.image j, ‖iteratedFDeriv ℝ m (B.coord j s) x‖ ≤ C :=
    fun m hm ↦ by
      obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
        ((ContinuousOn.continuousOn_iteratedFDeriv hcdU hU (by exact_mod_cast hm)).mono hKU)
      exact ⟨C, fun x ↦ hC x (hΩK x.property)⟩
  obtain ⟨δ, hδ, L', -, hL', -⟩ :=
    hK.exists_holderOnWith_thickening_and_norm_le fun y hy ↦ ⟨r y, hr y hy, L y, hL y hy⟩
  have hholder : MemHolder α fun x : B.image j ↦ iteratedFDeriv ℝ k (B.coord j s) x :=
    ⟨L', (hL'.mono (hΩK.trans (Metric.self_subset_thickening hδ K))).holderWith⟩
  exact ⟨CkHolderSpaceOn.ofContDiffOn _ (hcdU.mono (hΩK.trans hKU)) hbdd hholder,
    CkHolderSpaceOn.ofContDiffOn_apply _ _ hbdd hholder⟩

variable (B) in
/-- **Independence of `C^{k,α}` sections from the atlas.** For `k + 1 ≤ n` and `α ≤ 1`, a section
of a `Cⁿ` vector bundle with `C^{k,α}` readings in the charts of one finite bundle atlas has
`C^{k,α}` readings in the charts of every other finite bundle atlas. -/
theorem MemHolderSection.of_atlas (hα : α ≤ 1) (hn : (k : WithTop ℕ∞) + 1 ≤ n)
    {s : ∀ x, V x} (hs : A.MemHolderSection k α s) : B.MemHolderSection k α s := by
  refine memHolderSection_iff.2 fun j ↦ exists_eq_coord_of_forall_mem_closure j fun y hy ↦ ?_
  obtain ⟨x, hxcl, rfl⟩ := B.closure_image_subset_chart_image_closure_dom j hy
  obtain ⟨i, hi⟩ := A.exists_mem_dom x
  exact exists_contDiffOn_and_holderOnWith hα hn (memHolderSection_iff.1 hs i) j hxcl hi

variable (B) in
/-- **Sections localized in one chart.** For `k + 1 ≤ n` and `α ≤ 1`, a section of a `Cⁿ` vector
bundle that vanishes off a closed subset `L` of the domain of chart `i` of `A`, and whose reading in
chart `i` is `C^{k,α}` on the image of that chart, has `C^{k,α}` readings in the charts of every
finite bundle atlas. -/
theorem memHolderSection_of_forall_notMem_eq_zero (hα : α ≤ 1) (hn : (k : WithTop ℕ∞) + 1 ≤ n)
    {s : ∀ x, V x} {i : Fin A.n} {L : Set M} (hL : IsClosed L) (hLi : L ⊆ A.dom i)
    (hsL : ∀ x ∉ L, s x = 0)
    (hs : ∃ f : CkHolderSpaceOn k α (A.image i) F, ∀ y : A.image i, f y = A.coord i s y) :
    B.MemHolderSection k α s := by
  refine memHolderSection_iff.2 fun j ↦ exists_eq_coord_of_forall_mem_closure j fun y hy ↦ ?_
  obtain ⟨x, hxcl, rfl⟩ := B.closure_image_subset_chart_image_closure_dom j hy
  by_cases hi : x ∈ A.dom i
  · exact exists_contDiffOn_and_holderOnWith hα hn hs j hxcl hi
  -- Off `L` the section vanishes, so near `B.chart j x` its reading in chart `j` is zero.
  have hxs : x ∈ (B.chart j).source := B.closure_dom_subset_source j hxcl
  set N : Set E := (B.chart j).target ∩ (B.chart j).symm ⁻¹' (Lᶜ ∩ (B.triv j).baseSet)
  have hNo : IsOpen N :=
    (B.chart j).isOpen_inter_preimage_symm (hL.isOpen_compl.inter (B.triv j).open_baseSet)
  have hyN : B.chart j x ∈ N := ⟨(B.chart j).map_source hxs, by
    rw [mem_preimage, (B.chart j).left_inv hxs]
    exact ⟨fun h ↦ hi (hLi h), B.closure_dom_subset_baseSet j hxcl⟩⟩
  have heq : EqOn (B.coord j s) 0 N := fun z hz ↦ by
    rw [B.coord_def, hsL _ hz.2.1, ← (B.triv j).continuousLinearMapAt_apply_of_mem (R := ℝ) hz.2.2,
      map_zero, Pi.zero_apply]
  obtain ⟨r, hr, hrN⟩ := Metric.isOpen_iff.1 hNo _ hyN
  have hev (c : E) (hc : c ∈ Metric.ball (B.chart j x) r) :
      iteratedFDeriv ℝ k (B.coord j s) c = 0 := by
    rw [((heq.eventuallyEq_of_mem (hNo.mem_nhds (hrN hc))).iteratedFDeriv ℝ k).eq_of_nhds,
      iteratedFDeriv_zero, Pi.zero_apply]
  refine ⟨N, hNo, hyN, contDiffOn_const.congr heq, r, hr, 0, fun a ha b hb ↦ ?_⟩
  rw [hev a ha, hev b hb, edist_self]
  exact zero_le

variable (A B) in
/-- For `k + 1 ≤ n` and `α ≤ 1`, a section of a `Cⁿ` vector bundle has `C^{k,α}` readings in the
charts of one finite bundle atlas exactly when it has them in the charts of another. -/
theorem memHolderSection_iff_of_atlas (hα : α ≤ 1) (hn : (k : WithTop ℕ∞) + 1 ≤ n)
    {s : ∀ x, V x} : A.MemHolderSection k α s ↔ B.MemHolderSection k α s :=
  ⟨fun h ↦ h.of_atlas B hα hn, fun h ↦ h.of_atlas A hα hn⟩

end FiniteBundleAtlas

namespace HolderSection

variable {A B} {k : ℕ} {α : ℝ≥0} {n : WithTop ℕ∞} [IsManifold 𝓘(ℝ, E) n M]
  [ContMDiffVectorBundle n F V 𝓘(ℝ, E)]

variable (A B k α) in
/-- For `k + 1 ≤ n` and `α ≤ 1`, the Hölder spaces `C^{k,α}(V)` of two finite bundle atlases of a
`Cⁿ` vector bundle are linearly equivalent by the identity on underlying sections. -/
def atlasLinearEquiv (hα : α ≤ 1) (hn : (k : WithTop ℕ∞) + 1 ≤ n) :
    HolderSection A k α ≃ₗ[ℝ] HolderSection B k α where
  toFun w := ofSection (toSection w) ((A.memHolderSection_toSection w).of_atlas B hα hn)
  invFun w := ofSection (toSection w) ((B.memHolderSection_toSection w).of_atlas A hα hn)
  map_add' w w' := ext (by simp)
  map_smul' c w := ext (by simp)
  left_inv w := ext (by simp)
  right_inv w := ext (by simp)

/-- The identity of the two atlases preserves underlying sections. -/
@[simp]
theorem toSection_atlasLinearEquiv (hα : α ≤ 1) (hn : (k : WithTop ℕ∞) + 1 ≤ n)
    (w : HolderSection A k α) : toSection (atlasLinearEquiv A B k α hα hn w) = toSection w :=
  toSection_ofSection _ _

@[simp]
theorem toSection_atlasLinearEquiv_symm (hα : α ≤ 1) (hn : (k : WithTop ℕ∞) + 1 ≤ n)
    (w : HolderSection B k α) :
    toSection ((atlasLinearEquiv A B k α hα hn).symm w) = toSection w :=
  toSection_ofSection _ _

/-- The inverse of the identification of the Hölder spaces of `A` and `B` is the identification
of those of `B` and `A`. -/
theorem atlasLinearEquiv_symm (hα : α ≤ 1) (hn : (k : WithTop ℕ∞) + 1 ≤ n) :
    (atlasLinearEquiv A B k α hα hn).symm = atlasLinearEquiv B A k α hα hn :=
  LinearEquiv.ext fun w ↦ ext (by simp)

/-- The identification of the Hölder space of an atlas with itself is the identity. -/
@[simp]
theorem atlasLinearEquiv_refl (hα : α ≤ 1) (hn : (k : WithTop ℕ∞) + 1 ≤ n) :
    atlasLinearEquiv A A k α hα hn = LinearEquiv.refl ℝ _ :=
  LinearEquiv.ext fun w ↦ ext (by simp)

/-- The identifications of Hölder spaces compose. -/
@[simp]
theorem atlasLinearEquiv_trans (C : FiniteBundleAtlas E M F V) (hα : α ≤ 1)
    (hn : (k : WithTop ℕ∞) + 1 ≤ n) :
    (atlasLinearEquiv A B k α hα hn).trans (atlasLinearEquiv B C k α hα hn) =
      atlasLinearEquiv A C k α hα hn :=
  LinearEquiv.ext fun w ↦ ext (by simp)

variable [CompleteSpace F]

/-- When the model fibre is complete, the identification of the Hölder spaces of two atlases is
continuous, by the closed graph theorem. -/
theorem continuous_atlasLinearEquiv (hα : α ≤ 1) (hn : (k : WithTop ℕ∞) + 1 ≤ n) :
    Continuous (atlasLinearEquiv A B k α hα hn) := by
  refine (atlasLinearEquiv A B k α hα hn).toLinearMap.continuous_of_seq_closed_graph
    fun u w v hu hv ↦ ext (funext fun x ↦ ?_)
  obtain ⟨i, hi⟩ := A.exists_mem_dom x
  obtain ⟨j, hj⟩ := B.exists_mem_dom x
  refine B.eq_of_coord_chart_eq hj ?_
  have hv' : Tendsto (fun m ↦ B.coord j (toSection (u m)) (B.chart j x)) atTop
      (𝓝 (B.coord j (toSection v) (B.chart j x))) := by
    simpa [Function.comp_def] using
      ((continuous_coord_toSection (B.mem_image.2 ⟨x, hj, rfl⟩)).tendsto v).comp hv
  have hw' : Tendsto (fun m ↦ B.coord j (toSection (u m)) (B.chart j x)) atTop
      (𝓝 (B.coord j (toSection (atlasLinearEquiv A B k α hα hn w)) (B.chart j x))) := by
    simp only [toSection_atlasLinearEquiv, A.coord_chart_eq_coordChangeL_coord_chart B _ hi hj]
    exact (((A.triv i).coordChangeL ℝ (B.triv j) x).continuous.tendsto _).comp
      (((continuous_coord_toSection (A.mem_image.2 ⟨x, hi, rfl⟩)).tendsto w).comp hu)
  exact tendsto_nhds_unique hv' hw'

variable (A B k α) in
/-- **Independence of the Hölder space of sections from the atlas and the frames.** For a `Cⁿ`
vector bundle with complete model fibre, `k + 1 ≤ n` and `α ≤ 1`, the Hölder spaces `C^{k,α}(V)`
of two finite bundle atlases are isomorphic Banach spaces by the identity on underlying sections.
-/
def atlasEquiv (hα : α ≤ 1) (hn : (k : WithTop ℕ∞) + 1 ≤ n) :
    HolderSection A k α ≃L[ℝ] HolderSection B k α :=
  (atlasLinearEquiv A B k α hα hn).toContinuousLinearEquivOfContinuous
    (continuous_atlasLinearEquiv hα hn)

@[simp]
theorem toSection_atlasEquiv (hα : α ≤ 1) (hn : (k : WithTop ℕ∞) + 1 ≤ n)
    (w : HolderSection A k α) : toSection (atlasEquiv A B k α hα hn w) = toSection w :=
  toSection_atlasLinearEquiv hα hn w

@[simp]
theorem toLinearEquiv_atlasEquiv (hα : α ≤ 1) (hn : (k : WithTop ℕ∞) + 1 ≤ n) :
    (atlasEquiv A B k α hα hn).toLinearEquiv = atlasLinearEquiv A B k α hα hn :=
  LinearEquiv.ext fun w ↦ ext (by simp)

@[simp]
theorem toSection_atlasEquiv_symm (hα : α ≤ 1) (hn : (k : WithTop ℕ∞) + 1 ≤ n)
    (w : HolderSection B k α) : toSection ((atlasEquiv A B k α hα hn).symm w) = toSection w :=
  toSection_atlasLinearEquiv_symm hα hn w

/-- The inverse of the continuous identification of the Hölder spaces of `A` and `B` is that of
`B` and `A`. -/
theorem atlasEquiv_symm (hα : α ≤ 1) (hn : (k : WithTop ℕ∞) + 1 ≤ n) :
    (atlasEquiv A B k α hα hn).symm = atlasEquiv B A k α hα hn :=
  ContinuousLinearEquiv.ext <| funext fun w ↦ ext (by simp)

/-- The continuous identification of the Hölder space of an atlas with itself is the identity. -/
@[simp]
theorem atlasEquiv_refl (hα : α ≤ 1) (hn : (k : WithTop ℕ∞) + 1 ≤ n) :
    atlasEquiv A A k α hα hn = ContinuousLinearEquiv.refl ℝ _ :=
  ContinuousLinearEquiv.ext <| funext fun w ↦ ext (by simp)

/-- The continuous identifications of Hölder spaces compose. -/
@[simp]
theorem atlasEquiv_trans (C : FiniteBundleAtlas E M F V) (hα : α ≤ 1)
    (hn : (k : WithTop ℕ∞) + 1 ≤ n) :
    (atlasEquiv A B k α hα hn).trans (atlasEquiv B C k α hα hn) = atlasEquiv A C k α hα hn :=
  ContinuousLinearEquiv.ext <| funext fun w ↦ ext (by simp)

/-- **Equivalence of the `C^{k,α}` norms of two atlases.** There is a constant `C` such that each
of the two norms of an element is at most `C` times the other. -/
theorem exists_norm_atlasEquiv_le (hα : α ≤ 1) (hn : (k : WithTop ℕ∞) + 1 ≤ n) :
    ∃ C : ℝ, ∀ w : HolderSection A k α,
      ‖atlasEquiv A B k α hα hn w‖ ≤ C * ‖w‖ ∧ ‖w‖ ≤ C * ‖atlasEquiv A B k α hα hn w‖ := by
  set e := atlasEquiv A B k α hα hn
  refine ⟨max ‖(e : HolderSection A k α →L[ℝ] HolderSection B k α)‖
    ‖(e.symm : HolderSection B k α →L[ℝ] HolderSection A k α)‖, fun w ↦ ⟨?_, ?_⟩⟩
  · exact (e.toContinuousLinearMap.le_opNorm w).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg w))
  · have h := (e.symm : HolderSection B k α →L[ℝ] HolderSection A k α).le_opNorm (e w)
    rw [ContinuousLinearEquiv.coe_coe, e.symm_apply_apply] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

end HolderSection

end TauCeti
