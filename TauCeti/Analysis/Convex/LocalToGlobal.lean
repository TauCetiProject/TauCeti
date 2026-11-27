/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.StrictConvexBetween
public import Mathlib.Analysis.InnerProductSpace.Convex
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.Maps.Proper.Basic
public import TauCeti.Topology.Compactness.Compact
public import TauCeti.Topology.Connected.Basic
public import TauCeti.Topology.Frontier

import TauCeti.Topology.Maps.Proper.Metric
import TauCeti.Topology.Semicontinuity.Basic

/-!
# The local-to-global principle for convexity

Let `f : X → E` be a continuous proper map from a connected Hausdorff space to a
finite-dimensional real normed space. Suppose that `f` is *locally convex*: every point of `X`
lies in an open set `U` (a *convexity chart*, `TauCeti.IsConvexChart f U`) such that

* the image `f '' U` is convex,
* `f` maps every open subset of `U` onto a relatively open subset of `f '' U`, and
* every fibre `U ∩ f ⁻¹' {v}` of `f` in `U` is preconnected.

Then `f` is globally convex: its image is convex
(`IsProperMap.convex_range_of_isConvexChart`) and all of its fibres are preconnected, so connected
over points of the image (`IsProperMap.isPreconnected_preimage_singleton_of_isConvexChart`).
This is the local-to-global principle of Condevaux, Dazord and Molino and of Hilgert, Neeb and
Plank, the global step of their proofs of the convexity theorems of Atiyah, Guillemin–Sternberg and
Kirwan for moment maps: there, near each point, the moment map is open onto a convex cone with
connected fibres, and then a neighbourhood of the point is a convexity chart
(`TauCeti.exists_isConvexChart_inter_preimage_ball`). For a closed embedding `f` it is the theorem
of Tietze and Nakajima that a closed connected locally convex subset of `ℝⁿ` is convex.

## Proof

The proof is a metric argument in the spirit of Hilgert, Neeb and Plank. Two points are *linked*
when they lie in a common convexity chart, and the *chain distance* `ρ x y` is the infimum of the
lengths `∑ ‖f xᵢ - f xᵢ₊₁‖` of chains of linked points from `x` to `y`. Connectedness of `X` makes
it finite, and it is at least `‖f x - f y‖`. Its key properties are:

* `ρ` is continuous, and it equals `‖f a - f b‖` for points `a, b` of a common chart.
* (Midpoints.) For `t ∈ [0, 1]` there is a point `m` with `ρ x m = t ρ x y` and
  `ρ m y = (1 - t) ρ x y`: split almost minimal chains at the fraction `t` of their length, and take
  a cluster point of the splitting points, which lie in a compact set since `f` is proper.
* (Local rigidity.) Fibre components of `f` are compact. The convexity charts meeting the fibre
  component `C` of a point `p` glue, after shrinking to the preimage of a small ball, to one
  convexity chart `N` containing `C`, whose fibre through `p` is exactly `C`. Separating `C` from
  the rest of its fibre, a chain from `p` that leaves `N` crosses a frontier through a segment of
  some chart, so points `a` with `ρ p a` small lie in `N`. Then `ρ a b = ‖f a - f b‖` whenever
  `ρ p a` and `ρ p b` are small, uniformly for `p` in a compact set.
* (Straightening.) Repeated midpoints cut `x, y` into `n` steps `zᵢ` of chain length `ρ x y / n`.
  When the steps are shorter than the rigidity radius, the images of three consecutive points are
  spaced by `ρ x y / n` and their outer distance is `2 ρ x y / n`, so in a strictly convex norm the
  steps `f zᵢ₊₁ - f zᵢ` are all equal and `‖f y - f x‖ = ρ x y`.

Hence the image of the midpoint at fraction `t` is the point of `[f x, f y]` at fraction `t`, which
proves convexity, and two points of a fibre have chain distance `0`, so by local rigidity they lie
in the same fibre component. The general finite-dimensional statement follows by transporting the
norm to a Euclidean one.

## Main definitions

* `TauCeti.IsConvexChart f U`: `U` is a convexity chart of `f`.

## Main results

* `TauCeti.IsConvexChart.isPreconnected_inter_preimage`: in a convexity chart, the preimage of a
  preconnected subset of the image is preconnected.
* `TauCeti.exists_isConvexChart_inter_preimage_ball`: a map that is open onto a convex set near a
  point, with preconnected fibres there, has a convexity chart around that point.
* `TauCeti.IsConvexChart.source_inter_preimage`: convexity charts of a map read in a chart give
  convexity charts of the map.
* `TauCeti.isConvexChart_source_inter_preimage`: a map reading as an open linear map in a chart
  has the preimages of open convex sets as convexity charts.
* `IsProperMap.convex_range_of_isConvexChart`: a proper locally convex map from a connected
  Hausdorff space has convex image.
* `IsProperMap.isPreconnected_preimage_singleton_of_isConvexChart`: its fibres are preconnected,
  so connected over points of the image.

## References

* J. Hilgert, K.-H. Neeb, W. Plank, *Symplectic convexity theorems and coadjoint orbits*,
  Compositio Mathematica 94 (1994), 129–180, Section 3 (Theorem 3.10).
* M. Condevaux, P. Dazord, P. Molino, *Géométrie du moment*, Travaux du Séminaire Sud-Rhodanien
  de Géométrie I, Publications du Département de Mathématiques de Lyon (1988), 131–160.
* T. Bjorndahl, Y. Karshon, *Revisiting Tietze–Nakajima: local and global convexity for maps*,
  Canadian Journal of Mathematics 62 (2010), 975–993.
-/

public section

open Filter Function Metric Set Topology

namespace TauCeti

variable {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A *convexity chart* of a map `f : X → E` is an open set `U` on which `f` is a convex map onto
its image: the image `f '' U` is convex, `f` sends open subsets of `U` onto relatively open
subsets of `f '' U`, and every fibre of `f` in `U` is preconnected. A map all of whose points lie in
convexity charts is called locally convex; `TauCeti.exists_isConvexChart_inter_preimage_ball`
produces convexity charts from local convexity data, such as a map that is open onto a convex cone
near a point. -/
structure IsConvexChart (f : X → E) (U : Set X) : Prop where
  /-- A convexity chart is open. -/
  isOpen : IsOpen U
  /-- The image of a convexity chart is convex. -/
  convex_image : Convex ℝ (f '' U)
  /-- The map is open from a convexity chart onto its image. -/
  image_mem_nhdsWithin : ∀ W ⊆ U, IsOpen W → ∀ x ∈ W, f '' W ∈ 𝓝[f '' U] (f x)
  /-- The fibres of the map in a convexity chart are preconnected. -/
  isPreconnected_inter_preimage_singleton : ∀ v, IsPreconnected (U ∩ f ⁻¹' {v})

namespace IsConvexChart

variable {f : X → E} {U : Set X}

/-- In a convexity chart `U` of `f`, the preimage `U ∩ f ⁻¹' S` of a preconnected subset `S` of the
image is preconnected: a map that is open onto its image with preconnected fibres has preconnected
preimages of preconnected sets. -/
theorem isPreconnected_inter_preimage (hU : IsConvexChart f U) {S : Set E} (hS : IsPreconnected S)
    (hSU : S ⊆ f '' U) : IsPreconnected (U ∩ f ⁻¹' S) := by
  intro u v hu hv hcover ⟨a, ha, hau⟩ ⟨b, hb, hbv⟩
  by_contra hne
  -- Each fibre over `S` is a preconnected subset of `u ∪ v` missing `u ∩ v`, so the images
  -- `f '' (U ∩ u)` and `f '' (U ∩ v)` are disjoint on `S`.
  have hdisj : ∀ s ∈ S, s ∈ f '' (U ∩ u) → s ∉ f '' (U ∩ v) := by
    rintro s hs ⟨x, ⟨hxU, hxu⟩, rfl⟩ ⟨y, ⟨hyU, hyv⟩, hyx⟩
    have hS' : U ∩ f ⁻¹' {f x} ⊆ U ∩ f ⁻¹' S := fun z ⟨hzU, hz⟩ ↦ by
      rw [mem_preimage, mem_singleton_iff] at hz
      exact ⟨hzU, by rwa [mem_preimage, hz]⟩
    obtain ⟨z, hz, hzuv⟩ := hU.isPreconnected_inter_preimage_singleton (f x) u v hu hv
      (hS'.trans hcover) ⟨x, ⟨hxU, rfl⟩, hxu⟩ ⟨y, ⟨hyU, hyx⟩, hyv⟩
    exact hne ⟨z, hS' hz, hzuv⟩
  -- Relatively open pieces of `f '' U` give open sets in `E` with the same trace on `S`.
  have hopen : ∀ w : Set X, IsOpen w → ∀ s ∈ S, s ∈ f '' (U ∩ w) →
      s ∈ interior ((f '' U)ᶜ ∪ f '' (U ∩ w)) := by
    rintro w hw s - ⟨x, hx, rfl⟩
    have := hU.image_mem_nhdsWithin _ inter_subset_left (hU.isOpen.inter hw) x hx
    rw [mem_interior_iff_mem_nhds]
    filter_upwards [mem_nhdsWithin_iff_eventually.1 this] with y hy
    by_cases h : y ∈ f '' U
    · exact Or.inr (hy h)
    · exact Or.inl h
  have htrace : ∀ w : Set X, ∀ s ∈ S, s ∈ interior ((f '' U)ᶜ ∪ f '' (U ∩ w)) →
      s ∈ f '' (U ∩ w) := fun w s hs hsw ↦
    (interior_subset hsw).resolve_left (not_not.2 (hSU hs))
  obtain ⟨s, hs, hsu, hsv⟩ := hS _ _ isOpen_interior isOpen_interior
    (fun s hs ↦ by
      obtain ⟨x, hxU, rfl⟩ := hSU hs
      rcases hcover ⟨hxU, hs⟩ with hxu | hxv
      · exact Or.inl (hopen u hu _ hs ⟨x, ⟨hxU, hxu⟩, rfl⟩)
      · exact Or.inr (hopen v hv _ hs ⟨x, ⟨hxU, hxv⟩, rfl⟩))
    ⟨f a, ha.2, hopen u hu _ ha.2 ⟨a, ⟨ha.1, hau⟩, rfl⟩⟩
    ⟨f b, hb.2, hopen v hv _ hb.2 ⟨b, ⟨hb.1, hbv⟩, rfl⟩⟩
  exact hdisj s hs (htrace u s hs hsu) (htrace v s hs hsv)

/-- In a convexity chart `U` of `f`, the points of `U` lying over a segment between two points of
`f '' U` form a preconnected set. -/
theorem isPreconnected_inter_preimage_segment (hU : IsConvexChart f U) {x y : X} (hx : x ∈ U)
    (hy : y ∈ U) : IsPreconnected (U ∩ f ⁻¹' segment ℝ (f x) (f y)) :=
  hU.isPreconnected_inter_preimage (convex_segment _ _).isPreconnected
    (hU.convex_image.segment_subset (mem_image_of_mem f hx) (mem_image_of_mem f hy))

/-- Composing with a continuous linear equivalence `e` preserves convexity charts: a convexity chart
of `f` is one of `e ∘ f`. -/
theorem continuousLinearEquiv_comp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hU : IsConvexChart f U) (e : E ≃L[ℝ] F) : IsConvexChart (e ∘ f) U where
  isOpen := hU.isOpen
  convex_image := by
    rw [image_comp]
    exact hU.convex_image.linear_image (e : E →ₗ[ℝ] F)
  image_mem_nhdsWithin W hW hWo x hx := by
    have h := e.toHomeomorph.isEmbedding.map_nhdsWithin_eq (f '' U) (f x)
    simp only [ContinuousLinearEquiv.coe_toHomeomorph] at h
    rw [image_comp, image_comp, comp_apply, ← h]
    exact image_mem_map (hU.image_mem_nhdsWithin W hW hWo x hx)
  isPreconnected_inter_preimage_singleton w := by
    convert hU.isPreconnected_inter_preimage_singleton (e.symm w) using 2
    ext x
    simp [e.eq_symm_apply]

end IsConvexChart

/-- A cover of `X` by convexity charts of `f` is one by convexity charts of `e ∘ f`. -/
private theorem exists_isConvexChart_continuousLinearEquiv_comp {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : X → E}
    (hloc : ∀ x, ∃ U, x ∈ U ∧ IsConvexChart f U) (e : E ≃L[ℝ] F) (x : X) :
    ∃ U, x ∈ U ∧ IsConvexChart (e ∘ f) U :=
  let ⟨U, hx, hU⟩ := hloc x
  ⟨U, hx, hU.continuousLinearEquiv_comp e⟩

/-- **Convexity charts from local convexity data.** Suppose that `f` maps an open set `U` into a
convex set `C`, sending open subsets of `U` onto relative neighbourhoods in `C`, with preconnected
fibres in `U`; for instance `C` may be a convex cone with vertex `f x`, as in a local normal form of
a moment map near `x`. Then `U ∩ f ⁻¹' ball (f x) ε` is a convexity chart of `f` for some
`ε > 0`. -/
theorem exists_isConvexChart_inter_preimage_ball {f : X → E} (hf : Continuous f) {U : Set X}
    (hU : IsOpen U) {C : Set E} (hC : Convex ℝ C) (hUC : f '' U ⊆ C)
    (hopen : ∀ W ⊆ U, IsOpen W → ∀ x ∈ W, f '' W ∈ 𝓝[C] (f x))
    (hfib : ∀ v, IsPreconnected (U ∩ f ⁻¹' {v})) {x : X} (hx : x ∈ U) :
    ∃ ε > 0, IsConvexChart f (U ∩ f ⁻¹' ball (f x) ε) := by
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhdsWithin_iff.1 (hopen U subset_rfl hU x hx)
  have himage : f '' (U ∩ f ⁻¹' ball (f x) ε) = ball (f x) ε ∩ C := by
    refine Subset.antisymm ?_ fun v hv ↦ ?_
    · rintro _ ⟨y, ⟨hyU, hyB⟩, rfl⟩
      exact ⟨hyB, hUC (mem_image_of_mem f hyU)⟩
    · obtain ⟨y, hyU, rfl⟩ := hεU hv
      exact ⟨y, ⟨hyU, hv.1⟩, rfl⟩
  refine ⟨ε, hε, hU.inter (isOpen_ball.preimage hf), ?_, fun W hW hWo y hy ↦ ?_,
    isPreconnected_inter_preimage_singleton_of_forall_mem_image fun v hv ↦ ?_⟩
  · rw [himage]
    exact (convex_ball _ _).inter hC
  · rw [himage]
    exact nhdsWithin_mono _ inter_subset_right
      (hopen W (hW.trans inter_subset_left) hWo y hy)
  · rw [himage] at hv
    convert hfib v using 1
    ext y
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
    exact ⟨fun ⟨⟨hyU, _⟩, hyv⟩ ↦ ⟨hyU, hyv⟩, fun ⟨hyU, hyv⟩ ↦ ⟨⟨hyU, hyv ▸ hv.1⟩, hyv⟩⟩

/-- **Convexity charts read in a chart.** Let `e` be a partial homeomorphism from `X` to a
topological space `F`, and let `f` read in `e` as a map `g : F → E`, that is, `f = g ∘ e` on the
source of `e`. Then the preimage under `e` of a convexity chart `B ⊆ e.target` of `g` is a convexity
chart of `f`. This transports local models of `f`, such as the normal forms of the Morse–Bott lemma
or of a moment map, from coordinates to `X`. -/
theorem IsConvexChart.source_inter_preimage {F : Type*} [TopologicalSpace F]
    {e : OpenPartialHomeomorph X F} {g : F → E} {B : Set F} (hB : IsConvexChart g B)
    (hBt : B ⊆ e.target) {f : X → E} (hf : EqOn f (g ∘ e) e.source) :
    IsConvexChart f (e.source ∩ e ⁻¹' B) := by
  have himage : ∀ W ⊆ e.source ∩ e ⁻¹' B, f '' W = g '' (e '' W) := fun W hW ↦ by
    rw [(hf.mono (hW.trans inter_subset_left)).image_eq, image_comp]
  have hB' : e '' (e.source ∩ e ⁻¹' B) = B := by
    rw [← e.symm_image_eq_source_inter_preimage hBt]
    exact e.image_symm_image_of_subset_target hBt
  refine ⟨e.isOpen_inter_preimage hB.isOpen, ?_, fun W hW hWo x hx ↦ ?_, fun v ↦ ?_⟩
  · rw [himage _ subset_rfl, hB']
    exact hB.convex_image
  · rw [himage W hW, himage _ subset_rfl, hB', hf (hW hx).1, comp_apply]
    exact hB.image_mem_nhdsWithin _ (by rw [← hB']; exact image_mono hW)
      (e.isOpen_image_of_subset_source hWo (hW.trans inter_subset_left)) (e x)
      (mem_image_of_mem e hx)
  · -- The fibre is the image under `e⁻¹` of the fibre `B ∩ g⁻¹ {v}` of `g`.
    have hfib : e.source ∩ e ⁻¹' B ∩ f ⁻¹' {v} = e.symm '' (B ∩ g ⁻¹' {v}) := by
      rw [inter_right_comm, hf.inter_preimage_eq, preimage_comp, inter_assoc, ← preimage_inter,
        inter_comm (g ⁻¹' {v}), e.symm_image_eq_source_inter_preimage (inter_subset_left.trans hBt)]
    rw [hfib]
    exact (hB.isPreconnected_inter_preimage_singleton v).image _
      (e.continuousOn_symm.mono (inter_subset_left.trans hBt))

/-- **Convexity charts of a linear map read in a chart.** Let `e` be a partial homeomorphism from
`X` to a real normed space `F`, and let `f` read in `e` as an open linear map `g : F → E`, that is,
`f = g ∘ e` on the source of `e`. Then the preimage under `e` of every open convex subset `B` of the
target of `e` is a convexity chart of `f`: its image is `g '' B`, and its fibres are the images
under `e⁻¹` of the convex slices of `B` by the fibres of `g`. Open linear maps between
finite-dimensional spaces are the surjective ones (`LinearMap.isOpenMap_of_finiteDimensional`),
and a map in submersion normal form reads in this way. -/
theorem isConvexChart_source_inter_preimage {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {e : OpenPartialHomeomorph X F} {g : F →ₗ[ℝ] E} (hg : IsOpenMap g) {f : X → E}
    (hf : EqOn f (g ∘ e) e.source) {B : Set F} (hBo : IsOpen B) (hBc : Convex ℝ B)
    (hBt : B ⊆ e.target) : IsConvexChart f (e.source ∩ e ⁻¹' B) :=
  IsConvexChart.source_inter_preimage ⟨hBo, hBc.linear_image g,
    fun W _ hWo _ hx ↦ mem_nhdsWithin_of_mem_nhds ((hg W hWo).mem_nhds (mem_image_of_mem g hx)),
    fun v ↦ (hBc.inter ((convex_singleton v).linear_preimage g)).isPreconnected⟩ hBt hf

/-! ### Chains of linked points -/

section Chain

variable {f : X → E}

/-- Two points are linked when they lie in a common convexity chart. -/
private def Linked (f : X → E) (x y : X) : Prop :=
  ∃ U, IsConvexChart f U ∧ x ∈ U ∧ y ∈ U

/-- `Reach f x y ℓ`: there is a chain of linked points from `x` to `y` whose images have total
length `ℓ`. -/
private inductive Reach (f : X → E) (x : X) : X → ℝ → Prop
  | refl : Reach f x x 0
  | tail {y z : X} {ℓ : ℝ} : Reach f x y ℓ → Linked f y z → Reach f x z (ℓ + dist (f y) (f z))

/-- Any two points are joined by a chain of linked points. -/
private def ChainConnected (f : X → E) : Prop :=
  ∀ x y : X, ∃ ℓ : ℝ, Reach f x y ℓ

private theorem Reach.of_eq {x y : X} {ℓ ℓ' : ℝ} (h : Reach f x y ℓ) (e : ℓ = ℓ') :
    Reach f x y ℓ' :=
  e ▸ h

private theorem Linked.reach {x y : X} (h : Linked f x y) : Reach f x y (dist (f x) (f y)) :=
  (Reach.refl.tail h).of_eq (zero_add _)

private theorem Linked.symm {x y : X} (h : Linked f x y) : Linked f y x :=
  let ⟨U, hU, hx, hy⟩ := h
  ⟨U, hU, hy, hx⟩

private theorem Reach.dist_le {x y : X} {ℓ : ℝ} (h : Reach f x y ℓ) : dist (f x) (f y) ≤ ℓ := by
  induction h with
  | refl => simp
  | tail _ _ ih => exact (dist_triangle _ _ _).trans (add_le_add_left ih _)

private theorem Reach.nonneg {x y : X} {ℓ : ℝ} (h : Reach f x y ℓ) : 0 ≤ ℓ :=
  dist_nonneg.trans h.dist_le

private theorem Reach.trans {x y z : X} {a b : ℝ} (h₁ : Reach f x y a) (h₂ : Reach f y z b) :
    Reach f x z (a + b) := by
  induction h₂ with
  | refl => exact h₁.of_eq (add_zero a).symm
  | tail _ hl ih => exact (ih.tail hl).of_eq (add_assoc _ _ _)

private theorem Reach.symm {x y : X} {ℓ : ℝ} (h : Reach f x y ℓ) : Reach f y x ℓ := by
  induction h with
  | refl => exact Reach.refl
  | tail _ hl ih =>
    exact (hl.symm.reach.trans ih).of_eq (by rw [dist_comm, add_comm])

/-- **Splitting a chain.** A chain from `x` to `y` of length `ℓ` passes, at each length
`t ∈ [0, ℓ]`, through a point `m` reached from `x` by a chain of length `t` and from which `y` is
reached by a chain of length `ℓ - t`. -/
private theorem Reach.exists_split {x y : X} {ℓ : ℝ} (h : Reach f x y ℓ) {t : ℝ} (ht₀ : 0 ≤ t)
    (htℓ : t ≤ ℓ) : ∃ m, Reach f x m t ∧ Reach f m y (ℓ - t) := by
  induction h generalizing t with
  | refl =>
    obtain rfl : t = 0 := le_antisymm htℓ ht₀
    exact ⟨x, Reach.refl, Reach.refl.of_eq (sub_zero 0).symm⟩
  | @tail y z ℓ h hl ih =>
    by_cases hle : t ≤ ℓ
    · obtain ⟨m, hxm, hmy⟩ := ih ht₀ hle
      exact ⟨m, hxm, (hmy.tail hl).of_eq (by ring)⟩
    · -- The point of the last link at length `t` lies in its chart, whose image is convex.
      rw [not_le] at hle
      obtain ⟨U, hU, hyU, hzU⟩ := hl
      set d := dist (f y) (f z)
      have hd : 0 < d := by linarith
      set θ := (t - ℓ) / d
      have hθ₀ : 0 ≤ θ := div_nonneg (by linarith) hd.le
      have hθ₁ : θ ≤ 1 := (div_le_one hd).2 (by linarith)
      obtain ⟨m, hmU, hm⟩ : AffineMap.lineMap (f y) (f z) θ ∈ f '' U :=
        hU.convex_image.segment_subset (mem_image_of_mem f hyU) (mem_image_of_mem f hzU)
          (by rw [segment_eq_image_lineMap]; exact ⟨θ, ⟨hθ₀, hθ₁⟩, rfl⟩)
      have hθd : θ * d = t - ℓ := div_mul_cancel₀ _ hd.ne'
      have hym : dist (f y) (f m) = t - ℓ := by
        rw [hm, dist_left_lineMap, Real.norm_eq_abs, abs_of_nonneg hθ₀, hθd]
      have hmz : dist (f m) (f z) = ℓ + d - t := by
        rw [hm, dist_lineMap_right, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        linear_combination -hθd
      exact ⟨m, (h.tail ⟨U, hU, hyU, hmU⟩).of_eq (by rw [hym]; ring),
        (Linked.reach ⟨U, hU, hmU, hzU⟩).of_eq (by rw [hmz])⟩

/-- **Exit through a frontier.** A chain of length `ℓ` from a point of `O` to a point outside `O`
crosses the frontier of `O` at a point whose image lies within `ℓ` of the image of the start. -/
private theorem Reach.exists_mem_frontier {x y : X} {ℓ : ℝ} (h : Reach f x y ℓ) {O : Set X}
    (hx : x ∈ O) (hy : y ∉ O) : ∃ s ∈ frontier O, dist (f x) (f s) ≤ ℓ := by
  induction h with
  | refl => exact absurd hx hy
  | @tail y z ℓ h hl ih =>
    by_cases hyO : y ∈ O
    · obtain ⟨U, hU, hyU, hzU⟩ := hl
      obtain ⟨s, ⟨-, hs⟩, hsO⟩ := (hU.isPreconnected_inter_preimage_segment hyU hzU
        ).inter_frontier_nonempty ⟨y, ⟨hyU, left_mem_segment ℝ _ _⟩, hyO⟩
          ⟨z, ⟨hzU, right_mem_segment ℝ _ _⟩, hy⟩
      refine ⟨s, hsO, (dist_triangle _ (f y) _).trans (add_le_add h.dist_le ?_)⟩
      simpa [dist_comm] using segment_subset_closedBall_left (f y) (f z) hs
    · obtain ⟨s, hs, hsd⟩ := ih hyO
      exact ⟨s, hs, hsd.trans (le_add_of_nonneg_right dist_nonneg)⟩

/-- In a preconnected space covered by convexity charts, any two points are joined by a chain of
linked points. -/
private theorem exists_reach [PreconnectedSpace X] (hloc : ∀ x, ∃ U, x ∈ U ∧ IsConvexChart f U) :
    ChainConnected f := by
  intro x y
  have hopen : ∀ z, ∃ U, z ∈ U ∧ IsOpen U ∧ ∀ w ∈ U, Linked f z w := fun z ↦
    let ⟨U, hz, hU⟩ := hloc z
    ⟨U, hz, hU.isOpen, fun w hw ↦ ⟨U, hU, hz, hw⟩⟩
  have hS : IsClopen {y | ∃ ℓ, Reach f x y ℓ} := by
    refine ⟨isOpen_compl_iff.1 <| isOpen_iff_forall_mem_open.2 fun z hz ↦ ?_,
      isOpen_iff_forall_mem_open.2 fun z ⟨ℓ, hℓ⟩ ↦ ?_⟩
    · obtain ⟨U, hzU, hU, hlink⟩ := hopen z
      exact ⟨U, fun w hw ⟨ℓ, hℓ⟩ ↦ hz ⟨_, hℓ.tail (hlink w hw).symm⟩, hU, hzU⟩
    · obtain ⟨U, hzU, hU, hlink⟩ := hopen z
      exact ⟨U, fun w hw ↦ ⟨_, hℓ.tail (hlink w hw)⟩, hU, hzU⟩
  exact eq_univ_iff_forall.1 (hS.eq_univ ⟨x, 0, Reach.refl⟩) y

end Chain

/-! ### The chain distance -/

section ChainDist

variable {f : X → E}

/-- The chain distance from `x` to `y`: the infimum of the lengths of chains of linked points. -/
private noncomputable def chainDist (f : X → E) (x y : X) : ℝ :=
  sInf {ℓ | Reach f x y ℓ}

private theorem chainDist_le {x y : X} {ℓ : ℝ} (h : Reach f x y ℓ) : chainDist f x y ≤ ℓ :=
  csInf_le ⟨0, fun _ h ↦ h.nonneg⟩ h

private theorem dist_le_chainDist (hR : ChainConnected f) (x y : X) :
    dist (f x) (f y) ≤ chainDist f x y :=
  le_csInf (hR x y) fun _ h ↦ h.dist_le

private theorem chainDist_nonneg (hR : ChainConnected f) (x y : X) : 0 ≤ chainDist f x y :=
  dist_nonneg.trans (dist_le_chainDist hR x y)

private theorem exists_reach_lt (hR : ChainConnected f) {x y : X} {r : ℝ}
    (h : chainDist f x y < r) :
    ∃ ℓ < r, Reach f x y ℓ := by
  obtain ⟨ℓ, hℓ, hlt⟩ := exists_lt_of_csInf_lt (s := {ℓ | Reach f x y ℓ}) (hR x y) h
  exact ⟨ℓ, hlt, hℓ⟩

private theorem chainDist_triangle (hR : ChainConnected f) (x y z : X) :
    chainDist f x z ≤ chainDist f x y + chainDist f y z := by
  refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
  obtain ⟨a, ha, hxy⟩ := exists_reach_lt hR (lt_add_of_pos_right (chainDist f x y) (half_pos hε))
  obtain ⟨b, hb, hyz⟩ := exists_reach_lt hR (lt_add_of_pos_right (chainDist f y z) (half_pos hε))
  calc chainDist f x z ≤ a + b := chainDist_le (hxy.trans hyz)
    _ < _ := by linarith

private theorem chainDist_comm (hR : ChainConnected f) (x y : X) :
    chainDist f x y = chainDist f y x := by
  have key : ∀ x y : X, chainDist f y x ≤ chainDist f x y := fun x y ↦
    le_csInf (hR x y) fun _ h ↦ chainDist_le h.symm
  exact le_antisymm (key y x) (key x y)

private theorem chainDist_self (hR : ChainConnected f) (x : X) : chainDist f x x = 0 :=
  le_antisymm (chainDist_le Reach.refl) (chainDist_nonneg hR x x)

private theorem Linked.chainDist_eq (hR : ChainConnected f) {x y : X} (h : Linked f x y) :
    chainDist f x y = dist (f x) (f y) :=
  le_antisymm (chainDist_le h.reach) (dist_le_chainDist hR x y)

/-- The chain distance from a fixed point is continuous: near `y`, inside a chart, it moves by at
most the distance of the images. -/
private theorem continuous_chainDist (hR : ChainConnected f)
    (hloc : ∀ x, ∃ U, x ∈ U ∧ IsConvexChart f U) (hf : Continuous f) (x : X) :
    Continuous (chainDist f x) := by
  refine continuous_iff_continuousAt.2 fun y ↦ Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  obtain ⟨U, hyU, hU⟩ := hloc y
  filter_upwards [hU.isOpen.mem_nhds hyU,
    hf.continuousAt.preimage_mem_nhds (ball_mem_nhds (f y) hε)] with z hzU hz
  have hyz : chainDist f y z < ε :=
    (Linked.chainDist_eq hR ⟨U, hU, hyU, hzU⟩).trans_lt (by rw [dist_comm]; exact hz)
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor <;>
    linarith [chainDist_triangle hR x y z, chainDist_triangle hR x z y, chainDist_comm hR y z]

end ChainDist

section Proper

variable [ProperSpace E] {f : X → E}

/-- **Midpoints.** For every `t ∈ [0, 1]` there is a point at chain distance `t ρ x y` from `x` and
`(1 - t) ρ x y` from `y`. -/
private theorem exists_chainDist_eq_mul (hf : IsProperMap f)
    (hloc : ∀ x, ∃ U, x ∈ U ∧ IsConvexChart f U) (hR : ChainConnected f) (x y : X) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ m, chainDist f x m = t * chainDist f x y ∧
      chainDist f m y = (1 - t) * chainDist f x y := by
  set L := chainDist f x y
  have hL : 0 ≤ L := chainDist_nonneg hR x y
  -- Split almost minimal chains at the fraction `t` of their length.
  have hseq : ∀ n : ℕ, ∃ m, chainDist f x m ≤ t * (L + 1 / (n + 1)) ∧
      chainDist f m y ≤ (1 - t) * (L + 1 / (n + 1)) := by
    intro n
    obtain ⟨ℓ, hℓ, h⟩ :=
      exists_reach_lt hR (lt_add_of_pos_right L (Nat.one_div_pos_of_nat (n := n)))
    obtain ⟨m, hxm, hmy⟩ :=
      h.exists_split (mul_nonneg ht.1 h.nonneg) (mul_le_of_le_one_left h.nonneg ht.2)
    refine ⟨m, (chainDist_le hxm).trans (mul_le_mul_of_nonneg_left hℓ.le ht.1),
      (chainDist_le hmy).trans ?_⟩
    rw [show ℓ - t * ℓ = (1 - t) * ℓ by ring]
    exact mul_le_mul_of_nonneg_left hℓ.le (sub_nonneg.2 ht.2)
  choose m hxm hmy using hseq
  -- The splitting points have a cluster point.
  obtain ⟨m₀, -, hm₀⟩ := hf.exists_mapClusterPt_of_frequently_mem (l := atTop)
    (isBounded_closedBall (x := f x) (r := L + 1)) <| .of_forall fun n ↦ mem_closedBall'.2 <|
    calc dist (f x) (f (m n)) ≤ chainDist f x (m n) := dist_le_chainDist hR _ _
      _ ≤ t * (L + 1 / (n + 1)) := hxm n
      _ ≤ L + 1 / (n + 1) := mul_le_of_le_one_left (by positivity) ht.2
      _ ≤ L + 1 := by gcongr; exact div_le_one_of_le₀ (by simp) (by positivity)
  -- Bounds holding along the sequence up to errors tending to zero pass to the cluster point.
  have hbound : ∀ g : X → ℝ, Continuous g → ∀ s ∈ Icc (0 : ℝ) 1,
      (∀ n : ℕ, g (m n) ≤ s * (L + 1 / (n + 1))) → g m₀ ≤ s * L := fun g hg s hs hgm ↦
    hm₀.le_of_eventually_le_add hg.lowerSemicontinuous tendsto_one_div_add_atTop_nhds_zero_nat <|
      .of_forall fun n ↦ (hgm n).trans <| by
        rw [mul_add]
        exact add_le_add_right (mul_le_of_le_one_left (by positivity) hs.2) _
  have h₁ := hbound _ (continuous_chainDist hR hloc hf.continuous x) t ht hxm
  have h₂ := hbound _ ((continuous_chainDist hR hloc hf.continuous y).congr
    fun w ↦ chainDist_comm hR y w) (1 - t) ⟨sub_nonneg.2 ht.2, by linarith [ht.1]⟩ hmy
  have h₃ : L ≤ chainDist f x m₀ + chainDist f m₀ y := chainDist_triangle hR x m₀ y
  have h₄ : (1 - t) * L = L - t * L := by ring
  exact ⟨m₀, by linarith [h₄], by linarith [h₄]⟩

end Proper

/-! ### Gluing charts along a fibre component -/

/-- Convexity charts `U i`, `i ∈ T`, cut down to the preimage of an open convex set `B`, glue to a
convexity chart, provided that any two of them are joined by a chain of charts each of which,
over `B`, maps onto its part of the image of its overlap with the next one. -/
private theorem isConvexChart_biUnion {f : X → E} (hf : Continuous f) {T : Set X} {U : X → Set X}
    (hU : ∀ i ∈ T, IsConvexChart f (U i)) {B : Set E} (hBo : IsOpen B) (hBc : Convex ℝ B)
    {i₀ : X} (hi₀ : i₀ ∈ T)
    (hchain : ∀ i ∈ T, ∀ j ∈ T, Relation.ReflTransGen
      (fun i j ↦ i ∈ T ∧ j ∈ T ∧ B ∩ f '' U i ⊆ f '' (U i ∩ U j)) i j) :
    IsConvexChart f (⋃ i ∈ T, U i ∩ f ⁻¹' B) := by
  -- Over `B`, all the charts have the same image.
  have hgerm : ∀ i ∈ T, ∀ j ∈ T, B ∩ f '' U i ⊆ f '' U j := by
    intro i hi j hj
    have h := hchain i hi j hj
    clear hj
    induction h with
    | refl => exact inter_subset_right
    | tail _ hkl ih =>
      exact fun v hv ↦ image_mono inter_subset_right (hkl.2.2 ⟨hv.1, ih hv⟩)
  have himage : f '' ⋃ i ∈ T, U i ∩ f ⁻¹' B = B ∩ f '' U i₀ := by
    refine Subset.antisymm ?_ fun v ⟨hvB, x, hx, hxv⟩ ↦
      ⟨x, mem_biUnion hi₀ ⟨hx, by rw [mem_preimage, hxv]; exact hvB⟩, hxv⟩
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨i, hi, hxU, hxB⟩ := mem_iUnion₂.1 hx
    exact ⟨hxB, hgerm i hi i₀ hi₀ ⟨hxB, mem_image_of_mem f hxU⟩⟩
  refine ⟨isOpen_biUnion fun i hi ↦ (hU i hi).isOpen.inter (hBo.preimage hf), ?_, ?_,
    isPreconnected_inter_preimage_singleton_of_forall_mem_image fun v hv ↦ ?_⟩
  · rw [himage]
    exact hBc.inter (hU i₀ hi₀).convex_image
  · intro W hW hWo x hx
    obtain ⟨i, hi, hxU, -⟩ := mem_iUnion₂.1 (hW hx)
    have h := (hU i hi).image_mem_nhdsWithin (W ∩ U i) inter_subset_right
      (hWo.inter (hU i hi).isOpen) x ⟨hx, hxU⟩
    rw [himage]
    refine mem_of_superset (nhdsWithin_mono _ (fun v hv ↦ ?_) h) (image_mono inter_subset_left)
    exact hgerm i₀ hi₀ i hi hv
  · rw [himage] at hv
    have hfib : (⋃ i ∈ T, U i ∩ f ⁻¹' B) ∩ f ⁻¹' {v} = ⋃ i ∈ T, U i ∩ f ⁻¹' {v} := by
      ext x
      simp only [mem_inter_iff, mem_iUnion, mem_preimage, mem_singleton_iff, exists_prop]
      constructor
      · rintro ⟨⟨i, hi, hxU, -⟩, hxv⟩
        exact ⟨i, hi, hxU, hxv⟩
      · rintro ⟨i, hi, hxU, hxv⟩
        exact ⟨⟨i, hi, hxU, hxv ▸ hv.1⟩, hxv⟩
    rw [hfib]
    refine IsPreconnected.biUnion_of_reflTransGen
      (fun i hi ↦ (hU i hi).isPreconnected_inter_preimage_singleton v) fun i hi j hj ↦ ?_
    refine Relation.ReflTransGen.mono (fun k l ⟨hk, _, hkl⟩ ↦ ⟨?_, hk⟩) _ _ (hchain i hi j hj)
    obtain ⟨x, ⟨hxk, hxl⟩, hxv⟩ := hkl ⟨hv.1, hgerm i₀ hi₀ k hk hv⟩
    exact ⟨x, ⟨hxk, hxv⟩, hxl, hxv⟩

/-- **The chart of a fibre component.** The convexity charts meeting the connected component `C` of
`p` in its fibre glue, over a small ball around `f p`, to a single convexity chart containing `C`,
whose fibre through `p` is exactly `C`. -/
private theorem exists_isConvexChart_connectedComponentIn {f : X → E} (hf : IsProperMap f)
    (hloc : ∀ x, ∃ U, x ∈ U ∧ IsConvexChart f U) (p : X) :
    ∃ N, IsConvexChart f N ∧ connectedComponentIn (f ⁻¹' {f p}) p ⊆ N ∧
      N ∩ f ⁻¹' {f p} ⊆ connectedComponentIn (f ⁻¹' {f p}) p := by
  set C := connectedComponentIn (f ⁻¹' {f p}) p
  choose U hxU hU using hloc
  have hCf : ∀ c ∈ C, f c = f p := fun c hc ↦ connectedComponentIn_subset _ _ hc
  -- Finitely many charts, centred at points of `C`, cover `C`.
  obtain ⟨T, hTC, hTfin, hcover⟩ :=
    ((hf.isCompact_preimage isCompact_singleton).connectedComponentIn p).elim_finite_subcover_image
      (b := C) (c := U) (fun i _ ↦ (hU i).isOpen) fun c hc ↦ mem_biUnion hc (hxU c)
  have hpC : p ∈ C := mem_connectedComponentIn (mem_singleton (f p))
  obtain ⟨i₀, hi₀, -⟩ := mem_iUnion₂.1 (hcover hpC)
  -- Over a small ball `B` around `f p`, each chart maps onto its overlap with any chart that it
  -- meets in `C`.
  have hevent : ∀ ij ∈ T ×ˢ T, ∀ᶠ ε in 𝓝[>] (0 : ℝ), (U ij.1 ∩ U ij.2 ∩ C).Nonempty →
      ball (f p) ε ∩ f '' U ij.1 ⊆ f '' (U ij.1 ∩ U ij.2) := by
    rintro ⟨i, j⟩ -
    by_cases hij : (U i ∩ U j ∩ C).Nonempty
    · obtain ⟨c, ⟨hci, hcj⟩, hcC⟩ := hij
      have h := (hU i).image_mem_nhdsWithin (U i ∩ U j) inter_subset_left
        ((hU i).isOpen.inter (hU j).isOpen) c ⟨hci, hcj⟩
      rw [hCf c hcC, Metric.mem_nhdsWithin_iff] at h
      obtain ⟨δ, hδ, hδU⟩ := h
      filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε _
      exact (inter_subset_inter_left _ (ball_subset_ball hε.2.le)).trans hδU
    · exact Eventually.of_forall fun _ h ↦ absurd h hij
  obtain ⟨ε, hε, hε0⟩ := (((hTfin.prod hTfin).eventually_all).2 hevent).and
    self_mem_nhdsWithin |>.exists
  have hchain : ∀ i ∈ T, ∀ j ∈ T, Relation.ReflTransGen
      (fun i j ↦ i ∈ T ∧ j ∈ T ∧ ball (f p) ε ∩ f '' U i ⊆ f '' (U i ∩ U j)) i j :=
    fun i hi j hj ↦ Relation.ReflTransGen.mono (fun k l ⟨hk, hl, hkl⟩ ↦
      ⟨hk, hl, hε (k, l) ⟨hk, hl⟩ hkl⟩) _ _
      (isPreconnected_connectedComponentIn.reflTransGen_of_subset_biUnion
        (fun i _ ↦ (hU i).isOpen) hcover hi ⟨i, hxU i, hTC hi⟩ hj ⟨j, hxU j, hTC hj⟩)
  have hN := isConvexChart_biUnion hf.continuous (fun i _ ↦ hU i) isOpen_ball (convex_ball _ _)
    hi₀ hchain
  have hCN : C ⊆ ⋃ i ∈ T, U i ∩ f ⁻¹' ball (f p) ε := fun c hc ↦ by
    obtain ⟨i, hi, hcU⟩ := mem_iUnion₂.1 (hcover hc)
    exact mem_biUnion hi ⟨hcU, by simp [hCf c hc, hε0]⟩
  refine ⟨_, hN, hCN, ?_⟩
  exact (hN.isPreconnected_inter_preimage_singleton (f p)).subset_connectedComponentIn
    ⟨hCN hpC, rfl⟩ inter_subset_right

section Rigidity

variable [T2Space X] [ProperSpace E] {f : X → E}

/-- **Leaving a neighbourhood of a fibre component costs chain length.** If an open set `N`
contains the component `C` of `p` in its fibre, and meets that fibre only in `C`, then points at
small chain distance from `p` lie in `N`. -/
private theorem exists_pos_forall_chainDist_lt_mem (hf : IsProperMap f)
    (hR : ChainConnected f) {N : Set X} (hN : IsOpen N) (p : X)
    (hCN : connectedComponentIn (f ⁻¹' {f p}) p ⊆ N)
    (hNC : N ∩ f ⁻¹' {f p} ⊆ connectedComponentIn (f ⁻¹' {f p}) p) :
    ∃ r > 0, ∀ a, chainDist f p a < r → a ∈ N := by
  set C := connectedComponentIn (f ⁻¹' {f p}) p
  have hfib : IsCompact (f ⁻¹' {f p}) := hf.isCompact_preimage isCompact_singleton
  -- Separate `C` from the rest of its fibre.
  obtain ⟨O₁, O₂, hO₁, hO₂, hCO₁, hEO₂, hO₁₂⟩ := SeparatedNhds.of_isCompact_isCompact
    (hfib.connectedComponentIn p) (hfib.diff hN)
    (disjoint_left.2 fun c hc hc' ↦ hc'.2 (hCN hc))
  set O := O₁ ∩ N
  have hpO : p ∈ O := ⟨hCO₁ (mem_connectedComponentIn (mem_singleton (f p))),
    hCN (mem_connectedComponentIn (mem_singleton (f p)))⟩
  suffices ∃ r > 0, ∀ a, chainDist f p a < r → a ∈ O from
    let ⟨r, hr, h⟩ := this
    ⟨r, hr, fun a ha ↦ (h a ha).2⟩
  by_contra! hcon
  -- Otherwise chains from `p` of length tending to zero leave `O`, crossing its frontier at points
  -- whose images converge to `f p`.
  have hseq : ∀ n : ℕ, ∃ s ∈ frontier O, dist (f p) (f s) ≤ 1 / (n + 1) := fun n ↦ by
    obtain ⟨a, ha, haO⟩ := hcon _ (Nat.one_div_pos_of_nat (n := n))
    obtain ⟨ℓ, hℓ, h⟩ := exists_reach_lt hR ha
    obtain ⟨s, hs, hsd⟩ := h.exists_mem_frontier hpO haO
    exact ⟨s, hs, hsd.trans hℓ.le⟩
  choose s hsO hsd using hseq
  obtain ⟨s₀, -, hs₀⟩ := hf.exists_mapClusterPt_of_frequently_mem (l := atTop)
    (isBounded_closedBall (x := f p) (r := 1)) <| .of_forall fun n ↦ mem_closedBall'.2 <|
      (hsd n).trans (div_le_one_of_le₀ (by simp) (by positivity))
  have hs₀O : s₀ ∈ frontier O := isClosed_frontier.mem_of_mapClusterPt hs₀ (.of_forall hsO)
  have hfs₀ : f s₀ = f p := dist_le_zero.1 <|
    hs₀.le_of_eventually_le_add (g := fun w ↦ dist (f w) (f p))
      (hf.continuous.dist continuous_const).lowerSemicontinuous
      tendsto_one_div_add_atTop_nhds_zero_nat <| .of_forall fun n ↦ by
        rw [dist_comm, zero_add]
        exact hsd n
  by_cases hs₀N : s₀ ∈ N
  · -- The limit lies in `C ⊆ O`, which is open and so misses its frontier.
    have : s₀ ∈ O := ⟨hCO₁ (hNC ⟨hs₀N, hfs₀⟩), hs₀N⟩
    exact (hO₁.inter hN).inter_frontier_eq.subset ⟨this, hs₀O⟩
  · -- The limit lies in the rest of the fibre, inside `O₂`, which misses the closure of `O₁`.
    exact disjoint_left.1 (hO₁₂.closure_left hO₂)
      (closure_mono inter_subset_left (frontier_subset_closure hs₀O)) (hEO₂ ⟨hfs₀, hs₀N⟩)

/-- **Local rigidity.** Near each point `p`, for the chain distance: any two points at small chain
distance from `p` have chain distance equal to the distance of their images. -/
private theorem exists_pos_chainDist_eq_dist (hf : IsProperMap f)
    (hloc : ∀ x, ∃ U, x ∈ U ∧ IsConvexChart f U) (hR : ChainConnected f)
    (p : X) : ∃ r > 0, ∀ a b, chainDist f p a < r → chainDist f p b < r →
      chainDist f a b = dist (f a) (f b) := by
  obtain ⟨N, hN, hCN, hNC⟩ := exists_isConvexChart_connectedComponentIn hf hloc p
  obtain ⟨r, hr, hrN⟩ := exists_pos_forall_chainDist_lt_mem hf hR hN.isOpen p hCN hNC
  exact ⟨r, hr, fun a b ha hb ↦ Linked.chainDist_eq hR ⟨N, hN, hrN a ha, hrN b hb⟩⟩

/-- **Uniform local rigidity** on a compact set. -/
private theorem exists_pos_chainDist_eq_dist_of_isCompact (hf : IsProperMap f)
    (hloc : ∀ x, ∃ U, x ∈ U ∧ IsConvexChart f U) (hR : ChainConnected f)
    {K : Set X} (hK : IsCompact K) : ∃ r > 0, ∀ w ∈ K, ∀ a b, chainDist f w a < r →
      chainDist f w b < r → chainDist f a b = dist (f a) (f b) := by
  choose r hr hrig using exists_pos_chainDist_eq_dist hf hloc hR
  obtain ⟨T, -, hTfin, hcover⟩ := hK.elim_finite_subcover_image (b := K)
    (c := fun p ↦ {w | chainDist f p w < r p / 2})
    (fun p _ ↦ isOpen_lt (continuous_chainDist hR hloc hf.continuous p) continuous_const)
    fun w _ ↦ mem_biUnion (x := w) ‹_› (by simp [chainDist_self hR, hr w])
  obtain ⟨ρ, hρ, hρ0⟩ := ((hTfin.eventually_all (l := 𝓝[>] (0 : ℝ))
    (p := fun p ρ ↦ ρ ≤ r p / 2)).2 fun p _ ↦
      mem_of_superset (Ioo_mem_nhdsGT (half_pos (hr p))) fun _ h ↦ h.2.le).and
    self_mem_nhdsWithin |>.exists
  refine ⟨ρ, hρ0, fun w hw a b ha hb ↦ ?_⟩
  obtain ⟨p, hp, hpw⟩ := mem_iUnion₂.1 (hcover hw)
  have hρp := hρ p hp
  exact hrig p a b (by linarith [chainDist_triangle hR p w a, hpw.out])
    (by linarith [chainDist_triangle hR p w b, hpw.out])

omit [T2Space X] in
/-- **Subdivision.** Repeated midpoints cut `x, y` into `n` steps `zᵢ` of chain length
`ρ x y / n`, with `ρ x zᵢ = i ρ x y / n`, ending at a point at chain distance `0` from `y`. -/
private theorem exists_subdivision (hf : IsProperMap f)
    (hloc : ∀ x, ∃ U, x ∈ U ∧ IsConvexChart f U) (hR : ChainConnected f)
    (x y : X) {n : ℕ} (hn : 0 < n) :
    ∃ z : ℕ → X, z 0 = x ∧ chainDist f (z n) y = 0 ∧
      (∀ i ≤ n, chainDist f x (z i) = i * (chainDist f x y / n)) ∧
      ∀ i < n, chainDist f (z i) (z (i + 1)) = chainDist f x y / n := by
  set L := chainDist f x y with hxy
  set q := L / n
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hLq : L = n * q := (mul_div_cancel₀ L hn'.ne').symm
  clear_value q L
  choose! g hg₁ hg₂ using fun w (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) ↦
    exists_chainDist_eq_mul hf hloc hR w y hs
  let z : ℕ → X := fun i ↦ Nat.rec x (fun k w ↦ g w (1 / ((n : ℝ) - k))) i
  have hzs : ∀ k, z (k + 1) = g (z k) (1 / ((n : ℝ) - k)) := fun _ ↦ rfl
  have hpos : ∀ k < n, (0 : ℝ) < n - k := fun k hk ↦ sub_pos.2 (by exact_mod_cast hk)
  have hs : ∀ k < n, 1 / ((n : ℝ) - k) ∈ Icc (0 : ℝ) 1 := fun k hk ↦
    ⟨by have := hpos k hk; positivity, by
      rw [div_le_one (hpos k hk)]
      have : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
      linarith⟩
  have hto : ∀ k ≤ n, chainDist f (z k) y = L - k * q := by
    intro k hk
    induction k with
    | zero => simp [z, ← hxy]
    | succ k ih =>
      have hk' : k < n := hk
      rw [hzs, hg₂ _ _ (hs k hk'), ih hk'.le]
      have := (hpos k hk').ne'
      field_simp
      push_cast
      linear_combination -hLq
  have hstep : ∀ k < n, chainDist f (z k) (z (k + 1)) = q := by
    intro k hk
    rw [hzs, hg₁ _ _ (hs k hk), hto k hk.le]
    have := (hpos k hk).ne'
    field_simp
    linear_combination hLq
  refine ⟨z, rfl, by rw [hto n le_rfl, hLq]; ring, fun k hk ↦ ?_, hstep⟩
  induction k with
  | zero => simp [z, chainDist_self hR]
  | succ k ih =>
    have hk' : k < n := hk
    have h₁ := chainDist_triangle hR x (z k) (z (k + 1))
    have h₂ := chainDist_triangle hR x (z (k + 1)) y
    rw [← hxy] at h₂
    rw [ih hk'.le, hstep k hk'] at h₁
    rw [hto (k + 1) hk] at h₂
    push_cast at h₁ h₂ ⊢
    linarith

/-- **Rigid subdivision.** Points `x, y` are cut into `n` steps `zᵢ` of chain length
`q = ρ x y / n`, short enough for local rigidity: consecutive images are `q` apart and images two
steps apart are `2 q` apart. -/
private theorem exists_rigid_subdivision (hf : IsProperMap f)
    (hloc : ∀ x, ∃ U, x ∈ U ∧ IsConvexChart f U) (hR : ChainConnected f) (x y : X) :
    ∃ (n : ℕ) (q : ℝ) (z : ℕ → X), 0 < n ∧ chainDist f x y = n * q ∧ z 0 = x ∧
      f (z n) = f y ∧ (∀ i < n, dist (f (z i)) (f (z (i + 1))) = q) ∧
      ∀ i, i + 2 ≤ n → dist (f (z i)) (f (z (i + 2))) = 2 * q := by
  set L := chainDist f x y
  have hL : 0 ≤ L := chainDist_nonneg hR x y
  obtain ⟨r, hr, hrig⟩ := exists_pos_chainDist_eq_dist_of_isCompact hf hloc hR
    (hf.isCompact_preimage (isCompact_closedBall (f x) L))
  obtain ⟨n, hn⟩ := exists_nat_gt (L / r)
  have hn0 : 0 < n := by exact_mod_cast (div_nonneg hL hr.le).trans_lt hn
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn0
  have hq : L / n < r := by
    rw [div_lt_iff₀ hn']
    rw [div_lt_iff₀ hr] at hn
    linarith
  have hq0 : 0 ≤ L / n := div_nonneg hL hn'.le
  obtain ⟨z, hz0, hzn, hfrom, hstep⟩ := exists_subdivision hf hloc hR x y hn0
  set q := L / n
  have hLq : L = n * q := (mul_div_cancel₀ L hn'.ne').symm
  clear_value q
  have hzK : ∀ i ≤ n, z i ∈ f ⁻¹' closedBall (f x) L := fun i hi ↦ by
    rw [mem_preimage, mem_closedBall, dist_comm]
    calc dist (f x) (f (z i)) ≤ chainDist f x (z i) := dist_le_chainDist hR _ _
      _ = i * q := hfrom i hi
      _ ≤ n * q := mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hq0
      _ = L := hLq.symm
  -- Consecutive images are `q` apart, and images two steps apart are `2 q` apart.
  have hd : ∀ i < n, dist (f (z i)) (f (z (i + 1))) = q := fun i hi ↦ by
    rw [← hrig (z i) (hzK i hi.le) _ _ (by rw [chainDist_self hR]; exact hr)
      (by rw [hstep i hi]; exact hq), hstep i hi]
  have hd₂ : ∀ i, i + 2 ≤ n → dist (f (z i)) (f (z (i + 2))) = 2 * q := fun i hi ↦ by
    rw [← hrig (z (i + 1)) (hzK _ (by omega)) _ _
      (by rw [chainDist_comm hR, hstep i (by omega)]; exact hq)
      (by rw [hstep (i + 1) (by omega)]; exact hq)]
    have h₁ := chainDist_triangle hR x (z i) (z (i + 2))
    have h₂ := chainDist_triangle hR (z i) (z (i + 1)) (z (i + 2))
    rw [hfrom i (by omega), hfrom (i + 2) hi] at h₁
    rw [hstep i (by omega), hstep (i + 1) (by omega)] at h₂
    push_cast at h₁
    linarith
  exact ⟨n, q, z, hn0, hLq, hz0, dist_le_zero.1 ((dist_le_chainDist hR _ _).trans hzn.le), hd,
    hd₂⟩

/-- **The chain distance is the distance of the images**, for a proper locally convex map into a
strictly convex space. -/
private theorem chainDist_eq_dist [StrictConvexSpace ℝ E] (hf : IsProperMap f)
    (hloc : ∀ x, ∃ U, x ∈ U ∧ IsConvexChart f U) (hR : ChainConnected f)
    (x y : X) : chainDist f x y = dist (f x) (f y) := by
  obtain ⟨n, q, z, hn0, hLq, hz0, hfzn, hd, hd₂⟩ := exists_rigid_subdivision hf hloc hR x y
  -- In a strictly convex space the steps `f zᵢ₊₁ - f zᵢ` are all equal.
  set v : ℕ → E := fun i ↦ f (z (i + 1)) - f (z i)
  have hv : ∀ i, i + 1 < n → v (i + 1) = v i := fun i hi ↦ by
    have h₁ : ‖v i‖ = q := by rw [← dist_eq_norm', hd i (by omega)]
    have h₂ : ‖v (i + 1)‖ = q := by rw [← dist_eq_norm', hd (i + 1) hi]
    have h₃ : ‖v i + v (i + 1)‖ = ‖v i‖ + ‖v (i + 1)‖ := by
      rw [show v i + v (i + 1) = f (z (i + 2)) - f (z i) by simp only [v]; abel,
        ← dist_eq_norm', hd₂ i (by omega), h₁, h₂, two_mul]
    exact (eq_of_norm_eq_of_norm_add_eq (h₁.trans h₂.symm) h₃).symm
  have hv₀ : ∀ i < n, v i = v 0 := fun i hi ↦ by
    induction i with
    | zero => rfl
    | succ i ih => rw [hv i hi, ih (by omega)]
  have htel : f y - f x = n • v 0 := by
    rw [← hfzn, ← hz0, ← Finset.sum_range_sub (fun i ↦ f (z i)),
      Finset.sum_congr rfl fun i hi ↦ hv₀ i (Finset.mem_range.1 hi), Finset.sum_const,
      Finset.card_range]
  rw [dist_eq_norm', htel, hLq, ← hd 0 hn0, dist_eq_norm']
  simp [← Nat.cast_smul_eq_nsmul ℝ, norm_smul, v]

end Rigidity

/-! ### The local-to-global principle -/

section Main

variable [T2Space X] [PreconnectedSpace X] [ProperSpace E] [StrictConvexSpace ℝ E] {f : X → E}

/-- The local-to-global principle in a strictly convex proper space: the image is convex. -/
private theorem convex_range_of_strictConvexSpace (hf : IsProperMap f)
    (hloc : ∀ x, ∃ U, x ∈ U ∧ IsConvexChart f U) : Convex ℝ (range f) := by
  have hR := exists_reach hloc
  rw [convex_iff_segment_subset]
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  rw [segment_eq_image_lineMap]
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨m, hxm, hmy⟩ := exists_chainDist_eq_mul hf hloc hR x y ht
  rw [chainDist_eq_dist hf hloc hR, chainDist_eq_dist hf hloc hR] at hxm hmy
  exact ⟨m, eq_lineMap_of_dist_eq_mul_of_dist_eq_mul hxm hmy⟩

/-- The local-to-global principle in a strictly convex proper space: the fibres are preconnected,
so connected over points of the image. -/
private theorem isPreconnected_preimage_singleton_of_strictConvexSpace (hf : IsProperMap f)
    (hloc : ∀ x, ∃ U, x ∈ U ∧ IsConvexChart f U) (v : E) : IsPreconnected (f ⁻¹' {v}) := by
  have hR := exists_reach hloc
  rcases eq_empty_or_nonempty (f ⁻¹' {v}) with h | ⟨p, rfl⟩
  · rw [h]
    exact isPreconnected_empty
  -- Every point of the fibre is at chain distance `0` from `p`, hence in the component of `p`.
  obtain ⟨N, hN, hCN, hNC⟩ := exists_isConvexChart_connectedComponentIn hf hloc p
  obtain ⟨r, hr, hrN⟩ := exists_pos_forall_chainDist_lt_mem hf hR hN.isOpen p hCN hNC
  convert (isPreconnected_connectedComponentIn (F := f ⁻¹' {f p}) (x := p)) using 1
  refine Subset.antisymm (fun y hy ↦ hNC ⟨hrN y ?_, hy⟩) (connectedComponentIn_subset _ _)
  rw [chainDist_eq_dist hf hloc hR, mem_singleton_iff.1 hy, dist_self]
  exact hr

end Main

end TauCeti

namespace IsProperMap

open TauCeti

variable {X E : Type*} [TopologicalSpace X] [T2Space X] [PreconnectedSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : X → E}

/-- **The local-to-global principle for convexity** (Condevaux–Dazord–Molino, Hilgert–Neeb–Plank).
A proper map from a connected Hausdorff space to a finite-dimensional real normed space, every point
of which lies in a convexity chart, has convex image. -/
theorem convex_range_of_isConvexChart (hf : IsProperMap f)
    (hloc : ∀ x, ∃ U, x ∈ U ∧ IsConvexChart f U) : Convex ℝ (range f) := by
  set e := toEuclidean (E := E)
  have h := convex_range_of_strictConvexSpace (f := e ∘ f)
    (e.toHomeomorph.isProperMap.comp hf) (exists_isConvexChart_continuousLinearEquiv_comp hloc e)
  rw [range_comp] at h
  simpa [image_image] using h.linear_image (e.symm : _ →ₗ[ℝ] E)

/-- **The local-to-global principle for fibres.** A proper map from a connected Hausdorff space to
a finite-dimensional real normed space, every point of which lies in a convexity chart, has
preconnected fibres, so connected fibres over points of the image. -/
theorem isPreconnected_preimage_singleton_of_isConvexChart (hf : IsProperMap f)
    (hloc : ∀ x, ∃ U, x ∈ U ∧ IsConvexChart f U) (v : E) : IsPreconnected (f ⁻¹' {v}) := by
  set e := toEuclidean (E := E)
  have h := isPreconnected_preimage_singleton_of_strictConvexSpace (f := e ∘ f)
    (e.toHomeomorph.isProperMap.comp hf) (exists_isConvexChart_continuousLinearEquiv_comp hloc e)
    (e v)
  convert h using 1
  ext x
  simp

end IsProperMap
