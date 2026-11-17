/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import TauCeti.Analysis.Complex.PolynomialHull.Basic
public import TauCeti.Topology.FilledIn
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Topology.Algebra.Module.Equiv.Pi
import Mathlib.Topology.Order.Compact
import TauCeti.Analysis.Complex.PowerSeries.Approximation
import TauCeti.Analysis.Convex.Caratheodory
import TauCeti.Analysis.Normed.Module.Convex
import TauCeti.Topology.ConnectedComponents

/-!
# Holomorphic hulls

The *holomorphic hull* `TauCeti.holomorphicHull Ω K` of a subset `K` in a subset `Ω` of a complex
normed space `E` is the set of points `z ∈ Ω` at which every holomorphic `f : E → ℂ` on `Ω`
satisfies every real norm bound that it satisfies on `K`. For compact `K ⊆ Ω` these are the
points `z ∈ Ω` with `‖f z‖ ≤ sup_{w ∈ K} ‖f w‖` for every `f` holomorphic on `Ω`; quantifying
over all real bounds makes `holomorphicHull Ω ∅ = ∅` without a separate case.

In any complex normed space, taking the holomorphic hull is extensive (for `K ⊆ Ω`), monotone in
both `Ω` and `K`, idempotent, functorial under complex-linear homeomorphisms, and relatively closed
in open `Ω`. By the geometric Hahn–Banach separation theorem applied to exponential functions
`w ↦ exp (L w)` for `L ∈ StrongDual ℂ E`, the holomorphic hull always lies in the closed real
convex hull `closedConvexHull ℝ K` (hence in `convexHull ℝ K` when `K` is compact in finite
dimension), so hulls of bounded sets are bounded. In a nontrivial space, the maximum modulus
principle places the closure of every bounded connected component of `Ω \ K` whose closure stays in
`Ω` inside `holomorphicHull Ω K`; consequently `holomorphicHull Ω K` is always filled in `Ω`.

In one complex variable (`E = ℂ`), every open set is holomorphically convex: testing against
`z ↦ (z - ζ)⁻¹` for `ζ ∉ Ω` shows that `holomorphicHull Ω K` stays at least as far from each
`ζ ∉ Ω` as `K` does (`TauCeti.infEDist_le_edist_of_mem_holomorphicHull`), preserving the
extended distance to `Ωᶜ` (`TauCeti.iInf_edist_holomorphicHull_compl_eq`) and making
`holomorphicHull Ω K` compact whenever `Ω` is open and `K ⊆ Ω` is compact
(`IsCompact.holomorphicHull`). For `Ω = univ` and bounded `K`, approximating entire functions on
bounded sets by Taylor polynomials identifies `holomorphicHull univ K` with
`TauCeti.polynomialHull`. The exact identification of `holomorphicHull Ω K` with the union of `K`
and the relatively compact components of `Ω \ K` uses Runge's approximation theorem and is proved
in `TauCeti/Analysis/Complex/Runge/Approximation.lean`.

## Main definitions

* `TauCeti.holomorphicHull Ω K`: the holomorphic hull of `K` inside `Ω`.

## Main results

* `TauCeti.holomorphicHull_subset`, `TauCeti.subset_holomorphicHull`,
  `TauCeti.holomorphicHull_mono`, `TauCeti.holomorphicHull_mono_left`,
  `TauCeti.holomorphicHull_holomorphicHull`: basic closure properties.
* `TauCeti.isOpen_sdiff_holomorphicHull`, `TauCeti.closure_holomorphicHull_inter`: relative
  closedness in an open ambient set.
* `TauCeti.exists_differentiableOn_norm_lt_one_lt_of_notMem_holomorphicHull` and
  `IsCompact.notMem_holomorphicHull_of_forall_norm_lt`: separation of points outside the hull.
* `TauCeti.holomorphicHull_subset_closedConvexHull` and
  `IsCompact.holomorphicHull_subset_convexHull`: inclusion in the closed real convex hull and, for
  compact sets in finite dimension, in the real convex hull.
* `TauCeti.closure_connectedComponentIn_subset_holomorphicHull` and
  `TauCeti.isFilledIn_holomorphicHull`: maximum-principle inclusion of relatively compact
  complementary components and filledness of every holomorphic hull.
* `TauCeti.infEDist_le_edist_of_mem_holomorphicHull`,
  `TauCeti.iInf_edist_holomorphicHull_compl_eq`, and `IsCompact.holomorphicHull`: boundary distance
  preservation and compactness in `ℂ`.
* `TauCeti.holomorphicHull_univ_eq_polynomialHull` and
  `TauCeti.holomorphicHull_univ_eq_preimage_polynomialHull`: equality with `TauCeti.polynomialHull`
  for bounded subsets of `ℂ`.

## References

* A. Rainer, *Advanced Complex Analysis*, Lemma 11.3.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Theorem 1.3.9 and §2.7.
-/

public section

open Bornology Metric Set
open scoped Topology

namespace TauCeti

section NormedSpace

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The **holomorphic hull** of `K` inside `Ω`: the points `z ∈ Ω` at which every function
`f : E → ℂ` holomorphic on `Ω` satisfies every real norm bound that it satisfies on `K`. For
compact `K ⊆ Ω`, these are the points of `Ω` where `‖f z‖ ≤ sup_{w ∈ K} ‖f w‖` for every `f`
holomorphic on `Ω`; quantifying over all real bounds makes the hull of `∅` empty. -/
def holomorphicHull (Ω K : Set E) : Set E :=
  {z | z ∈ Ω ∧ ∀ f : E → ℂ, DifferentiableOn ℂ f Ω →
    ∀ B : ℝ, (∀ w ∈ K, ‖f w‖ ≤ B) → ‖f z‖ ≤ B}

variable {Ω Ω₁ Ω₂ K L : Set E} {z : E}

theorem mem_holomorphicHull_iff :
    z ∈ holomorphicHull Ω K ↔
      z ∈ Ω ∧ ∀ f : E → ℂ, DifferentiableOn ℂ f Ω →
        ∀ B : ℝ, (∀ w ∈ K, ‖f w‖ ≤ B) → ‖f z‖ ≤ B :=
  Iff.rfl

theorem holomorphicHull_subset (Ω K : Set E) : holomorphicHull Ω K ⊆ Ω :=
  fun _ hz ↦ hz.1

theorem subset_holomorphicHull (hKΩ : K ⊆ Ω) : K ⊆ holomorphicHull Ω K :=
  fun z hz ↦ ⟨hKΩ hz, fun _ _ _ hB ↦ hB z hz⟩

@[simp]
theorem holomorphicHull_empty (Ω : Set E) : holomorphicHull Ω ∅ = ∅ :=
  eq_empty_of_forall_notMem fun _ hz ↦
    (hz.2 0 (differentiableOn_const 0) (-1) (by simp)).not_gt (by simp)

@[simp]
theorem holomorphicHull_empty_left (K : Set E) : holomorphicHull (∅ : Set E) K = ∅ :=
  subset_empty_iff.1 (holomorphicHull_subset ∅ K)

@[gcongr]
theorem holomorphicHull_mono (h : K ⊆ L) : holomorphicHull Ω K ⊆ holomorphicHull Ω L :=
  fun _ hz ↦ ⟨hz.1, fun f hf B hB ↦ hz.2 f hf B fun w hw ↦ hB w (h hw)⟩

@[gcongr]
theorem holomorphicHull_mono_left (h : Ω₁ ⊆ Ω₂) :
    holomorphicHull Ω₁ K ⊆ holomorphicHull Ω₂ K :=
  fun _ hz ↦ ⟨h hz.1, fun f hf B hB ↦ hz.2 f (hf.mono h) B hB⟩

/-- Taking the holomorphic hull in a fixed ambient set `Ω` is idempotent. -/
@[simp]
theorem holomorphicHull_holomorphicHull (Ω K : Set E) :
    holomorphicHull Ω (holomorphicHull Ω K) = holomorphicHull Ω K :=
  Subset.antisymm
    (fun _ hz ↦ ⟨hz.1, fun f hf B hB ↦ hz.2 f hf B fun _ hw ↦ hw.2 f hf B hB⟩)
    (subset_holomorphicHull (holomorphicHull_subset Ω K))

/-- For an open ambient set `Ω`, the complement of `holomorphicHull Ω K` in `Ω` is open. -/
theorem isOpen_sdiff_holomorphicHull (hΩ : IsOpen Ω) (K : Set E) :
    IsOpen (Ω \ holomorphicHull Ω K) := by
  refine isOpen_iff_mem_nhds.2 fun x hx ↦ ?_
  have hx' := hx.2
  simp only [mem_holomorphicHull_iff, hx.1, true_and, not_forall, not_le, exists_prop] at hx'
  obtain ⟨f, hf, B, hKB, hBx⟩ := hx'
  have hcont : ContinuousAt (fun w ↦ ‖f w‖) x :=
    (hf.continuousOn.continuousAt (hΩ.mem_nhds hx.1)).norm
  refine Filter.mem_of_superset
    (Filter.inter_mem (hΩ.mem_nhds hx.1) (hcont.eventually (Ioi_mem_nhds hBx))) ?_
  rintro w ⟨hwΩ, hwB⟩
  exact ⟨hwΩ, fun hwH ↦ (hwH.2 f hf B hKB).not_gt hwB⟩

/-- For an open ambient set `Ω`, the holomorphic hull is relatively closed in `Ω`. -/
theorem closure_holomorphicHull_inter (hΩ : IsOpen Ω) (K : Set E) :
    closure (holomorphicHull Ω K) ∩ Ω = holomorphicHull Ω K := by
  refine Subset.antisymm (fun x ⟨hxcl, hxΩ⟩ ↦ by_contra fun hxH ↦ ?_)
    (subset_inter subset_closure (holomorphicHull_subset Ω K))
  obtain ⟨y, hy, hyH⟩ :=
    mem_closure_iff.1 hxcl _ (isOpen_sdiff_holomorphicHull hΩ K) ⟨hxΩ, hxH⟩
  exact hy.2 hyH

/-- A point of `Ω` outside `holomorphicHull Ω K` is separated from `K` by a function holomorphic
on `Ω` of modulus `< 1` on `K` and `> 1` at the point. -/
theorem exists_differentiableOn_norm_lt_one_lt_of_notMem_holomorphicHull
    (hzΩ : z ∈ Ω) (hz : z ∉ holomorphicHull Ω K) :
    ∃ f : E → ℂ, DifferentiableOn ℂ f Ω ∧
      (∀ w ∈ K, ‖f w‖ < 1) ∧ 1 < ‖f z‖ := by
  simp only [mem_holomorphicHull_iff, hzΩ, true_and, not_forall, not_le, exists_prop] at hz
  obtain ⟨f, hf, B, hKB, hBz⟩ := hz
  set s := ‖f z‖
  rcases (norm_nonneg (f z)).eq_or_lt with hs | hs
  · have hK : ∀ w ∈ K, False := fun w hw ↦
      ((norm_nonneg _).trans (hKB w hw)).not_gt (hs ▸ hBz)
    exact ⟨fun _ ↦ 2, differentiableOn_const 2, fun w hw ↦ (hK w hw).elim, by norm_num⟩
  set a := max B (s / 2)
  have has : a < s := max_lt hBz (half_lt_self hs)
  have hr : 0 < 2 / (a + s) := by positivity
  refine ⟨fun w ↦ ((2 / (a + s) : ℝ) : ℂ) * f w, (differentiableOn_const _).mul hf,
    fun w hw ↦ ?_, ?_⟩
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le, div_mul_eq_mul_div,
      div_lt_one (by positivity)]
    linarith [(hKB w hw).trans (le_max_left B (s / 2))]
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le, div_mul_eq_mul_div,
      one_lt_div (by positivity)]
    linarith

/-- A subset `K ⊆ Ω` equals its holomorphic hull in `Ω` exactly when every point of `Ω \ K` is
separated from `K` by a function holomorphic on `Ω` of modulus `< 1` on `K` and `> 1` at the
point. -/
theorem holomorphicHull_eq_self_iff_forall_notMem_exists_differentiableOn_norm_lt_one_lt
    (hKΩ : K ⊆ Ω) :
    holomorphicHull Ω K = K ↔
      ∀ z ∈ Ω \ K, ∃ f : E → ℂ, DifferentiableOn ℂ f Ω ∧
        (∀ w ∈ K, ‖f w‖ < 1) ∧ 1 < ‖f z‖ := by
  refine ⟨fun h z hz ↦ exists_differentiableOn_norm_lt_one_lt_of_notMem_holomorphicHull hz.1
    (h.symm ▸ hz.2), fun h ↦ Subset.antisymm (fun z hz ↦ by_contra fun hzK ↦ ?_)
    (subset_holomorphicHull hKΩ)⟩
  obtain ⟨f, hf, hK, hfz⟩ := h z ⟨hz.1, hzK⟩
  exact (hz.2 f hf 1 fun w hw ↦ (hK w hw).le).not_gt hfz

/-- If a function holomorphic on `Ω` has strictly smaller modulus at every point of a compact set
`K ⊆ Ω` than at `z`, then `z` does not lie in `holomorphicHull Ω K`. -/
theorem _root_.IsCompact.notMem_holomorphicHull_of_forall_norm_lt (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) {f : E → ℂ} (hf : DifferentiableOn ℂ f Ω)
    (hlt : ∀ w ∈ K, ‖f w‖ < ‖f z‖) : z ∉ holomorphicHull Ω K := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨w₀, hw₀, hmax⟩ := hK.exists_isMaxOn hne (hf.continuousOn.mono hKΩ).norm
  exact fun hz ↦ (hz.2 f hf _ fun w hw ↦ hmax hw).not_gt (hlt w₀ hw₀)

/-- Continuous complex-linear equivalences commute with taking holomorphic hulls. -/
theorem image_holomorphicHull (e : E ≃L[ℂ] F) (Ω K : Set E) :
    e '' holomorphicHull Ω K = holomorphicHull (e '' Ω) (e '' K) := by
  ext y
  refine ⟨?_, ?_⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨mem_image_of_mem e hx.1, fun f hf B hB ↦ ?_⟩
    exact hx.2 (f ∘ e) (hf.comp e.differentiable.differentiableOn (mapsTo_image e Ω)) B
      fun w hw ↦ hB (e w) (mem_image_of_mem e hw)
  · rintro ⟨⟨x, hxΩ, rfl⟩, hy⟩
    refine ⟨x, ⟨hxΩ, fun f hf B hB ↦ ?_⟩, rfl⟩
    have hcomp : DifferentiableOn ℂ (f ∘ e.symm) (e '' Ω) :=
      hf.comp e.symm.differentiable.differentiableOn fun _ ⟨w, hw, hw'⟩ ↦ by
        rw [← hw', e.symm_apply_apply]; exact hw
    have h := hy (f ∘ e.symm) hcomp B (by
      rintro _ ⟨w, hw, rfl⟩
      simpa using hB w hw)
    simpa using h

/-- Preimages under continuous complex-linear equivalences commute with taking holomorphic hulls. -/
theorem preimage_holomorphicHull (e : E ≃L[ℂ] F) (Ω K : Set F) :
    e ⁻¹' holomorphicHull Ω K = holomorphicHull (e ⁻¹' Ω) (e ⁻¹' K) := by
  have h := congrArg (fun s ↦ e ⁻¹' s) (image_holomorphicHull e (e ⁻¹' Ω) (e ⁻¹' K))
  rw [e.surjective.image_preimage, e.surjective.image_preimage, e.injective.preimage_image] at h
  exact h.symm

/-- **Convex hull bound.** The holomorphic hull of any set `K` in any ambient set `Ω` lies in its
closed real convex hull. -/
theorem holomorphicHull_subset_closedConvexHull (Ω K : Set E) :
    holomorphicHull Ω K ⊆ closedConvexHull ℝ K := by
  intro z hz
  by_contra hzC
  obtain ⟨L, u, hLK, huL⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ)
    convex_closedConvexHull isClosed_closedConvexHull hzC
  have hf : DifferentiableOn ℂ (fun w ↦ Complex.exp (L w)) Ω :=
    (Complex.differentiable_exp.comp L.differentiable).differentiableOn
  have hbound : ‖Complex.exp (L z)‖ ≤ Real.exp u := hz.2 _ hf (Real.exp u) fun w hw ↦ by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.2 (hLK w (subset_closedConvexHull hw)).le
  rw [Complex.norm_exp, Real.exp_le_exp] at hbound
  exact hbound.not_gt huL

/-- In finite dimension, the holomorphic hull of a compact set lies in its real convex hull. -/
theorem _root_.IsCompact.holomorphicHull_subset_convexHull [FiniteDimensional ℝ E]
    (hK : IsCompact K) (Ω : Set E) : holomorphicHull Ω K ⊆ convexHull ℝ K :=
  (holomorphicHull_subset_closedConvexHull Ω K).trans <|
    closedConvexHull_min (subset_convexHull ℝ K) (convex_convexHull ℝ K) hK.convexHull.isClosed

/-- The holomorphic hull of a bounded set is bounded. -/
protected theorem _root_.Bornology.IsBounded.holomorphicHull (hK : IsBounded K) (Ω : Set E) :
    IsBounded (holomorphicHull Ω K) :=
  (isBounded_closedConvexHull.2 hK).subset (holomorphicHull_subset_closedConvexHull Ω K)

/-- **Maximum-principle inclusion.** In a nontrivial complex normed space, if `Ω \ K` is open,
every bounded connected component of `Ω \ K` whose closure stays in `Ω` has its closure contained
in `holomorphicHull Ω K`. -/
theorem closure_connectedComponentIn_subset_holomorphicHull [Nontrivial E]
    (hΩK : IsOpen (Ω \ K)) {x : E} (hb : IsBounded (connectedComponentIn (Ω \ K) x))
    (hsub : closure (connectedComponentIn (Ω \ K) x) ⊆ Ω) :
    closure (connectedComponentIn (Ω \ K) x) ⊆ holomorphicHull Ω K := by
  set C := connectedComponentIn (Ω \ K) x
  have hfr : frontier C ⊆ K := fun y hy ↦ by
    by_contra hyK
    exact frontier_connectedComponentIn_subset_compl hΩK x hy ⟨hsub hy.1, hyK⟩
  refine fun z hz ↦ ⟨hsub hz, fun f hf B hB ↦ ?_⟩
  have hdiff : DiffContOnCl ℂ f C :=
    ⟨hf.mono (subset_closure.trans hsub), hf.continuousOn.mono hsub⟩
  exact Complex.norm_le_of_forall_mem_frontier_norm_le hb hdiff (fun w hw ↦ hB w (hfr hw)) hz

/-- Every bounded connected component of an open `Ω \ K` whose closure stays in `Ω` lies in
`holomorphicHull Ω K`. -/
theorem connectedComponentIn_subset_holomorphicHull [Nontrivial E]
    (hΩK : IsOpen (Ω \ K)) {x : E} (hb : IsBounded (connectedComponentIn (Ω \ K) x))
    (hsub : closure (connectedComponentIn (Ω \ K) x) ⊆ Ω) :
    connectedComponentIn (Ω \ K) x ⊆ holomorphicHull Ω K :=
  subset_closure.trans (closure_connectedComponentIn_subset_holomorphicHull hΩK hb hsub)

/-- Every holomorphic hull in an open subset of a nontrivial complex normed space is filled in that
open set. -/
theorem isFilledIn_holomorphicHull [Nontrivial E] (hΩ : IsOpen Ω) (K : Set E) :
    IsFilledIn (holomorphicHull Ω K) Ω := by
  rw [isFilledIn_iff]
  rintro x hx ⟨hcpt, hsub⟩
  have hmem := connectedComponentIn_subset_holomorphicHull (isOpen_sdiff_holomorphicHull hΩ K)
    (hcpt.isBounded.subset subset_closure) hsub (mem_connectedComponentIn hx)
  rw [holomorphicHull_holomorphicHull] at hmem
  exact hx.2 hmem

end NormedSpace

section Complex

variable {Ω K : Set ℂ}

/-- **Distance to an exterior point.** Every point of `holomorphicHull Ω K` is at least as far from
any `ζ ∉ Ω` as `K` is, tested through the holomorphic function `z ↦ (z - ζ)⁻¹`. -/
theorem infEDist_le_edist_of_mem_holomorphicHull {z ζ : ℂ}
    (hz : z ∈ holomorphicHull Ω K) (hζ : ζ ∉ Ω) :
    infEDist ζ K ≤ edist z ζ := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · simp at hz
  by_contra hlt
  rw [not_le] at hlt
  have htop : infEDist ζ K ≠ ⊤ := infEDist_ne_top hKne
  set d := (infEDist ζ K).toReal
  have hd_lt : dist z ζ < d := by
    rw [← ENNReal.toReal_ofReal dist_nonneg, ← edist_dist]
    exact ENNReal.toReal_strict_mono htop hlt
  have hd_pos : 0 < d := dist_nonneg.trans_lt hd_lt
  have hdiff : DifferentiableOn ℂ (fun w : ℂ ↦ (w - ζ)⁻¹) Ω :=
    (differentiableOn_id.sub (differentiableOn_const ζ)).inv fun w hw h ↦
      hζ ((sub_eq_zero.1 h : w = ζ) ▸ hw)
  have hbound : ‖(z - ζ)⁻¹‖ ≤ d⁻¹ := hz.2 _ hdiff d⁻¹ fun w hw ↦ by
    rw [norm_inv, ← dist_eq_norm]
    have hdw : d ≤ dist w ζ := by
      rw [← ENNReal.ofReal_le_ofReal_iff dist_nonneg, ← edist_dist, ENNReal.ofReal_toReal htop,
        edist_comm]
      exact infEDist_le_edist_of_mem hw
    exact inv_anti₀ hd_pos hdw
  have hzζ : 0 < dist z ζ := dist_pos.2 fun h ↦ hζ (h ▸ hz.1)
  rw [norm_inv, ← dist_eq_norm, inv_le_inv₀ hzζ hd_pos] at hbound
  exact hd_lt.not_ge hbound

/-- **Boundary distance preservation.** Taking the holomorphic hull in `Ω ⊆ ℂ` preserves the
extended distance to `Ωᶜ`. Empty infima equal `⊤`, covering `K = ∅` and `Ω = univ`. -/
theorem iInf_edist_holomorphicHull_compl_eq (hKΩ : K ⊆ Ω) :
    (⨅ z ∈ holomorphicHull Ω K, ⨅ ζ ∈ Ωᶜ, edist z ζ) =
      ⨅ z ∈ K, ⨅ ζ ∈ Ωᶜ, edist z ζ := by
  refine le_antisymm (biInf_mono (subset_holomorphicHull hKΩ)) ?_
  refine le_iInf₂ fun z hz ↦ le_iInf₂ fun ζ hζ ↦ ?_
  calc ⨅ w ∈ K, ⨅ ξ ∈ Ωᶜ, edist w ξ
      ≤ ⨅ w ∈ K, edist w ζ := iInf₂_mono fun w _ ↦ iInf₂_le ζ hζ
    _ = infEDist ζ K := by simp only [infEDist, edist_comm]
    _ ≤ edist z ζ := infEDist_le_edist_of_mem_holomorphicHull hz hζ

/-- **Compactness of the holomorphic hull in `ℂ`.** Every open subset of `ℂ` is holomorphically
convex: the holomorphic hull of a compact subset `K ⊆ Ω` is compact. -/
protected theorem _root_.IsCompact.holomorphicHull (hK : IsCompact K) (hΩ : IsOpen Ω)
    (hKΩ : K ⊆ Ω) : IsCompact (holomorphicHull Ω K) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ (hK.isBounded.holomorphicHull Ω)
  have hcl : closure (holomorphicHull Ω K) ⊆ Ω := by
    intro ζ hζcl
    by_contra hζΩ
    have hζK : ζ ∈ Kᶜ := fun h ↦ hζΩ (hKΩ h)
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hK.isClosed.isOpen_compl ζ hζK
    have hr_le : ENNReal.ofReal r ≤ infEDist ζ K := by
      rw [le_infEDist]
      intro w hw
      rw [edist_dist, ENNReal.ofReal_le_ofReal_iff dist_nonneg]
      by_contra hlt
      exact hball (mem_ball'.2 (not_le.1 hlt)) hw
    obtain ⟨z, hzH, hzr⟩ := Metric.mem_closure_iff.1 hζcl r hr
    have hle := hr_le.trans (infEDist_le_edist_of_mem_holomorphicHull hzH hζΩ)
    rw [edist_dist, ENNReal.ofReal_le_ofReal_iff dist_nonneg, dist_comm] at hle
    exact hzr.not_ge hle
  rw [← closure_subset_iff_isClosed]
  calc closure (holomorphicHull Ω K)
      ⊆ closure (holomorphicHull Ω K) ∩ Ω := subset_inter Subset.rfl hcl
    _ = holomorphicHull Ω K := closure_holomorphicHull_inter hΩ K

/-- For a bounded subset of `Fin 1 → ℂ`, the holomorphic hull in the whole space coincides with
`TauCeti.polynomialHull`. Boundedness is essential: for the unbounded set `ℝ ⊆ ℂ`, the polynomial
hull is all of `ℂ`, whereas `exp (i z)` and `exp (-i z)` cut the holomorphic hull down to `ℝ`. -/
theorem holomorphicHull_univ_eq_polynomialHull {K : Set (Fin 1 → ℂ)} (hK : IsBounded K) :
    holomorphicHull univ K = polynomialHull K := by
  refine Subset.antisymm (fun z hz ↦ mem_polynomialHull_iff.2 fun p B hB ↦ ?_)
    (fun z hz ↦ ⟨mem_univ z, fun f hf B hB ↦ ?_⟩)
  · exact hz.2 (fun w ↦ MvPolynomial.eval w p)
      (fun w _ ↦
        (AnalyticOnNhd.eval_mvPolynomial p w trivial).differentiableAt.differentiableWithinAt)
      B hB
  · -- Transfer `f` to `ℂ` via `e = funUnique`, approximate on `insert (e z) (e '' K)` by a
    -- univariate polynomial, and lift it to `MvPolynomial (Fin 1) ℂ`.
    let e : (Fin 1 → ℂ) ≃L[ℂ] ℂ := ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ
    have hf' : Differentiable ℂ (f ∘ e.symm) :=
      (differentiableOn_univ.1 hf).comp e.symm.differentiable
    have hK' : IsBounded (insert (e z) (e '' K)) :=
      (e.toContinuousLinearMap.lipschitzWith.isBounded_image hK).insert (e z)
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    obtain ⟨p, hp⟩ := hf'.exists_polynomial_norm_sub_lt hK' (half_pos hε)
    set q : MvPolynomial (Fin 1) ℂ := Polynomial.aeval (MvPolynomial.X 0) p
    have hq (w : Fin 1 → ℂ) : MvPolynomial.eval w q = p.eval (e w) := by
      dsimp only [q]
      rw [← MvPolynomial.aeval_eq_eval, ← Polynomial.aeval_algHom_apply]
      simp [e, ContinuousLinearEquiv.coe_funUnique]
    have hqK : ∀ w ∈ K, ‖MvPolynomial.eval w q‖ ≤ B + ε / 2 := fun w hw ↦ by
      rw [hq w]
      have hfw : ‖f w - p.eval (e w)‖ < ε / 2 := by
        simpa [Function.comp_apply, e.symm_apply_apply] using
          hp (e w) (mem_insert_of_mem _ (mem_image_of_mem e hw))
      calc ‖p.eval (e w)‖ = ‖f w - (f w - p.eval (e w))‖ := by ring_nf
        _ ≤ ‖f w‖ + ‖f w - p.eval (e w)‖ := norm_sub_le _ _
        _ ≤ B + ε / 2 := add_le_add (hB w hw) hfw.le
    have hqz : ‖p.eval (e z)‖ ≤ B + ε / 2 := by
      rw [← hq z]
      exact mem_polynomialHull_iff.1 hz q (B + ε / 2) hqK
    have hfz : ‖f z - p.eval (e z)‖ < ε / 2 := by
      simpa [Function.comp_apply, e.symm_apply_apply] using hp (e z) (mem_insert _ _)
    calc ‖f z‖ = ‖p.eval (e z) + (f z - p.eval (e z))‖ := by ring_nf
      _ ≤ ‖p.eval (e z)‖ + ‖f z - p.eval (e z)‖ := norm_add_le _ _
      _ ≤ (B + ε / 2) + ε / 2 := add_le_add hqz hfz.le
      _ = B + ε := by ring

/-- For a bounded subset `K ⊆ ℂ`, the entire holomorphic hull of `K` is the preimage of
`TauCeti.polynomialHull` under the canonical embedding `z ↦ (fun _ : Fin 1 ↦ z)`. -/
theorem holomorphicHull_univ_eq_preimage_polynomialHull (hK : IsBounded K) :
    holomorphicHull univ K =
      Function.const (Fin 1) ⁻¹' polynomialHull (Function.const (Fin 1) '' K) := by
  let e : ℂ ≃L[ℂ] (Fin 1 → ℂ) := (ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ).symm
  have heK : IsBounded (e '' K) := e.toContinuousLinearMap.lipschitzWith.isBounded_image hK
  have h1 := preimage_holomorphicHull e univ (e '' K)
  rw [preimage_univ, e.injective.preimage_image, holomorphicHull_univ_eq_polynomialHull heK] at h1
  simpa [e, ContinuousLinearEquiv.coe_funUnique_symm] using h1.symm

/-- A bounded subset `K ⊆ ℂ` equals its entire holomorphic hull exactly when its image in
`Fin 1 → ℂ` is polynomially convex. -/
theorem holomorphicHull_univ_eq_self_iff_isPolynomiallyConvex (hK : IsBounded K) :
    holomorphicHull univ K = K ↔ IsPolynomiallyConvex (Function.const (Fin 1) '' K) := by
  let e : ℂ ≃L[ℂ] (Fin 1 → ℂ) := (ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ).symm
  rw [isPolynomiallyConvex_iff_polynomialHull_eq,
    holomorphicHull_univ_eq_preimage_polynomialHull hK]
  have he : (e : ℂ → Fin 1 → ℂ) = Function.const (Fin 1) :=
    ContinuousLinearEquiv.coe_funUnique_symm
  rw [← he]
  exact ⟨fun h ↦ by nth_rw 2 [← h]; exact (e.surjective.image_preimage _).symm,
    fun h ↦ by rw [h, e.injective.preimage_image]⟩

end Complex

end TauCeti
