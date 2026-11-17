/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import TauCeti.Analysis.Complex.PolynomialHull.Basic
public import TauCeti.Topology.FilledIn
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Complex.Runge.Approximation
import TauCeti.Analysis.Complex.Runge.SimpleFraction
import TauCeti.Analysis.Convex.Caratheodory
import TauCeti.Analysis.Normed.Module.FilledHull
import TauCeti.Topology.ConnectedComponents

/-!
# Holomorphic hulls in the complex plane

The *holomorphic hull* `TauCeti.holomorphicHull Ω K` of a subset `K ⊆ ℂ` relative to a set `Ω ⊆ ℂ`
consists of all points `z ∈ Ω` at which every holomorphic function on `Ω` satisfies every real
modulus bound it satisfies on `K`. For compact `K ⊆ Ω`, this is the set of `z ∈ Ω` with
`|f(z)| ≤ max_K |f|` for all `f` holomorphic on `Ω`, and the universal-bound formulation forces
`holomorphicHull Ω ∅ = ∅` automatically.

## Main declarations and results

* `TauCeti.holomorphicHull`: the `Ω`-holomorphic hull of `K`, with extensivity
  (`TauCeti.subset_holomorphicHull`), monotonicity in `K` (`TauCeti.holomorphicHull_mono`) and in
  `Ω` (`TauCeti.holomorphicHull_mono_domain`), idempotence
  (`TauCeti.holomorphicHull_holomorphicHull`), and point separation
  (`TauCeti.exists_differentiableOn_norm_lt_one_lt_of_notMem_holomorphicHull`).
* **Convexity, distance, and compactness:**
  `TauCeti.holomorphicHull_subset_closedConvexHull` bounds the hull inside `closedConvexHull ℝ K`
  using complex Hahn–Banach separation (`RCLike.geometric_hahn_banach_closed_point`) and
  exponentials, giving `TauCeti.holomorphicHull_subset_convexHull` for compact `K` and
  `TauCeti.isBounded_holomorphicHull` for bounded `K`. Testing with `(w - ζ)⁻¹` for `ζ ∉ Ω` yields
  `TauCeti.infEDist_le_edist_of_mem_holomorphicHull` and equality of extended distances to `Ωᶜ`
  (`TauCeti.iInf_infEDist_holomorphicHull_compl`), whence closedness
  (`TauCeti.isClosed_holomorphicHull`) and compactness (`TauCeti.isCompact_holomorphicHull`)
  without requiring openness of `Ω` or Runge approximation.
* **Topological fill characterization:**
  `TauCeti.mem_holomorphicHull_of_isBounded_connectedComponentIn` places every bounded component of
  `Ω \ K` whose closure stays in `Ω` inside the hull via the maximum modulus principle, giving
  `TauCeti.isFilledIn_holomorphicHull`. Conversely, for open `Ω` and compact `K ⊆ Ω`,
  simple-fraction Runge approximation (`TauCeti.IsFilledIn.exists_differentiableOn_norm_inv_sub_lt`)
  yields `TauCeti.holomorphicHull_eq_fill`: `holomorphicHull Ω K` is the union of `K` and the
  relatively compact connected components of `Ω \ K` in `Ω`. Hence `holomorphicHull Ω K = K` is
  equivalent to `TauCeti.IsFilledIn K Ω` (`TauCeti.holomorphicHull_eq_self_iff_isFilledIn`) and to
  Runge approximability
  (`TauCeti.holomorphicHull_eq_self_iff_forall_exists_differentiableOn_norm_sub_lt`).
* **Global comparison (`Ω = univ`):**
  For compact `K`, `holomorphicHull univ K = filledHull K`
  (`TauCeti.holomorphicHull_univ_eq_filledHull`). For any bounded `K` and `[Nonempty ι]`,
  `holomorphicHull univ K` agrees with the preimage of
  `TauCeti.polynomialHull (Function.const ι '' K)`
  (`TauCeti.holomorphicHull_univ_eq_preimage_polynomialHull`), identifying polynomial convexity of
  `Function.const ι '' K` for compact `K` with filledness in `univ`
  (`TauCeti.isPolynomiallyConvex_image_const_iff_isFilledIn_univ`) and with connectedness of `Kᶜ`
  (`TauCeti.isPolynomiallyConvex_image_const_iff_isConnected_compl`).

## References

* A. Rainer, *Advanced Complex Analysis*, Lemma 11.3, pp. 27–28.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, §1.3 and §2.7.
-/

public section

open Bornology Filter Metric Set Topology
open scoped ENNReal Polynomial

namespace TauCeti

/-! ### Definition and basic properties -/

/-- The `Ω`-holomorphic hull of `K ⊆ ℂ`: all points `z ∈ Ω` at which every function holomorphic on
`Ω` satisfies every real modulus bound it satisfies on `K`. -/
def holomorphicHull (Ω K : Set ℂ) : Set ℂ :=
  {z ∈ Ω | ∀ (f : ℂ → ℂ) (c : ℝ), DifferentiableOn ℂ f Ω → (∀ w ∈ K, ‖f w‖ ≤ c) → ‖f z‖ ≤ c}

variable {Ω Ω₁ Ω₂ K L : Set ℂ} {z : ℂ}

theorem mem_holomorphicHull_iff :
    z ∈ holomorphicHull Ω K ↔
      z ∈ Ω ∧ ∀ (f : ℂ → ℂ) (c : ℝ), DifferentiableOn ℂ f Ω → (∀ w ∈ K, ‖f w‖ ≤ c) → ‖f z‖ ≤ c :=
  Iff.rfl

theorem holomorphicHull_subset (Ω K : Set ℂ) : holomorphicHull Ω K ⊆ Ω :=
  fun _ hz ↦ hz.1

theorem subset_holomorphicHull (hKΩ : K ⊆ Ω) : K ⊆ holomorphicHull Ω K :=
  fun _ hz ↦ ⟨hKΩ hz, fun _ _ _ hc ↦ hc _ hz⟩

@[gcongr]
theorem holomorphicHull_mono (h : K ⊆ L) : holomorphicHull Ω K ⊆ holomorphicHull Ω L :=
  fun _ hz ↦ ⟨hz.1, fun f c hf hc ↦ hz.2 f c hf fun w hw ↦ hc w (h hw)⟩

@[gcongr]
theorem holomorphicHull_mono_domain (h : Ω₁ ⊆ Ω₂) : holomorphicHull Ω₁ K ⊆ holomorphicHull Ω₂ K :=
  fun _ hz ↦ ⟨h hz.1, fun f c hf hc ↦ hz.2 f c (hf.mono h) hc⟩

@[simp]
theorem holomorphicHull_empty (Ω : Set ℂ) : holomorphicHull Ω ∅ = ∅ :=
  eq_empty_of_forall_notMem fun _ hz ↦
    (hz.2 (fun _ ↦ 1) 0 (differentiableOn_const 1) (by simp)).not_gt (by simp)

/-- Taking the holomorphic hull is idempotent. -/
@[simp]
theorem holomorphicHull_holomorphicHull (Ω K : Set ℂ) :
    holomorphicHull Ω (holomorphicHull Ω K) = holomorphicHull Ω K :=
  (subset_holomorphicHull (holomorphicHull_subset Ω K)).antisymm' fun _ hz ↦
    ⟨hz.1, fun f c hf hc ↦ hz.2 f c hf fun _ hw ↦ hw.2 f c hf hc⟩

/-- A point of `Ω` outside `holomorphicHull Ω K` is separated from `K` by a function holomorphic on
`Ω` with modulus `< 1` on `K` and `> 1` at the point. -/
theorem exists_differentiableOn_norm_lt_one_lt_of_notMem_holomorphicHull (hzΩ : z ∈ Ω)
    (hz : z ∉ holomorphicHull Ω K) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f Ω ∧ (∀ w ∈ K, ‖f w‖ < 1) ∧ 1 < ‖f z‖ := by
  simp only [mem_holomorphicHull_iff, hzΩ, true_and, not_forall, not_le, exists_prop] at hz
  obtain ⟨f, c, hf, hfK, hcz⟩ := hz
  set s := ‖f z‖
  rcases (norm_nonneg (f z)).eq_or_lt with hs | hs
  · have hK : ∀ w ∈ K, False := fun w hw ↦
      ((norm_nonneg _).trans (hfK w hw)).not_gt (hs ▸ hcz)
    exact ⟨fun _ ↦ 2, differentiableOn_const 2, fun w hw ↦ (hK w hw).elim, by norm_num⟩
  set a := max c (s / 2)
  have has : a < s := max_lt hcz (half_lt_self hs)
  have hr : 0 < 2 / (a + s) := by positivity
  have hnorm (w : ℂ) : ‖((2 / (a + s) : ℝ) : ℂ) * f w‖ = 2 * ‖f w‖ / (a + s) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le, div_mul_eq_mul_div]
  refine ⟨fun w ↦ ((2 / (a + s) : ℝ) : ℂ) * f w, (differentiableOn_const _).mul hf,
    fun w hw ↦ ?_, ?_⟩
  · rw [hnorm, div_lt_one (by positivity)]
    linarith [(hfK w hw).trans (le_max_left c (s / 2))]
  · rw [hnorm, one_lt_div (by positivity)]
    linarith

/-- A subset `K ⊆ Ω` equals its `Ω`-holomorphic hull if and only if every point of `Ω \ K` is
separated from `K` by a function holomorphic on `Ω` of modulus `< 1` on `K` and `> 1` at the
point. -/
theorem holomorphicHull_eq_self_iff_forall_notMem_exists_differentiableOn_norm_lt_one_lt
    (hKΩ : K ⊆ Ω) :
    holomorphicHull Ω K = K ↔
      ∀ z ∈ Ω \ K, ∃ f : ℂ → ℂ, DifferentiableOn ℂ f Ω ∧ (∀ w ∈ K, ‖f w‖ < 1) ∧ 1 < ‖f z‖ := by
  refine ⟨fun h z hz ↦ exists_differentiableOn_norm_lt_one_lt_of_notMem_holomorphicHull hz.1
    (h.symm ▸ hz.2), fun h ↦ Subset.antisymm (fun z hz ↦ by_contra fun hzK ↦ ?_)
    (subset_holomorphicHull hKΩ)⟩
  obtain ⟨f, hf, hfK, hfz⟩ := h z ⟨hz.1, hzK⟩
  exact (hz.2 f 1 hf fun w hw ↦ (hfK w hw).le).not_gt hfz

/-- If a function holomorphic on `Ω` and continuous on a compact set `K` has strictly smaller
modulus at every point of `K` than at `z`, then `z ∉ holomorphicHull Ω K`. -/
theorem _root_.IsCompact.notMem_holomorphicHull_of_forall_norm_lt (hK : IsCompact K)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω) (hfc : ContinuousOn f K)
    (h : ∀ w ∈ K, ‖f w‖ < ‖f z‖) :
    z ∉ holomorphicHull Ω K := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨w₀, hw₀, hmax⟩ := hK.exists_isMaxOn hne hfc.norm
  exact fun hz ↦ (hz.2 f _ hf fun w hw ↦ hmax hw).not_gt (h w₀ hw₀)

/-! ### Convexity, distance to the complement, and compactness -/

/-- The holomorphic hull of any set lies in its closed convex hull. -/
theorem holomorphicHull_subset_closedConvexHull (Ω K : Set ℂ) :
    holomorphicHull Ω K ⊆ closedConvexHull ℝ K := by
  intro z hz
  by_contra hzC
  obtain ⟨φ, u, hφK, hφz⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ)
    convex_closedConvexHull isClosed_closedConvexHull hzC
  have hle : ‖Complex.exp (φ z)‖ ≤ Real.exp u :=
    hz.2 (fun w ↦ Complex.exp (φ w)) (Real.exp u)
      (Complex.differentiable_exp.comp φ.differentiable).differentiableOn fun w hw ↦ by
        rw [Complex.norm_exp]
        exact Real.exp_le_exp.mpr (hφK w (subset_closedConvexHull hw)).le
  rw [Complex.norm_exp, Real.exp_le_exp] at hle
  exact hle.not_gt hφz

/-- The holomorphic hull of a compact set lies in its convex hull. -/
theorem holomorphicHull_subset_convexHull (hK : IsCompact K) :
    holomorphicHull Ω K ⊆ convexHull ℝ K :=
  (holomorphicHull_subset_closedConvexHull Ω K).trans <|
    closedConvexHull_min (subset_convexHull ℝ K) (convex_convexHull ℝ K) hK.convexHull.isClosed

/-- The holomorphic hull of a bounded set is bounded. -/
theorem isBounded_holomorphicHull (hK : IsBounded K) : IsBounded (holomorphicHull Ω K) :=
  (isBounded_closedConvexHull.mpr hK).subset (holomorphicHull_subset_closedConvexHull Ω K)

/-- No point of `holomorphicHull Ω K` is strictly closer to a point `ζ ∉ Ω` than `K` is. -/
theorem infEDist_le_edist_of_mem_holomorphicHull {ζ : ℂ} (hz : z ∈ holomorphicHull Ω K)
    (hζ : ζ ∉ Ω) : infEDist ζ K ≤ edist z ζ := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨r, -, hzr, hrK⟩ := ENNReal.lt_iff_exists_real_btwn.mp hlt
  have hne : z ≠ ζ := fun h ↦ hζ (h ▸ hz.1)
  have hdist_lt : ‖z - ζ‖ < r := by
    rwa [edist_dist, dist_eq_norm, ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg _)] at hzr
  have hr : 0 < r := (norm_pos_iff.mpr (sub_ne_zero.mpr hne)).trans hdist_lt
  have hf : DifferentiableOn ℂ (fun w : ℂ ↦ (w - ζ)⁻¹) Ω :=
    (differentiableOn_id.sub (differentiableOn_const ζ)).inv fun w hw h ↦
      hζ (sub_eq_zero.mp (by simpa using h) ▸ hw)
  have hbound : ∀ w ∈ K, ‖(w - ζ)⁻¹‖ ≤ r⁻¹ := fun w hw ↦ by
    have hrw : r ≤ ‖w - ζ‖ := by
      have hle : ENNReal.ofReal r ≤ edist ζ w := hrK.le.trans (infEDist_le_edist_of_mem hw)
      rw [edist_dist, dist_comm, dist_eq_norm, ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)] at hle
      exact hle
    rw [norm_inv]
    exact inv_anti₀ hr hrw
  have hzle := hz.2 (fun w ↦ (w - ζ)⁻¹) r⁻¹ hf hbound
  rw [norm_inv, inv_le_inv₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hne)) hr] at hzle
  exact hdist_lt.not_ge hzle

/-- Taking the `Ω`-holomorphic hull of `K ⊆ Ω` preserves the extended distance to `Ωᶜ`. -/
theorem iInf_infEDist_holomorphicHull_compl (hKΩ : K ⊆ Ω) :
    (⨅ z ∈ holomorphicHull Ω K, infEDist z Ωᶜ) = ⨅ z ∈ K, infEDist z Ωᶜ := by
  refine le_antisymm (biInf_mono (subset_holomorphicHull hKΩ)) ?_
  refine le_iInf₂ fun z hz ↦ le_infEDist.2 fun ζ hζ ↦ ?_
  refine le_trans ?_ (infEDist_le_edist_of_mem_holomorphicHull hz hζ)
  refine le_infEDist.2 fun w hw ↦ ?_
  calc (⨅ y ∈ K, infEDist y Ωᶜ) ≤ infEDist w Ωᶜ := biInf_le _ hw
    _ ≤ edist w ζ := infEDist_le_edist_of_mem hζ
    _ = edist ζ w := edist_comm w ζ

/-- The holomorphic hull of a closed subset `K ⊆ Ω` is closed in `ℂ`, without requiring `Ω` to be
open. -/
theorem isClosed_holomorphicHull (hK : IsClosed K) (hKΩ : K ⊆ Ω) :
    IsClosed (holomorphicHull Ω K) := by
  rw [← closure_subset_iff_isClosed]
  intro z hz
  have hzΩ : z ∈ Ω := by
    by_contra hzΩ
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hK.isOpen_compl z fun hzK ↦ hzΩ (hKΩ hzK)
    obtain ⟨y, hy, hyz⟩ := Metric.mem_closure_iff.mp hz r hr
    have hle : ENNReal.ofReal r ≤ infEDist z K := le_infEDist.2 fun w hw ↦ by
      rw [edist_dist, ENNReal.ofReal_le_ofReal_iff dist_nonneg]
      by_contra hlt
      exact hball (mem_ball.mpr (by rw [dist_comm]; exact not_le.mp hlt)) hw
    have hlt : edist y z < ENNReal.ofReal r := by
      rw [edist_dist, dist_comm]
      exact (ENNReal.ofReal_lt_ofReal_iff hr).mpr hyz
    exact (hle.trans (infEDist_le_edist_of_mem_holomorphicHull hy hzΩ)).not_gt hlt
  refine ⟨hzΩ, fun f c hf hfK ↦ ?_⟩
  have hcont : ContinuousWithinAt (fun w ↦ ‖f w‖) (holomorphicHull Ω K) z :=
    ((hf.continuousOn z hzΩ).norm).mono (holomorphicHull_subset Ω K)
  have : (𝓝[holomorphicHull Ω K] z).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hz
  exact le_of_tendsto hcont (eventually_nhdsWithin_of_forall fun w hw ↦ hw.2 f c hf hfK)

/-- The holomorphic hull of a compact subset `K ⊆ Ω` is compact, without requiring `Ω` to be
open. -/
theorem isCompact_holomorphicHull (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    IsCompact (holomorphicHull Ω K) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_holomorphicHull hK.isClosed hKΩ)
    (isBounded_holomorphicHull hK.isBounded)

/-! ### Topological fill characterization -/

/-- **Maximum-modulus inclusion.** Every point `z ∈ Ω` whose connected component in `Ω \ K` is
bounded with closure contained in `Ω` belongs to `holomorphicHull Ω K`. -/
theorem mem_holomorphicHull_of_isBounded_connectedComponentIn (hΩ : IsOpen Ω) (hz : z ∈ Ω)
    (hbd : IsBounded (connectedComponentIn (Ω \ K) z))
    (hsub : closure (connectedComponentIn (Ω \ K) z) ⊆ Ω) : z ∈ holomorphicHull Ω K := by
  by_cases hzK : z ∈ K
  · exact ⟨hz, fun _ _ _ hc ↦ hc z hzK⟩
  refine ⟨hz, fun f c hf hfK ↦ ?_⟩
  set C := connectedComponentIn (Ω \ K) z
  have hdiff : DiffContOnCl ℂ f C :=
    ⟨hf.mono (subset_closure.trans hsub), hf.continuousOn.mono hsub⟩
  refine Complex.norm_le_of_forall_mem_frontier_norm_le hbd hdiff (fun w hw ↦ ?_)
    (subset_closure (mem_connectedComponentIn ⟨hz, hzK⟩))
  have hwΩ : w ∈ Ω := hsub hw.1
  have hwK : w ∈ closure K := by_contra fun hwK ↦
    frontier_connectedComponentIn_subset_compl_interior z hw
      (interior_maximal (sdiff_subset_sdiff_right subset_closure) (hΩ.sdiff isClosed_closure)
        ⟨hwΩ, hwK⟩)
  have hcont : ContinuousAt (fun y ↦ ‖f y‖) w :=
    (hf.continuousOn.continuousAt (hΩ.mem_nhds hwΩ)).norm
  have : (𝓝[K] w).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hwK
  exact le_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds)
    (eventually_nhdsWithin_of_forall hfK)

/-- The holomorphic hull of any set in an open `Ω ⊆ ℂ` is filled in `Ω`. -/
theorem isFilledIn_holomorphicHull (hΩ : IsOpen Ω) (K : Set ℂ) :
    IsFilledIn (holomorphicHull Ω K) Ω := by
  rw [isFilledIn_iff]
  rintro z ⟨hzΩ, hzH⟩ ⟨hcpt, hsub⟩
  have hmem := mem_holomorphicHull_of_isBounded_connectedComponentIn hΩ hzΩ
    (hcpt.isBounded.subset subset_closure) hsub
  rw [holomorphicHull_holomorphicHull] at hmem
  exact hzH hmem

/-- Filling `K` with the relatively compact connected components of `Ω \ K` in `Ω` produces a
compact set filled in `Ω`. -/
private theorem isCompact_and_isFilledIn_fill (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    let L := K ∪ {z ∈ Ω \ K | IsCompact (closure (connectedComponentIn (Ω \ K) z)) ∧
      closure (connectedComponentIn (Ω \ K) z) ⊆ Ω}
    L ⊆ holomorphicHull Ω K ∧ IsCompact L ∧ IsFilledIn L Ω := by
  intro L
  have hLsub : L ⊆ holomorphicHull Ω K := by
    rintro z (hzK | ⟨⟨hzΩ, -⟩, hcpt, hsub⟩)
    · exact subset_holomorphicHull hKΩ hzK
    · exact mem_holomorphicHull_of_isBounded_connectedComponentIn hΩ hzΩ
        (hcpt.isBounded.subset subset_closure) hsub
  have hcomp_sub : ∀ x ∈ Ω \ L, connectedComponentIn (Ω \ K) x ⊆ Ω \ L := by
    rintro x ⟨hxΩ, hxL⟩ y hy
    have hxy : connectedComponentIn (Ω \ K) y = connectedComponentIn (Ω \ K) x :=
      (connectedComponentIn_eq hy).symm
    have hyK : y ∈ Ω \ K := connectedComponentIn_subset _ _ hy
    refine ⟨hyK.1, ?_⟩
    rintro (hyK' | ⟨-, hrel⟩)
    · exact hyK.2 hyK'
    · exact hxL (Or.inr ⟨⟨hxΩ, fun hxK ↦ hxL (Or.inl hxK)⟩, hxy ▸ hrel⟩)
  have hopen : IsOpen (Ω \ L) := isOpen_iff_mem_nhds.mpr fun x hx ↦
    Filter.mem_of_superset
      (((hΩ.sdiff hK.isClosed).connectedComponentIn).mem_nhds
        (mem_connectedComponentIn ⟨hx.1, fun hxK ↦ hx.2 (Or.inl hxK)⟩))
      (hcomp_sub x hx)
  have hLeq : L = holomorphicHull Ω K \ (Ω \ L) := by
    refine Subset.antisymm (fun z hz ↦ ⟨hLsub hz, fun h ↦ h.2 hz⟩) fun z ⟨hzH, hznot⟩ ↦ ?_
    by_contra hzL
    exact hznot ⟨hzH.1, hzL⟩
  have hL_cpt : IsCompact L := hLeq ▸ (isCompact_holomorphicHull hK hKΩ).diff hopen
  have hL_fill : IsFilledIn L Ω := by
    rw [isFilledIn_iff]
    rintro x ⟨hxΩ, hxL⟩ hrel
    have hceq : connectedComponentIn (Ω \ L) x = connectedComponentIn (Ω \ K) x :=
      Subset.antisymm (connectedComponentIn_mono x (sdiff_subset_sdiff_right subset_union_left))
        (isPreconnected_connectedComponentIn.subset_connectedComponentIn
          (mem_connectedComponentIn ⟨hxΩ, fun hxK ↦ hxL (Or.inl hxK)⟩) (hcomp_sub x ⟨hxΩ, hxL⟩))
    rw [hceq] at hrel
    exact hxL (Or.inr ⟨⟨hxΩ, fun hxK ↦ hxL (Or.inl hxK)⟩, hrel⟩)
  exact ⟨hLsub, hL_cpt, hL_fill⟩

/-- **Topological characterization of the holomorphic hull.** For open `Ω ⊆ ℂ` and compact
`K ⊆ Ω`, `holomorphicHull Ω K` is the union of `K` and all connected components of `Ω \ K` that
are relatively compact in `Ω`. -/
theorem holomorphicHull_eq_fill (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    holomorphicHull Ω K =
      K ∪ {z ∈ Ω \ K | IsCompact (closure (connectedComponentIn (Ω \ K) z)) ∧
        closure (connectedComponentIn (Ω \ K) z) ⊆ Ω} := by
  set L := K ∪ {z ∈ Ω \ K | IsCompact (closure (connectedComponentIn (Ω \ K) z)) ∧
    closure (connectedComponentIn (Ω \ K) z) ⊆ Ω}
  obtain ⟨hLsub, hLcpt, hLfill⟩ := isCompact_and_isFilledIn_fill hΩ hK hKΩ
  refine Subset.antisymm (fun a ha ↦ by_contra fun haL ↦ ?_) hLsub
  have hLΩ : L ⊆ Ω := hLsub.trans (holomorphicHull_subset Ω K)
  obtain ⟨R, hR⟩ := hLcpt.isBounded.subset_closedBall a
  set M : ℝ := max R 1
  have hM : 0 < M := by positivity
  obtain ⟨g, hg, happrox⟩ := hLfill.exists_differentiableOn_norm_inv_sub_lt hΩ hLcpt hLΩ haL
    (ε := (2 * M)⁻¹) (by positivity)
  set h : ℂ → ℂ := fun w ↦ 1 - (w - a) * g w
  have hh : DifferentiableOn ℂ h Ω :=
    (differentiableOn_const 1).sub ((differentiableOn_id.sub (differentiableOn_const a)).mul hg)
  have hbound : ∀ w ∈ K, ‖h w‖ ≤ 1 / 2 := fun w hw ↦ by
    have hwL : w ∈ L := Or.inl hw
    have hwa : w - a ≠ 0 := sub_ne_zero.mpr fun heq ↦ haL (heq ▸ hwL)
    have hhw : h w = (w - a) * ((w - a)⁻¹ - g w) := by
      simp only [h, mul_sub, mul_inv_cancel₀ hwa]
    have hnorm_wa : ‖w - a‖ ≤ M := by
      rw [← dist_eq_norm]
      exact (mem_closedBall.mp (hR hwL)).trans (le_max_left R 1)
    rw [hhw, norm_mul]
    calc ‖w - a‖ * ‖(w - a)⁻¹ - g w‖ ≤ M * (2 * M)⁻¹ :=
          mul_le_mul hnorm_wa (happrox w hwL).le (norm_nonneg _) hM.le
      _ = 1 / 2 := by field_simp [hM.ne']
  have ha_le := ha.2 h (1 / 2) hh hbound
  simp [h] at ha_le
  linarith

/-- For open `Ω ⊆ ℂ` and compact `K ⊆ Ω`, `K` equals its `Ω`-holomorphic hull if and only if `K` is
filled in `Ω`. -/
theorem holomorphicHull_eq_self_iff_isFilledIn (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    holomorphicHull Ω K = K ↔ IsFilledIn K Ω := by
  constructor
  · intro h
    rw [← h]
    exact isFilledIn_holomorphicHull hΩ K
  · intro hfill
    rw [holomorphicHull_eq_fill hΩ hK hKΩ, union_eq_left]
    rintro z ⟨hz, hrel⟩
    exact (isFilledIn_iff.mp hfill z hz hrel).elim

/-- For open `Ω ⊆ ℂ` and compact `K ⊆ Ω`, `K` equals its `Ω`-holomorphic hull if and only if every
function holomorphic on an open neighbourhood of `K` can be uniformly approximated on `K` by
functions holomorphic on `Ω`. -/
theorem holomorphicHull_eq_self_iff_forall_exists_differentiableOn_norm_sub_lt (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    holomorphicHull Ω K = K ↔
      ∀ U : Set ℂ, IsOpen U → K ⊆ U → ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U →
        ∀ ε > 0, ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ K, ‖f z - g z‖ < ε :=
  (holomorphicHull_eq_self_iff_isFilledIn hΩ hK hKΩ).trans
    (isFilledIn_iff_forall_exists_differentiableOn_norm_sub_lt hΩ hK hKΩ)

/-! ### Comparison with filled hulls and polynomial hulls for `Ω = univ` -/

/-- The holomorphic hull of a compact set `K ⊆ ℂ` in the whole plane is its filled hull. -/
theorem holomorphicHull_univ_eq_filledHull (hK : IsCompact K) :
    holomorphicHull univ K = filledHull K := by
  rw [holomorphicHull_eq_fill isOpen_univ hK (subset_univ K)]
  ext z
  simp only [mem_union, mem_ofPred_eq, subset_univ, and_true, ← compl_eq_univ_sdiff]
  constructor
  · rintro (hzK | ⟨-, hcpt⟩)
    · exact subset_filledHull hzK
    · exact mem_filledHull_iff.mpr (hcpt.isBounded.subset subset_closure)
  · intro hz
    by_cases hzK : z ∈ K
    · exact Or.inl hzK
    · exact Or.inr ⟨hzK, (mem_filledHull_iff.mp hz).isCompact_closure⟩

/-- For any bounded set `K ⊆ ℂ` and nonempty index type `ι`, the holomorphic hull of `K` in `ℂ`
is the preimage of `TauCeti.polynomialHull (Function.const ι '' K)` under `Function.const ι`. -/
theorem holomorphicHull_univ_eq_preimage_polynomialHull {ι : Type*} [Nonempty ι]
    (hK : IsBounded K) :
    holomorphicHull univ K = Function.const ι ⁻¹' polynomialHull (Function.const ι '' K) := by
  ext z
  simp only [mem_holomorphicHull_iff, mem_univ, true_and, mem_preimage, mem_polynomialHull_iff]
  constructor
  · intro hz P c hPK
    set p : ℂ[X] := MvPolynomial.eval₂ Polynomial.C (fun _ ↦ Polynomial.X) P
    have heval (w : ℂ) : p.eval w = MvPolynomial.eval (Function.const ι w) P := by
      rw [← Polynomial.coe_evalRingHom, MvPolynomial.hom_eval₂]
      have hC : (Polynomial.evalRingHom w).comp Polynomial.C = RingHom.id ℂ := by ext x; simp
      rw [hC]; simp only [Polynomial.coe_evalRingHom, Polynomial.eval_X, MvPolynomial.eval₂_id]; rfl
    rw [← heval z]
    exact hz (fun w ↦ p.eval w) c (Polynomial.differentiable p).differentiableOn fun w hw ↦ by
      rw [heval w]
      exact hPK _ ⟨w, hw, rfl⟩
  · intro hz f c hf hfK
    by_contra hlt
    rw [not_le] at hlt
    set ε : ℝ := (‖f z‖ - c) / 3 with hε_def
    have hε : 0 < ε := by positivity
    obtain ⟨p, hp⟩ := (differentiableOn_univ.mp hf).exists_polynomial_norm_sub_lt (hK.insert z) hε
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    set P : MvPolynomial ι ℂ := p.eval₂ MvPolynomial.C (MvPolynomial.X i₀)
    have heval (w : ℂ) : MvPolynomial.eval (Function.const ι w) P = p.eval w := by
      rw [Polynomial.hom_eval₂]
      have hC : (MvPolynomial.eval (Function.const ι w)).comp MvPolynomial.C = RingHom.id ℂ := by
        ext x; simp
      rw [hC, MvPolynomial.eval_X]; rfl
    have hPbound : ∀ u ∈ Function.const ι '' K, ‖MvPolynomial.eval u P‖ ≤ c + ε := by
      rintro _ ⟨w, hw, rfl⟩
      rw [heval w]
      have h1 : ‖p.eval w‖ ≤ ‖f w‖ + ‖f w - p.eval w‖ := by
        simpa [sub_eq_add_neg] using norm_le_norm_add_norm_sub (f w) (p.eval w)
      linarith [hfK w hw, hp w (mem_insert_of_mem z hw)]
    have hPz : ‖p.eval z‖ ≤ c + ε := by
      rw [← heval z]
      exact hz P (c + ε) hPbound
    have hfz : ‖f z‖ ≤ ‖p.eval z‖ + ‖f z - p.eval z‖ := norm_le_insert' (f z) (p.eval z)
    linarith [hp z (mem_insert z K), hε_def]

/-- For a bounded set `K ⊆ ℂ` and nonempty index type `ι`, `Function.const ι '' K` is polynomially
convex if and only if `holomorphicHull univ K = K`. -/
theorem isPolynomiallyConvex_image_const_iff_holomorphicHull_univ_eq {ι : Type*} [Nonempty ι]
    (hK : IsBounded K) :
    IsPolynomiallyConvex (Function.const ι '' K) ↔ holomorphicHull univ K = K := by
  have hsub_range : polynomialHull (Function.const ι '' K) ⊆ range (Function.const ι) := by
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    intro u hu
    refine ⟨u i₀, funext fun i ↦ ?_⟩
    have h0 : ‖MvPolynomial.eval u (MvPolynomial.X i - MvPolynomial.X i₀ : MvPolynomial ι ℂ)‖ ≤ 0 :=
      (mem_polynomialHull_iff.mp hu) _ 0 fun _ ⟨w, _, hw⟩ ↦ by subst hw; simp
    simp only [map_sub, MvPolynomial.eval_X, norm_le_zero_iff, sub_eq_zero] at h0
    exact h0.symm
  rw [isPolynomiallyConvex_iff, ← image_preimage_eq_of_subset hsub_range,
    Set.image_subset_image_iff Function.const_injective,
    ← holomorphicHull_univ_eq_preimage_polynomialHull hK]
  exact ⟨fun h ↦ h.antisymm (subset_holomorphicHull (subset_univ K)), fun h ↦ h.subset⟩

/-- For a compact set `K ⊆ ℂ` and nonempty index type `ι`, `Function.const ι '' K` is polynomially
convex if and only if `K` is filled in `univ`. -/
theorem isPolynomiallyConvex_image_const_iff_isFilledIn_univ {ι : Type*} [Nonempty ι]
    (hK : IsCompact K) :
    IsPolynomiallyConvex (Function.const ι '' K) ↔ IsFilledIn K univ :=
  (isPolynomiallyConvex_image_const_iff_holomorphicHull_univ_eq hK.isBounded).trans
    (holomorphicHull_eq_self_iff_isFilledIn isOpen_univ hK (subset_univ K))

/-- For a compact set `K ⊆ ℂ` and nonempty index type `ι`, `Function.const ι '' K` is polynomially
convex if and only if `Kᶜ` is connected. -/
theorem isPolynomiallyConvex_image_const_iff_isConnected_compl {ι : Type*} [Nonempty ι]
    (hK : IsCompact K) :
    IsPolynomiallyConvex (Function.const ι '' K) ↔ IsConnected Kᶜ := by
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]; exact Nat.one_lt_ofNat
  exact ((isPolynomiallyConvex_image_const_iff_isFilledIn_univ hK).trans
    (isFilledIn_univ_iff hK.isClosed)).trans
      (filledHull_eq_self_iff_isConnected_compl hrank hK.isBounded)

end TauCeti
