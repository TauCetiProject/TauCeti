/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Analysis.Complex.PolynomialHull.Basic
public import TauCeti.Analysis.Complex.Runge.Approximation
public import TauCeti.Analysis.Normed.Module.FilledHull
public import TauCeti.Topology.FilledIn
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Connected.LocallyConnected
import TauCeti.Topology.ConnectedComponents

/-!
# Holomorphic hulls and their topological characterization

For a subset `K` of a planar set `Ω ⊆ ℂ`, the **`Ω`-holomorphic hull** `TauCeti.holomorphicHull Ω K`
consists of the points `z ∈ Ω` at which every `Ω`-holomorphic function `f : ℂ → ℂ` satisfies every
modulus bound `‖f z‖ ≤ B` that holds across `K`.

The first half of the file develops the properties of `TauCeti.holomorphicHull` that follow
directly from global holomorphicity without Runge approximation:
* Hahn–Banach separation paired with `z ↦ exp (φ z)` places `TauCeti.holomorphicHull Ω K` inside
  `closedConvexHull ℝ K` (`TauCeti.holomorphicHull_subset_closedConvexHull`), preserving
  boundedness and diameter.
* Testing against `(w - a)⁻¹` for points `a ∉ Ω` shows that passing from `K ⊆ Ω` to
  `TauCeti.holomorphicHull Ω K` preserves the extended distance to `Ωᶜ`
  (`TauCeti.biInf_edist_compl_holomorphicHull`).
* The maximum modulus principle places every point of `Ω` whose connected component in `Ω \ K` has
  compact closure inside `Ω` into `TauCeti.holomorphicHull Ω K`
  (`TauCeti.mem_holomorphicHull_of_isCompact_closure_connectedComponentIn`).

Combining that maximum-modulus inclusion with Runge point separation
(`TauCeti.IsRungeCompactPair.exists_differentiableOn_norm_lt_one_lt`) and compactness of the
topological fill in the open subspace `↥Ω`
(`IsCompact.isCompact_setOf_isCompact_closure_connectedComponentIn_compl`) yields the exact
topological description `TauCeti.holomorphicHull_eq_fill`: for open `Ω` and compact `K ⊆ Ω`,
`TauCeti.holomorphicHull Ω K` is compact and equals `K` together with all connected components of
`Ω \ K` having compact closure in `Ω`. In particular `(Ω, holomorphicHull Ω K)` is always a
compact Runge pair (`IsOpen.isRungeCompactPair_holomorphicHull`), and for open `Ω` and compact `K`,
`(Ω, K)` is a compact Runge pair if and only if `holomorphicHull Ω K = K`
(`TauCeti.isRungeCompactPair_iff_holomorphicHull_eq_self`).

On `Ω = Set.univ`, `TauCeti.holomorphicHull Set.univ K` coincides both with the topological filled
hull `TauCeti.filledHull K` (`IsCompact.holomorphicHull_univ_eq_filledHull`) and with the pullback
of the one-variable polynomial hull `TauCeti.polynomialHull`
(`TauCeti.holomorphicHull_univ_eq_preimage_polynomialHull`), giving the classical polynomial Runge
theorem on `ℂ` (`IsCompact.isPreconnected_compl_iff_polynomial_approximation`).

## Main definitions

* `TauCeti.holomorphicHull`: the `Ω`-holomorphic hull of `K ⊆ ℂ`.

## Main results

* `TauCeti.holomorphicHull_subset_closedConvexHull`: `holomorphicHull Ω K ⊆ closedConvexHull ℝ K`.
* `TauCeti.biInf_edist_compl_holomorphicHull`: taking the `Ω`-holomorphic hull preserves the
  extended distance to `Ωᶜ`.
* `TauCeti.holomorphicHull_eq_fill`: compactness and exact topological formula for
  `holomorphicHull Ω K`.
* `IsOpen.isRungeCompactPair_holomorphicHull`: `(Ω, holomorphicHull Ω K)` is a compact Runge pair.
* `TauCeti.isRungeCompactPair_iff_holomorphicHull_eq_self`: `(Ω, K)` is a compact Runge pair iff
  `holomorphicHull Ω K = K`.
* `TauCeti.holomorphicHull_univ_eq_preimage_polynomialHull` and
  `IsCompact.isPreconnected_compl_iff_polynomial_approximation`: comparison with
  `TauCeti.polynomialHull` and polynomial Runge approximation on `ℂ`.

## References

* W. Rudin, *Real and Complex Analysis*, 3rd ed., McGraw-Hill, 1987, Theorem 13.9.
* J. B. Conway, *Functions of One Complex Variable I*, 2nd ed., Springer, 1978, §VIII.1.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Theorem 1.3.3.
-/

public section

open Bornology Filter Metric Set Topology

namespace TauCeti

/-- The **`Ω`-holomorphic hull** of `K`: points of `Ω` where every `Ω`-holomorphic function obeys
every modulus bound valid on `K`. For compact `K ⊆ Ω` this is the set of `z ∈ Ω` satisfying
`|f(z)| ≤ sup_K |f|` for all `f ∈ O(Ω)` (stated in bound form to avoid `sSup` conventions on empty
sets). -/
def holomorphicHull (Ω K : Set ℂ) : Set ℂ :=
  {z | z ∈ Ω ∧
    ∀ f : ℂ → ℂ, DifferentiableOn ℂ f Ω → ∀ B : ℝ, (∀ w ∈ K, ‖f w‖ ≤ B) → ‖f z‖ ≤ B}

theorem holomorphicHull_def (Ω K : Set ℂ) :
    holomorphicHull Ω K =
      {z | z ∈ Ω ∧
        ∀ f : ℂ → ℂ, DifferentiableOn ℂ f Ω → ∀ B : ℝ, (∀ w ∈ K, ‖f w‖ ≤ B) → ‖f z‖ ≤ B} :=
  (rfl)

@[simp]
theorem mem_holomorphicHull_iff {Ω K : Set ℂ} {z : ℂ} :
    z ∈ holomorphicHull Ω K ↔
      z ∈ Ω ∧ ∀ f : ℂ → ℂ, DifferentiableOn ℂ f Ω → ∀ B : ℝ, (∀ w ∈ K, ‖f w‖ ≤ B) → ‖f z‖ ≤ B :=
  Iff.rfl

/-- The `Ω`-holomorphic hull of `K` is contained in `Ω`. -/
theorem holomorphicHull_subset {Ω K : Set ℂ} : holomorphicHull Ω K ⊆ Ω :=
  fun _ hz ↦ hz.1

/-- Any subset `K ⊆ Ω` is contained in its `Ω`-holomorphic hull. -/
theorem subset_holomorphicHull {Ω K : Set ℂ} (hKΩ : K ⊆ Ω) : K ⊆ holomorphicHull Ω K :=
  fun z hz ↦ ⟨hKΩ hz, fun _ _ _ hB ↦ hB z hz⟩

@[simp]
theorem holomorphicHull_empty (Ω : Set ℂ) : holomorphicHull Ω ∅ = ∅ :=
  eq_empty_of_forall_notMem fun _ hz ↦
    (hz.2 (fun _ ↦ 1) (differentiableOn_const 1) 0 (by simp)).not_gt (by simp)

@[gcongr]
theorem holomorphicHull_mono {Ω K L : Set ℂ} (hKL : K ⊆ L) :
    holomorphicHull Ω K ⊆ holomorphicHull Ω L :=
  fun _ hz ↦ ⟨hz.1, fun f hf B hB ↦ hz.2 f hf B fun w hw ↦ hB w (hKL hw)⟩

@[gcongr]
theorem holomorphicHull_mono_left {Ω₁ Ω₂ K : Set ℂ} (hΩ : Ω₁ ⊆ Ω₂) :
    holomorphicHull Ω₁ K ⊆ holomorphicHull Ω₂ K :=
  fun _ hz ↦ ⟨hΩ hz.1, fun f hf B hB ↦ hz.2 f (hf.mono hΩ) B hB⟩

/-- The `Ω`-holomorphic hull of an intersection lies inside the intersection of the hulls. -/
theorem holomorphicHull_inter_subset {Ω K L : Set ℂ} :
    holomorphicHull Ω (K ∩ L) ⊆ holomorphicHull Ω K ∩ holomorphicHull Ω L :=
  subset_inter (holomorphicHull_mono inter_subset_left) (holomorphicHull_mono inter_subset_right)

/-- Taking the `Ω`-holomorphic hull is idempotent. -/
@[simp]
theorem holomorphicHull_holomorphicHull (Ω K : Set ℂ) :
    holomorphicHull Ω (holomorphicHull Ω K) = holomorphicHull Ω K :=
  (subset_holomorphicHull holomorphicHull_subset).antisymm'
    fun _ hz ↦ ⟨hz.1, fun f hf B hB ↦ hz.2 f hf B fun _ hw ↦ hw.2 f hf B hB⟩

/-- Every point outside `holomorphicHull Ω K` (with `K ⊆ Ω`) is strictly separated from `K` by an
`Ω`-holomorphic function of modulus `< 1` on `K` and `> 1` at `a`. -/
theorem exists_differentiableOn_norm_lt_one_lt_of_notMem_holomorphicHull {Ω K : Set ℂ}
    (hKΩ : K ⊆ Ω) {a : ℂ} (ha : a ∉ holomorphicHull Ω K) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ (∀ z ∈ K, ‖g z‖ < 1) ∧ 1 < ‖g a‖ := by
  by_cases haΩ : a ∈ Ω
  · simp only [mem_holomorphicHull_iff, haΩ, true_and, not_forall, not_le] at ha
    obtain ⟨f, hf, B, hB, hfa⟩ := ha
    rcases lt_or_ge B 0 with hB0 | hB0
    · refine ⟨fun _ ↦ (2 : ℂ), differentiableOn_const 2, fun z hz ↦ ?_, by norm_num⟩
      exact absurd ((norm_nonneg (f z)).trans (hB z hz)) hB0.not_ge
    · set c : ℝ := (B + ‖f a‖) / 2 with hc_def
      have hc_pos : 0 < c := by linarith [hc_def]
      refine ⟨fun z ↦ (c : ℂ)⁻¹ * f z, hf.const_mul _, fun z hz ↦ ?_, ?_⟩
      · rw [norm_mul, norm_inv, Complex.norm_of_nonneg hc_pos.le, inv_mul_eq_div,
          div_lt_one hc_pos]
        linarith [hB z hz, hc_def]
      · rw [norm_mul, norm_inv, Complex.norm_of_nonneg hc_pos.le, inv_mul_eq_div,
          one_lt_div hc_pos]
        linarith [hc_def]
  · refine ⟨({a} : Set ℂ).indicator fun _ ↦ (2 : ℂ),
      (differentiableOn_const 0).congr fun z hz ↦
        indicator_of_notMem (fun hza : z ∈ ({a} : Set ℂ) ↦ haΩ (mem_singleton_iff.mp hza ▸ hz)) _,
      fun z hz ↦ ?_, ?_⟩
    · rw [indicator_of_notMem
        (fun hza : z ∈ ({a} : Set ℂ) ↦ haΩ (mem_singleton_iff.mp hza ▸ hKΩ hz))]
      simp
    · rw [indicator_of_mem (mem_singleton a)]
      norm_num

section DirectProperties

/-- **Convex-hull bound.** Every `Ω`-holomorphic hull lies inside the closed real convex hull of
`K`: a point outside `closedConvexHull ℝ K` is separated from it by the real part of a continuous
`ℂ`-linear functional `φ`, and the entire function `w ↦ exp (φ w)` converts that real-part bound
into a modulus separation. -/
theorem holomorphicHull_subset_closedConvexHull (Ω K : Set ℂ) :
    holomorphicHull Ω K ⊆ closedConvexHull ℝ K := by
  intro z hz
  by_contra hzC
  obtain ⟨φ, u, hφK, huz⟩ :=
    RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ) convex_closedConvexHull
      isClosed_closedConvexHull hzC
  simp only [RCLike.re_to_complex] at hφK huz
  have hle : ‖Complex.exp (φ z)‖ ≤ Real.exp u :=
    hz.2 (fun w ↦ Complex.exp (φ w))
      (Complex.differentiable_exp.comp φ.differentiable).differentiableOn (Real.exp u)
      fun w hw ↦ by
        rw [Complex.norm_exp]
        exact Real.exp_le_exp.mpr (hφK w (subset_closedConvexHull hw)).le
  rw [Complex.norm_exp] at hle
  exact (Real.exp_lt_exp.mpr huz).not_ge hle

/-- The `Ω`-holomorphic hull of a bounded set is bounded. -/
theorem isBounded_holomorphicHull {Ω K : Set ℂ} (hK : IsBounded K) :
    IsBounded (holomorphicHull Ω K) :=
  (isBounded_closedConvexHull.mpr hK).subset (holomorphicHull_subset_closedConvexHull Ω K)

@[simp]
theorem diam_holomorphicHull {Ω K : Set ℂ} (hKΩ : K ⊆ Ω) :
    diam (holomorphicHull Ω K) = diam K := by
  by_cases hK : IsBounded K
  · refine le_antisymm ?_ (diam_mono (subset_holomorphicHull hKΩ) (isBounded_holomorphicHull hK))
    exact (diam_mono (holomorphicHull_subset_closedConvexHull Ω K)
      (isBounded_closedConvexHull.mpr hK)).trans_eq diam_closedConvexHull
  · have hH : ¬ IsBounded (holomorphicHull Ω K) :=
      fun hb ↦ hK (hb.subset (subset_holomorphicHull hKΩ))
    rw [diam_eq_zero_of_unbounded hH, diam_eq_zero_of_unbounded hK]

/-- Testing `z ∈ holomorphicHull Ω K` against `(w - a)⁻¹` for `a ∉ Ω` transfers any lower bound on
the distance from `K` to `a` to `z`. -/
theorem dist_le_of_mem_holomorphicHull {Ω K : Set ℂ} {z a : ℂ}
    (hz : z ∈ holomorphicHull Ω K) (ha : a ∉ Ω) {r : ℝ}
    (hK : ∀ w ∈ K, r ≤ dist w a) : r ≤ dist z a := by
  rcases le_or_gt r 0 with hr | hr
  · exact hr.trans dist_nonneg
  have hza : 0 < dist z a := dist_pos.mpr fun h0 ↦ ha (h0 ▸ hz.1)
  have hf : DifferentiableOn ℂ (fun w ↦ (w - a)⁻¹) Ω :=
    (differentiableOn_id.fun_sub (differentiableOn_const a)).inv fun w hw ↦
      sub_ne_zero.mpr fun h0 ↦ ha (h0 ▸ hw)
  have hle : ‖(z - a)⁻¹‖ ≤ r⁻¹ := hz.2 _ hf r⁻¹ fun w hw ↦ by
    rw [norm_inv, ← dist_eq_norm]
    exact inv_anti₀ hr (hK w hw)
  rw [norm_inv, ← dist_eq_norm] at hle
  exact (inv_le_inv₀ hza hr).mp hle

/-- For every point `a ∉ Ω` and every `z ∈ holomorphicHull Ω K`, the extended distance from `z` to
`a` is at least `⨅ w ∈ K, edist w a`. -/
theorem iInf_edist_le_of_mem_holomorphicHull {Ω K : Set ℂ} {z a : ℂ}
    (hz : z ∈ holomorphicHull Ω K) (ha : a ∉ Ω) :
    (⨅ w ∈ K, edist w a) ≤ edist z a := by
  have hKne : K.Nonempty := nonempty_iff_ne_empty.mpr fun h0 ↦ by simp [h0] at hz
  obtain ⟨w₀, hw₀⟩ := hKne
  set m : ENNReal := ⨅ w ∈ K, edist w a
  have hm_ne_top : m ≠ ⊤ :=
    ne_top_of_le_ne_top (edist_ne_top w₀ a) (iInf₂_le (f := fun x _ ↦ edist x a) w₀ hw₀)
  have hdist : m.toReal ≤ dist z a :=
    dist_le_of_mem_holomorphicHull hz ha fun w hw ↦ by
      have hw_le : m ≤ edist w a := iInf₂_le (f := fun x _ ↦ edist x a) w hw
      rw [← ENNReal.ofReal_toReal hm_ne_top, edist_dist] at hw_le
      exact (ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp hw_le
  rw [← ENNReal.ofReal_toReal hm_ne_top, edist_dist]
  exact ENNReal.ofReal_le_ofReal hdist

/-- **Distance to `Ωᶜ` is preserved by the holomorphic hull.** For `K ⊆ Ω`, replacing `K` by
`holomorphicHull Ω K` leaves the extended distance to `Ωᶜ` unchanged. -/
theorem biInf_edist_compl_holomorphicHull {Ω K : Set ℂ} (hKΩ : K ⊆ Ω) :
    (⨅ z ∈ holomorphicHull Ω K, ⨅ a ∈ Ωᶜ, edist z a) = ⨅ z ∈ K, ⨅ a ∈ Ωᶜ, edist z a := by
  refine le_antisymm (biInf_mono (subset_holomorphicHull hKΩ)) ?_
  refine le_iInf₂ fun z hz ↦ le_iInf₂ fun a ha ↦ ?_
  refine le_trans ?_ (iInf_edist_le_of_mem_holomorphicHull hz ha)
  exact le_iInf₂ fun w hw ↦
    le_trans (iInf₂_le (f := fun x _ ↦ ⨅ b ∈ Ωᶜ, edist x b) w hw)
      (iInf₂_le (f := fun b _ ↦ edist w b) a ha)

/-- **Maximum-modulus inclusion of relatively compact holes.** If `Ω` is open and the connected
component of `z ∈ Ω` in `Ω \ K` has compact closure contained in `Ω`, then `z` belongs to
`holomorphicHull Ω K`. -/
theorem mem_holomorphicHull_of_isCompact_closure_connectedComponentIn {Ω K : Set ℂ}
    (hΩ : IsOpen Ω) {z : ℂ} (hz : z ∈ Ω)
    (hcpt : IsCompact (closure (connectedComponentIn (Ω \ K) z)))
    (hclΩ : closure (connectedComponentIn (Ω \ K) z) ⊆ Ω) :
    z ∈ holomorphicHull Ω K := by
  by_cases hzK : z ∈ K
  · exact ⟨hz, fun _ _ _ hB ↦ hB z hzK⟩
  refine ⟨hz, fun f hf B hB ↦ ?_⟩
  set C : Set ℂ := connectedComponentIn (Ω \ K) z
  have hC_bdd : IsBounded C := hcpt.isBounded.subset subset_closure
  have hd : DiffContOnCl ℂ f C :=
    ⟨hf.mono (subset_closure.trans hclΩ), hf.continuousOn.mono hclΩ⟩
  have hcl_le : ∀ w ∈ closure (K ∩ Ω) ∩ Ω, ‖f w‖ ≤ B := fun w ⟨hwcl, hwΩ⟩ ↦ by
    have : NeBot (𝓝[K ∩ Ω] w) := mem_closure_iff_nhdsWithin_neBot.mp hwcl
    exact le_of_tendsto ((hf.continuousOn w hwΩ).mono inter_subset_right).norm
      (eventually_nhdsWithin_of_forall fun x hx ↦ hB x hx.1)
  have hfr : ∀ w ∈ frontier C, ‖f w‖ ≤ B := fun w hw ↦ by
    have hwΩ : w ∈ Ω := hclΩ (frontier_subset_closure hw)
    refine hcl_le w ⟨by_contra fun hwcl ↦ ?_, hwΩ⟩
    have hopen : IsOpen (Ω \ closure (K ∩ Ω)) := hΩ.sdiff isClosed_closure
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen w ⟨hwΩ, hwcl⟩
    have hballC : ball w r ⊆ Ω \ K := fun y hy ↦
      ⟨(hball hy).1, fun hyK ↦ (hball hy).2 (subset_closure ⟨hyK, (hball hy).1⟩)⟩
    obtain ⟨y, hyC, hyb⟩ := Metric.mem_closure_iff.mp hw.1 r hr
    have hsubC : ball w r ⊆ C := by
      dsimp only [C] at hyC ⊢
      rw [connectedComponentIn_eq hyC]
      exact (convex_ball w r).isPreconnected.subset_connectedComponentIn
        (mem_ball_comm.mp hyb) hballC
    exact hw.2 (mem_interior.mpr ⟨ball w r, hsubC, isOpen_ball, mem_ball_self hr⟩)
  exact Complex.norm_le_of_forall_mem_frontier_norm_le hC_bdd hd hfr
    (subset_closure (mem_connectedComponentIn ⟨hz, hzK⟩))

end DirectProperties

section TopologicalFill

/-- Internal shorthand for `K` together with the connected components of `Ω \ K` having compact
closure inside `Ω`. -/
private def topologicalFill (Ω K : Set ℂ) : Set ℂ :=
  K ∪ {z | z ∈ Ω \ K ∧ IsCompact (closure (connectedComponentIn (Ω \ K) z)) ∧
    closure (connectedComponentIn (Ω \ K) z) ⊆ Ω}

/-- Under the inclusion `↥Ω → ℂ`, the connected component of `y ∈ ↥Ω \ K'` in `K'ᶜ` maps onto the
connected component of `y.1` in `Ω \ K`. -/
private theorem image_subtype_connectedComponentIn_compl_eq {Ω K : Set ℂ} {y : ↥Ω}
    (hy : (y : ℂ) ∉ K) :
    ((↑) : ↥Ω → ℂ) '' connectedComponentIn (((↑) : ↥Ω → ℂ) ⁻¹' K)ᶜ y =
      connectedComponentIn (Ω \ K) y.1 := by
  set K' : Set ↥Ω := ((↑) : ↥Ω → ℂ) ⁻¹' K
  refine Subset.antisymm ?_ ?_
  · exact (isPreconnected_connectedComponentIn.image _ continuous_subtype_val.continuousOn)
      |>.subset_connectedComponentIn
        (mem_image_of_mem _ (mem_connectedComponentIn hy))
        (by rintro _ ⟨w, hw, rfl⟩; exact ⟨w.2, connectedComponentIn_subset _ _ hw⟩)
  · set C : Set ℂ := connectedComponentIn (Ω \ K) y.1
    have hCΩ : C ⊆ Ω := (connectedComponentIn_subset _ _).trans sdiff_subset
    set P : Set ↥Ω := ((↑) : ↥Ω → ℂ) ⁻¹' C
    have himgP : ((↑) : ↥Ω → ℂ) '' P = C :=
      Subset.antisymm (image_preimage_subset _ _) fun z hz ↦ ⟨⟨z, hCΩ hz⟩, hz, rfl⟩
    have hP_pre : IsPreconnected P :=
      Topology.IsInducing.subtypeVal.isPreconnected_image.mp (himgP.symm ▸
        isPreconnected_connectedComponentIn)
    have hsub : P ⊆ connectedComponentIn K'ᶜ y :=
      hP_pre.subset_connectedComponentIn (mem_connectedComponentIn ⟨y.2, hy⟩)
        fun w hw ↦ (connectedComponentIn_subset _ _ hw).2
    simpa only [himgP] using image_mono (f := ((↑) : ↥Ω → ℂ)) hsub

/-- `topologicalFill Ω K` is the image under `((↑) : ↥Ω → ℂ)` of the points of `↥Ω` whose
connected component in `(((↑) : ↥Ω → ℂ) ⁻¹' K)ᶜ` has compact closure in `↥Ω`. -/
private theorem image_subtype_setOf_isCompact_closure_connectedComponentIn_compl {Ω K : Set ℂ}
    (hKΩ : K ⊆ Ω) :
    ((↑) : ↥Ω → ℂ) ''
        {y : ↥Ω | IsCompact (closure (connectedComponentIn (((↑) : ↥Ω → ℂ) ⁻¹' K)ᶜ y))} =
      topologicalFill Ω K := by
  set K' : Set ↥Ω := ((↑) : ↥Ω → ℂ) ⁻¹' K
  refine Subset.antisymm ?_ ?_
  · rintro _ ⟨y, hyB, rfl⟩
    by_cases hyK : (y : ℂ) ∈ K
    · exact Or.inl hyK
    · refine Or.inr ⟨⟨y.2, hyK⟩, ?_⟩
      set L : Set ℂ := ((↑) : ↥Ω → ℂ) '' closure (connectedComponentIn K'ᶜ y)
      have hLcpt : IsCompact L := hyB.image continuous_subtype_val
      have hCL : connectedComponentIn (Ω \ K) y.1 ⊆ L := by
        rw [← image_subtype_connectedComponentIn_compl_eq hyK]
        exact image_mono subset_closure
      have hclL : closure (connectedComponentIn (Ω \ K) y.1) ⊆ L :=
        closure_minimal hCL hLcpt.isClosed
      exact ⟨hLcpt.of_isClosed_subset isClosed_closure hclL,
        hclL.trans (by rintro _ ⟨w, -, rfl⟩; exact w.2)⟩
  · rintro z (hzK | ⟨hz, hcpt, hclΩ⟩)
    · refine ⟨⟨z, hKΩ hzK⟩, ?_, rfl⟩
      have hnot : (⟨z, hKΩ hzK⟩ : ↥Ω) ∉ K'ᶜ := fun h ↦ h hzK
      simp [connectedComponentIn_eq_empty hnot]
    · refine ⟨⟨z, hz.1⟩, ?_, rfl⟩
      set M' : Set ↥Ω := ((↑) : ↥Ω → ℂ) ⁻¹' closure (connectedComponentIn (Ω \ K) z)
      have himgM' : ((↑) : ↥Ω → ℂ) '' M' = closure (connectedComponentIn (Ω \ K) z) :=
        Subset.antisymm (image_preimage_subset _ _) fun w hw ↦ ⟨⟨w, hclΩ hw⟩, hw, rfl⟩
      have hM'cpt : IsCompact M' :=
        Topology.IsInducing.subtypeVal.isCompact_iff.mpr (himgM'.symm ▸ hcpt)
      have hsubM' : connectedComponentIn K'ᶜ ⟨z, hz.1⟩ ⊆ M' := fun w hw ↦ by
        have hw_img : (w : ℂ) ∈ connectedComponentIn (Ω \ K) z := by
          rw [← image_subtype_connectedComponentIn_compl_eq (y := ⟨z, hz.1⟩) hz.2]
          exact mem_image_of_mem _ hw
        exact subset_closure hw_img
      exact hM'cpt.of_isClosed_subset isClosed_closure (closure_minimal hsubM' hM'cpt.isClosed)

/-- Compactness of `topologicalFill Ω K`, proved by viewing `K` inside the locally compact, locally
connected open subspace `↥Ω` and applying
`IsCompact.isCompact_setOf_isCompact_closure_connectedComponentIn_compl`. -/
private theorem isCompact_topologicalFill {Ω K : Set ℂ} (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) : IsCompact (topologicalFill Ω K) := by
  let : LocallyCompactSpace ↥Ω := hΩ.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let : LocallyConnectedSpace ↥Ω := hΩ.locallyConnectedSpace
  set K' : Set ↥Ω := ((↑) : ↥Ω → ℂ) ⁻¹' K
  have himgK' : ((↑) : ↥Ω → ℂ) '' K' = K :=
    Subset.antisymm (image_preimage_subset _ _) fun z hz ↦ ⟨⟨z, hKΩ hz⟩, hz, rfl⟩
  have hK' : IsCompact K' :=
    Topology.IsInducing.subtypeVal.isCompact_iff.mpr (himgK'.symm ▸ hK)
  have hno_cpt : ∀ y : ↥Ω, ¬ IsCompact (connectedComponent y) := fun y hcpt ↦ by
    have himg : ((↑) : ↥Ω → ℂ) '' connectedComponent y = connectedComponentIn Ω y.1 :=
      (connectedComponentIn_eq_image y.2).symm
    have hcptC : IsCompact (connectedComponentIn Ω y.1) :=
      himg ▸ hcpt.image continuous_subtype_val
    refine isFilledIn_iff.mp hΩ.isFilledIn_empty y.1 ⟨y.2, notMem_empty _⟩ ⟨?_, ?_⟩
    · simpa only [sdiff_empty, hcptC.isClosed.closure_eq] using hcptC
    · simpa only [sdiff_empty, hcptC.isClosed.closure_eq] using connectedComponentIn_subset Ω y.1
  rw [← image_subtype_setOf_isCompact_closure_connectedComponentIn_compl hKΩ]
  exact (hK'.isCompact_setOf_isCompact_closure_connectedComponentIn_compl hno_cpt).image
    continuous_subtype_val

/-- Filling all relatively compact components of `Ω \ K` leaves no relatively compact components in
`Ω`: `topologicalFill Ω K` is filled in `Ω`. -/
private theorem isFilledIn_topologicalFill {Ω K : Set ℂ} :
    IsFilledIn (topologicalFill Ω K) Ω := by
  rw [isFilledIn_iff]
  rintro x ⟨hxΩ, hxF⟩ ⟨hcpt, hclΩ⟩
  have hxK : x ∉ K := fun h ↦ hxF (Or.inl h)
  set C : Set ℂ := connectedComponentIn (Ω \ K) x
  have hCF : C ⊆ Ω \ topologicalFill Ω K := fun w hw ↦ by
    refine ⟨(connectedComponentIn_subset _ _ hw).1, fun hwF ↦ ?_⟩
    rcases hwF with hwK | ⟨-, hwcpt, hwcl⟩
    · exact (connectedComponentIn_subset _ _ hw).2 hwK
    · rw [← connectedComponentIn_eq hw] at hwcpt hwcl
      exact hxF (Or.inr ⟨⟨hxΩ, hxK⟩, hwcpt, hwcl⟩)
  have hcomp_eq : connectedComponentIn (Ω \ topologicalFill Ω K) x = C :=
    Subset.antisymm
      (connectedComponentIn_mono x (sdiff_subset_sdiff subset_rfl subset_union_left))
      (isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn ⟨hxΩ, hxK⟩) hCF)
  rw [hcomp_eq] at hcpt hclΩ
  exact hxF (Or.inr ⟨⟨hxΩ, hxK⟩, hcpt, hclΩ⟩)

/-- **Topological characterization of the holomorphic hull.** In one complex variable, the
`Ω`-holomorphic hull of a compact `K ⊆ Ω` inside an open `Ω ⊆ ℂ` is compact and is obtained by
adjoining the connected components of `Ω \ K` whose closures are compact subsets of `Ω`. -/
theorem holomorphicHull_eq_fill {Ω K : Set ℂ} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    IsCompact (holomorphicHull Ω K) ∧
      holomorphicHull Ω K =
        K ∪ {z | z ∈ Ω \ K ∧ IsCompact (closure (connectedComponentIn (Ω \ K) z)) ∧
          closure (connectedComponentIn (Ω \ K) z) ⊆ Ω} := by
  have hFcpt : IsCompact (topologicalFill Ω K) := isCompact_topologicalFill hΩ hK hKΩ
  have hFΩ : topologicalFill Ω K ⊆ Ω := union_subset hKΩ fun _ hz ↦ hz.1.1
  have hRunge : IsRungeCompactPair Ω (topologicalFill Ω K) :=
    isRungeCompactPair_iff.mpr ⟨hΩ, hFcpt, hFΩ, isFilledIn_topologicalFill⟩
  have hEq : holomorphicHull Ω K = topologicalFill Ω K := by
    refine Subset.antisymm (fun a ha ↦ by_contra fun haF ↦ ?_) ?_
    · obtain ⟨g, hgΩ, hgF, hga⟩ := hRunge.exists_differentiableOn_norm_lt_one_lt haF
      have hle : ‖g a‖ ≤ 1 := ha.2 g hgΩ 1 fun w hw ↦ (hgF w (Or.inl hw)).le
      exact hga.not_ge hle
    · exact union_subset (subset_holomorphicHull hKΩ) fun z hz ↦
        mem_holomorphicHull_of_isCompact_closure_connectedComponentIn hΩ hz.1.1 hz.2.1 hz.2.2
  exact ⟨hEq ▸ hFcpt, hEq⟩

/-- For any open `Ω` and compact `K ⊆ Ω`, `(Ω, holomorphicHull Ω K)` is a compact Runge pair. -/
theorem _root_.IsOpen.isRungeCompactPair_holomorphicHull {Ω K : Set ℂ} (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) : IsRungeCompactPair Ω (holomorphicHull Ω K) := by
  obtain ⟨hcpt, hEq⟩ := holomorphicHull_eq_fill hΩ hK hKΩ
  exact isRungeCompactPair_iff.mpr
    ⟨hΩ, hcpt, holomorphicHull_subset, hEq ▸ isFilledIn_topologicalFill⟩

/-- For open `Ω` and compact `K ⊆ Ω`, `K` equals its `Ω`-holomorphic hull if and only if `K` is
filled in `Ω`. -/
theorem holomorphicHull_eq_self_iff_isFilledIn {Ω K : Set ℂ} (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) : holomorphicHull Ω K = K ↔ IsFilledIn K Ω := by
  rw [(holomorphicHull_eq_fill hΩ hK hKΩ).2, isFilledIn_iff]
  constructor
  · intro hEq x hx hrel
    have hxK : x ∈ K := hEq ▸ Or.inr ⟨hx, hrel⟩
    exact hx.2 hxK
  · intro hfill
    refine Subset.antisymm (union_subset subset_rfl fun x hx ↦ ?_) subset_union_left
    exact (hfill x hx.1 hx.2).elim

/-- For open `Ω` and compact `K`, `(Ω, K)` is a compact Runge pair if and only if
`holomorphicHull Ω K = K`. -/
theorem isRungeCompactPair_iff_holomorphicHull_eq_self {Ω K : Set ℂ} (hΩ : IsOpen Ω)
    (hK : IsCompact K) : IsRungeCompactPair Ω K ↔ holomorphicHull Ω K = K :=
  ⟨fun h ↦ (holomorphicHull_eq_self_iff_isFilledIn hΩ hK h.subset).mpr h.isFilledIn,
    fun hEq ↦
      have hKΩ : K ⊆ Ω := hEq ▸ holomorphicHull_subset
      isRungeCompactPair_iff.mpr
        ⟨hΩ, hK, hKΩ, (holomorphicHull_eq_self_iff_isFilledIn hΩ hK hKΩ).mp hEq⟩⟩

end TopologicalFill

section WholePlane

/-- On `Ω = Set.univ`, the holomorphic hull of a compact set `K ⊆ ℂ` agrees with its topological
filled hull `TauCeti.filledHull K`. -/
theorem _root_.IsCompact.holomorphicHull_univ_eq_filledHull {K : Set ℂ} (hK : IsCompact K) :
    holomorphicHull univ K = filledHull K := by
  rw [(holomorphicHull_eq_fill isOpen_univ hK (subset_univ K)).2]
  ext z
  constructor
  · rintro (hzK | ⟨-, hcpt, -⟩)
    · exact subset_filledHull hzK
    · rw [← compl_eq_univ_sdiff] at hcpt
      exact mem_filledHull_iff.mpr (hcpt.isBounded.subset subset_closure)
  · intro hzF
    by_cases hzK : z ∈ K
    · exact Or.inl hzK
    · refine Or.inr ⟨⟨mem_univ z, hzK⟩, ?_, subset_univ _⟩
      rw [← compl_eq_univ_sdiff]
      exact (mem_filledHull_iff.mp hzF).isCompact_closure

/-- For compact `K ⊆ ℂ`, `(Set.univ, K)` is a compact Runge pair if and only if `Kᶜ` is
preconnected. -/
theorem _root_.IsCompact.isRungeCompactPair_univ_iff_isPreconnected_compl {K : Set ℂ}
    (hK : IsCompact K) : IsRungeCompactPair univ K ↔ IsPreconnected Kᶜ := by
  rw [isRungeCompactPair_iff, isFilledIn_univ_iff hK.isClosed]
  refine ⟨fun ⟨_, _, _, hfill⟩ ↦ ?_, fun hpre ↦ ⟨isOpen_univ, hK, subset_univ K, ?_⟩⟩
  · rw [← hfill]
    exact (isConnected_compl_filledHull (by simp [Complex.rank_real_complex])
      hK.isBounded).isPreconnected
  · refine filledHull_eq_self hpre fun hbdd ↦ ?_
    have huniv : IsBounded (univ : Set ℂ) := by
      simpa only [union_compl_self] using hK.isBounded.union hbdd
    exact NormedSpace.unbounded_univ ℝ ℂ huniv

/-- Partial sums of an entire function's Taylor series at `0` uniformly approximate it on any
compact subset of `ℂ`. -/
theorem _root_.IsCompact.exists_polynomial_norm_sub_lt_of_differentiable {K : Set ℂ}
    (hK : IsCompact K) {g : ℂ → ℂ} (hg : Differentiable ℂ g) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : Polynomial ℂ, ∀ z ∈ K, ‖g z - P.eval z‖ < ε := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  set r : NNReal := ⟨max R 0 + 1, by positivity⟩
  have hr_coe : (r : ℝ) = max R 0 + 1 := rfl
  have hKball : K ⊆ ball (0 : ℂ) r := fun z hz ↦ by
    have hzR : dist z 0 ≤ R := mem_closedBall.mp (hR hz)
    rw [mem_ball, hr_coe]
    linarith [le_max_left R 0]
  obtain ⟨p, hp⟩ : ∃ p, HasFPowerSeriesOnBall g p 0 ⊤ := ⟨_, hg.hasFPowerSeriesOnBall 0 one_pos⟩
  have hunif : TendstoUniformlyOn (fun n z ↦ p.partialSum n (z - 0)) g atTop (ball 0 r) :=
    hp.tendstoUniformlyOn' ENNReal.coe_lt_top
  obtain ⟨n, hn⟩ := (Metric.tendstoUniformlyOn_iff.mp hunif ε hε).exists
  refine ⟨∑ k ∈ Finset.range n, Polynomial.C (p.coeff k) * Polynomial.X ^ k, fun z hz ↦ ?_⟩
  have heval : (∑ k ∈ Finset.range n, Polynomial.C (p.coeff k) * Polynomial.X ^ k).eval z =
      p.partialSum n (z - 0) := by
    rw [← Polynomial.coe_evalRingHom, map_sum, FormalMultilinearSeries.partialSum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, sub_zero, FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul,
      mul_comm]
  rw [heval, ← dist_eq_norm]
  exact hn z (hKball hz)

/-- **Polynomial Runge theorem on `ℂ`.** A compact set `K ⊆ ℂ` has preconnected complement if and
only if every function holomorphic on an open neighborhood of `K` can be uniformly approximated on
`K` by complex polynomials. -/
theorem _root_.IsCompact.isPreconnected_compl_iff_polynomial_approximation {K : Set ℂ}
    (hK : IsCompact K) :
    IsPreconnected Kᶜ ↔
      ∀ U : Set ℂ, IsOpen U → K ⊆ U → ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U →
        ∀ ε > 0, ∃ P : Polynomial ℂ, ∀ z ∈ K, ‖f z - P.eval z‖ < ε := by
  rw [← hK.isRungeCompactPair_univ_iff_isPreconnected_compl,
    isRungeCompactPair_iff_approximation isOpen_univ hK (subset_univ K)]
  constructor
  · intro happrox U hU hKU f hf ε hε
    obtain ⟨g, hg_univ, hg⟩ := happrox U hU hKU f hf (ε / 2) (half_pos hε)
    obtain ⟨P, hP⟩ := hK.exists_polynomial_norm_sub_lt_of_differentiable
      (differentiableOn_univ.mp hg_univ) (half_pos hε)
    refine ⟨P, fun z hz ↦ ?_⟩
    calc ‖f z - P.eval z‖
        = ‖(f z - g z) + (g z - P.eval z)‖ := by ring_nf
      _ ≤ ‖f z - g z‖ + ‖g z - P.eval z‖ := norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add (hg z hz) (hP z hz)
      _ = ε := add_halves ε
  · intro hpoly U hU hKU f hf ε hε
    obtain ⟨P, hP⟩ := hpoly U hU hKU f hf ε hε
    exact ⟨fun z ↦ P.eval z, (AnalyticOnNhd.eval_polynomial P).differentiableOn, hP⟩

/-- For any bounded `K ⊆ ℂ`, the entire-function hull `holomorphicHull Set.univ K` coincides with
the pullback of the one-variable polynomial hull `TauCeti.polynomialHull` along `z ↦ (fun _ ↦ z)`.
-/
theorem holomorphicHull_univ_eq_preimage_polynomialHull {K : Set ℂ} (hK : IsBounded K) :
    holomorphicHull univ K =
      (fun z (_ : Fin 1) ↦ z) ⁻¹' polynomialHull ((fun z (_ : Fin 1) ↦ z) '' K) := by
  ext z
  simp only [mem_holomorphicHull_iff, mem_univ, true_and, mem_preimage, mem_polynomialHull_iff,
    forall_mem_image]
  constructor
  · intro hz Q c hc
    exact hz (fun w ↦ MvPolynomial.eval (fun _ ↦ w) Q)
      (AnalyticOnNhd.eval_continuousLinearMap' (fun _ ↦ ContinuousLinearMap.id ℂ ℂ)
        Q).differentiableOn c hc
  · intro hpoly f hf B hB
    refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
    have hcpt : IsCompact (closure (Insert.insert z K)) := (hK.insert z).isCompact_closure
    obtain ⟨P, hP⟩ := hcpt.exists_polynomial_norm_sub_lt_of_differentiable
      (differentiableOn_univ.mp hf) (half_pos hε)
    have hevalQ (w : ℂ) (R : Polynomial ℂ) :
        MvPolynomial.eval (fun _ : Fin 1 ↦ w) (Polynomial.aeval (MvPolynomial.X 0) R) =
          R.eval w := by
      refine R.induction_on (fun a ↦ by simp) (fun p q hp hq ↦ by simp [hp, hq])
        fun n a _ ↦ ?_
      simp [pow_succ, ← mul_assoc]
    set Q : MvPolynomial (Fin 1) ℂ := Polynomial.aeval (MvPolynomial.X 0) P
    have hQK : ∀ w ∈ K, ‖MvPolynomial.eval (fun _ ↦ w) Q‖ ≤ B + ε / 2 := fun w hw ↦ by
      rw [hevalQ]
      have hPw := hP w (subset_closure (mem_insert_of_mem z hw))
      have htri : ‖P.eval w‖ - ‖f w‖ ≤ ‖f w - P.eval w‖ := by
        rw [norm_sub_rev]
        exact norm_sub_norm_le _ _
      linarith [hB w hw]
    have hQz : ‖P.eval z‖ ≤ B + ε / 2 := by
      simpa only [Q, hevalQ] using hpoly Q (B + ε / 2) hQK
    have hPz := hP z (subset_closure (mem_insert z K))
    have htri : ‖f z‖ - ‖P.eval z‖ ≤ ‖f z - P.eval z‖ := norm_sub_norm_le _ _
    linarith

/-- For compact `K ⊆ ℂ`, the image of `K` in `ℂ¹ = (Fin 1 → ℂ)` is polynomially convex if and only
if `Kᶜ` is preconnected. -/
theorem _root_.IsCompact.isPolynomiallyConvex_image_const_iff_isPreconnected_compl {K : Set ℂ}
    (hK : IsCompact K) :
    IsPolynomiallyConvex ((fun z (_ : Fin 1) ↦ z) '' K) ↔ IsPreconnected Kᶜ := by
  rw [← hK.isRungeCompactPair_univ_iff_isPreconnected_compl,
    isRungeCompactPair_iff_holomorphicHull_eq_self isOpen_univ hK,
    holomorphicHull_univ_eq_preimage_polynomialHull hK.isBounded, isPolynomiallyConvex_iff]
  have hinj : Function.Injective (fun (z : ℂ) (_ : Fin 1) ↦ z) := fun z w h ↦ congrFun h 0
  constructor
  · intro hsub
    refine Subset.antisymm (fun z hz ↦ hinj.mem_set_image.mp (hsub hz))
      fun z hz ↦ subset_polynomialHull _ (mem_image_of_mem _ hz)
  · intro hEq p hp
    have hp0 : (fun _ : Fin 1 ↦ p 0) = p := funext fun i ↦ congrArg p (Subsingleton.elim 0 i)
    rw [← hp0] at hp ⊢
    exact mem_image_of_mem _ (hEq ▸ hp)

end WholePlane

end TauCeti

end
