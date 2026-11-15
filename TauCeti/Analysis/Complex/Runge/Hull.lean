/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Analysis.Complex.PolynomialHull.Basic
public import TauCeti.Analysis.Normed.Module.Exhaustion
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.SpecialFunctions.Exp
import TauCeti.Analysis.Convex.Caratheodory
import TauCeti.Analysis.Normed.Module.FilledHull
import TauCeti.Topology.ConnectedComponents

/-!
# Runge compact pairs and holomorphic hulls in the complex plane

Given an open set `Ω ⊆ ℂ` and a subset `K ⊆ Ω`, this file introduces the two hull-side notions
underlying Runge's approximation theorem on plane domains:

* `TauCeti.IsRungeCompactPair Ω K` packages `IsOpen Ω`, `IsCompact K`, `K ⊆ Ω`, and
  `TauCeti.IsFilledIn K Ω` (no connected component of `Ω \ K` has compact closure contained in
  `Ω`).
* `TauCeti.holomorphicHull Ω K` consists of the points `z ∈ Ω` at which every `Ω`-holomorphic
  function `f` obeys every uniform real bound `‖f‖ ≤ B` that holds on `K`. Requiring universal
  real bounds makes `holomorphicHull Ω ∅ = ∅`.

This file establishes the hull properties that precede Runge's approximation theorem:

* Extensivity (`subset_holomorphicHull`), joint monotonicity (`holomorphicHull_mono`), and
  idempotence (`holomorphicHull_holomorphicHull`).
* Preservation of the extended distance to `Ωᶜ` (`biInf_edist_compl_holomorphicHull`) and closedness
  of `holomorphicHull Ω K` in `ℂ` whenever `K ⊆ Ω` is closed (`IsClosed.isClosed_holomorphicHull`).
* Inclusion in `closedConvexHull ℝ K` (`holomorphicHull_subset_closedConvexHull`, hence in
  `convexHull ℝ K` for compact `K`), which combines with closedness to give compactness
  (`IsCompact.holomorphicHull`).
* Inclusion of every relatively compact connected component of `Ω \ K`
  (`connectedComponentIn_sdiff_subset_holomorphicHull`), from which `holomorphicHull Ω K` is itself
  filled in `Ω` (`IsCompact.isFilledIn_holomorphicHull`).
* Agreement on `Ω = univ` with `TauCeti.polynomialHull` for bounded `K`
  (`IsBounded.holomorphicHull_univ_eq_preimage_polynomialHull`).

The converse inclusion identifying `holomorphicHull Ω K` with `K` union the relatively compact
components of `Ω \ K` is proved in `TauCeti/Analysis/Complex/Runge/Basic.lean`
(`TauCeti.holomorphicHull_eq_fill`).

## Main declarations

* `TauCeti.IsRungeCompactPair`: an open set `Ω ⊆ ℂ` together with a compact `K ⊆ Ω` filled in `Ω`.
* `TauCeti.holomorphicHull`: the `Ω`-holomorphic hull of `K`.
* `IsClosed.isClosed_holomorphicHull`, `IsCompact.holomorphicHull`: closedness and compactness of
  the holomorphic hull.
* `TauCeti.biInf_edist_compl_holomorphicHull`: `holomorphicHull Ω K` has the same extended
  distance to `Ωᶜ` as `K`.
* `TauCeti.holomorphicHull_subset_closedConvexHull`, `IsCompact.holomorphicHull_subset_convexHull`:
  inclusion in the closed (and ordinary, for compact `K`) convex hull.
* `TauCeti.connectedComponentIn_sdiff_subset_holomorphicHull`,
  `IsCompact.isFilledIn_holomorphicHull`: maximum-principle inclusion of relatively compact holes
  and filledness of `holomorphicHull Ω K`.
* `IsBounded.holomorphicHull_univ_eq_preimage_polynomialHull`: comparison with
  `TauCeti.polynomialHull` when `Ω = univ`.
* `IsOpen.isRungeCompactPair_closedBall_sdiff_thickening`,
  `IsOpen.exists_isRungeCompactPair_exhaustion`: explicit Runge compact exhaustions of open plane
  sets.

## References

* A. Rainer, *Advanced Complex Analysis*, §11, Lemma 11.3 and Theorem 12.1.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed., Theorem 1.3.3.
-/

public section

open Bornology Filter Metric MvPolynomial Set Topology
open scoped ENNReal NNReal

/-- The empty set is filled in every open subset of a nontrivial proper real normed space. -/
theorem IsOpen.isFilledIn_empty {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] [Nontrivial E] {Ω : Set E} (hΩ : IsOpen Ω) :
    TauCeti.IsFilledIn (∅ : Set E) Ω := by
  rw [TauCeti.isFilledIn_iff_forall_mem_filledHull_sdiff_not_connectedComponentIn_subset
    isClosed_empty hΩ (empty_subset Ω), TauCeti.filledHull_empty]
  simp

namespace TauCeti

section RungeCompactPair

/-- A **Runge compact pair** `(Ω, K)` in `ℂ`: an open set `Ω`, a compact subset `K ⊆ Ω`, and
`IsFilledIn K Ω`, meaning that no connected component of `Ω \ K` has compact closure contained in
`Ω`. -/
def IsRungeCompactPair (Ω K : Set ℂ) : Prop :=
  IsOpen Ω ∧ IsCompact K ∧ K ⊆ Ω ∧ IsFilledIn K Ω

theorem isRungeCompactPair_iff {Ω K : Set ℂ} :
    IsRungeCompactPair Ω K ↔ IsOpen Ω ∧ IsCompact K ∧ K ⊆ Ω ∧ IsFilledIn K Ω :=
  Iff.rfl

theorem IsRungeCompactPair.isOpen {Ω K : Set ℂ} (h : IsRungeCompactPair Ω K) : IsOpen Ω :=
  h.1

theorem IsRungeCompactPair.isCompact {Ω K : Set ℂ} (h : IsRungeCompactPair Ω K) : IsCompact K :=
  h.2.1

theorem IsRungeCompactPair.subset {Ω K : Set ℂ} (h : IsRungeCompactPair Ω K) : K ⊆ Ω :=
  h.2.2.1

theorem IsRungeCompactPair.isFilledIn {Ω K : Set ℂ} (h : IsRungeCompactPair Ω K) :
    IsFilledIn K Ω :=
  h.2.2.2

/-- `(Ω, ∅)` is a Runge compact pair for every open `Ω ⊆ ℂ`. -/
theorem _root_.IsOpen.isRungeCompactPair_empty {Ω : Set ℂ} (hΩ : IsOpen Ω) :
    IsRungeCompactPair Ω ∅ :=
  ⟨hΩ, isCompact_empty, empty_subset Ω, hΩ.isFilledIn_empty⟩

/-- Every explicit ball-minus-thickening stage `closedBall a r \ thickening δ Ωᶜ` (`0 ≤ r`,
`0 < δ`) forms a Runge compact pair with an open set `Ω ⊆ ℂ`. -/
theorem _root_.IsOpen.isRungeCompactPair_closedBall_sdiff_thickening {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (a : ℂ) {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ) :
    IsRungeCompactPair Ω (closedBall a r \ thickening δ Ωᶜ) :=
  ⟨hΩ, (isCompact_closedBall a r).diff isOpen_thickening,
    fun _ hx ↦ by_contra fun hxΩ ↦ hx.2 (self_subset_thickening hδ Ωᶜ hxΩ),
    hΩ.isFilledIn_closedBall_sdiff_thickening a hr hδ⟩

/-- Every open subset `Ω ⊆ ℂ` admits a compact exhaustion `K n` with `K n ⊆ interior (K (n + 1))`
such that `(Ω, K n)` is a Runge compact pair for every `n`. -/
theorem _root_.IsOpen.exists_isRungeCompactPair_exhaustion {Ω : Set ℂ} (hΩ : IsOpen Ω) :
    ∃ K : ℕ → Set ℂ, (∀ n, IsRungeCompactPair Ω (K n)) ∧
      (∀ n, K n ⊆ interior (K (n + 1))) ∧ ⋃ n, K n = Ω := by
  refine ⟨fun n ↦ closedBall 0 (n + 1) \ thickening (n + 1 : ℝ)⁻¹ Ωᶜ,
    fun n ↦ hΩ.isRungeCompactPair_closedBall_sdiff_thickening 0 (by positivity) (by positivity),
    fun n ↦ ?_, hΩ.iUnion_closedBall_sdiff_thickening 0⟩
  simpa only [Nat.cast_add, Nat.cast_one] using
    closedBall_sdiff_thickening_subset_interior 0 (by linarith) (by positivity)
      (inv_strictAnti₀ (by positivity) (by linarith)) Ωᶜ

end RungeCompactPair

section HolomorphicHull

variable {Ω Ω₁ Ω₂ K K₁ K₂ : Set ℂ} {z : ℂ}

/-- The **holomorphic hull** of `K` in `Ω`: the set of points `z ∈ Ω` such that every function
holomorphic on `Ω` satisfies at `z` every real norm bound it satisfies on `K`. Quantifying over
all `B : ℝ` forces the hull of the empty set to be empty. -/
def holomorphicHull (Ω K : Set ℂ) : Set ℂ :=
  {z | z ∈ Ω ∧ ∀ f : ℂ → ℂ, DifferentiableOn ℂ f Ω →
    ∀ B : ℝ, (∀ w ∈ K, ‖f w‖ ≤ B) → ‖f z‖ ≤ B}

theorem mem_holomorphicHull_iff :
    z ∈ holomorphicHull Ω K ↔
      z ∈ Ω ∧ ∀ f : ℂ → ℂ, DifferentiableOn ℂ f Ω →
        ∀ B : ℝ, (∀ w ∈ K, ‖f w‖ ≤ B) → ‖f z‖ ≤ B :=
  Iff.rfl

theorem holomorphicHull_subset_left : holomorphicHull Ω K ⊆ Ω :=
  fun _ hz ↦ hz.1

theorem subset_holomorphicHull (hKΩ : K ⊆ Ω) : K ⊆ holomorphicHull Ω K :=
  fun _ hz ↦ ⟨hKΩ hz, fun _ _ _ hB ↦ hB _ hz⟩

@[simp]
theorem holomorphicHull_empty (Ω : Set ℂ) : holomorphicHull Ω ∅ = ∅ :=
  eq_empty_of_forall_notMem fun _ hz ↦
    (hz.2 0 (differentiableOn_const 0) (-1) (by simp)).not_gt (by simp)

/-- `holomorphicHull` is monotone in both arguments: enlarging `Ω` restricts the test functions
while enlarging `K` weakens their hypotheses. -/
theorem holomorphicHull_mono (hΩ : Ω₁ ⊆ Ω₂) (hK : K₁ ⊆ K₂) :
    holomorphicHull Ω₁ K₁ ⊆ holomorphicHull Ω₂ K₂ :=
  fun _ hz ↦ ⟨hΩ hz.1, fun f hf B hB ↦ hz.2 f (hf.mono hΩ) B fun w hw ↦ hB w (hK hw)⟩

theorem holomorphicHull_mono_right (hK : K₁ ⊆ K₂) :
    holomorphicHull Ω K₁ ⊆ holomorphicHull Ω K₂ :=
  holomorphicHull_mono Subset.rfl hK

theorem holomorphicHull_mono_left (hΩ : Ω₁ ⊆ Ω₂) :
    holomorphicHull Ω₁ K ⊆ holomorphicHull Ω₂ K :=
  holomorphicHull_mono hΩ Subset.rfl

/-- Taking the `Ω`-holomorphic hull is idempotent. -/
@[simp]
theorem holomorphicHull_holomorphicHull (Ω K : Set ℂ) :
    holomorphicHull Ω (holomorphicHull Ω K) = holomorphicHull Ω K :=
  (subset_holomorphicHull holomorphicHull_subset_left).antisymm'
    fun _ hz ↦ ⟨hz.1, fun f hf B hB ↦ hz.2 f hf B fun _ hu ↦ hu.2 f hf B hB⟩

/-- Every point of `Ω \ holomorphicHull Ω K` is separated from `K` by an `Ω`-holomorphic function
of modulus `< 1` on `K` and `> 1` at the point. -/
theorem exists_differentiableOn_norm_lt_one_lt_of_notMem_holomorphicHull (hzΩ : z ∈ Ω)
    (hz : z ∉ holomorphicHull Ω K) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f Ω ∧ (∀ w ∈ K, ‖f w‖ < 1) ∧ 1 < ‖f z‖ := by
  simp only [mem_holomorphicHull_iff, hzΩ, true_and, not_forall, not_le, exists_prop] at hz
  obtain ⟨f, hf, B, hfK, hBz⟩ := hz
  set s := ‖f z‖
  rcases (norm_nonneg (f z)).eq_or_lt with hs | hs
  · have hK : ∀ w ∈ K, False := fun w hw ↦
      ((norm_nonneg _).trans (hfK w hw)).not_gt (hs ▸ hBz)
    exact ⟨fun _ ↦ 2, differentiableOn_const 2, fun w hw ↦ (hK w hw).elim, by norm_num⟩
  set a := max B (s / 2)
  have has : a < s := max_lt hBz (half_lt_self hs)
  have hr : 0 < 2 / (a + s) := by positivity
  have hnorm (w : ℂ) : ‖((2 / (a + s) : ℝ) : ℂ) * f w‖ = 2 * ‖f w‖ / (a + s) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le, div_mul_eq_mul_div]
  refine ⟨fun w ↦ ((2 / (a + s) : ℝ) : ℂ) * f w, hf.const_mul _, fun w hw ↦ ?_, ?_⟩
  · rw [hnorm, div_lt_one (by positivity)]
    linarith [(hfK w hw).trans (le_max_left B (s / 2))]
  · rw [hnorm, one_lt_div (by positivity)]
    linarith

/-- No point of `holomorphicHull Ω K` lies closer to a complement point `ζ ∉ Ω` than `K` does. -/
theorem infEDist_le_edist_of_mem_holomorphicHull {ζ : ℂ} (hζ : ζ ∉ Ω)
    (hz : z ∈ holomorphicHull Ω K) : Metric.infEDist ζ K ≤ edist z ζ := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · simp at hz
  by_contra! hlt
  have hzζ : z ≠ ζ := fun h ↦ hζ (h ▸ hz.1)
  have hd_pos : 0 < dist z ζ := dist_pos.mpr hzζ
  have hd_lt : dist z ζ < Metric.infDist ζ K :=
    (ENNReal.ofReal_lt_iff_lt_toReal hd_pos.le (Metric.infEDist_ne_top hKne)).mp
      (edist_dist z ζ ▸ hlt)
  have hr_pos : 0 < Metric.infDist ζ K := hd_pos.trans hd_lt
  have hf : DifferentiableOn ℂ (fun w : ℂ ↦ (w - ζ)⁻¹) Ω :=
    (differentiableOn_id.sub_const ζ).inv fun w hw ↦
      sub_ne_zero.mpr fun (h : w = ζ) ↦ hζ (h ▸ hw)
  have hzle := hz.2 _ hf (Metric.infDist ζ K)⁻¹ fun w hw ↦ by
    rw [norm_inv, ← dist_eq_norm, dist_comm]
    exact inv_anti₀ hr_pos (Metric.infDist_le_dist_of_mem hw)
  rw [norm_inv, ← dist_eq_norm] at hzle
  exact hzle.not_gt (inv_strictAnti₀ hd_pos hd_lt)

theorem infEDist_le_infEDist_holomorphicHull {ζ : ℂ} (hζ : ζ ∉ Ω) :
    Metric.infEDist ζ K ≤ Metric.infEDist ζ (holomorphicHull Ω K) :=
  Metric.le_infEDist.mpr fun z hz ↦
    edist_comm z ζ ▸ infEDist_le_edist_of_mem_holomorphicHull hζ hz

/-- `holomorphicHull Ω K` has the same extended distance to `Ωᶜ` as `K`. Both sides equal `∞` when
`K = ∅` or `Ω = univ`. -/
theorem biInf_edist_compl_holomorphicHull (hKΩ : K ⊆ Ω) :
    (⨅ z ∈ holomorphicHull Ω K, ⨅ ζ ∈ Ωᶜ, edist z ζ) = ⨅ z ∈ K, ⨅ ζ ∈ Ωᶜ, edist z ζ := by
  refine le_antisymm (biInf_mono (subset_holomorphicHull hKΩ)) ?_
  refine le_iInf₂ fun z hz ↦ le_iInf₂ fun ζ hζ ↦ ?_
  refine le_trans ?_ (infEDist_le_edist_of_mem_holomorphicHull hζ hz)
  rw [Metric.infEDist]
  exact le_iInf₂ fun w hw ↦ (iInf₂_le w hw).trans <| (iInf₂_le ζ hζ).trans_eq (edist_comm w ζ)

/-- The `Ω`-holomorphic hull of `K` is contained in its closed real convex hull
`closedConvexHull ℝ K`. -/
theorem holomorphicHull_subset_closedConvexHull (Ω K : Set ℂ) :
    holomorphicHull Ω K ⊆ closedConvexHull ℝ K := by
  intro z hz
  by_contra hzC
  obtain ⟨φ, u, hφz, hφC⟩ := geometric_hahn_banach_point_closed convex_closedConvexHull
    isClosed_closedConvexHull hzC
  let ψ : ℂ →L[ℝ] ℝ := -φ
  let a : ℂ := ψ 1 - Complex.I * ψ Complex.I
  have hre (w : ℂ) : (a * w).re = ψ w := by
    have hw : w.re • (1 : ℂ) + w.im • Complex.I = w := by simp [Complex.real_smul]
    calc (a * w).re
      _ = ψ 1 * w.re + ψ Complex.I * w.im := by simp [a]
      _ = ψ (w.re • (1 : ℂ) + w.im • Complex.I) := by
          rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_comm (ψ 1),
            mul_comm (ψ Complex.I)]
      _ = ψ w := by rw [hw]
  have hf : DifferentiableOn ℂ (fun w : ℂ ↦ Complex.exp (a * w)) Ω :=
    (Complex.differentiable_exp.comp (differentiable_id.const_mul a)).differentiableOn
  have hzle := hz.2 _ hf (Real.exp (-u)) fun w hw ↦ by
    rw [Complex.norm_exp, hre, Real.exp_le_exp]
    exact neg_le_neg (hφC w (subset_closedConvexHull hw)).le
  rw [Complex.norm_exp, hre, Real.exp_le_exp] at hzle
  exact hzle.not_gt (neg_lt_neg hφz)

/-- For compact `K`, the holomorphic hull lies inside the ordinary real convex hull
`convexHull ℝ K`. -/
theorem _root_.IsCompact.holomorphicHull_subset_convexHull (hK : IsCompact K) (Ω : Set ℂ) :
    holomorphicHull Ω K ⊆ convexHull ℝ K :=
  (holomorphicHull_subset_closedConvexHull Ω K).trans <|
    closedConvexHull_min (subset_convexHull ℝ K) (convex_convexHull ℝ K) hK.convexHull.isClosed

/-- The holomorphic hull of a bounded set is bounded. -/
theorem _root_.Bornology.IsBounded.holomorphicHull (hK : IsBounded K) (Ω : Set ℂ) :
    IsBounded (holomorphicHull Ω K) :=
  (isBounded_closedConvexHull.mpr hK).subset (holomorphicHull_subset_closedConvexHull Ω K)

/-- If `K ⊆ Ω` is closed in `ℂ`, then `holomorphicHull Ω K` is closed in `ℂ`. -/
theorem _root_.IsClosed.isClosed_holomorphicHull (hK : IsClosed K) (hKΩ : K ⊆ Ω) :
    IsClosed (holomorphicHull Ω K) := by
  refine isClosed_iff_clusterPt.mpr fun z hz ↦ ?_
  have hzcl : z ∈ closure (holomorphicHull Ω K) := mem_closure_iff_clusterPt.mpr hz
  have hzΩ : z ∈ Ω := by
    by_contra hzΩ
    have hzK : z ∉ closure K := hK.closure_eq.symm ▸ fun h ↦ hzΩ (hKΩ h)
    have hne : Metric.infEDist z K ≠ 0 := mt Metric.mem_closure_iff_infEDist_zero.mpr hzK
    exact hne <| nonpos_iff_eq_zero.mp <|
      (infEDist_le_infEDist_holomorphicHull hzΩ).trans_eq
        (Metric.mem_closure_iff_infEDist_zero.mp hzcl)
  refine ⟨hzΩ, fun f hf B hB ↦ ?_⟩
  have hcont : ContinuousWithinAt (fun u ↦ ‖f u‖) (holomorphicHull Ω K) z :=
    (hf.continuousOn z hzΩ).norm.mono holomorphicHull_subset_left
  have : (𝓝[holomorphicHull Ω K] z).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hzcl
  exact le_of_tendsto hcont (eventually_nhdsWithin_of_forall fun u hu ↦ hu.2 f hf B hB)

/-- The holomorphic hull of a compact subset `K ⊆ Ω` is compact. -/
theorem _root_.IsCompact.holomorphicHull (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    IsCompact (holomorphicHull Ω K) :=
  Metric.isCompact_of_isClosed_isBounded (hK.isClosed.isClosed_holomorphicHull hKΩ)
    (hK.isBounded.holomorphicHull Ω)

/-- **Inclusion of relatively compact holes.** Every connected component of `Ω \ K` with compact
closure contained in `Ω` lies in `holomorphicHull Ω K`. -/
theorem connectedComponentIn_sdiff_subset_holomorphicHull (hΩ : IsOpen Ω) (hK : IsClosed K)
    (hcpt : IsCompact (closure (connectedComponentIn (Ω \ K) z)))
    (hclΩ : closure (connectedComponentIn (Ω \ K) z) ⊆ Ω) :
    connectedComponentIn (Ω \ K) z ⊆ holomorphicHull Ω K := by
  set C := connectedComponentIn (Ω \ K) z
  have hfrK : frontier C ⊆ K := fun w hw ↦ by
    have hwΩ : w ∈ Ω := hclΩ (frontier_subset_closure hw)
    have hwC : w ∈ (Ω \ K)ᶜ := frontier_connectedComponentIn_subset_compl (hΩ.sdiff hK) z hw
    exact by_contra fun hwK ↦ hwC ⟨hwΩ, hwK⟩
  intro u hu
  refine ⟨(connectedComponentIn_subset (Ω \ K) z hu).1, fun f hf B hB ↦ ?_⟩
  exact Complex.norm_le_of_forall_mem_frontier_norm_le (hcpt.isBounded.subset subset_closure)
    ⟨hf.mono (subset_closure.trans hclΩ), (hf.mono hclΩ).continuousOn⟩
    (fun w hw ↦ hB w (hfrK hw)) (subset_closure hu)

/-- The holomorphic hull of a compact subset `K ⊆ Ω` is filled in `Ω`. -/
theorem _root_.IsCompact.isFilledIn_holomorphicHull (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) : IsFilledIn (holomorphicHull Ω K) Ω :=
  isFilledIn_iff.mpr fun x hx ⟨hcpt, hclΩ⟩ ↦ by
    have hxH := connectedComponentIn_sdiff_subset_holomorphicHull hΩ
      (hK.holomorphicHull hKΩ).isClosed hcpt hclΩ (mem_connectedComponentIn hx)
    rw [holomorphicHull_holomorphicHull] at hxH
    exact hx.2 hxH

/-- `(Ω, holomorphicHull Ω K)` is a Runge compact pair whenever `Ω` is open and `K ⊆ Ω` is
compact. -/
theorem _root_.IsCompact.isRungeCompactPair_holomorphicHull (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) : IsRungeCompactPair Ω (holomorphicHull Ω K) :=
  ⟨hΩ, hK.holomorphicHull hKΩ, holomorphicHull_subset_left,
    hK.isFilledIn_holomorphicHull hΩ hKΩ⟩

/-- For every `K ⊆ ℂ`, `holomorphicHull univ K` is contained in the preimage of `polynomialHull`
along `z ↦ fun _ : Fin 1 ↦ z`. -/
theorem holomorphicHull_univ_subset_preimage_polynomialHull (K : Set ℂ) :
    holomorphicHull univ K ⊆
      (fun z (_ : Fin 1) ↦ z) ⁻¹' polynomialHull ((fun z (_ : Fin 1) ↦ z) '' K) :=
  fun _ hz ↦ mem_polynomialHull_iff.mpr fun p ↦ by
    have hd : Differentiable ℂ (fun w : ℂ ↦ eval (fun _ : Fin 1 ↦ w) p) := by
      induction p using MvPolynomial.induction_on with
      | C a => simp
      | add f g hf hg => convert hf.add hg using 1; ext w; simp
      | mul_X f i hf => convert hf.mul differentiable_id using 1; ext w; simp
    exact fun c hc ↦ hz.2 _ hd.differentiableOn c fun w hw ↦ hc _ ⟨w, hw, rfl⟩

/-- **Comparison with `polynomialHull` on `ℂ`.** For a bounded set `K ⊆ ℂ`, the whole-plane
holomorphic hull `holomorphicHull univ K` coincides with the preimage of
`polynomialHull ((fun z (_ : Fin 1) ↦ z) '' K)`. Boundedness is essential: for `K = ℝ`, bounded
exponentials `exp (±I * z)` cut `holomorphicHull univ ℝ` down to `ℝ`, while `polynomialHull` of its
image is all of `Fin 1 → ℂ`. -/
theorem _root_.Bornology.IsBounded.holomorphicHull_univ_eq_preimage_polynomialHull
    (hK : IsBounded K) :
    holomorphicHull univ K =
      (fun z (_ : Fin 1) ↦ z) ⁻¹' polynomialHull ((fun z (_ : Fin 1) ↦ z) '' K) := by
  refine (holomorphicHull_univ_subset_preimage_polynomialHull K).antisymm fun z hz ↦ ?_
  refine ⟨mem_univ z, fun f hf B hB ↦ le_of_forall_pos_le_add fun ε hε ↦ ?_⟩
  have hf_ent : Differentiable ℂ f := differentiableOn_univ.mp hf
  obtain ⟨r, hr⟩ := (hK.insert z).subset_closedBall (0 : ℂ)
  set R : ℝ≥0 := (max r 0 + 1).toNNReal
  have hR_val : (R : ℝ) = max r 0 + 1 := Real.coe_toNNReal _ (by positivity)
  have hps := hf_ent.hasFPowerSeriesOnBall 0 (R := (1 : ℝ≥0)) one_pos
  have hu := hps.tendstoUniformlyOn (r' := R) ENNReal.coe_lt_top
  obtain ⟨N, hN⟩ := (Metric.tendstoUniformlyOn_iff.mp hu (ε / 2) (half_pos hε)).exists
  set p := cauchyPowerSeries f 0 (1 : ℝ≥0)
  let q : MvPolynomial (Fin 1) ℂ := ∑ k ∈ Finset.range N, C (p.coeff k) * X 0 ^ k
  have heval (w : ℂ) : eval (fun _ : Fin 1 ↦ w) q = p.partialSum N w := by
    simp only [q, FormalMultilinearSeries.partialSum, map_sum, map_mul, map_pow, eval_C, eval_X,
      FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul, mul_comm]
  have happrox {w : ℂ} (hw : w ∈ insert z K) : ‖f w - eval (fun _ : Fin 1 ↦ w) q‖ < ε / 2 := by
    have hwR : w ∈ ball (0 : ℂ) R := by
      rw [mem_ball, hR_val]
      exact (mem_closedBall.mp (hr hw)).trans_lt (by linarith [le_max_left r 0])
    have hNw : ‖f (0 + w) - p.partialSum N w‖ < ε / 2 := by
      simpa only [dist_eq_norm] using hN w hwR
    rwa [zero_add, ← heval] at hNw
  have hqK : ∀ u ∈ (fun w (_ : Fin 1) ↦ w) '' K, ‖eval u q‖ ≤ B + ε / 2 := by
    rintro _ ⟨w, hw, rfl⟩
    have hw_err := (happrox (mem_insert_of_mem z hw)).le
    have hsub : ‖eval (fun _ : Fin 1 ↦ w) q‖ - ‖f w‖ ≤ ‖f w - eval (fun _ : Fin 1 ↦ w) q‖ := by
      rw [norm_sub_rev]
      exact norm_sub_norm_le _ _
    linarith [hB w hw]
  have hqz : ‖eval (fun _ : Fin 1 ↦ z) q‖ ≤ B + ε / 2 :=
    mem_polynomialHull_iff.mp hz q (B + ε / 2) hqK
  have hz_err := (happrox (mem_insert z K)).le
  have hsubz : ‖f z‖ - ‖eval (fun _ : Fin 1 ↦ z) q‖ ≤ ‖f z - eval (fun _ : Fin 1 ↦ z) q‖ :=
    norm_sub_norm_le _ _
  linarith

/-- A bounded set `K ⊆ ℂ` equals its whole-plane holomorphic hull if and only if its image in
`Fin 1 → ℂ` is polynomially convex. -/
theorem _root_.Bornology.IsBounded.holomorphicHull_univ_eq_self_iff_isPolynomiallyConvex
    (hK : IsBounded K) :
    holomorphicHull univ K = K ↔ IsPolynomiallyConvex ((fun z (_ : Fin 1) ↦ z) '' K) := by
  let e : ℂ → Fin 1 → ℂ := fun z _ ↦ z
  have hinj : Function.Injective e := fun _ _ h ↦ congrFun h 0
  rw [hK.holomorphicHull_univ_eq_preimage_polynomialHull,
    isPolynomiallyConvex_iff_polynomialHull_eq]
  refine ⟨fun h ↦ (subset_polynomialHull _).antisymm' fun u hu ↦ ?_, fun h ↦ ?_⟩
  · have : e (u 0) = u := funext fun i ↦ congrArg u (Subsingleton.elim 0 i)
    rw [← this]
    exact mem_image_of_mem e (h ▸ (this.symm ▸ hu : e (u 0) ∈ polynomialHull (e '' K)))
  · rw [h, preimage_image_eq K hinj]

end HolomorphicHull

end TauCeti
