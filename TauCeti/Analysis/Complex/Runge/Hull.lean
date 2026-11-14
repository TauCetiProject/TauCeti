/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Convex.Topology
public import TauCeti.Analysis.Complex.PolynomialHull.Basic
public import TauCeti.Analysis.Normed.Module.Exhaustion
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.LocallyConvex.Separation
import TauCeti.Analysis.Convex.Caratheodory
import TauCeti.Topology.MetricSpace.HausdorffDistance

/-!
# Holomorphic hulls and Runge compact pairs in the complex plane

For subsets `Ω` and `K` of `ℂ`, the *`Ω`-holomorphic hull* `TauCeti.holomorphicHull Ω K` consists
of all points `z ∈ Ω` at which every real upper bound satisfied on `K` by a function holomorphic
on `Ω` remains valid. Universal real bounds force `holomorphicHull Ω ∅ = ∅`, while for compact
`K ⊆ Ω` membership is equivalent to `‖f z‖ ≤ sSup ((‖f ·‖) '' K)` for every `Ω`-holomorphic `f`
(`IsCompact.mem_holomorphicHull_iff_norm_le_sSup`).

Without invoking any approximation theorem, this file establishes the basic geometric and
topological properties of `holomorphicHull Ω K`:

* **Extensivity, monotonicity, and idempotence**: `K ⊆ holomorphicHull Ω K` when `K ⊆ Ω`,
  monotonicity in both arguments, and
  `holomorphicHull Ω (holomorphicHull Ω K) = holomorphicHull Ω K`.
* **Distance preservation and compactness**: for `z ∈ holomorphicHull Ω K` and `ζ ∉ Ω`, testing
  against `w ↦ (w - ζ)⁻¹` yields `infEDist ζ K ≤ edist z ζ`, whence `holomorphicHull Ω K` and `K`
  have the same extended and ordinary distances to `Ωᶜ` and `frontier Ω` whenever `K ⊆ Ω`.
  Together with relative closedness (`closure (holomorphicHull Ω K) ∩ Ω = holomorphicHull Ω K`)
  and boundedness via the coordinate `id`, this shows that `holomorphicHull Ω K` is closed for
  closed `K ⊆ Ω` and compact for compact `K ⊆ Ω`.
* **Convex hull bound**: geometric Hahn–Banach separation combined with complex exponentials
  `w ↦ exp (l w)` gives `holomorphicHull Ω K ⊆ closedConvexHull ℝ K` unconditionally, and hence
  `holomorphicHull Ω K ⊆ convexHull ℝ K` for compact `K`.
* **Maximum-principle inclusion and filledness**: in an open `Ω`, every connected component of
  `Ω \ K` whose closure is compact and contained in `Ω` has frontier in `closure K` and therefore
  lies inside `holomorphicHull Ω K`. Combined with idempotence, `holomorphicHull Ω K` is always
  filled in `Ω` (`IsOpen.isFilledIn_holomorphicHull`).
* **Runge compact pairs and exhaustions**: `TauCeti.IsRungeCompactPair Ω K` bundles `IsOpen Ω`,
  `IsCompact K`, `K ⊆ Ω`, and `TauCeti.IsFilledIn K Ω`. Both `holomorphicHull Ω K` (for compact
  `K ⊆ Ω`) and the explicit exhaustion stages `TauCeti.filledExhaustion Ω n` form Runge compact
  pairs in any open `Ω`.
* **Comparison with polynomial hulls on `ℂ`**: for `Ω = univ` and bounded `K ⊆ ℂ`, uniform Taylor
  approximation of entire functions on disks identifies `holomorphicHull univ K` with the preimage
  of `TauCeti.polynomialHull (Function.const ι '' K)` under the diagonal embedding
  `Function.const ι : ℂ → (ι → ℂ)` for any nonempty index type `ι` (in particular for `ι = Fin 1`,
  where `Function.const (Fin 1)` is `⇑(ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ).symm`). The
  closed unbounded line `ℝ ⊆ ℂ` has `holomorphicHull univ ℝ = ℝ` whereas its univariate polynomial
  hull is `univ` (`TauCeti.polynomialHull_image_const_range_ofReal`), showing that boundedness is
  essential.

## Main declarations

* `TauCeti.holomorphicHull`: the `Ω`-holomorphic hull of `K ⊆ ℂ`.
* `TauCeti.IsRungeCompactPair`: an open set `Ω ⊆ ℂ` and a compact `K ⊆ Ω` filled in `Ω`.
* `IsClosed.holomorphicHull`, `Bornology.IsBounded.holomorphicHull`, `IsCompact.holomorphicHull`:
  closedness, boundedness, and compactness of the holomorphic hull.
* `TauCeti.biInf_holomorphicHull_edist_compl` and
  `TauCeti.sInf_image_infDist_frontier_holomorphicHull`: preservation of distances to `Ωᶜ` and
  `frontier Ω`.
* `TauCeti.holomorphicHull_subset_closedConvexHull` and
  `IsCompact.holomorphicHull_subset_convexHull`: inclusion in the closed convex hull (and convex
  hull when `K` is compact).
* `TauCeti.connectedComponentIn_sdiff_subset_holomorphicHull` and
  `IsOpen.isFilledIn_holomorphicHull`: maximum-principle inclusion of relatively compact
  complementary components and filledness of the hull.
* `IsOpen.isRungeCompactPair_holomorphicHull` and `IsOpen.isRungeCompactPair_filledExhaustion`:
  holomorphic hulls of compacts and stages of `TauCeti.filledExhaustion` give Runge compact pairs.
* `Bornology.IsBounded.holomorphicHull_univ_eq_preimage_polynomialHull` and
  `Bornology.IsBounded.holomorphicHull_univ_eq_self_iff_isPolynomiallyConvex`: agreement of
  `holomorphicHull univ K` with `TauCeti.polynomialHull` for bounded `K`.

## References

* A. Rainer, *Advanced Complex Analysis*, Lemma 11.3 and Theorem 12.1.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed., §1.3 and §2.7.
-/

public section

open Bornology Filter Metric Set
open scoped Topology ENNReal NNReal

namespace TauCeti

/-! ### Definition and elementary properties of the holomorphic hull -/

/-- The `Ω`-holomorphic hull of `K ⊆ ℂ`: the points `z ∈ Ω` at which every real upper bound
satisfied on `K` by an `Ω`-holomorphic function continues to hold. Quantifying over all real bounds
`B` makes the hull of the empty set empty. -/
def holomorphicHull (Ω K : Set ℂ) : Set ℂ :=
  {z | z ∈ Ω ∧ ∀ f : ℂ → ℂ, DifferentiableOn ℂ f Ω →
    ∀ B : ℝ, (∀ w ∈ K, ‖f w‖ ≤ B) → ‖f z‖ ≤ B}

theorem holomorphicHull_def (Ω K : Set ℂ) :
    holomorphicHull Ω K =
      {z | z ∈ Ω ∧ ∀ f : ℂ → ℂ, DifferentiableOn ℂ f Ω →
        ∀ B : ℝ, (∀ w ∈ K, ‖f w‖ ≤ B) → ‖f z‖ ≤ B} :=
  (rfl)

theorem mem_holomorphicHull_iff {Ω K : Set ℂ} {z : ℂ} :
    z ∈ holomorphicHull Ω K ↔
      z ∈ Ω ∧ ∀ f : ℂ → ℂ, DifferentiableOn ℂ f Ω →
        ∀ B : ℝ, (∀ w ∈ K, ‖f w‖ ≤ B) → ‖f z‖ ≤ B :=
  (Iff.rfl)

/-- The `Ω`-holomorphic hull of any set lies in `Ω`. -/
theorem holomorphicHull_subset_left (Ω K : Set ℂ) : holomorphicHull Ω K ⊆ Ω :=
  fun _ hz ↦ hz.1

@[simp]
theorem holomorphicHull_empty_left (K : Set ℂ) : holomorphicHull ∅ K = ∅ :=
  subset_empty_iff.mp (holomorphicHull_subset_left ∅ K)

@[simp]
theorem holomorphicHull_empty (Ω : Set ℂ) : holomorphicHull Ω ∅ = ∅ :=
  eq_empty_of_forall_notMem fun _ hz ↦
    (hz.2 (fun _ ↦ 0) (differentiableOn_const 0) (-1) (by simp)).not_gt (by norm_num)

/-- Every point of `K ∩ Ω` lies in `holomorphicHull Ω K`. -/
theorem inter_subset_holomorphicHull (Ω K : Set ℂ) : K ∩ Ω ⊆ holomorphicHull Ω K :=
  fun _ hz ↦ ⟨hz.2, fun _ _ _ hB ↦ hB _ hz.1⟩

/-- For `K ⊆ Ω`, `K` lies in its `Ω`-holomorphic hull. -/
theorem subset_holomorphicHull {Ω K : Set ℂ} (hKΩ : K ⊆ Ω) : K ⊆ holomorphicHull Ω K :=
  (subset_inter Subset.rfl hKΩ).trans (inter_subset_holomorphicHull Ω K)

/-- Monotonicity of `holomorphicHull` in the second argument. -/
@[gcongr]
theorem holomorphicHull_mono {Ω K L : Set ℂ} (h : K ⊆ L) :
    holomorphicHull Ω K ⊆ holomorphicHull Ω L :=
  fun _ hz ↦ ⟨hz.1, fun f hf B hB ↦ hz.2 f hf B fun w hw ↦ hB w (h hw)⟩

/-- Monotonicity of `holomorphicHull` in the ambient domain `Ω`. -/
@[gcongr]
theorem holomorphicHull_mono_left {Ω₁ Ω₂ K : Set ℂ} (h : Ω₁ ⊆ Ω₂) :
    holomorphicHull Ω₁ K ⊆ holomorphicHull Ω₂ K :=
  fun _ hz ↦ ⟨h hz.1, fun f hf B hB ↦ hz.2 f (hf.mono h) B hB⟩

/-- Taking the `Ω`-holomorphic hull is idempotent. -/
@[simp]
theorem holomorphicHull_holomorphicHull (Ω K : Set ℂ) :
    holomorphicHull Ω (holomorphicHull Ω K) = holomorphicHull Ω K :=
  (subset_holomorphicHull (holomorphicHull_subset_left Ω K)).antisymm' fun _ hz ↦
    ⟨hz.1, fun f hf B hB ↦ hz.2 f hf B fun _ hw ↦ hw.2 f hf B hB⟩

/-- A point `z ∈ Ω` outside `holomorphicHull Ω K` is strictly separated from `K` by an
`Ω`-holomorphic function of modulus `< 1` on `K` and `> 1` at `z`. -/
theorem exists_differentiableOn_norm_lt_one_lt_of_notMem_holomorphicHull {Ω K : Set ℂ} {z : ℂ}
    (hzΩ : z ∈ Ω) (hz : z ∉ holomorphicHull Ω K) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f Ω ∧ (∀ w ∈ K, ‖f w‖ < 1) ∧ 1 < ‖f z‖ := by
  rw [mem_holomorphicHull_iff] at hz
  push Not at hz
  obtain ⟨f, hf, B, hfK, hBz⟩ := hz hzΩ
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

/-- For compact `K ⊆ Ω`, membership in `holomorphicHull Ω K` is equivalent to the supremum bound
`‖f z‖ ≤ sSup ((‖f ·‖) '' K)` for every `Ω`-holomorphic `f` (including `K = ∅`, where `sSup ∅ = 0`).
-/
theorem _root_.IsCompact.mem_holomorphicHull_iff_norm_le_sSup {Ω K : Set ℂ}
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) {z : ℂ} :
    z ∈ holomorphicHull Ω K ↔
      z ∈ Ω ∧ ∀ f : ℂ → ℂ, DifferentiableOn ℂ f Ω → ‖f z‖ ≤ sSup ((fun w ↦ ‖f w‖) '' K) := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp only [holomorphicHull_empty, mem_empty_iff_false, image_empty, Real.sSup_empty, false_iff,
      not_and, not_forall, not_le]
    exact fun _ ↦ ⟨fun _ ↦ 1, differentiableOn_const 1, by simp⟩
  · refine ⟨fun hz ↦ ⟨hz.1, fun f hf ↦ ?_⟩, fun ⟨hzΩ, hz⟩ ↦ ?_⟩
    · have hbdd : BddAbove ((fun w ↦ ‖f w‖) '' K) :=
        (hK.image_of_continuousOn (hf.continuousOn.mono hKΩ).norm).bddAbove
      exact hz.2 f hf _ fun w hw ↦ le_csSup hbdd (mem_image_of_mem _ hw)
    · rw [mem_holomorphicHull_iff]
      exact ⟨hzΩ, fun f hf B hB ↦
        (hz f hf).trans (csSup_le (hne.image _) (forall_mem_image.mpr hB))⟩

/-! ### Distance to the complement, relative closedness, and compactness -/

/-- No point of `holomorphicHull Ω K` lies closer in extended distance to `ζ ∉ Ω` than `K` does. -/
theorem infEDist_le_edist_of_mem_holomorphicHull {Ω K : Set ℂ} {z ζ : ℂ}
    (hz : z ∈ holomorphicHull Ω K) (hζ : ζ ∉ Ω) :
    infEDist ζ K ≤ edist z ζ := by
  -- Test against `w ↦ (w - ζ)⁻¹`, which is holomorphic on `Ω`.
  by_contra hlt
  rw [not_le] at hlt
  have hKne : K.Nonempty := nonempty_iff_ne_empty.mpr fun h ↦ by simp [h] at hz
  have hzζ : z ≠ ζ := fun h ↦ hζ (h ▸ hz.1)
  have hd_pos : 0 < dist z ζ := dist_pos.mpr hzζ
  have hm_ne_top : infEDist ζ K ≠ ∞ := infEDist_ne_top hKne
  set m := (infEDist ζ K).toReal
  have hdm : dist z ζ < m := by
    rw [edist_dist] at hlt
    exact (ENNReal.ofReal_lt_iff_lt_toReal hd_pos.le hm_ne_top).mp hlt
  have hm_pos : 0 < m := hd_pos.trans hdm
  have hf : DifferentiableOn ℂ (fun w : ℂ ↦ (w - ζ)⁻¹) Ω :=
    (differentiableOn_id.sub (differentiableOn_const ζ)).inv fun w hw ↦
      sub_ne_zero.mpr fun h : w = ζ ↦ hζ (h ▸ hw)
  have hbound : ∀ w ∈ K, ‖(w - ζ)⁻¹‖ ≤ m⁻¹ := fun w hw ↦ by
    have hmw : m ≤ ‖w - ζ‖ := by
      rw [← dist_eq_norm, dist_comm]
      exact infDist_le_dist_of_mem hw
    rw [norm_inv]
    exact inv_anti₀ hm_pos hmw
  have hz_le := hz.2 _ hf m⁻¹ hbound
  rw [norm_inv, ← dist_eq_norm] at hz_le
  exact hdm.not_ge ((inv_le_inv₀ hd_pos hm_pos).mp hz_le)

/-- Ordinary-distance form of `TauCeti.infEDist_le_edist_of_mem_holomorphicHull`. -/
theorem infDist_le_dist_of_mem_holomorphicHull {Ω K : Set ℂ} {z ζ : ℂ}
    (hz : z ∈ holomorphicHull Ω K) (hζ : ζ ∉ Ω) :
    infDist ζ K ≤ dist z ζ := by
  rw [infDist, dist_edist]
  exact ENNReal.toReal_mono (edist_ne_top z ζ) (infEDist_le_edist_of_mem_holomorphicHull hz hζ)

/-- For `K ⊆ Ω`, `holomorphicHull Ω K` and `K` have the same extended set distance to `Ωᶜ`
(including `∞` when `K = ∅` or `Ω = univ`). -/
theorem biInf_holomorphicHull_edist_compl {Ω K : Set ℂ} (hKΩ : K ⊆ Ω) :
    (⨅ z ∈ holomorphicHull Ω K, ⨅ ζ ∈ Ωᶜ, edist z ζ) = ⨅ z ∈ K, ⨅ ζ ∈ Ωᶜ, edist z ζ := by
  refine le_antisymm (biInf_mono (subset_holomorphicHull hKΩ)) ?_
  refine le_iInf₂ fun z hz ↦ le_iInf₂ fun ζ hζ ↦ ?_
  refine le_trans ?_ (infEDist_le_edist_of_mem_holomorphicHull hz hζ)
  exact le_infEDist.mpr fun w hw ↦
    (iInf₂_le w hw).trans ((iInf₂_le ζ hζ).trans_eq (edist_comm w ζ))

/-- For `K ⊆ Ω`, `holomorphicHull Ω K` and `K` have the same extended set distance to `frontier Ω`.
-/
theorem biInf_holomorphicHull_edist_frontier {Ω K : Set ℂ} (hKΩ : K ⊆ Ω) :
    (⨅ z ∈ holomorphicHull Ω K, ⨅ ζ ∈ frontier Ω, edist z ζ) =
      ⨅ z ∈ K, ⨅ ζ ∈ frontier Ω, edist z ζ := by
  have hpoint {z : ℂ} (hz : z ∈ Ω) :
      (⨅ ζ ∈ frontier Ω, edist z ζ) = ⨅ ζ ∈ Ωᶜ, edist z ζ := by
    simpa only [Metric.infEDist] using
      Metric.infEDist_frontier_of_mem_closure (subset_closure hz)
  calc
    (⨅ z ∈ holomorphicHull Ω K, ⨅ ζ ∈ frontier Ω, edist z ζ)
        = ⨅ z ∈ holomorphicHull Ω K, ⨅ ζ ∈ Ωᶜ, edist z ζ :=
      iInf_congr fun z ↦ iInf_congr fun hz ↦ hpoint hz.1
    _ = ⨅ z ∈ K, ⨅ ζ ∈ Ωᶜ, edist z ζ := biInf_holomorphicHull_edist_compl hKΩ
    _ = ⨅ z ∈ K, ⨅ ζ ∈ frontier Ω, edist z ζ :=
      iInf_congr fun z ↦ iInf_congr fun hz ↦ (hpoint (hKΩ hz)).symm

/-- For `K ⊆ Ω`, `holomorphicHull Ω K` and `K` have the same ordinary distance to `Ωᶜ`. -/
theorem sInf_image_infDist_compl_holomorphicHull {Ω K : Set ℂ} (hKΩ : K ⊆ Ω) :
    sInf ((fun z ↦ infDist z Ωᶜ) '' holomorphicHull Ω K) =
      sInf ((fun z ↦ infDist z Ωᶜ) '' K) := by
  rw [Metric.sInf_image_infDist_eq_toReal_biInf, Metric.sInf_image_infDist_eq_toReal_biInf,
    biInf_holomorphicHull_edist_compl hKΩ]

/-- For `K ⊆ Ω`, `holomorphicHull Ω K` and `K` have the same ordinary distance to `frontier Ω`. -/
theorem sInf_image_infDist_frontier_holomorphicHull {Ω K : Set ℂ} (hKΩ : K ⊆ Ω) :
    sInf ((fun z ↦ infDist z (frontier Ω)) '' holomorphicHull Ω K) =
      sInf ((fun z ↦ infDist z (frontier Ω)) '' K) := by
  rw [Metric.sInf_image_infDist_eq_toReal_biInf, Metric.sInf_image_infDist_eq_toReal_biInf,
    biInf_holomorphicHull_edist_frontier hKΩ]

/-- The `Ω`-holomorphic hull of any set is relatively closed in `Ω`. -/
theorem closure_holomorphicHull_inter_eq (Ω K : Set ℂ) :
    closure (holomorphicHull Ω K) ∩ Ω = holomorphicHull Ω K := by
  refine Subset.antisymm (fun z ⟨hzcl, hzΩ⟩ ↦ ⟨hzΩ, fun f hf B hB ↦ ?_⟩)
    (subset_inter subset_closure (holomorphicHull_subset_left Ω K))
  have : (𝓝[holomorphicHull Ω K] z).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hzcl
  have hcont : Tendsto (fun w ↦ ‖f w‖) (𝓝[holomorphicHull Ω K] z) (𝓝 ‖f z‖) :=
    ((hf.continuousOn z hzΩ).mono (holomorphicHull_subset_left Ω K)).norm
  exact le_of_tendsto hcont (eventually_nhdsWithin_of_forall fun w hw ↦ hw.2 f hf B hB)

/-- If `K` is bounded, then `holomorphicHull Ω K` is bounded. -/
theorem _root_.Bornology.IsBounded.holomorphicHull {Ω K : Set ℂ} (hK : IsBounded K) :
    IsBounded (TauCeti.holomorphicHull Ω K) := by
  obtain ⟨R, hR⟩ := hK.subset_closedBall 0
  refine (isBounded_closedBall (x := (0 : ℂ)) (r := R)).subset fun z hz ↦
    mem_closedBall_zero_iff.mpr ?_
  exact hz.2 id differentiableOn_id R fun w hw ↦ mem_closedBall_zero_iff.mp (hR hw)

/-- If `K ⊆ Ω` is closed in `ℂ`, then `holomorphicHull Ω K` is closed in `ℂ`. -/
theorem _root_.IsClosed.holomorphicHull {Ω K : Set ℂ} (hK : IsClosed K) (hKΩ : K ⊆ Ω) :
    IsClosed (TauCeti.holomorphicHull Ω K) := by
  -- Relative closedness handles adherence inside `Ω`, while distance preservation keeps the hull
  -- away from every point of `Ωᶜ`.
  refine isClosed_of_closure_subset fun z hzcl ↦ ?_
  suffices hzΩ : z ∈ Ω from (closure_holomorphicHull_inter_eq Ω K).subset ⟨hzcl, hzΩ⟩
  by_contra hzΩ
  have hzK : z ∉ K := fun h ↦ hzΩ (hKΩ h)
  have hpos : 0 < infEDist z K := by
    rw [pos_iff_ne_zero]
    intro h0
    exact hzK (hK.closure_eq ▸ mem_closure_iff_infEDist_zero.mpr h0)
  have h0 : infEDist z (TauCeti.holomorphicHull Ω K) < infEDist z K := by
    rwa [mem_closure_iff_infEDist_zero.mp hzcl]
  obtain ⟨w, hw, hwz⟩ := infEDist_lt_iff.mp h0
  exact hwz.not_ge ((infEDist_le_edist_of_mem_holomorphicHull hw hzΩ).trans_eq (edist_comm w z))

/-- If `K ⊆ Ω` is compact, then `holomorphicHull Ω K` is compact. -/
theorem _root_.IsCompact.holomorphicHull {Ω K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    IsCompact (TauCeti.holomorphicHull Ω K) :=
  Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨hK.isClosed.holomorphicHull hKΩ, hK.isBounded.holomorphicHull⟩

/-! ### Convex hull comparison -/

/-- The `Ω`-holomorphic hull of any set lies in its closed real convex hull. -/
theorem holomorphicHull_subset_closedConvexHull (Ω K : Set ℂ) :
    holomorphicHull Ω K ⊆ closedConvexHull ℝ K := by
  -- Separate outside points by the real part of `l : StrongDual ℂ ℂ` and test against `exp (l ·)`.
  intro z hz
  by_contra hzK
  obtain ⟨l, u, hlK, hlz⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ)
    convex_closedConvexHull isClosed_closedConvexHull hzK
  have hf : DifferentiableOn ℂ (fun w ↦ Complex.exp (l w)) Ω :=
    (Complex.differentiable_exp.comp l.differentiable).differentiableOn
  have hbound : ∀ w ∈ K, ‖Complex.exp (l w)‖ ≤ Real.exp u := fun w hw ↦ by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr (hlK w (subset_closedConvexHull hw)).le
  have hle := hz.2 _ hf (Real.exp u) hbound
  rw [Complex.norm_exp, Real.exp_le_exp] at hle
  exact hlz.not_ge hle

/-- For compact `K ⊆ ℂ`, the `Ω`-holomorphic hull of `K` lies in its ordinary convex hull
`convexHull ℝ K`. -/
theorem _root_.IsCompact.holomorphicHull_subset_convexHull {Ω K : Set ℂ} (hK : IsCompact K) :
    holomorphicHull Ω K ⊆ convexHull ℝ K := by
  have hcl : closedConvexHull ℝ K = convexHull ℝ K := by
    rw [closedConvexHull_eq_closure_convexHull, (hK.convexHull (𝕜 := ℝ)).isClosed.closure_eq]
  exact hcl ▸ holomorphicHull_subset_closedConvexHull Ω K

/-! ### Maximum-principle inclusion, filledness, and Runge compact pairs -/

/-- **Maximum-principle inclusion.** In an open plane set `Ω`, if the connected component `C` of
`z` in `Ω \ K` has compact closure contained in `Ω`, then `closure C` lies in `holomorphicHull Ω K`.
-/
theorem closure_connectedComponentIn_sdiff_subset_holomorphicHull {Ω K : Set ℂ} (hΩ : IsOpen Ω)
    {z : ℂ} (hcpt : IsCompact (closure (connectedComponentIn (Ω \ K) z)))
    (hcl : closure (connectedComponentIn (Ω \ K) z) ⊆ Ω) :
    closure (connectedComponentIn (Ω \ K) z) ⊆ holomorphicHull Ω K := by
  set C := connectedComponentIn (Ω \ K) z
  have hfr : frontier C ⊆ closure K := frontier_connectedComponentIn_sdiff_subset_closure hΩ hcl
  intro w hw
  refine ⟨hcl hw, fun f hf B hB ↦ ?_⟩
  refine Complex.norm_le_of_forall_mem_frontier_norm_le (hcpt.isBounded.subset subset_closure)
    (hf.mono hcl).diffContOnCl (fun ζ hζ ↦ ?_) hw
  have hζΩ : ζ ∈ Ω := hcl hζ.1
  have hζcl : ζ ∈ closure (K ∩ Ω) := by
    rw [_root_.mem_closure_iff]
    intro V hV hζV
    obtain ⟨u, huVO, huK⟩ := _root_.mem_closure_iff.mp (hfr hζ) (V ∩ Ω) (hV.inter hΩ) ⟨hζV, hζΩ⟩
    exact ⟨u, huVO.1, huK, huVO.2⟩
  have : (𝓝[K ∩ Ω] ζ).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hζcl
  have hcont : Tendsto (fun u ↦ ‖f u‖) (𝓝[K ∩ Ω] ζ) (𝓝 ‖f ζ‖) :=
    ((hf.continuousOn ζ hζΩ).mono inter_subset_right).norm
  exact le_of_tendsto hcont (eventually_nhdsWithin_of_forall fun u hu ↦ hB u hu.1)

/-- In an open plane set `Ω`, every connected component of `Ω \ K` whose closure is compact and
contained in `Ω` lies in `holomorphicHull Ω K`. -/
theorem connectedComponentIn_sdiff_subset_holomorphicHull {Ω K : Set ℂ} (hΩ : IsOpen Ω) {z : ℂ}
    (hcpt : IsCompact (closure (connectedComponentIn (Ω \ K) z)))
    (hcl : closure (connectedComponentIn (Ω \ K) z) ⊆ Ω) :
    connectedComponentIn (Ω \ K) z ⊆ holomorphicHull Ω K :=
  subset_closure.trans (closure_connectedComponentIn_sdiff_subset_holomorphicHull hΩ hcpt hcl)

/-- For `K ⊆ Ω` with `Ω` open, `K` together with all relatively compact connected components of
`Ω \ K` in `Ω` lies inside `holomorphicHull Ω K`. -/
theorem union_relCompactComponents_subset_holomorphicHull {Ω K : Set ℂ}
    (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω) :
    K ∪ {z | z ∈ Ω \ K ∧
      IsCompact (closure (connectedComponentIn (Ω \ K) z)) ∧
      closure (connectedComponentIn (Ω \ K) z) ⊆ Ω} ⊆ holomorphicHull Ω K :=
  union_subset (subset_holomorphicHull hKΩ) fun _ ⟨hz, hcpt, hcl⟩ ↦
    connectedComponentIn_sdiff_subset_holomorphicHull hΩ hcpt hcl (mem_connectedComponentIn hz)

/-- The `Ω`-holomorphic hull of any set is filled in an open set `Ω`. -/
theorem _root_.IsOpen.isFilledIn_holomorphicHull {Ω : Set ℂ} (hΩ : IsOpen Ω) (K : Set ℂ) :
    IsFilledIn (holomorphicHull Ω K) Ω := by
  rw [isFilledIn_iff]
  rintro z hz ⟨hcpt, hcl⟩
  have hz' := connectedComponentIn_sdiff_subset_holomorphicHull hΩ hcpt hcl
    (mem_connectedComponentIn hz)
  rw [holomorphicHull_holomorphicHull] at hz'
  exact hz.2 hz'

/-- A Runge compact pair `(Ω, K)`: an open plane set `Ω` and a compact subset `K ⊆ Ω` that is
filled in `Ω` (`TauCeti.IsFilledIn K Ω`, meaning no connected component of `Ω \ K` is relatively
compact in `Ω`). -/
def IsRungeCompactPair (Ω K : Set ℂ) : Prop :=
  IsOpen Ω ∧ IsCompact K ∧ K ⊆ Ω ∧ IsFilledIn K Ω

theorem isRungeCompactPair_iff {Ω K : Set ℂ} :
    IsRungeCompactPair Ω K ↔ IsOpen Ω ∧ IsCompact K ∧ K ⊆ Ω ∧ IsFilledIn K Ω :=
  (Iff.rfl)

theorem IsRungeCompactPair.isOpen {Ω K : Set ℂ} (h : IsRungeCompactPair Ω K) : IsOpen Ω :=
  h.1

theorem IsRungeCompactPair.isCompact {Ω K : Set ℂ} (h : IsRungeCompactPair Ω K) : IsCompact K :=
  h.2.1

theorem IsRungeCompactPair.subset {Ω K : Set ℂ} (h : IsRungeCompactPair Ω K) : K ⊆ Ω :=
  h.2.2.1

theorem IsRungeCompactPair.isFilledIn {Ω K : Set ℂ} (h : IsRungeCompactPair Ω K) :
    IsFilledIn K Ω :=
  h.2.2.2

@[simp]
theorem isRungeCompactPair_empty {Ω : Set ℂ} : IsRungeCompactPair Ω ∅ ↔ IsOpen Ω :=
  ⟨fun h ↦ h.isOpen, fun hΩ ↦ ⟨hΩ, isCompact_empty, empty_subset Ω, by
    simpa only [holomorphicHull_empty] using hΩ.isFilledIn_holomorphicHull ∅⟩⟩

/-- For an open set `Ω` and a compact `K ⊆ Ω`, `(Ω, holomorphicHull Ω K)` is a Runge compact pair.
-/
theorem _root_.IsOpen.isRungeCompactPair_holomorphicHull {Ω K : Set ℂ} (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    IsRungeCompactPair Ω (holomorphicHull Ω K) :=
  ⟨hΩ, hK.holomorphicHull hKΩ, holomorphicHull_subset_left Ω K, hΩ.isFilledIn_holomorphicHull K⟩

/-- A compact set `K` equal to its `Ω`-holomorphic hull in an open `Ω` forms a Runge compact pair.
-/
theorem _root_.IsOpen.isRungeCompactPair_of_holomorphicHull_eq {Ω K : Set ℂ} (hΩ : IsOpen Ω)
    (hK : IsCompact K) (h : holomorphicHull Ω K = K) :
    IsRungeCompactPair Ω K :=
  h ▸ hΩ.isRungeCompactPair_holomorphicHull hK (h ▸ holomorphicHull_subset_left Ω K)

/-- Every stage `filledExhaustion Ω n` of an open plane set `Ω` forms a Runge compact pair
`(Ω, K n)`. -/
theorem _root_.IsOpen.isRungeCompactPair_filledExhaustion {Ω : Set ℂ} (hΩ : IsOpen Ω) (n : ℕ) :
    IsRungeCompactPair Ω (filledExhaustion Ω n) :=
  ⟨hΩ, isCompact_filledExhaustion Ω n, filledExhaustion_subset Ω n,
    hΩ.isFilledIn_filledExhaustion n⟩

/-- Every compact subset `K` of an open plane set `Ω` lies inside the interior of a compact `L`
forming a Runge compact pair `(Ω, L)`. -/
theorem _root_.IsOpen.exists_subset_interior_and_isRungeCompactPair {Ω K : Set ℂ}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ L, K ⊆ interior L ∧ IsRungeCompactPair Ω L := by
  obtain ⟨n, hn⟩ := hΩ.exists_subset_interior_filledExhaustion hK hKΩ
  exact ⟨filledExhaustion Ω n, hn, hΩ.isRungeCompactPair_filledExhaustion n⟩

/-! ### Comparison with polynomial hulls on `ℂ` -/

/-- For any index type `ι` and any `K ⊆ ℂ`, `holomorphicHull univ K` lies in the preimage of
`TauCeti.polynomialHull (Function.const ι '' K)` under `Function.const ι`. -/
theorem holomorphicHull_univ_subset_preimage_polynomialHull (ι : Type*) (K : Set ℂ) :
    holomorphicHull univ K ⊆ Function.const ι ⁻¹' polynomialHull (Function.const ι '' K) := by
  intro z hz
  rw [mem_preimage, mem_polynomialHull_iff]
  intro p c hc
  set q : Polynomial ℂ := MvPolynomial.aeval (fun _ : ι ↦ Polynomial.X) p
  have heval (w : ℂ) : MvPolynomial.eval (Function.const ι w) p = q.eval w := by
    change MvPolynomial.eval (fun _ ↦ w) p = _
    simpa [q] using
      (MvPolynomial.comp_aeval_apply (f := fun _ : ι ↦ Polynomial.X) (Polynomial.aeval w) p).symm
  rw [heval]
  refine hz.2 (fun w ↦ q.eval w) q.differentiable.differentiableOn c fun w hw ↦ ?_
  rw [← heval]
  exact hc _ (mem_image_of_mem _ hw)

/-- **Holomorphic hull on `ℂ` equals the polynomial hull.** For any nonempty index type `ι` (in
particular `ι = Fin 1`, where `Function.const (Fin 1)` is
`⇑(ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ).symm`) and any bounded set `K ⊆ ℂ`, the entire
holomorphic hull `holomorphicHull univ K` equals the preimage of
`TauCeti.polynomialHull (Function.const ι '' K)` under `Function.const ι`. -/
theorem _root_.Bornology.IsBounded.holomorphicHull_univ_eq_preimage_polynomialHull {ι : Type*}
    [Nonempty ι] {K : Set ℂ} (hK : IsBounded K) :
    TauCeti.holomorphicHull univ K =
      Function.const ι ⁻¹' polynomialHull (Function.const ι '' K) := by
  refine Subset.antisymm (holomorphicHull_univ_subset_preimage_polynomialHull ι K) fun z hz ↦ ?_
  by_contra hzH
  rw [mem_holomorphicHull_iff] at hzH
  push Not at hzH
  obtain ⟨g, hg_on, B, hgK, hBz⟩ := hzH (mem_univ z)
  have hg : Differentiable ℂ g := differentiableOn_univ.mp hg_on
  obtain ⟨R₀, hR₀⟩ := (hK.insert z).subset_ball 0
  set R : ℝ≥0 := ⟨max R₀ 1, by positivity⟩
  have hsub : insert z K ⊆ ball (0 : ℂ) R :=
    hR₀.trans (ball_subset_ball (le_max_left R₀ 1))
  obtain ⟨p, hfps⟩ : ∃ p, HasFPowerSeriesOnBall g p 0 ∞ :=
    ⟨_, hg.hasFPowerSeriesOnBall 0 zero_lt_one⟩
  have htend : TendstoUniformlyOn (fun n y ↦ p.partialSum n y) (fun y ↦ g (0 + y)) atTop
      (ball (0 : ℂ) R) :=
    hfps.tendstoUniformlyOn (ENNReal.coe_lt_top (r := R))
  set ε := (‖g z‖ - B) / 3 with hε_def
  have hε : 0 < ε := by linarith [hε_def]
  obtain ⟨n, hn⟩ := (Metric.tendstoUniformlyOn_iff.mp htend ε hε).exists
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  let P : MvPolynomial ι ℂ :=
    ∑ k ∈ Finset.range n, MvPolynomial.C (p.coeff k) * MvPolynomial.X i₀ ^ k
  have heval (y : ℂ) : MvPolynomial.eval (Function.const ι y) P = p.partialSum n y := by
    rw [FormalMultilinearSeries.partialSum]
    simp only [P, map_sum, map_mul, map_pow, MvPolynomial.eval_C, MvPolynomial.eval_X,
      Function.const_apply]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [p.apply_eq_pow_smul_coeff, smul_eq_mul, mul_comm]
  have hPK : ∀ u ∈ Function.const ι '' K, ‖MvPolynomial.eval u P‖ ≤ B + ε := by
    rintro _ ⟨w, hw, rfl⟩
    rw [heval]
    have hdist : ‖g w - p.partialSum n w‖ < ε := by
      simpa only [zero_add, dist_eq_norm] using hn w (hsub (mem_insert_of_mem z hw))
    have htri : ‖p.partialSum n w‖ ≤ ‖g w‖ + ‖g w - p.partialSum n w‖ := by
      simpa only [sub_sub_cancel] using norm_sub_le (g w) (g w - p.partialSum n w)
    linarith [hgK w hw]
  have hPz : ‖p.partialSum n z‖ ≤ B + ε := by
    rw [← heval]
    exact mem_polynomialHull_iff.mp hz P (B + ε) hPK
  have hdistz : ‖g z - p.partialSum n z‖ < ε := by
    simpa only [zero_add, dist_eq_norm] using hn z (hsub (mem_insert z K))
  have htriz : ‖g z‖ ≤ ‖p.partialSum n z‖ + ‖g z - p.partialSum n z‖ := by
    simpa only [add_sub_cancel] using norm_add_le (p.partialSum n z) (g z - p.partialSum n z)
  linarith [hε_def]

/-- For any nonempty index type `ι` and any bounded `K ⊆ ℂ`, `K` equals its entire holomorphic hull
`holomorphicHull univ K` if and only if `Function.const ι '' K` is polynomially convex. -/
theorem _root_.Bornology.IsBounded.holomorphicHull_univ_eq_self_iff_isPolynomiallyConvex
    {ι : Type*} [Nonempty ι] {K : Set ℂ} (hK : IsBounded K) :
    TauCeti.holomorphicHull univ K = K ↔ IsPolynomiallyConvex (Function.const ι '' K) := by
  rw [hK.holomorphicHull_univ_eq_preimage_polynomialHull (ι := ι), isPolynomiallyConvex_iff]
  refine ⟨fun h u hu ↦ ?_, fun h ↦ Subset.antisymm (fun z hz ↦ ?_) ?_⟩
  · obtain ⟨w, rfl⟩ := polynomialHull_image_const_subset_range K hu
    exact mem_image_of_mem _ (h.subset hu)
  · obtain ⟨w, hw, hwz⟩ := h hz
    exact Function.const_injective hwz ▸ hw
  · intro z hz
    exact subset_polynomialHull _ (mem_image_of_mem _ hz)

/-- The entire holomorphic hull of the real axis `ℝ ⊆ ℂ` is `ℝ` itself. -/
@[simp]
theorem holomorphicHull_univ_range_ofReal :
    holomorphicHull univ (range Complex.ofReal) = range Complex.ofReal := by
  -- `exp (I w)` and `exp (-I w)` have modulus `1` on `ℝ` and exclude nonzero imaginary parts.
  refine Subset.antisymm (fun z hz ↦ ?_) (subset_holomorphicHull (subset_univ _))
  have hexp (s : ℂ) (hs : s.re = 0) : ‖Complex.exp (s * z)‖ ≤ 1 := by
    refine hz.2 (fun w ↦ Complex.exp (s * w))
      (Complex.differentiable_exp.comp (differentiable_id.const_mul s)).differentiableOn 1 ?_
    rintro _ ⟨x, rfl⟩
    rw [Complex.norm_exp]
    have hre : (s * (x : ℂ)).re = 0 := by simp [Complex.mul_re, hs]
    simp [hre]
  have him1 : -z.im ≤ 0 := by
    have h := hexp Complex.I Complex.I_re
    rw [Complex.norm_exp, ← Real.exp_zero, Real.exp_le_exp] at h
    simpa [Complex.mul_re] using h
  have him2 : z.im ≤ 0 := by
    have h := hexp (-Complex.I) (by simp)
    rw [Complex.norm_exp, ← Real.exp_zero, Real.exp_le_exp] at h
    simpa [Complex.mul_re] using h
  exact ⟨z.re, Complex.ext (by simp) (by simp [le_antisymm him2 (by linarith)])⟩

end TauCeti
