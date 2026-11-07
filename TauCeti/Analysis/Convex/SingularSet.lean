/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Subdifferential
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.Topology.Instances.Rat

/-!
# Lipschitz graphs covering multivalued subgradients

For a function on `E × ℝ`, consider points admitting two continuous subgradients with different
vertical components. These points lie in a countable union of globally Lipschitz graphs over
`E`. No convexity or regularity assumption on the function is needed: the monotonicity of its
subdifferential suffices. In finite dimensions, applying this result in each coordinate direction
is the geometric ingredient for differentiability outside countably many Lipschitz hypersurfaces.

The quantitative step separates the vertical components by `b - a > 0` and bounds the norms of
the subgradients by `M`. On such a slice, the height is `2 * M / (b - a)`-Lipschitz. Rational
separations and natural norm bounds give the countable cover. Mathlib's McShane extension
`LipschitzOnWith.extend_real` extends the slice heights to all of `E`. Consequently, a measure
vanishing on every Lipschitz graph sees a unique vertical subgradient component almost everywhere.

## References

* L. Zajíček, *On the differentiation of convex functions in finite and infinite dimensional
  spaces*, Czechoslovak Mathematical Journal 29 (1979), 340–348, for the stronger covering of
  singular sets by differences of convex hypersurfaces.
* C. Villani, *Topics in Optimal Transportation*, §2.4, for the use of Lipschitz hypersurface
  coverings in transport with sources not charging hypersurfaces.
-/

public section

open Set
open scoped NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : E × ℝ → EReal}

/-- Separating the vertical components of bounded subgradients controls differences of heights.
The subgradient at the lower point has vertical component at least `b`, and that at the higher
point has vertical component at most `a`. -/
private theorem sub_mul_le_norm_fst_sub_of_mem_subdifferential
    {x y : E × ℝ} {α β : (E × ℝ) →L[ℝ] ℝ} {a b M : ℝ}
    (hα : α ∈ subdifferential (topDualPairing ℝ (E × ℝ)).flip f x)
    (hβ : β ∈ subdifferential (topDualPairing ℝ (E × ℝ)).flip f y)
    (hαM : ‖α‖ ≤ M) (hβM : ‖β‖ ≤ M)
    (hαa : α (0, 1) ≤ a) (hbβ : b ≤ β (0, 1)) (hyx : y.2 ≤ x.2) :
    (b - a) * (x.2 - y.2) ≤ 2 * M * ‖x.1 - y.1‖ := by
  have hmono := apply_le_apply_of_mem_subdifferential
    (topDualPairing ℝ (E × ℝ)).flip hβ hα
  simp only [LinearMap.flip_apply, topDualPairing_apply] at hmono
  have hsplit (ℓ : (E × ℝ) →L[ℝ] ℝ) :
      ℓ (x - y) = ℓ (x.1 - y.1, 0) + (x.2 - y.2) * ℓ (0, 1) := by
    have heq : x - y = (x.1 - y.1, 0) + (x.2 - y.2) • (0, 1) := by ext <;> simp
    rw [heq, map_add, map_smul]
    rfl
  rw [hsplit α, hsplit β] at hmono
  have hαbound : α (x.1 - y.1, 0) ≤ M * ‖x.1 - y.1‖ := by
    exact (le_abs_self _).trans <| (α.le_opNorm _).trans <| by
      simpa using mul_le_mul_of_nonneg_right hαM (norm_nonneg (x.1 - y.1))
  have hβbound : -(M * ‖x.1 - y.1‖) ≤ β (x.1 - y.1, 0) := by
    have h := (β.le_opNorm (x.1 - y.1, 0)).trans
      (by simpa using mul_le_mul_of_nonneg_right hβM (norm_nonneg (x.1 - y.1)))
    exact (neg_le_neg h).trans (neg_abs_le _)
  have ht : 0 ≤ x.2 - y.2 := sub_nonneg.mpr hyx
  have ha := mul_le_mul_of_nonneg_left hαa ht
  have hb := mul_le_mul_of_nonneg_left hbβ ht
  nlinarith

/-- A set on which bounded subgradients have uniformly separated vertical components lies on a
globally Lipschitz graph. The bound is quantitative and does not require a finite-dimensional
base or a convexity assumption on `f`. -/
theorem exists_lipschitzWith_graph_of_subdifferential_separation
    {s : Set (E × ℝ)} {a b : ℝ} (hab : a < b) (M : ℝ≥0)
    (hs : ∀ x ∈ s, ∃ α β : (E × ℝ) →L[ℝ] ℝ,
      α ∈ subdifferential (topDualPairing ℝ (E × ℝ)).flip f x ∧
      β ∈ subdifferential (topDualPairing ℝ (E × ℝ)).flip f x ∧
      ‖α‖ ≤ M ∧ ‖β‖ ≤ M ∧ α (0, 1) ≤ a ∧ b ≤ β (0, 1)) :
    ∃ g : E → ℝ, LipschitzWith (2 * M / NNReal.mk (b - a) (sub_nonneg.mpr hab.le)) g ∧
      ∀ x ∈ s, x.2 = g x.1 := by
  classical
  let K : ℝ≥0 := 2 * M / NNReal.mk (b - a) (sub_nonneg.mpr hab.le)
  have hheight (x : E × ℝ) (hx : x ∈ s) (y : E × ℝ) (hy : y ∈ s) :
      dist x.2 y.2 ≤ K * dist x.1 y.1 := by
    obtain ⟨αx, βx, hαx, hβx, hαxM, hβxM, hαxa, hbβx⟩ := hs x hx
    obtain ⟨αy, βy, hαy, hβy, hαyM, hβyM, hαya, hbβy⟩ := hs y hy
    have hK : (K : ℝ) = 2 * M / (b - a) := by
      simp [K]
    rw [hK, dist_eq_norm, Real.norm_eq_abs, div_mul_eq_mul_div,
      le_div_iff₀ (sub_pos.mpr hab), dist_eq_norm]
    rcases le_total y.2 x.2 with h | h
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]
      nlinarith [sub_mul_le_norm_fst_sub_of_mem_subdifferential
        hαx hβy hαxM hβyM hαxa hbβy h]
    · rw [abs_of_nonpos (sub_nonpos.mpr h)]
      have hbound := sub_mul_le_norm_fst_sub_of_mem_subdifferential
        hαy hβx hαyM hβxM hαya hbβx h
      rw [norm_sub_rev y.1 x.1] at hbound
      nlinarith
  let g : E → ℝ := fun u => (Function.invFunOn Prod.fst s u).2
  have hg (x : E × ℝ) (hx : x ∈ s) : g x.1 = x.2 := by
    have hex : ∃ y ∈ s, y.1 = x.1 := ⟨x, hx, rfl⟩
    have h := hheight _ (Function.invFunOn_mem hex) x hx
    rw [Function.invFunOn_eq hex, dist_self, mul_zero] at h
    exact dist_le_zero.mp h
  have hgL : LipschitzOnWith K g (Prod.fst '' s) := by
    apply LipschitzOnWith.of_dist_le_mul
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hg x hx, hg y hy]
    exact hheight x hx y hy
  obtain ⟨G, hG, hGg⟩ := hgL.extend_real
  exact ⟨G, hG, fun x hx => (hg x hx).symm.trans (hGg ⟨x, hx, rfl⟩)⟩

/-- The points with two subgradients having different vertical components are covered by a
countable family of globally Lipschitz graphs. The index records two rational slope cutoffs
and a natural bound for the norms of the subgradients. -/
theorem exists_lipschitzWith_graphs_cover_subdifferential_vertical_ne
    (f : E × ℝ → EReal) :
    ∃ (K : ℚ × ℚ × ℕ → ℝ≥0) (g : (ℚ × ℚ × ℕ) → E → ℝ),
      (∀ i, LipschitzWith (K i) (g i)) ∧
      ∀ (x : E × ℝ) (α β : (E × ℝ) →L[ℝ] ℝ),
        α ∈ subdifferential (topDualPairing ℝ (E × ℝ)).flip f x →
        β ∈ subdifferential (topDualPairing ℝ (E × ℝ)).flip f x →
        α (0, 1) ≠ β (0, 1) → ∃ i, x.2 = g i x.1 := by
  classical
  let s : (ℚ × ℚ × ℕ) → Set (E × ℝ) := fun i =>
    {x | ∃ α β : (E × ℝ) →L[ℝ] ℝ,
      α ∈ subdifferential (topDualPairing ℝ (E × ℝ)).flip f x ∧
      β ∈ subdifferential (topDualPairing ℝ (E × ℝ)).flip f x ∧
      ‖α‖ ≤ (i.2.2 : ℝ) ∧ ‖β‖ ≤ (i.2.2 : ℝ) ∧
      α (0, 1) ≤ (i.1 : ℝ) ∧ (i.2.1 : ℝ) ≤ β (0, 1)}
  have hex (i : ℚ × ℚ × ℕ) :
      ∃ (K : ℝ≥0) (g : E → ℝ), LipschitzWith K g ∧
        (i.1 < i.2.1 → ∀ x ∈ s i, x.2 = g x.1) := by
    by_cases h : i.1 < i.2.1
    · obtain ⟨g, hg, hs⟩ := exists_lipschitzWith_graph_of_subdifferential_separation
        (f := f) (s := s i) (a := i.1) (b := i.2.1) (by exact_mod_cast h)
        (i.2.2 : ℝ≥0) (by simp [s])
      exact ⟨_, g, hg, fun _ => hs⟩
    · exact ⟨0, 0, LipschitzWith.const 0, fun h' => (h h').elim⟩
  choose K g hg hsg using hex
  refine ⟨K, g, hg, ?_⟩
  have hcover (x : E × ℝ) (α β : (E × ℝ) →L[ℝ] ℝ)
      (hα : α ∈ subdifferential (topDualPairing ℝ (E × ℝ)).flip f x)
      (hβ : β ∈ subdifferential (topDualPairing ℝ (E × ℝ)).flip f x)
      (hαβ : α (0, 1) < β (0, 1)) : ∃ i, x.2 = g i x.1 := by
    obtain ⟨a, hαa, haβ⟩ := exists_rat_btwn hαβ
    obtain ⟨b, hab, hbβ⟩ := exists_rat_btwn haβ
    obtain ⟨N, hN⟩ := exists_nat_gt (max ‖α‖ ‖β‖)
    have hab' : a < b := by exact_mod_cast hab
    refine ⟨(a, b, N), hsg (a, b, N) hab' x ?_⟩
    exact ⟨α, β, hα, hβ, (le_max_left _ _).trans hN.le,
      (le_max_right _ _).trans hN.le, hαa.le, hbβ.le⟩
  intro x α β hα hβ hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact hcover x α β hα hβ h
  · exact hcover x β α hβ hα h

/-- A measure vanishing on every Lipschitz graph sees no ambiguity in the vertical component of
subgradients almost everywhere. No measurability assumption on `f` or finiteness of the measure
is needed. -/
theorem ae_subdifferential_vertical_eq_of_null_lipschitz_graphs
    [MeasurableSpace (E × ℝ)] (f : E × ℝ → EReal) {μ : MeasureTheory.Measure (E × ℝ)}
    (hμ : ∀ (K : ℝ≥0) (g : E → ℝ), LipschitzWith K g → μ {x | x.2 = g x.1} = 0) :
    ∀ᵐ x ∂μ, ∀ α ∈ subdifferential (topDualPairing ℝ (E × ℝ)).flip f x,
      ∀ β ∈ subdifferential (topDualPairing ℝ (E × ℝ)).flip f x, α (0, 1) = β (0, 1) := by
  obtain ⟨K, g, hg, hcover⟩ := exists_lipschitzWith_graphs_cover_subdifferential_vertical_ne f
  have hnull : μ (⋃ i, {x | x.2 = g i x.1}) = 0 :=
    MeasureTheory.measure_iUnion_null fun i => hμ (K i) (g i) (hg i)
  filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hnull] with x hx
  intro α hα β hβ
  by_contra hne
  obtain ⟨i, hi⟩ := hcover x α β hα hβ hne
  exact hx (mem_iUnion.mpr ⟨i, hi⟩)

end TauCeti
