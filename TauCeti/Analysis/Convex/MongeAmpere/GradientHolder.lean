/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.MongeAmpere.Engulfing
public import TauCeti.Analysis.Convex.TangentGrowth

/-!
# Hölder gradients from contained sections and Monge–Ampère bounds

For a differentiable convex globally Lipschitz potential, two-sided Aleksandrov measure bounds and a
common height of bounded sections with closure inside the domain give a Hölder bound for its
gradient on compact subsets of the allowed centers. The section containment and regularity
hypotheses are explicit. Engulfing gives a comparison of tangent errors, and the tangent-growth
estimate converts this comparison into the standard `HolderOnWith` conclusion.

This is a conditional section estimate in Caffarelli's interior regularity argument. The
engulfing theorem and its sources are in `TauCeti.Analysis.Convex.MongeAmpere.Engulfing`; the
analytic tangent-growth argument and its sources are in `TauCeti.Analysis.Convex.TangentGrowth`.
-/

public section

open MeasureTheory Measure Set Metric
open scoped Gradient ContDiff NNReal ENNReal

namespace TauCeti

private lemma reverse_gap_le_of_convexSection
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {Ω : Set E} {u : E → ℝ} {x y : E} {ℓ m : E →ₗ[ℝ] ℝ} {θ H : ℝ}
    (hx : x ∈ Ω) (hθ : 1 ≤ θ)
    (hD : 0 ≤ u y - u x - ℓ (y - x))
    (hH : 2 * (u y - u x - ℓ (y - x)) < H)
    (heng : ∀ h : ℝ, u y - u x - ℓ (y - x) < h → 2 * h ≤ H →
      convexSection Ω u x ℓ h ⊆ convexSection Ω u y m (θ * h)) :
    u x - u y - m (x - y) ≤ θ * (u y - u x - ℓ (y - x)) := by
  let D := u y - u x - ℓ (y - x)
  have hθ0 : 0 ≤ θ := le_trans zero_le_one hθ
  have hθ1 : 0 < θ + 1 := by linarith
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := min (ε / (θ + 1)) ((H - 2 * D) / 2)
  have hδ : 0 < δ := lt_min (div_pos hε hθ1) (by dsimp only [D]; linarith)
  have hδH : 2 * (D + δ) ≤ H := by
    have h := min_le_right (ε / (θ + 1)) ((H - 2 * D) / 2)
    dsimp only [δ]
    linarith
  have hxS : x ∈ convexSection Ω u x ℓ (D + δ) := by
    refine mem_convexSection_iff.2 ⟨hx, ?_⟩
    simp only [sub_self, map_zero]
    dsimp only [D] at hδ ⊢
    linarith
  have hs := mem_convexSection_iff.1
    (heng (D + δ) (by dsimp only [D]; linarith) hδH hxS)
  have hδε : θ * δ ≤ ε := by
    calc
      θ * δ ≤ (θ + 1) * δ := by nlinarith
      _ ≤ (θ + 1) * (ε / (θ + 1)) :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) hθ1.le
      _ = ε := mul_div_cancel₀ _ hθ1.ne'
  dsimp only [D] at hs hδε ⊢
  nlinarith only [hs.2, hδε]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- Two-sided Monge–Ampère bounds and a uniform height of sections compactly contained in the
open convex domain give a Hölder gradient for a differentiable convex globally Lipschitz
potential. -/
theorem exists_holderOnWith_gradient_of_mongeAmpereMeasure_bounds
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {Ω U K : Set E} [DecidablePred (· ∈ Ω)]
    (hΩ : IsOpen Ω) (hcΩ : Convex ℝ Ω) (hU : IsOpen U) (hUΩ : U ⊆ Ω)
    (hK : IsCompact K) (hKU : K ⊆ U)
    {u : E → ℝ} (hu : ConvexOn ℝ univ u) (hd : Differentiable ℝ u)
    {L : ℝ≥0} (hLip : LipschitzWith L u) {H : ℝ} (hH : 0 < H)
    (hsections : ∀ x ∈ U,
      Bornology.IsBounded (convexSection Ω u x (innerₗ E (gradient u x)) H) ∧
      closure (convexSection Ω u x (innerₗ E (gradient u x)) H) ⊆ Ω)
    {lam Lam : ℝ≥0} (hlam : 0 < lam)
    (hlo : (lam : ℝ≥0∞) • μ.restrict Ω ≤
      mongeAmpereMeasure μ (fun y ↦ if y ∈ Ω then (u y : EReal) else ⊤))
    (hhi : mongeAmpereMeasure μ (fun y ↦ if y ∈ Ω then (u y : EReal) else ⊤) ≤
      (Lam : ℝ≥0∞) • μ.restrict Ω) :
    ∃ α C : ℝ≥0, 0 < α ∧ α ≤ 1 ∧ HolderOnWith C α (gradient u) K := by
  obtain ⟨C, heng⟩ := exists_convexSection_subset_convexSection μ (E := E)
  let θ : ℝ≥0 := 1 + C * Lam / lam
  have hθ : 1 ≤ θ := by
    dsimp only [θ]
    exact le_add_of_nonneg_right (by positivity)
  have hθ' : (1 : ℝ) ≤ θ := by exact_mod_cast hθ
  have hsupport (x : E) : ∀ y ∈ Ω,
      u x + ((innerₗ E (gradient u x)) y - (innerₗ E (gradient u x)) x) ≤ u y := by
    intro y _
    have hs := hu.inner_gradient_sub_le (hd x) y
    rw [← map_sub, innerₗ_apply_apply]
    linarith only [hs]
  have hgrad (x : E) : ‖gradient u x‖ ≤ L := by
    rw [norm_gradient_eq_norm_fderiv]
    exact norm_fderiv_le_of_lipschitz ℝ hLip
  obtain ⟨ρ, hρ, hρU⟩ := hK.exists_cthickening_subset_open hU hKU
  let r := min ρ (H / (8 * ((L : ℝ) + 1)))
  have hr : 0 < r := lt_min hρ (by positivity)
  have hrρ : r ≤ ρ := min_le_left _ _
  have hrH : 8 * ((L : ℝ) + 1) * r ≤ H := by
    have h := (le_div_iff₀ (by positivity : 0 < 8 * ((L : ℝ) + 1))).1
      (show r ≤ H / (8 * ((L : ℝ) + 1)) from min_le_right _ _)
    simpa only [mul_comm] using h
  have hsoft : ∀ x ∈ K, ∀ z : E, ‖z - x‖ ≤ r →
      u z - u x - inner ℝ (gradient u x) (z - x) ≤
        θ * (u x - u z - inner ℝ (gradient u z) (x - z)) := by
    intro x hx z hz
    have hxU := hKU hx
    have hzU : z ∈ U := hρU (mem_cthickening_of_dist_le z x ρ K hx
      (by simpa only [dist_eq_norm] using hz.trans hrρ))
    let ℓ := innerₗ E (gradient u z)
    let m := innerₗ E (gradient u x)
    have hD : 0 ≤ u x - u z - ℓ (x - z) := by
      have hs := hsupport z x (hUΩ hxU)
      rw [← map_sub] at hs
      linarith only [hs]
    have hgap : u x - u z - ℓ (x - z) ≤ 2 * (L : ℝ) * ‖z - x‖ := by
      have huabs := hLip.dist_le_mul x z
      rw [dist_eq_norm, dist_eq_norm, Real.norm_eq_abs, norm_sub_rev x z] at huabs
      have hi : -inner ℝ (gradient u z) (x - z) ≤ L * ‖z - x‖ := by
        calc
          -inner ℝ (gradient u z) (x - z) ≤ |inner ℝ (gradient u z) (x - z)| := neg_le_abs _
          _ ≤ ‖gradient u z‖ * ‖x - z‖ := abs_real_inner_le_norm _ _
          _ ≤ L * ‖z - x‖ := by rw [norm_sub_rev x z]; gcongr; exact hgrad z
      simp only [ℓ, innerₗ_apply_apply]
      linarith only [huabs, hi, le_abs_self (u x - u z)]
    have hheight : 2 * (u x - u z - ℓ (x - z)) < H := by
      nlinarith [L.coe_nonneg]
    have hreverse := reverse_gap_le_of_convexSection (Ω := Ω) (u := u)
      (x := z) (y := x) (ℓ := ℓ) (m := m) (hUΩ hzU) hθ' hD hheight
      (fun h hh hH' ↦ ?_)
    · simpa only [ℓ, m, innerₗ_apply_apply] using hreverse
    · have hloc := isBounded_convexSection_and_closure_subset_of_le hH' (hsections z hzU)
      have hxS : x ∈ convexSection Ω u z ℓ h := mem_convexSection_iff.2
        ⟨hUΩ hxU, by linarith only [hh]⟩
      have hi := heng Ω u z ℓ h lam Lam hΩ (hu.subset (subset_univ _) hcΩ)
        (hsupport z) hloc.1 hloc.2 hlam hlo hhi x hxS m (hsupport x)
      simpa only [θ, NNReal.coe_add, NNReal.coe_one, NNReal.coe_div, NNReal.coe_mul] using hi
  obtain ⟨B, hB⟩ := exists_holderOnWith_gradient_of_soft_comparison hu hd hLip hr hθ hsoft
  refine ⟨θ⁻¹, B, inv_pos.2 (lt_of_lt_of_le zero_lt_one hθ), inv_le_one_of_one_le₀ hθ, hB⟩

end TauCeti
