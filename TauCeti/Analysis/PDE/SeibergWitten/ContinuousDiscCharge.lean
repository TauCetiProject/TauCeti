/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Winding.Number.Continuous
public import TauCeti.Analysis.PDE.SeibergWitten.DiscCharge
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox

/-!
# Framed charges of continuous discs

Let `(a, α)` be an abelian Higgs pair with `a = i b`, and let `Θ = i F_a + d(χ(|α|²) τ)` be its
cutoff current, where `χ` vanishes near `0`. For a `C²` disc `σ` whose boundary circle lies in
`{χ(|α|²) = 1}`, the charge `(2π)⁻¹ ∫_D σ^* Θ` is an integer, the winding number of `α ∘ σ`
around the boundary circle (`TauCeti.Analysis.PDE.SeibergWitten.DiscCharge`). This file extends
the charge to discs that are only continuous, as the **framed winding number**
`TauCeti.Contour.circleWindingNumber (α ∘ σ) z₀ r` of `α ∘ σ` along the boundary circle. It is
defined as soon as `α ∘ σ` has no zero on that circle, needs no derivative of `σ`, and agrees with
the integral for `C²` discs
(`TauCeti.SeibergWitten.integral_cutoffCurrent_comp_closedBall_eq_circleWindingNumber`).

For continuous discs, the laws of the charge are those of the winding number in
`TauCeti.Analysis.Contour.Winding.Number.Continuous`: it is invariant under homotopies of discs
whose boundary circles avoid the zeros of `α`
(`TauCeti.Contour.circleWindingNumber_eq_of_continuousOn_uncurry`), it is unchanged when the disc
is shrunk through an annulus free of zeros of `α ∘ σ`
(`TauCeti.Contour.circleWindingNumber_eq_of_annulus`), and it vanishes on a disc where `α ∘ σ`
has no zero (`TauCeti.Contour.circleWindingNumber_eq_zero`).

The main result is the **stabilization of continuous charges**
(`TauCeti.SeibergWitten.exists_int_eventually_circleWindingNumber_comp_eq`). Along a family of
pairs `(bₖ, αₖ)` whose cutoff currents converge as distributions, the charges of a fixed `C²`
disc are eventually constant
(`TauCeti.SeibergWitten.exists_int_eventually_integral_cutoffCurrent_comp_closedBall_eq`).
The same holds for a continuous disc `σ`, provided all boundary points within a fixed distance
`δ` of `σ` of the boundary circle eventually lie in `{χ(|αₖ|²) = 1}`. Indeed `σ` is uniformly
approximated on the boundary circle by smooth discs `σ'`, within `δ / 2`, and the straight-line
homotopy from `σ` to `σ'` keeps the boundary circle in the region where `αₖ` has no zero, so the
continuous charges of `σ` are those of `σ'`, which stabilize.

In Taubes's passage from Seiberg–Witten solutions to pseudoholomorphic curves, these integers are
the charges of continuous discs whose boundary avoids the limiting support, on which the
reconstruction of the limiting curve and its multiplicities is based.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

noncomputable section

open ContinuousAlternatingMap Complex Filter Set MeasureTheory TauCeti.Contour
open scoped Topology Real ContDiff

namespace TauCeti.SeibergWitten

variable {χ : ℝ → ℝ}

/-- **The charge of a `C²` disc is its framed winding number.** Let `σ : ℂ → E` be a `C²` disc such
that `χ(|α|²) = 1` along `σ` of the boundary circle of a closed disc. Then the integral over the
disc of the pullback by `σ` of the cutoff current is `2π` times the winding number of `α ∘ σ`
along the boundary circle. -/
theorem integral_cutoffCurrent_comp_closedBall_eq_circleWindingNumber {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {α : E → ℂ} {b : E → E [⋀^Fin 1]→L[ℝ] ℝ}
    {σ : ℂ → E} {z₀ : ℂ} {r : ℝ} (hr : 0 ≤ r) (hα : ContDiff ℝ 2 α) (hb : ContDiff ℝ 1 b)
    (hχ : ContDiff ℝ 1 χ) (hχ₀ : χ =ᶠ[𝓝 0] 0) (hσ : ContDiff ℝ 2 σ)
    (hbd : ∀ θ, χ (normSq (α (σ (circleMap z₀ r θ)))) = 1) :
    ∫ z in Metric.closedBall z₀ r,
      (cutoffCurrent χ b α (σ z)).compContinuousLinearMap (fderiv ℝ σ z) ![1, I] =
        2 * π * circleWindingNumber (α ∘ σ) z₀ r := by
  obtain ⟨n, hn, hI⟩ := exists_int_integral_cutoffCurrent_comp_closedBall hr hα hb hχ hχ₀ hσ hbd
  -- On the boundary circle `χ(|α ∘ σ|²) = 1`, and `χ` vanishes near `0`, so `α ∘ σ` has no zero.
  have hne (z : ℂ) (hz : z ∈ Metric.sphere z₀ |r|) : (α ∘ σ) z ≠ 0 := by
    obtain ⟨θ, rfl⟩ : z ∈ range (circleMap z₀ r) := by rwa [range_circleMap]
    intro h
    have h₁ := hbd θ
    rw [← Function.comp_apply (f := α), h, normSq_zero, hχ₀.eq_of_nhds] at h₁
    exact zero_ne_one h₁
  have hw := coe_circleWindingNumber_eq_windingNumber (hα.comp hσ).continuous.continuousOn hne
    ((hα.comp (hσ.comp (contDiff_circleMap z₀ r))).of_le one_le_two)
  rw [Function.comp_assoc, hn, Int.cast_inj] at hw
  rw [hI, hw]

/-- **Stabilization of the charges of a continuous disc.** Let `(bₖ, αₖ)` be a family of abelian
Higgs pairs along a filter `l`, with cutoff currents `Θₖ`, and let `σ` be a continuous disc.
Suppose that eventually along `l` every point within distance `δ` of `σ` of the boundary circle
of a closed disc lies in `{χ(|αₖ|²) = 1}`, and that the coefficients of `Θₖ` converge as
distributions: for every smooth compactly supported `φ` and every pair of vectors `m`, the
pairings `∫ φ(y) Θₖ(y)(m) dμ(y)` converge. Then the framed winding numbers of `αₖ ∘ σ` along the
boundary circle are eventually constant. -/
theorem exists_int_eventually_circleWindingNumber_comp_eq {ι E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {l : Filter ι} [l.NeBot]
    {α : ι → E → ℂ} {b : ι → E → E [⋀^Fin 1]→L[ℝ] ℝ} {σ : ℂ → E} {z₀ : ℂ} {r δ : ℝ}
    (hr : 0 ≤ r) (hδ : 0 < δ) (hα : ∀ k, ContDiff ℝ 2 (α k)) (hb : ∀ k, ContDiff ℝ 1 (b k))
    (hχ : ContDiff ℝ 1 χ) (hχ₀ : χ =ᶠ[𝓝 0] 0) (hσ : Continuous σ)
    (hbd : ∀ᶠ k in l, ∀ p ∈ Metric.closedBall (0 : E) δ, ∀ θ,
      χ (normSq (α k (σ (circleMap z₀ r θ) + p))) = 1)
    (hlim : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → ∀ m : Fin 2 → E,
      ∃ L, Tendsto (fun k ↦ ∫ y, φ y * cutoffCurrent χ (b k) (α k) y m ∂μ) l (𝓝 L)) :
    ∃ n : ℤ, ∀ᶠ k in l, circleWindingNumber (α k ∘ σ) z₀ r = n := by
  -- A smooth disc `σ'` within `δ / 2` of `σ` on the boundary circle.
  obtain ⟨σ', hσ', hclose⟩ : ∃ σ' : ℂ → E, ContDiff ℝ ∞ σ' ∧
      ∀ w ∈ Metric.sphere z₀ r, dist (σ' w) (σ w) < δ / 2 := by
    have h := ContinuousMap.dense_setOfPred_contDiff (E := ℂ) (F := E) ⟨σ, hσ⟩
    rw [mem_closure_iff_nhds_basis
      (nhds_basis_uniformity Metric.uniformity_basis_dist.compactConvergenceUniformity)] at h
    obtain ⟨g, hg, hgK⟩ := h ⟨Metric.sphere z₀ r, δ / 2⟩ ⟨isCompact_sphere z₀ r, half_pos hδ⟩
    exact ⟨g, hg, fun w hw ↦ hgK w hw⟩
  have hσ'₂ : ContDiff ℝ 2 σ' := hσ'.of_le (by norm_cast)
  -- The charges of `σ'` stabilize: its translates by at most `δ / 2` stay within `δ` of `σ`.
  have hoff (θ : ℝ) (p : E) (hp : p ∈ Metric.closedBall (0 : E) (δ / 2)) :
      σ' (circleMap z₀ r θ) + p = σ (circleMap z₀ r θ) +
        (σ' (circleMap z₀ r θ) - σ (circleMap z₀ r θ) + p) := by abel
  have hoff_mem (θ : ℝ) (p : E) (hp : p ∈ Metric.closedBall (0 : E) (δ / 2)) :
      σ' (circleMap z₀ r θ) - σ (circleMap z₀ r θ) + p ∈ Metric.closedBall (0 : E) δ := by
    rw [mem_closedBall_zero_iff] at hp ⊢
    have h := hclose _ (circleMap_mem_sphere z₀ hr θ)
    rw [dist_eq_norm] at h
    linarith [norm_add_le (σ' (circleMap z₀ r θ) - σ (circleMap z₀ r θ)) p]
  obtain ⟨n, hn⟩ := exists_int_eventually_integral_cutoffCurrent_comp_closedBall_eq hr
    (half_pos hδ) hα hb hχ hχ₀ hσ'₂
    (hbd.mono fun k hk p hp θ ↦ by rw [hoff θ p hp]; exact hk _ (hoff_mem θ p hp) θ) hlim
  refine ⟨n, (hbd.and hn).mono fun k ⟨hk, hkn⟩ ↦ ?_⟩
  -- `σ'` is in the boundary region, so its winding number is its charge `n`.
  have hσ'n : circleWindingNumber (α k ∘ σ') z₀ r = n := by
    have h := integral_cutoffCurrent_comp_closedBall_eq_circleWindingNumber hr (hα k) (hb k) hχ
      hχ₀ hσ'₂ fun θ ↦ by
        have h := hk _ (hoff_mem θ 0 (Metric.mem_closedBall_self (half_pos hδ).le)) θ
        rwa [add_zero, add_sub_cancel] at h
    rw [hkn] at h
    exact_mod_cast (mul_left_cancel₀ (by positivity) h).symm
  -- Every segment from `σ` to `σ'` on the boundary circle stays within `δ / 2` of `σ`, where
  -- `αₖ` has no zero.
  refine (circleWindingNumber_comp_eq_of_forall_mem_segment (hα k).continuous hσ.continuousOn
    hσ'.continuous.continuousOn fun z hz y hy ↦ ?_).trans hσ'n
  obtain ⟨θ, rfl⟩ : z ∈ range (circleMap z₀ r) := by rwa [range_circleMap]
  rw [segment_eq_image'] at hy
  obtain ⟨s, hs, rfl⟩ := hy
  have hmem : s • (σ' (circleMap z₀ r θ) - σ (circleMap z₀ r θ)) ∈
      Metric.closedBall (0 : E) δ := by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg hs.1]
    have h₁ := hclose _ (circleMap_mem_sphere z₀ hr θ)
    rw [dist_eq_norm] at h₁
    nlinarith [norm_nonneg (σ' (circleMap z₀ r θ) - σ (circleMap z₀ r θ)), hs.2]
  intro h
  have h₁ := hk _ hmem θ
  rw [h, normSq_zero, hχ₀.eq_of_nhds] at h₁
  exact zero_ne_one h₁

end TauCeti.SeibergWitten
