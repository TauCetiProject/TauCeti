/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.BoundedMeanOscillation
import TauCeti.Analysis.Normed.Group.UniformContinuity
import TauCeti.Topology.Algebra.Order.Field

/-!
# Mean oscillation of bilinear products

For a continuous bilinear map `B`, an essentially bounded `f` and a bounded `g`,

`η_{B(f, g)}(r) ≤ ‖B‖ (2 N η_f(r) + M ε)`

whenever `‖f‖ ≤ M` almost everywhere, `‖g‖ ≤ N`, and `g` varies by at most `ε` between points at
distance less than `2 r` (`ContinuousLinearMap.vmoModulus_bilinear_le`). So `x ↦ B (f x) (g x)`
has vanishing mean oscillation when `f` does and `g` is uniformly continuous
(`TauCeti.MemVMO.bilinear`). Flattening the boundary of a domain multiplies the coefficients of
an equation by derivatives of the chart, which are bounded and uniformly continuous; this result
shows that coefficients of vanishing mean oscillation stay so.

## The argument

`B (f x) (g x) - B (f y) (g y) = B (f x - f y) (g x) + B (f y) (g x - g y)` bounds the average of
`‖B (f x) (g x) - B (f y) (g y)‖` over pairs of points of a ball by
`‖B‖ (N ⨍⨍ ‖f x - f y‖ + M ε)`, and the average of `‖f x - f y‖` over pairs is at most twice the
mean oscillation of `f`.

## References

* D. Sarason, *Functions of vanishing mean oscillation*, Trans. Amer. Math. Soc. **207** (1975),
  391–405.
-/

public section

namespace TauCeti

open Filter MeasureTheory Metric Set
open scoped ENNReal NNReal Topology

section Bilinear

variable {X F G H : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
  [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H] {μ : Measure X}
  {f : X → F} {g : X → G}

/-- **Mean oscillation of a product.** Let `B` be a continuous bilinear map, `f` bounded by `M`
almost everywhere and `g` bounded by `N`, and suppose that `g` varies by at most `ε` between points
at distance less than `2 r`. Then the mean oscillation of `x ↦ B (f x) (g x)` on balls of radius at
most `r` is at most `‖B‖ (2 N η_f(r) + M ε)`. -/
theorem _root_.ContinuousLinearMap.vmoModulus_bilinear_le (B : F →L[ℝ] G →L[ℝ] H)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) {M N : ℝ≥0} {ε : ℝ≥0∞} {r : ℝ}
    (hfM : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ M) (hgN : ∀ x, ‖g x‖ₑ ≤ N)
    (hgε : ∀ x y, dist x y < 2 * r → ‖g x - g y‖ₑ ≤ ε) :
    vmoModulus (fun x => B (f x) (g x)) μ r ≤ ‖B‖ₑ * (2 * N * vmoModulus f μ r + M * ε) := by
  refine vmoModulus_le fun c s hs => ?_
  rcases eq_or_ne (μ (ball c s)) 0 with h0 | h0
  · simp [Measure.restrict_eq_zero.2 h0]
  rcases eq_or_ne (μ (ball c s)) ⊤ with htop | htop
  · simp [setLAverage_eq, htop]
  -- For `x, y ∈ B(c, s)`, split `B (f x) (g x) - B (f y) (g y)` as
  -- `B (f x - f y) (g x) + B (f y) (g x - g y)`.
  have hpt : ∀ᵐ x ∂μ.restrict (ball c s), ∀ᵐ y ∂μ.restrict (ball c s),
      ‖B (f x) (g x) - B (f y) (g y)‖ₑ ≤ ‖B‖ₑ * N * ‖f x - f y‖ₑ + ‖B‖ₑ * M * ε := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae hfM] with y hy hyM
    have hxy : dist x y < 2 * r := by
      have := dist_triangle_right x y c
      rw [mem_ball] at hx hy
      linarith
    have heq : B (f x) (g x) - B (f y) (g y) = B (f x - f y) (g x) + B (f y) (g x - g y) := by
      simp only [map_sub, FunLike.coe_sub, Pi.sub_apply]
      abel
    calc ‖B (f x) (g x) - B (f y) (g y)‖ₑ
        ≤ ‖B (f x - f y) (g x)‖ₑ + ‖B (f y) (g x - g y)‖ₑ := heq ▸ eNorm_add_le _ _
      _ ≤ ‖B‖ₑ * ‖f x - f y‖ₑ * ‖g x‖ₑ + ‖B‖ₑ * ‖f y‖ₑ * ‖g x - g y‖ₑ :=
          add_le_add (B.le_opENorm₂ _ _) (B.le_opENorm₂ _ _)
      _ ≤ ‖B‖ₑ * ‖f x - f y‖ₑ * N + ‖B‖ₑ * M * ε := by
          gcongr
          exacts [hgN x, hgε x y hxy]
      _ = ‖B‖ₑ * N * ‖f x - f y‖ₑ + ‖B‖ₑ * M * ε := by ring
  calc ⨍⁻ x in ball c s, ‖B (f x) (g x) - ⨍ z in ball c s, B (f z) (g z) ∂μ‖ₑ ∂μ
      ≤ ⨍⁻ x in ball c s, ⨍⁻ y in ball c s, ‖B (f x) (g x) - B (f y) (g y)‖ₑ ∂μ ∂μ :=
        setLAverage_enorm_sub_setAverage_le_setLAverage_setLAverage
          (B.aestronglyMeasurable_comp₂ hf hg).restrict
    _ ≤ ⨍⁻ x in ball c s, ⨍⁻ y in ball c s,
          (‖B‖ₑ * N * ‖f x - f y‖ₑ + ‖B‖ₑ * M * ε) ∂μ ∂μ :=
        laverage_mono_ae (hpt.mono fun x hx => laverage_mono_ae hx)
    _ = ‖B‖ₑ * N * ⨍⁻ x in ball c s, ⨍⁻ y in ball c s, ‖f x - f y‖ₑ ∂μ ∂μ + ‖B‖ₑ * M * ε := by
        have hBN : ‖B‖ₑ * (N : ℝ≥0∞) ≠ ⊤ := by finiteness
        simp_rw [setLAverage_add_const h0 htop, laverage_const_mul hBN]
    _ ≤ ‖B‖ₑ * N * (2 * vmoModulus f μ r) + ‖B‖ₑ * M * ε := by
        gcongr
        refine (setLAverage_setLAverage_enorm_sub_le (⨍ y in ball c s, f y ∂μ)).trans ?_
        gcongr
        exact setLAverage_enorm_sub_setAverage_le_vmoModulus f μ c hs
    _ = ‖B‖ₑ * (2 * N * vmoModulus f μ r + M * ε) := by ring

/-- **Products with uniformly continuous functions.** Let `B` be a continuous bilinear map. If `f`
has vanishing mean oscillation and is essentially bounded, and `g` is bounded and uniformly
continuous, then `x ↦ B (f x) (g x)` has vanishing mean oscillation. -/
theorem MemVMO.bilinear [SecondCountableTopology X] (B : F →L[ℝ] G →L[ℝ] H) (hf : MemVMO f μ)
    {M N : ℝ≥0} (hfM : ∀ᵐ x ∂μ, ‖f x‖ ≤ M) (hg : UniformContinuous g) (hgN : ∀ x, ‖g x‖ ≤ N) :
    MemVMO (fun x => B (f x) (g x)) μ := by
  have hfm := hf.memBMO.locallyIntegrable.aestronglyMeasurable
  have hgm : AEStronglyMeasurable g μ := hg.continuous.aestronglyMeasurable
  have hfM' : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ M := hfM.mono fun x hx => by
    rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal hx
  have hgN' (x : X) : ‖g x‖ₑ ≤ N := by
    rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (hgN x)
  set ω := fun r : ℝ => ⨆ (x : X) (y : X) (_ : dist x y < 2 * r), ‖g x - g y‖ₑ
  have hη (r : ℝ) : vmoModulus (fun x => B (f x) (g x)) μ r ≤
      ‖B‖ₑ * (2 * N * vmoModulus f μ r + M * ω r) :=
    B.vmoModulus_bilinear_le hfm hgm hfM' hgN' fun x y hxy => le_iSup₂_of_le x y (le_iSup_of_le
      hxy le_rfl)
  have hloc : LocallyIntegrable (fun x => B (f x) (g x)) μ :=
    (hf.memBMO.locallyIntegrable.smul (‖B‖ * N)).mono
      (B.aestronglyMeasurable_comp₂ hfm hgm) (Eventually.of_forall fun x => by
        rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg (by positivity)]
        calc ‖B (f x) (g x)‖ ≤ ‖B‖ * ‖f x‖ * ‖g x‖ := B.le_opNorm₂ _ _
          _ ≤ ‖B‖ * ‖f x‖ * N := by gcongr; exact hgN x
          _ = ‖B‖ * N * ‖f x‖ := by ring)
  refine memVMO_iff_tendsto.2 ⟨memBMO_iff.2 ⟨hloc, ?_⟩, ?_⟩
  · -- `g` varies by at most `2 N` at every scale.
    have hω (r : ℝ) : ω r ≤ 2 * N := iSup₂_le fun x y => iSup_le fun _ =>
      (eNorm_sub_le).trans (by rw [two_mul]; exact add_le_add (hgN' x) (hgN' y))
    rw [← iSup_vmoModulus]
    refine lt_of_le_of_lt (iSup_le fun r => (hη r).trans ?_)
      (show ‖B‖ₑ * (2 * N * bmoSeminorm f μ + M * (2 * N)) < ⊤ from
        ENNReal.mul_lt_top (by finiteness) (ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top
          (by finiteness) hf.memBMO.bmoSeminorm_lt_top, by finiteness⟩))
    gcongr
    exacts [vmoModulus_le_bmoSeminorm f μ r, hω r]
  · have hscale : Tendsto (fun r : ℝ => 2 * r) (𝓝[>] 0) (𝓝[>] 0) :=
      tendsto_const_mul_nhdsGT_zero two_pos
    have hlim : Tendsto (fun r => ‖B‖ₑ * (2 * N * vmoModulus f μ r + M * ω r)) (𝓝[>] 0)
        (𝓝 (‖B‖ₑ * (2 * N * 0 + M * 0))) :=
      ENNReal.Tendsto.const_mul ((ENNReal.Tendsto.const_mul hf.tendsto_vmoModulus
        (Or.inr (by finiteness))).add (ENNReal.Tendsto.const_mul
          (hg.tendsto_iSup_enorm_sub.comp hscale) (Or.inr (by finiteness))))
        (Or.inr (by finiteness))
    simp only [mul_zero, add_zero] at hlim
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le) hη

end Bilinear

end TauCeti
