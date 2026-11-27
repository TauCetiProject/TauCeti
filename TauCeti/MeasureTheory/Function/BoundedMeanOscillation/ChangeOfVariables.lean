/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.BoundedMeanOscillation
import TauCeti.Analysis.Normed.Group.UniformContinuity
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Function.LpSeminorm.Comp

/-!
# Mean oscillation under changes of variables

Let `Φ : X → Y` be an `L`-Lipschitz map between pseudometric measure spaces, `L > 0`, whose
push-forward of `μ` is dominated by a multiple of `ν`, `Φ_* μ ≤ K ν`, and suppose that the balls
`B(Φ c, L s)` are not much larger than the balls `B(c, s)`: `ν (B(Φ c, L s)) ≤ D μ (B(c, s))`.
This file proves that precomposition with `Φ` controls mean oscillation scale by scale,

`η_{f ∘ Φ}(r) ≤ 2 K D η_f(L r)`

(`TauCeti.vmoModulus_comp_le_of_map_le`), and hence `‖f ∘ Φ‖_{BMO} ≤ 2 K D ‖f‖_{BMO}`
(`TauCeti.bmoSeminorm_comp_le_of_map_le`), and that `f ∘ Φ` has bounded, respectively vanishing,
mean oscillation when `f` has (`TauCeti.MemBMO.comp_of_map_le`, `TauCeti.MemVMO.comp_of_map_le`).

On a finite-dimensional real normed space `E` with an additive Haar measure `μ`, the ball
condition holds with `D = Lⁿ`, `n = dim E`, for every map, so only the Lipschitz bound and the
bound `Φ_* μ ≤ K μ` on the push-forward remain
(`TauCeti.vmoModulus_comp_le_pow_finrank_of_map_le`, `TauCeti.MemVMO.comp_of_map_le_of_addHaar`).
For a diffeomorphism the push-forward bound says that the Jacobian determinant of `Φ` is at least
`1 / K`. Measure-preserving maps have `K = 1`; the shear `(t, y) ↦ (t - γ y, y)` by a Lipschitz
`γ`, which flattens the region above the graph of `γ`, is such a map.

Such changes of variables flatten the boundary of a domain. Flattening also multiplies the
coefficients by derivatives of the chart, which are bounded and uniformly continuous. For a
continuous bilinear map `B`, an essentially bounded `f` and a bounded `g`,

`η_{B(f, g)}(r) ≤ ‖B‖ (2 N η_f(r) + M ε)`

whenever `‖f‖ ≤ M` almost everywhere, `‖g‖ ≤ N`, and `g` varies by at most `ε` between points at
distance less than `2 r` (`TauCeti.vmoModulus_bilinear_le`). So `x ↦ B (f x) (g x)` has vanishing
mean oscillation when `f` does and `g` is uniformly continuous (`TauCeti.MemVMO.bilinear`). With
both results, a coefficient field of vanishing mean oscillation stays one after flattening, which
is what the `W^{2,p}` and `W^{1,p}` estimates for coefficients of vanishing mean oscillation up to
the boundary require of the transformed equation.

## The argument

On a ball `B = B(c, s)`, with `B' = B(Φ c, L s) ⊇ Φ(B)` and `k` the average of `f` over `B'`, the
mean oscillation of `f ∘ Φ` on `B` is at most the average of `‖f (Φ x) - f (Φ y)‖` over pairs of
points of `B`, hence at most twice the mean deviation `⨍_B ‖f ∘ Φ - k‖`. Pushing the integral
forward along `Φ`,

`∫_B ‖f (Φ x) - k‖ dμ ≤ ∫_{B'} ‖f - k‖ d(Φ_* μ) ≤ K ∫_{B'} ‖f - k‖ dν`,

and `ν B' ≤ D μ B` turns this into `⨍_B ‖f ∘ Φ - k‖ ≤ K D ⨍_{B'} ‖f - k‖`, the mean oscillation of
`f` on a ball of radius `L s`. No integrability of `f` is needed for these estimates.

For the product, `B (f x) (g x) - B (f y) (g y) = B (f x - f y) (g x) + B (f y) (g x - g y)`
bounds the average of `‖B (f x) (g x) - B (f y) (g y)‖` over pairs of points of a ball by
`‖B‖ (N ⨍⨍ ‖f x - f y‖ + M ε)`, and the average of `‖f x - f y‖` over pairs is at most twice the
mean oscillation of `f`.

## References

* D. Sarason, *Functions of vanishing mean oscillation*, Trans. Amer. Math. Soc. **207** (1975),
  391–405.
* F. Chiarenza, M. Frasca and P. Longo, *W^{2,p}-solvability of the Dirichlet problem for
  nondivergence elliptic equations with VMO coefficients*, Trans. Amer. Math. Soc. **336** (1993),
  841–853 (flattening the boundary of a domain for coefficients of vanishing mean oscillation).
-/

public section

namespace TauCeti

open Filter MeasureTheory Metric Set
open scoped ENNReal NNReal Topology

section PseudoMetricSpace

variable {X Y F : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [PseudoMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [NormedAddCommGroup F] {μ : Measure X}
  {ν : Measure Y} {f : Y → F} {Φ : X → Y} {L K D : ℝ≥0}

/-- **Pushing a ball average forward.** Under the hypotheses of `vmoModulus_comp_le_of_map_le`,
the mean deviation of `f ∘ Φ` from a constant `k` on `B(c, s)` is at most `K D` times that of `f`
on `B(Φ c, L s)`. -/
private theorem setLAverage_ball_enorm_comp_sub_le (hΦ : LipschitzWith L Φ) (hL : L ≠ 0)
    (hmap : μ.map Φ ≤ K • ν) (hf : StronglyMeasurable f) (k : F) {c : X} {s : ℝ}
    (hD : ν (ball (Φ c) (L * s)) ≤ D * μ (ball c s)) :
    ⨍⁻ x in ball c s, ‖f (Φ x) - k‖ₑ ∂μ ≤
      K * D * ⨍⁻ y in ball (Φ c) (L * s), ‖f y - k‖ₑ ∂ν := by
  set A := ⨍⁻ y in ball (Φ c) (L * s), ‖f y - k‖ₑ ∂ν
  rcases eq_or_ne (μ (ball c s)) 0 with h0 | h0
  · simp [Measure.restrict_eq_zero.2 h0]
  rcases eq_or_ne (μ (ball c s)) ⊤ with htop | htop
  · simp [setLAverage_eq, htop]
  have hν : ν (ball (Φ c) (L * s)) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top htop) hD
  have hint := hΦ.setLIntegral_ball_comp_le_of_map_le hL hmap (g := fun y => ‖f y - k‖ₑ)
    (hf.sub stronglyMeasurable_const).eNorm c s
  rw [← measure_mul_setLAverage _ hν] at hint
  rw [setLAverage_eq, ENNReal.div_eq_inv_mul]
  calc (μ (ball c s))⁻¹ * ∫⁻ x in ball c s, ‖f (Φ x) - k‖ₑ ∂μ
      ≤ (μ (ball c s))⁻¹ * (K * (ν (ball (Φ c) (L * s)) * A)) := by gcongr
    _ ≤ (μ (ball c s))⁻¹ * (K * (D * μ (ball c s) * A)) := by gcongr
    _ = K * D * A * ((μ (ball c s))⁻¹ * μ (ball c s)) := by ring
    _ = K * D * A := by rw [ENNReal.inv_mul_cancel h0 htop, mul_one]

/-- `f ∘ Φ` agrees almost everywhere with the composite of a strongly measurable modification of
`f`, since `Φ_* μ ≪ ν`. -/
private theorem comp_ae_eq_mk (hΦ : LipschitzWith L Φ) (hmap : μ.map Φ ≤ K • ν)
    (hf : AEStronglyMeasurable f ν) : f ∘ Φ =ᵐ[μ] hf.mk f ∘ Φ :=
  ae_eq_comp hΦ.continuous.measurable.aemeasurable
    ((Measure.absolutelyContinuous_of_le_smul hmap).ae_le hf.ae_eq_mk)

variable [NormedSpace ℝ F] [CompleteSpace F]

/-- **Mean oscillation under a change of variables.** Let `Φ : X → Y` be `L`-Lipschitz, `L ≠ 0`,
with `Φ_* μ ≤ K ν`, and suppose that `ν (B(Φ c, L s)) ≤ D μ (B(c, s))` for every ball. Then
`η_{f ∘ Φ}(r) ≤ 2 K D η_f(L r)`. -/
theorem vmoModulus_comp_le_of_map_le (hΦ : LipschitzWith L Φ) (hL : L ≠ 0)
    (hmap : μ.map Φ ≤ K • ν)
    (hD : ∀ c s, 0 < s → ν (ball (Φ c) (L * s)) ≤ D * μ (ball c s))
    (hf : AEStronglyMeasurable f ν) (r : ℝ) :
    vmoModulus (f ∘ Φ) μ r ≤ 2 * K * D * vmoModulus f ν (L * r) := by
  rw [vmoModulus_congr_ae (comp_ae_eq_mk hΦ hmap hf), vmoModulus_congr_ae hf.ae_eq_mk]
  set g := hf.mk f
  have hg : StronglyMeasurable g := hf.stronglyMeasurable_mk
  refine vmoModulus_le fun c s hs => ?_
  rcases le_or_gt s 0 with hs0 | hs0
  · simp [ball_eq_empty.2 hs0]
  set k := ⨍ y in ball (Φ c) (L * s), g y ∂ν
  calc ⨍⁻ x in ball c s, ‖(g ∘ Φ) x - ⨍ z in ball c s, (g ∘ Φ) z ∂μ‖ₑ ∂μ
      ≤ ⨍⁻ x in ball c s, ⨍⁻ y in ball c s, ‖g (Φ x) - g (Φ y)‖ₑ ∂μ ∂μ :=
        setLAverage_enorm_sub_setAverage_le_setLAverage_setLAverage
          (hg.comp_measurable hΦ.continuous.measurable).aestronglyMeasurable
    _ ≤ 2 * ⨍⁻ x in ball c s, ‖g (Φ x) - k‖ₑ ∂μ :=
        setLAverage_setLAverage_enorm_sub_le k
    _ ≤ 2 * (K * D * ⨍⁻ y in ball (Φ c) (L * s), ‖g y - k‖ₑ ∂ν) := by
        gcongr
        exact setLAverage_ball_enorm_comp_sub_le hΦ hL hmap hg k (hD c s hs0)
    _ ≤ 2 * (K * D * vmoModulus g ν (L * r)) := by
        gcongr
        exact setLAverage_enorm_sub_setAverage_le_vmoModulus g ν (Φ c)
          (mul_le_mul_of_nonneg_left hs L.coe_nonneg)
    _ = 2 * K * D * vmoModulus g ν (L * r) := by ring

/-- **The BMO seminorm under a change of variables.** Under the hypotheses of
`vmoModulus_comp_le_of_map_le`, `‖f ∘ Φ‖_{BMO} ≤ 2 K D ‖f‖_{BMO}`. -/
theorem bmoSeminorm_comp_le_of_map_le (hΦ : LipschitzWith L Φ) (hL : L ≠ 0)
    (hmap : μ.map Φ ≤ K • ν)
    (hD : ∀ c s, 0 < s → ν (ball (Φ c) (L * s)) ≤ D * μ (ball c s))
    (hf : AEStronglyMeasurable f ν) :
    bmoSeminorm (f ∘ Φ) μ ≤ 2 * K * D * bmoSeminorm f ν := by
  rw [← iSup_vmoModulus]
  exact iSup_le fun r => (vmoModulus_comp_le_of_map_le hΦ hL hmap hD hf r).trans
    (mul_le_mul_right (vmoModulus_le_bmoSeminorm f ν _) _)

/-- **Bounded mean oscillation under a change of variables.** Under the hypotheses of
`vmoModulus_comp_le_of_map_le`, `f ∘ Φ` has bounded mean oscillation when `f` has. -/
theorem MemBMO.comp_of_map_le [SecondCountableTopology Y] (hf : MemBMO f ν)
    (hΦ : LipschitzWith L Φ) (hL : L ≠ 0)
    (hmap : μ.map Φ ≤ K • ν)
    (hD : ∀ c s, 0 < s → ν (ball (Φ c) (L * s)) ≤ D * μ (ball c s)) :
    MemBMO (f ∘ Φ) μ :=
  memBMO_iff.2 ⟨hf.locallyIntegrable.comp_of_map_le hΦ.continuous hmap ENNReal.coe_ne_top,
    (bmoSeminorm_comp_le_of_map_le hΦ hL hmap hD
      hf.locallyIntegrable.aestronglyMeasurable).trans_lt
        (ENNReal.mul_lt_top (by finiteness) hf.bmoSeminorm_lt_top)⟩

/-- **Vanishing mean oscillation under a change of variables.** Under the hypotheses of
`vmoModulus_comp_le_of_map_le`, `f ∘ Φ` has vanishing mean oscillation when `f` has. -/
theorem MemVMO.comp_of_map_le [SecondCountableTopology Y] (hf : MemVMO f ν)
    (hΦ : LipschitzWith L Φ) (hL : L ≠ 0)
    (hmap : μ.map Φ ≤ K • ν)
    (hD : ∀ c s, 0 < s → ν (ball (Φ c) (L * s)) ≤ D * μ (ball c s)) :
    MemVMO (f ∘ Φ) μ := by
  refine memVMO_iff_tendsto.2 ⟨hf.memBMO.comp_of_map_le hΦ hL hmap hD, ?_⟩
  have hscale : Tendsto (fun r : ℝ => (L : ℝ) * r) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa using ((continuous_const_mul (L : ℝ)).tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hL)) hr
  have hlim := ENNReal.Tendsto.const_mul (hf.tendsto_vmoModulus.comp hscale)
    (Or.inr (show 2 * (K : ℝ≥0∞) * D ≠ ∞ by finiteness))
  rw [mul_zero] at hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
    fun r => vmoModulus_comp_le_of_map_le hΦ hL hmap hD
      hf.memBMO.locallyIntegrable.aestronglyMeasurable r

end PseudoMetricSpace

section Bilinear

variable {X F G H : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
  [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H] {μ : Measure X}
  {f : X → F} {g : X → G}

/-- **Mean oscillation of a product.** Let `B` be a continuous bilinear map, `f` bounded by `M`
almost everywhere and `g` bounded by `N`, and suppose that `g` varies by at most `ε` between points
at distance less than `2 r`. Then the mean oscillation of `x ↦ B (f x) (g x)` on balls of radius at
most `r` is at most `‖B‖ (2 N η_f(r) + M ε)`. -/
theorem vmoModulus_bilinear_le (B : F →L[ℝ] G →L[ℝ] H) (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) {M N : ℝ≥0} {ε : ℝ≥0∞} {r : ℝ}
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
    vmoModulus_bilinear_le B hfm hgm hfM' hgN' fun x y hxy => le_iSup₂_of_le x y (le_iSup_of_le
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
  · have hscale : Tendsto (fun r : ℝ => 2 * r) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · simpa using ((continuous_const_mul (2 : ℝ)).tendsto 0).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr
        exact mul_pos two_pos hr
    have hlim : Tendsto (fun r => ‖B‖ₑ * (2 * N * vmoModulus f μ r + M * ω r)) (𝓝[>] 0)
        (𝓝 (‖B‖ₑ * (2 * N * 0 + M * 0))) :=
      ENNReal.Tendsto.const_mul ((ENNReal.Tendsto.const_mul hf.tendsto_vmoModulus
        (Or.inr (by finiteness))).add (ENNReal.Tendsto.const_mul
          (hg.tendsto_iSup_enorm_sub.comp hscale) (Or.inr (by finiteness))))
        (Or.inr (by finiteness))
    simp only [mul_zero, add_zero] at hlim
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le) hη

end Bilinear

section AddHaar

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace F] {f : E → F} {Φ : E → E} {L K : ℝ≥0}

/-- For an additive Haar measure, the ball `B(Φ c, L s)` has `Lⁿ` times the measure of `B(c, s)`,
`n = dim E`. -/
private theorem addHaar_ball_mul_le (hL : L ≠ 0) (c : E) (s : ℝ) :
    μ (ball (Φ c) (L * s)) ≤ ((L ^ Module.finrank ℝ E : ℝ≥0) : ℝ≥0∞) * μ (ball c s) := by
  rw [μ.addHaar_ball_mul_of_pos _ (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hL)),
    μ.addHaar_ball_center c,
    ENNReal.ofReal_pow L.coe_nonneg, ENNReal.ofReal_coe_nnreal, ENNReal.coe_pow]

/-- **Mean oscillation under a change of variables of `E`.** For an additive Haar measure on a
finite-dimensional space `E` of dimension `n`, if `Φ : E → E` is `L`-Lipschitz, `L ≠ 0`, with
`Φ_* μ ≤ K μ`, then `η_{f ∘ Φ}(r) ≤ 2 K Lⁿ η_f(L r)`. -/
theorem vmoModulus_comp_le_pow_finrank_of_map_le (hΦ : LipschitzWith L Φ) (hL : L ≠ 0)
    (hmap : μ.map Φ ≤ K • μ) (hf : AEStronglyMeasurable f μ) (r : ℝ) :
    vmoModulus (f ∘ Φ) μ r ≤ 2 * K * L ^ Module.finrank ℝ E * vmoModulus f μ (L * r) := by
  simpa using vmoModulus_comp_le_of_map_le hΦ hL hmap
    (fun c s _ => addHaar_ball_mul_le hL c s) hf r

/-- **Vanishing mean oscillation under a change of variables of `E`.** For an additive Haar measure
on a finite-dimensional space `E`, if `Φ : E → E` is Lipschitz with `Φ_* μ ≤ K μ`, then `f ∘ Φ` has
vanishing mean oscillation when `f` has. In particular this holds for measure-preserving
Lipschitz maps. -/
theorem MemVMO.comp_of_map_le_of_addHaar (hf : MemVMO f μ) (hΦ : LipschitzWith L Φ)
    (hmap : μ.map Φ ≤ K • μ) : MemVMO (f ∘ Φ) μ :=
  hf.comp_of_map_le (hΦ.weaken (le_max_left L 1)) (by positivity) hmap
    fun c s _ => addHaar_ball_mul_le (by positivity) c s

end AddHaar

end TauCeti
