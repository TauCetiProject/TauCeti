/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Weak
public import TauCeti.Analysis.Complex.Wirtinger.DivergenceLaplace
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.MetricSpace.Thickening
import TauCeti.Analysis.Distribution.TestFunction.Inner
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Sobolev.Local.Multiplication
import TauCeti.Analysis.Sobolev.Local.SobolevEmbedding
import TauCeti.Analysis.Sobolev.Mollification.Interior
import TauCeti.Analysis.Sobolev.WeakDeriv.Bilinear.Holder
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
import TauCeti.MeasureTheory.Function.Lp.Holder

/-!
# Order-zero interior regularity for Cauchy–Riemann operators with Sobolev coefficients

Let `Ω ⊆ ℂ` be open, write `z = s + i t`, and let `V` be a finite-dimensional real inner product
space. For Sobolev coefficients `J ∈ W^{1,p}_loc(Ω; V →L[ℝ] V)` and `S ∈ Lᵖ_loc(Ω; V →L[ℝ] V)`
with `2 < p < ∞` and `J² = -1` almost everywhere on `Ω`, consider a weak solution `ξ ∈ L^q_loc(Ω)`
of

`∂_s ξ + J ∂_t ξ + S ξ = η`

in the sense of `TauCeti.IsWeakCRSolution q Ω J DJ S ξ η`, where `DJ` is a weak derivative of `J`.

This file proves the order-zero interior regularity theorem (McDuff–Salamon, Lemma B.4.6 and the
base case `k = 0` of Proposition B.4.9):

1. **Divergence-form Laplace reduction**
   (`TauCeti.IsSobolevCRCoefficients.integral_laplacian_smul_eq`). When `J` is continuous on `Ω`
   with `J² = -1` on `Ω` and `p⁻¹ + q⁻¹ ≤ 1` (allowing `q = ∞`), `ξ` weakly solves
   `Δξ = ∂_s f + ∂_t g` on `Ω` with `f = η + (∂_t J) ξ - S ξ` and
   `g = -J f - (∂_s J) ξ - (∂_t J)(J ξ)`. Because `J` is only `W^{1,p}_loc`, `Jᵀ ∂_t φ` is not a
   test function; the proof mollifies `J` on a relatively compact subdomain so that `J_n → J`
   uniformly on `tsupport φ` while `DJ_n → DJ` in `Lᵖ`, tests the weak equation against
   `J_nᵀ ∂_t(φ • w)`, and passes to the limit.
2. **Single-step Sobolev gain** (`TauCeti.IsWeakCRSolution.memWkpLoc_one_of_inv_add_inv_le`,
   McDuff–Salamon Lemma B.4.6). For `2 < p < ∞`, `1 < r < ∞`, `p⁻¹ + q⁻¹ ≤ r⁻¹` and `η ∈ Lʳ_loc`,
   Morrey's embedding supplies a continuous representative of `J` with square `-1` everywhere on
   `Ω`, the auxiliary fields `f` and `g` lie in `Lʳ_loc`, and
   `TauCeti.memWkpLoc_one_of_forall_integral_laplacian_smul_eq` yields `ξ ∈ W^{1,r}_loc(Ω)`.
3. **Bootstrap across the critical exponent**
   (`TauCeti.IsWeakCRSolution.memWkpLoc_one_of_memLpLoc` and
   `TauCeti.IsWeakCRSolution.memWkpLoc_one`). When `p⁻¹ + q⁻¹ < 1` and `η ∈ Lʳ_loc` with
   `1 < r ≤ p`, iterating the single-step gain with the two-dimensional Sobolev embedding
   decreases `q⁻¹` by `(2⁻¹ - p⁻¹) / 2 > 0` at each step until the product exponent exceeds `2`,
   where Morrey's embedding puts `ξ` in `L^∞_loc` and one final step reaches `W^{1,r}_loc(Ω)`.

## Main declarations

* `TauCeti.IsSobolevCRCoefficients.integral_laplacian_smul_eq`: the weak divergence-form Laplace
  identity `Δξ = ∂_s f + ∂_t g`.
* `TauCeti.IsWeakCRSolution.memWkpLoc_one_of_inv_add_inv_le`: single-step regularity
  `ξ ∈ W^{1,r}_loc` when `p⁻¹ + q⁻¹ ≤ r⁻¹` and `η ∈ Lʳ_loc`.
* `TauCeti.IsWeakCRSolution.memWkpLoc_one_of_memLpLoc`: full order-zero gain `ξ ∈ W^{1,r}_loc`
  for `p⁻¹ + q⁻¹ < 1`, `1 < r ≤ p` and `η ∈ Lʳ_loc`.
* `TauCeti.IsWeakCRSolution.memWkpLoc_one`: order-zero regularity `ξ ∈ W^{1,q}_loc` for
  `1 < q ≤ p`, `p⁻¹ + q⁻¹ < 1` and `η ∈ L^q_loc`.
* `TauCeti.exists_isWeakCRSolution_zero_not_memWkpLoc_one`: without `J² = -1`, a bounded weak
  solution for smooth coefficients need not lie in `W^{1,q}_loc`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4 (Lemma B.4.6, Proposition B.4.9).
-/

public noncomputable section

open Complex Filter Function Laplacian LineDeriv MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Convolution Distributions ENNReal InnerProductSpace NNReal Topology

namespace TauCeti

section HolderApply

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] {U : Set ℂ} {p q r : ℝ≥0∞}

/-- Applying a locally `Lᵖ` operator field to a locally `L^q` vector field gives a locally `Lʳ`
field whenever `p⁻¹ + q⁻¹ ≤ r⁻¹`. -/
private theorem MemLpLoc.clm_apply_of_inv_add_inv_le {A : ℂ → F →L[ℝ] G} {w : ℂ → F}
    (hA : MemLpLoc p U A) (hw : MemLpLoc q U w) (hpqr : p⁻¹ + q⁻¹ ≤ r⁻¹) :
    MemLpLoc r U (fun z => A z (w z)) := by
  have hrs : r ≤ (p⁻¹ + q⁻¹)⁻¹ := by
    rw [← inv_inv r]
    exact ENNReal.inv_le_inv.2 hpqr
  have : ENNReal.HolderTriple p q (p⁻¹ + q⁻¹)⁻¹ := ⟨(inv_inv _).symm⟩
  have hmem : MemLpLoc (p⁻¹ + q⁻¹)⁻¹ U (fun z => A z (w z)) :=
    memLpLoc_iff.2 fun K hKU hK =>
      (ContinuousLinearMap.id ℝ (F →L[ℝ] G)).memLp_of_bilin _
        (memLpLoc_iff.1 hA K hKU hK) (memLpLoc_iff.1 hw K hKU hK)
  exact hmem.mono_exponent hrs

/-- Applying a continuous operator field on `U` preserves local `L^q` membership. -/
private theorem MemLpLoc.clm_apply_of_continuousOn {A : ℂ → F →L[ℝ] G} {w : ℂ → F}
    (hA : ContinuousOn A U) (hw : MemLpLoc q U w) : MemLpLoc q U (fun z => A z (w z)) :=
  (hA.memLpLoc (p := ⊤)).clm_apply_of_inv_add_inv_le hw (by simp)

end HolderApply

section LaplaceReduction

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {Ω : Opens ℂ} {p q : ℝ≥0∞}
  {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}

private local instance : NormedAddCommGroup (V →L[ℝ] V) := inferInstance
private local instance : NormedSpace ℝ (V →L[ℝ] V) := inferInstance
private local instance : NormedAddCommGroup (ℂ →L[ℝ] V →L[ℝ] V) := inferInstance
private local instance : NormedSpace ℝ (ℂ →L[ℝ] V →L[ℝ] V) := inferInstance

omit [CompleteSpace V] in
/-- Pairing a test function against `A_n z (u z)` passes to the limit when `A_n → B` uniformly on
the topological support of the test function and `u` is locally integrable. -/
private theorem tendsto_integral_inner_clm_of_uniform (Θ : 𝓓(Ω, V)) {u : ℂ → V}
    (hu : LocallyIntegrableOn u Ω volume) {A : ℕ → ℂ → V →L[ℝ] V} {B : ℂ → V →L[ℝ] V}
    (hA : ∀ n, Continuous (A n)) (hB : ContinuousOn B Ω)
    (hunif : TendstoUniformlyOn A B atTop (tsupport (Θ : ℂ → V))) :
    Tendsto (fun n => ∫ z, ⟪(Θ : ℂ → V) z, A n z (u z)⟫_ℝ) atTop
      (𝓝 (∫ z, ⟪(Θ : ℂ → V) z, B z (u z)⟫_ℝ)) := by
  have hloc := Ω.isOpen.isLocallyClosed
  have hu1 : MemLpLoc 1 Ω u := (memLpLoc_one_iff_locallyIntegrableOn hloc).2 hu
  have hintB : Integrable (fun z => ⟪(Θ : ℂ → V) z, B z (u z)⟫_ℝ) :=
    Θ.integrable_inner ((hu1.clm_apply_of_continuousOn hB).locallyIntegrableOn le_rfl hloc)
  have hintA (n : ℕ) : Integrable (fun z => ⟪(Θ : ℂ → V) z, A n z (u z)⟫_ℝ) :=
    Θ.integrable_inner
      ((hu1.clm_apply_of_continuousOn (hA n).continuousOn).locallyIntegrableOn le_rfl hloc)
  set K := tsupport (Θ : ℂ → V)
  obtain ⟨CΘ, hCΘ⟩ := Θ.continuous.bounded_above_of_compact_support Θ.hasCompactSupport
  have huK : Integrable (K.indicator fun z => ‖u z‖) :=
    (integrable_indicator_iff Θ.hasCompactSupport.measurableSet).2
      (hu.integrableOn_compact_subset Θ.tsupport_subset Θ.hasCompactSupport).norm
  rw [Metric.tendsto_nhds]
  intro ε hε
  set M : ℝ := CΘ * ∫ z, K.indicator (fun w => ‖u w‖) z
  have hCΘ0 : 0 ≤ CΘ := (norm_nonneg ((Θ : ℂ → V) 0)).trans (hCΘ 0)
  have hM0 : 0 ≤ M := mul_nonneg hCΘ0
    (integral_nonneg fun z => indicator_nonneg (fun _ _ => norm_nonneg _) z)
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hunif (ε / (M + 1))
    (div_pos hε (by linarith))] with n hn
  rw [Real.dist_eq, ← Real.norm_eq_abs, ← integral_sub (hintA n) hintB]
  calc ‖∫ z, (⟪(Θ : ℂ → V) z, A n z (u z)⟫_ℝ - ⟪(Θ : ℂ → V) z, B z (u z)⟫_ℝ)‖
      ≤ ∫ z, (ε / (M + 1)) * (CΘ * K.indicator (fun w => ‖u w‖) z) := by
        refine norm_integral_le_of_norm_le ((huK.const_mul CΘ).const_mul _) (.of_forall fun z => ?_)
        by_cases hz : z ∈ K
        · rw [Real.norm_eq_abs, indicator_of_mem hz, ← inner_sub_right, ← sub_apply]
          have h1 := (abs_real_inner_le_norm ((Θ : ℂ → V) z) ((A n z - B z) (u z))).trans
            (mul_le_mul (hCΘ z) ((A n z - B z).le_opNorm (u z)) (norm_nonneg _) hCΘ0)
          have h2 : ‖A n z - B z‖ ≤ ε / (M + 1) := by simpa only [dist_eq_norm'] using (hn z hz).le
          exact h1.trans ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2
            (norm_nonneg _)) hCΘ0).trans_eq (by ring))
        · simp [K, indicator_of_notMem hz, image_eq_zero_of_notMem_tsupport hz]
    _ = (ε / (M + 1)) * M := by rw [integral_const_mul, integral_const_mul]
    _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
        linarith

omit [CompleteSpace V] in
/-- If `Θ ∈ 𝓓(Ω, V)` has `tsupport Θ ⊆ W`, `g n` and `g₀` are integrable against `Θ`, and
`∫⁻ z in W, ‖g n z - g₀ z‖ₑ → 0`, then `∫ z, ⟪Θ z, g n z⟫_ℝ → ∫ z, ⟪Θ z, g₀ z⟫_ℝ`. -/
private theorem tendsto_integral_inner_of_setLIntegral {W : Set ℂ}
    (Θ : 𝓓(Ω, V)) (hΘW : tsupport (Θ : ℂ → V) ⊆ W) {g : ℕ → ℂ → V} {g₀ : ℂ → V}
    (hg₀ : Integrable (fun z => ⟪(Θ : ℂ → V) z, g₀ z⟫_ℝ))
    (hg : ∀ n, Integrable (fun z => ⟪(Θ : ℂ → V) z, g n z⟫_ℝ))
    (hL1 : Tendsto (fun n => ∫⁻ z in W, ‖g n z - g₀ z‖ₑ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z, ⟪(Θ : ℂ → V) z, g n z⟫_ℝ) atTop
      (𝓝 (∫ z, ⟪(Θ : ℂ → V) z, g₀ z⟫_ℝ)) := by
  obtain ⟨M, hM⟩ := Θ.continuous.bounded_above_of_compact_support Θ.hasCompactSupport
  have hlimM : Tendsto (fun n => ENNReal.ofReal M * ∫⁻ z in W, ‖g n z - g₀ z‖ₑ)
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hL1 (Or.inr ENNReal.ofReal_ne_top)
  refine tendsto_integral_of_L1 _ hg₀.aestronglyMeasurable (.of_forall hg) ?_
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlimM
    (fun _ => zero_le) fun n => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (lintegral_mono fun z => ?_).trans (lintegral_indicator_le _ _)
  by_cases hzW : z ∈ W
  · rw [indicator_of_mem hzW, ← inner_sub_right, Real.eNorm_eq_ofReal_abs]
    have h1 := (abs_real_inner_le_norm ((Θ : ℂ → V) z) (g n z - g₀ z)).trans
      (mul_le_mul_of_nonneg_right (hM z) (norm_nonneg _))
    exact (ENNReal.ofReal_le_ofReal h1).trans_eq
      (by rw [ENNReal.ofReal_mul ((norm_nonneg _).trans (hM z)), _root_.ofReal_norm])
  · simp [indicator_of_notMem hzW, image_eq_zero_of_notMem_tsupport fun h => hzW (hΘW h)]

/-- Pairing a test function supported in `W` against `((ρ_n ⋆ 1_W U) z v) (u z)` passes to the
limit when `U ∈ Lᵖ(W)`, `u ∈ L^q(W)` and `p⁻¹ + q⁻¹ ≤ 1` with `p < ∞` (allowing `q = ∞`). -/
private theorem tendsto_integral_inner_convolution_of_memLp (hp : p ≠ ⊤) (hpq : p⁻¹ + q⁻¹ ≤ 1)
    {W : Opens ℂ} (hWc : IsCompact (closure (W : Set ℂ))) (Θ : 𝓓(Ω, V))
    (hΘW : tsupport (Θ : ℂ → V) ⊆ W) {U : ℂ → ℂ →L[ℝ] V →L[ℝ] V}
    (hU : MemLp U p (volume.restrict W)) (v : ℂ) {u : ℂ → V}
    (hu : MemLp u q (volume.restrict W)) {φ : ℕ → ContDiffBump (0 : ℂ)}
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z, ⟪(Θ : ℂ → V) z,
        (((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          (W : Set ℂ).indicator U) z v) (u z)⟫_ℝ)
      atTop (𝓝 (∫ z, ⟪(Θ : ℂ → V) z, U z v (u z)⟫_ℝ)) := by
  have : Fact (1 ≤ p) := ⟨ENNReal.inv_le_one.1 (le_self_add.trans hpq)⟩
  have : Fact (1 ≤ q) := ⟨ENNReal.inv_le_one.1 (le_add_self.trans hpq)⟩
  set r := (p⁻¹ + q⁻¹)⁻¹
  have : Fact (1 ≤ r) := ⟨ENNReal.one_le_inv.2 hpq⟩
  have : ENNReal.HolderTriple p q r := ⟨(inv_inv _).symm⟩
  have hWm := W.isOpen.measurableSet.nullMeasurableSet (μ := volume)
  have hUext : MemLp ((W : Set ℂ).indicator U) p volume := (memLp_indicator_iff_restrict hWm).2 hU
  have huext : MemLp ((W : Set ℂ).indicator u) q volume := (memLp_indicator_iff_restrict hWm).2 hu
  have hWfin : volume (W : Set ℂ) < ⊤ := (measure_mono subset_closure).trans_lt hWc.measure_lt_top
  let B : (ℂ →L[ℝ] V →L[ℝ] V) →L[ℝ] V →L[ℝ] V :=
    (ContinuousLinearMap.id ℝ (V →L[ℝ] V)).comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) v)
  have hB (L : ℂ →L[ℝ] V →L[ℝ] V) (x : V) : B L x = L v x := by simp [B]
  have hL1 := tendsto_setLIntegral_enorm_bilin_sub (r := r) B hWfin
    (tendsto_normedBumpLp hp hφ (hUext.toLp _)) tendsto_const_nhds
    (fun n => normedBumpLp_ae_eq_convolution hp (φ n) hUext)
    (hUext.coeFn_toLp_indicator_restrict W.isOpen.measurableSet subset_rfl)
    (fun _ => huext.coeFn_toLp)
    (huext.coeFn_toLp_indicator_restrict W.isOpen.measurableSet subset_rfl)
  let ΘW : 𝓓(W, V) := ⟨Θ, Θ.contDiff, Θ.hasCompactSupport, hΘW⟩
  have : IsFiniteMeasure (volume.restrict (W : Set ℂ)) := isFiniteMeasure_restrict.2 hWfin.ne
  have hint_lim : Integrable (fun z => ⟪(Θ : ℂ → V) z, U z v (u z)⟫_ℝ) := by
    simpa [ΘW, hB] using ΘW.integrable_inner (IntegrableOn.locallyIntegrableOn
      ((B.memLp_of_bilin r hU hu).integrable Fact.out))
  have hint_n (n : ℕ) : Integrable (fun z => ⟪(Θ : ℂ → V) z,
      (((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (W : Set ℂ).indicator U) z v) (u z)⟫_ℝ) := by
    have hc := ((φ n).hasCompactSupport_normed (μ := volume)).continuous_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ →L[ℝ] V →L[ℝ] V))
      ((φ n).continuous_normed (μ := volume)) (hUext.locallyIntegrable Fact.out)
    obtain ⟨C, hC⟩ := hWc.exists_bound_of_continuousOn hc.continuousOn
    have hmem := B.memLp_of_bilin q (memLp_top_of_bound hc.aestronglyMeasurable C
      ((ae_restrict_iff' W.isOpen.measurableSet).2
        (.of_forall fun z hz => hC z (subset_closure hz)))) hu
    simpa [ΘW, hB] using ΘW.integrable_inner
      (IntegrableOn.locallyIntegrableOn (hmem.integrable Fact.out))
  refine tendsto_integral_inner_of_setLIntegral Θ hΘW hint_lim hint_n
    (hL1.congr fun n => setLIntegral_congr_fun W.isOpen.measurableSet fun z hz => ?_)
  rw [indicator_of_mem hz, hB, hB]

/-- Local integrability of the auxiliary fields `f` and `g` in the divergence-form Laplace
reduction when `J` is continuous on `Ω`. -/
private theorem IsSobolevCRCoefficients.locallyIntegrableOn_laplace_aux
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hpq : p⁻¹ + q⁻¹ ≤ 1)
    (hJcont : ContinuousOn J Ω) (hsol : IsWeakCRSolution q Ω J DJ S ξ η) :
    LocallyIntegrableOn (fun z => η z + DJ z I (ξ z) - S z (ξ z)) Ω volume ∧
      LocallyIntegrableOn (fun z => -J z (η z + DJ z I (ξ z) - S z (ξ z)) -
        DJ z 1 (ξ z) - DJ z I (J z (ξ z))) Ω volume := by
  have hloc := Ω.isOpen.isLocallyClosed
  have hDJ1 : MemLpLoc p Ω (fun z => DJ z 1) :=
    hc.memLpLoc_deriv.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) 1)
  have hDJI : MemLpLoc p Ω (fun z => DJ z I) :=
    hc.memLpLoc_deriv.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) I)
  have hJξ : MemLpLoc q Ω (fun z => J z (ξ z)) := hsol.memLpLoc.clm_apply_of_continuousOn hJcont
  have hf : LocallyIntegrableOn (fun z => η z + DJ z I (ξ z) - S z (ξ z)) Ω volume :=
    (hsol.locallyIntegrableOn.add
      (hDJI.locallyIntegrableOn_clm_apply hsol.memLpLoc hpq hloc)).sub
      (hc.memLpLoc_zeroth.locallyIntegrableOn_clm_apply hsol.memLpLoc hpq hloc)
  have hf1 : MemLpLoc 1 Ω (fun z => η z + DJ z I (ξ z) - S z (ξ z)) :=
    (memLpLoc_one_iff_locallyIntegrableOn hloc).2 hf
  have hJf : LocallyIntegrableOn (fun z => J z (η z + DJ z I (ξ z) - S z (ξ z))) Ω volume :=
    (hf1.clm_apply_of_continuousOn hJcont).locallyIntegrableOn le_rfl hloc
  exact ⟨hf, (hJf.neg.sub (hDJ1.locallyIntegrableOn_clm_apply hsol.memLpLoc hpq hloc)).sub
    (hDJI.locallyIntegrableOn_clm_apply hJξ hpq hloc)⟩

/-- Applying the Hilbert adjoint of a smooth operator field `A` to a test function `Ψ` produces a
test function on `Ω`. -/
private def adjointApplyTestFunction {A : ℂ → V →L[ℝ] V} (hA : ContDiff ℝ ∞ A) (Ψ : 𝓓(Ω, V)) :
    𝓓(Ω, V) :=
  let adjL : (V →L[ℝ] V) ≃ₗᵢ[ℝ] V →L[ℝ] V := ContinuousLinearMap.adjoint
  have hsupp : support (fun z => (A z).adjoint ((Ψ : ℂ → V) z)) ⊆ support (Ψ : ℂ → V) :=
    fun z hz h0 => hz (by simp [h0])
  ⟨fun z => (A z).adjoint ((Ψ : ℂ → V) z), (adjL.contDiff.comp hA).clm_apply Ψ.contDiff,
    Ψ.hasCompactSupport.mono hsupp, (closure_mono hsupp).trans Ψ.tsupport_subset⟩

/-- Pointwise formula for `adjointApplyTestFunction`. -/
private theorem adjointApplyTestFunction_apply {A : ℂ → V →L[ℝ] V} (hA : ContDiff ℝ ∞ A)
    (Ψ : 𝓓(Ω, V)) (z : ℂ) :
    (adjointApplyTestFunction hA Ψ : ℂ → V) z = (A z).adjoint ((Ψ : ℂ → V) z) :=
  rfl

/-- Pointwise expansion of `⟪crFormalAdjoint J DJ S (A† Ψ) z, v⟫_ℝ` for smooth `A`. -/
private theorem inner_crFormalAdjoint_adjointApplyTestFunction {A : ℂ → V →L[ℝ] V}
    (hA : ContDiff ℝ ∞ A) (Ψ : 𝓓(Ω, V)) (z : ℂ) (v : V) :
    ⟪crFormalAdjoint J DJ S (adjointApplyTestFunction hA Ψ) z, v⟫_ℝ =
      -⟪(∂_{(1 : ℂ)} Ψ : 𝓓(Ω, V)) z, A z v⟫_ℝ - ⟪(Ψ : ℂ → V) z, fderiv ℝ A z 1 v⟫_ℝ -
        ⟪(∂_{I} Ψ : 𝓓(Ω, V)) z, A z (J z v)⟫_ℝ - ⟪(Ψ : ℂ → V) z, fderiv ℝ A z I (J z v)⟫_ℝ -
        ⟪(Ψ : ℂ → V) z, A z (DJ z I v)⟫_ℝ + ⟪(Ψ : ℂ → V) z, A z (S z v)⟫_ℝ := by
  let adjL : (V →L[ℝ] V) ≃ₗᵢ[ℝ] V →L[ℝ] V := ContinuousLinearMap.adjoint
  have hAz : HasFDerivAt A (fderiv ℝ A z) z := (hA.differentiable (by simp) z).hasFDerivAt
  have hΨz : HasFDerivAt (Ψ : ℂ → V) (fderiv ℝ (Ψ : ℂ → V) z) z :=
    (Ψ.contDiff.differentiable (by simp) z).hasFDerivAt
  have hdf (u : ℂ) : fderiv ℝ (adjointApplyTestFunction hA Ψ : ℂ → V) z u =
      (A z).adjoint ((∂_{u} Ψ : 𝓓(Ω, V)) z) + (fderiv ℝ A z u).adjoint ((Ψ : ℂ → V) z) := by
    rw [TestFunction.lineDerivOp_apply_eq_fderiv]
    change fderiv ℝ (fun y => adjL (A y) ((Ψ : ℂ → V) y)) z u =
      adjL (A z) (fderiv ℝ (Ψ : ℂ → V) z u) + adjL (fderiv ℝ A z u) ((Ψ : ℂ → V) z)
    have h := congr($(((adjL.hasFDerivAt.comp z hAz).clm_apply hΨz).fderiv) u)
    simpa only [Function.comp_apply, add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, LinearIsometryEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe] using h
  rw [inner_crFormalAdjoint, hdf 1, hdf I]
  simp only [adjointApplyTestFunction_apply, inner_add_left,
    ContinuousLinearMap.adjoint_inner_left]
  ring

/-- Interior mollifiers on `W ⋐ Ω` converge uniformly on a compact subset `K ⊆ W` when `J` is
continuous on `W`. -/
private theorem exists_mollifier_tendstoUniformlyOn {W : Opens ℂ} (hJcont : ContinuousOn J W)
    {K : Set ℂ} (hK : IsCompact K) (hKW : K ⊆ W) :
    ∃ ρ : ℕ → ContDiffBump (0 : ℂ), Tendsto (fun n => (ρ n).rOut) atTop (𝓝 0) ∧
      (∀ n, ∀ z ∈ K, closedBall z (ρ n).rOut ⊆ W) ∧
      TendstoUniformlyOn
        (fun n => (ρ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          (W : Set ℂ).indicator J) J atTop K := by
  obtain ⟨δ, hδ, hδW⟩ := hK.exists_cthickening_subset_open W.isOpen hKW
  set r : ℕ → ℝ := fun n => δ / ((n : ℝ) + 2)
  have hr (n : ℕ) : 0 < r n := by positivity
  have hrlt (n : ℕ) : r n < δ := div_lt_self hδ (by linarith [Nat.cast_nonneg (α := ℝ) n])
  let ρ : ℕ → ContDiffBump (0 : ℂ) := fun n => ⟨r n / 2, r n, half_pos (hr n), half_lt_self (hr n)⟩
  have hρ0 : Tendsto (fun n => (ρ n).rOut) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := δ)).div_atTop
      (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  have hball (n : ℕ) {z : ℂ} (hz : z ∈ K) : closedBall z (ρ n).rOut ⊆ W :=
    (closedBall_subset_closedBall (hrlt n).le).trans
      ((closedBall_subset_cthickening hz δ).trans hδW)
  have hmeas : AEStronglyMeasurable ((W : Set ℂ).indicator J) volume :=
    (aestronglyMeasurable_indicator_iff W.isOpen.measurableSet).2
      (hJcont.aestronglyMeasurable W.isOpen.measurableSet)
  refine ⟨ρ, hρ0, fun n z hz => hball n hz, Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_⟩
  obtain ⟨γ, hγ, hucont⟩ := Metric.uniformContinuousOn_iff.1
    (hK.cthickening.uniformContinuousOn_of_continuous (hJcont.mono hδW)) (ε / 2) (half_pos hε)
  filter_upwards [hρ0.eventually (gt_mem_nhds hγ)] with n hn z hz
  rw [dist_comm]
  have hle : dist (((ρ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      (W : Set ℂ).indicator J) z) ((W : Set ℂ).indicator J z) ≤ ε / 2 := by
    refine (ρ n).dist_normed_convolution_le hmeas fun y hy => ?_
    have hyW : y ∈ (W : Set ℂ) := hball n hz (ball_subset_closedBall hy)
    have hzW : z ∈ (W : Set ℂ) := hKW hz
    rw [indicator_of_mem hyW, indicator_of_mem hzW]
    exact (hucont y (mem_cthickening_of_dist_le y z δ K hz
      ((mem_ball.1 hy).le.trans (hrlt n).le)) z (self_subset_cthickening K hz)
      ((mem_ball.1 hy).trans hn)).le
  rw [indicator_of_mem (hKW hz)] at hle
  linarith

/-- Testing the weak Cauchy–Riemann equation against `J_n† Ψ` at mollification scale `ρ` and
replacing `fderiv ℝ J_n` on `tsupport Ψ` by the mollified weak derivative `DJ_n`. -/
private theorem integral_inner_mollified_adjoint_eq (hpq : p⁻¹ + q⁻¹ ≤ 1)
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hJcont : ContinuousOn J Ω)
    (hsol : IsWeakCRSolution q Ω J DJ S ξ η) (Ψ : 𝓓(Ω, V)) {W : Opens ℂ}
    (hWΩ : closure (W : Set ℂ) ⊆ Ω) (ρ : ContDiffBump (0 : ℂ))
    (hball : ∀ z ∈ tsupport (Ψ : ℂ → V), closedBall z ρ.rOut ⊆ W)
    (hJW : MemLp J p (volume.restrict W)) (hDJW : MemLp DJ p (volume.restrict W))
    (hJsmooth : ContDiff ℝ ∞
      (ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (W : Set ℂ).indicator J)) :
    let J_ρ := ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (W : Set ℂ).indicator J;
    let DJ_ρ := ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (W : Set ℂ).indicator DJ;
    -(∫ z, ⟪(∂_{(1 : ℂ)} Ψ : 𝓓(Ω, V)) z, J_ρ z (ξ z)⟫_ℝ) -
      (∫ z, ⟪(Ψ : ℂ → V) z, DJ_ρ z 1 (ξ z)⟫_ℝ) -
      (∫ z, ⟪(∂_{I} Ψ : 𝓓(Ω, V)) z, J_ρ z (J z (ξ z))⟫_ℝ) -
      (∫ z, ⟪(Ψ : ℂ → V) z, DJ_ρ z I (J z (ξ z))⟫_ℝ) -
      (∫ z, ⟪(Ψ : ℂ → V) z, J_ρ z (DJ z I (ξ z))⟫_ℝ) +
      (∫ z, ⟪(Ψ : ℂ → V) z, J_ρ z (S z (ξ z))⟫_ℝ) =
      ∫ z, ⟪(Ψ : ℂ → V) z, J_ρ z (η z)⟫_ℝ := by
  intro J_ρ DJ_ρ
  have hp1 : 1 ≤ p := ENNReal.inv_le_one.1 (le_self_add.trans hpq)
  have hq1 : 1 ≤ q := ENNReal.inv_le_one.1 (le_add_self.trans hpq)
  have hloc := Ω.isOpen.isLocallyClosed
  have hDJ_eq (v : ℂ) (w : V) (z : ℂ) :
      ⟪(Ψ : ℂ → V) z, fderiv ℝ J_ρ z v w⟫_ℝ = ⟪(Ψ : ℂ → V) z, DJ_ρ z v w⟫_ℝ := by
    by_cases hz : z ∈ tsupport (Ψ : ℂ → V)
    · have hd := (hc.hasWeakFDerivOn.mono
        (SetLike.coe_subset_coe.1 (subset_closure.trans hWΩ))).fderiv_indicator_convolution_normed
        hJW hDJW hp1 hp1 ρ z (hball z hz)
      simp only [convolution_flip] at hd; rw [hd]
    · simp [image_eq_zero_of_notMem_tsupport hz]
  have hξloc := hsol.memLpLoc.locallyIntegrableOn hq1 hloc
  have hJξloc := (hsol.memLpLoc.clm_apply_of_continuousOn hJcont).locallyIntegrableOn hq1 hloc
  have hi (Θ : 𝓓(Ω, V)) {A : ℂ → V →L[ℝ] V} (hA : Continuous A) {w : ℂ → V}
      (hw : LocallyIntegrableOn w Ω volume) :
      Integrable (fun z => ⟪(Θ : ℂ → V) z, A z (w z)⟫_ℝ) :=
    Θ.integrable_inner ((((memLpLoc_one_iff_locallyIntegrableOn hloc).2
      hw).clm_apply_of_continuousOn hA.continuousOn).locallyIntegrableOn le_rfl hloc)
  have hDJcont (v : ℂ) : Continuous (fun z => fderiv ℝ J_ρ z v) :=
    (hJsmooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have i1 := hi (∂_{(1 : ℂ)} Ψ) hJsmooth.continuous hξloc
  have i2 := hi Ψ (hDJcont 1) hξloc
  have i3 := hi (∂_{I} Ψ) hJsmooth.continuous hJξloc
  have i4 := hi Ψ (hDJcont I) hJξloc
  have i5 := hi Ψ hJsmooth.continuous (w := fun z => DJ z I (ξ z)) ((hc.memLpLoc_deriv.clm_comp
    (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) I)).locallyIntegrableOn_clm_apply
    hsol.memLpLoc hpq hloc)
  have i6 := hi Ψ hJsmooth.continuous
    (hc.memLpLoc_zeroth.locallyIntegrableOn_clm_apply hsol.memLpLoc hpq hloc)
  have hsplit : ∫ z, ⟪crFormalAdjoint J DJ S (adjointApplyTestFunction hJsmooth Ψ) z, ξ z⟫_ℝ =
      -(∫ z, ⟪(∂_{(1 : ℂ)} Ψ : 𝓓(Ω, V)) z, J_ρ z (ξ z)⟫_ℝ) -
        (∫ z, ⟪(Ψ : ℂ → V) z, fderiv ℝ J_ρ z 1 (ξ z)⟫_ℝ) -
        (∫ z, ⟪(∂_{I} Ψ : 𝓓(Ω, V)) z, J_ρ z (J z (ξ z))⟫_ℝ) -
        (∫ z, ⟪(Ψ : ℂ → V) z, fderiv ℝ J_ρ z I (J z (ξ z))⟫_ℝ) -
        (∫ z, ⟪(Ψ : ℂ → V) z, J_ρ z (DJ z I (ξ z))⟫_ℝ) +
        ∫ z, ⟪(Ψ : ℂ → V) z, J_ρ z (S z (ξ z))⟫_ℝ := by
    simp only [inner_crFormalAdjoint_adjointApplyTestFunction]
    rw [integral_add _ i6, integral_sub _ i5, integral_sub _ i4, integral_sub _ i3,
      integral_sub _ i2, integral_neg]
    exacts [i1.neg, i1.neg.sub i2, (i1.neg.sub i2).sub i3, ((i1.neg.sub i2).sub i3).sub i4,
      (((i1.neg.sub i2).sub i3).sub i4).sub i5]
  have hsol_ρ := hsol.integral_inner_crFormalAdjoint (adjointApplyTestFunction hJsmooth Ψ)
  simp only [adjointApplyTestFunction_apply, ContinuousLinearMap.adjoint_inner_left,
    hsplit] at hsol_ρ
  simp_rw [hDJ_eq] at hsol_ρ; exact hsol_ρ

/-- Algebraic expansion of the right-hand side pairing in `integral_inner_adjoint_limit`. -/
private theorem integral_inner_adjoint_rhs_eq (hpq : p⁻¹ + q⁻¹ ≤ 1)
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hJcont : ContinuousOn J Ω)
    (hsol : IsWeakCRSolution q Ω J DJ S ξ η)
    (hJξ : MemLpLoc q Ω (fun z => J z (ξ z))) (Ψ : 𝓓(Ω, V)) :
    -∫ z, ⟪(Ψ : ℂ → V) z,
        -J z (η z + DJ z I (ξ z) - S z (ξ z)) - DJ z 1 (ξ z) - DJ z I (J z (ξ z))⟫_ℝ =
      (∫ z, ⟪(Ψ : ℂ → V) z, J z (η z)⟫_ℝ) +
        (∫ z, ⟪(Ψ : ℂ → V) z, J z (DJ z I (ξ z))⟫_ℝ) -
        (∫ z, ⟪(Ψ : ℂ → V) z, J z (S z (ξ z))⟫_ℝ) +
        (∫ z, ⟪(Ψ : ℂ → V) z, DJ z 1 (ξ z)⟫_ℝ) +
        ∫ z, ⟪(Ψ : ℂ → V) z, DJ z I (J z (ξ z))⟫_ℝ := by
  have hloc := Ω.isOpen.isLocallyClosed
  have hDJI : MemLpLoc p Ω (fun z => DJ z I) :=
    hc.memLpLoc_deriv.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) I)
  have hDJ1 : MemLpLoc p Ω (fun z => DJ z 1) :=
    hc.memLpLoc_deriv.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) 1)
  have hDJIξ : LocallyIntegrableOn (fun z => DJ z I (ξ z)) Ω volume :=
    hDJI.locallyIntegrableOn_clm_apply hsol.memLpLoc hpq hloc
  have hSξ : LocallyIntegrableOn (fun z => S z (ξ z)) Ω volume :=
    hc.memLpLoc_zeroth.locallyIntegrableOn_clm_apply hsol.memLpLoc hpq hloc
  have hclm {w : ℂ → V} (hw : LocallyIntegrableOn w Ω volume) :
      Integrable (fun z => ⟪(Ψ : ℂ → V) z, J z (w z)⟫_ℝ) :=
    Ψ.integrable_inner ((((memLpLoc_one_iff_locallyIntegrableOn hloc).2
      hw).clm_apply_of_continuousOn hJcont).locallyIntegrableOn le_rfl hloc)
  obtain ⟨hf, -⟩ := hc.locallyIntegrableOn_laplace_aux hpq hJcont hsol
  have hJf_eq : ∫ z, ⟪(Ψ : ℂ → V) z, J z (η z + DJ z I (ξ z) - S z (ξ z))⟫_ℝ =
      (∫ z, ⟪(Ψ : ℂ → V) z, J z (η z)⟫_ℝ) + (∫ z, ⟪(Ψ : ℂ → V) z, J z (DJ z I (ξ z))⟫_ℝ) -
        ∫ z, ⟪(Ψ : ℂ → V) z, J z (S z (ξ z))⟫_ℝ := by
    simp only [map_sub, map_add, inner_sub_right, inner_add_right]
    rw [integral_sub _ (hclm hSξ), integral_add (hclm hsol.locallyIntegrableOn) (hclm hDJIξ)]
    exact (hclm hsol.locallyIntegrableOn).add (hclm hDJIξ)
  have j1 := hclm hf
  have j2 : Integrable (fun z => ⟪(Ψ : ℂ → V) z, DJ z 1 (ξ z)⟫_ℝ) :=
    Ψ.integrable_inner (hDJ1.locallyIntegrableOn_clm_apply hsol.memLpLoc hpq hloc)
  have j3 : Integrable (fun z => ⟪(Ψ : ℂ → V) z, DJ z I (J z (ξ z))⟫_ℝ) :=
    Ψ.integrable_inner (hDJI.locallyIntegrableOn_clm_apply hJξ hpq hloc)
  have hg_eq : -∫ z, ⟪(Ψ : ℂ → V) z,
        -J z (η z + DJ z I (ξ z) - S z (ξ z)) - DJ z 1 (ξ z) - DJ z I (J z (ξ z))⟫_ℝ =
      (∫ z, ⟪(Ψ : ℂ → V) z, J z (η z + DJ z I (ξ z) - S z (ξ z))⟫_ℝ) +
        (∫ z, ⟪(Ψ : ℂ → V) z, DJ z 1 (ξ z)⟫_ℝ) +
        ∫ z, ⟪(Ψ : ℂ → V) z, DJ z I (J z (ξ z))⟫_ℝ := by
    simp only [inner_sub_right, inner_neg_right]
    rw [integral_sub _ j3, integral_sub _ j2, integral_neg]
    · ring
    exacts [j1.neg, j1.neg.sub j2]
  linarith [hJf_eq, hg_eq]

/-- Limit and algebraic assembly for `IsSobolevCRCoefficients.integral_inner_adjoint_limit`. -/
private theorem integral_inner_adjoint_limit_aux (hp : p ≠ ⊤) (hpq : p⁻¹ + q⁻¹ ≤ 1)
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hJcont : ContinuousOn J Ω)
    (hJsq : ∀ z ∈ (Ω : Set ℂ), J z * J z = -1) (hsol : IsWeakCRSolution q Ω J DJ S ξ η)
    (Ψ : 𝓓(Ω, V)) {W : Opens ℂ} (hWc : IsCompact (closure (W : Set ℂ)))
    (hWΩ : closure (W : Set ℂ) ⊆ Ω) (hΨW : tsupport (Ψ : ℂ → V) ⊆ W)
    {ρ : ℕ → ContDiffBump (0 : ℂ)} (hρ0 : Tendsto (fun n => (ρ n).rOut) atTop (𝓝 0))
    (hball : ∀ n, ∀ z ∈ tsupport (Ψ : ℂ → V), closedBall z (ρ n).rOut ⊆ W)
    (hunif : TendstoUniformlyOn
      (fun n => (ρ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (W : Set ℂ).indicator J) J atTop (tsupport (Ψ : ℂ → V)))
    (hJW : MemLp J p (volume.restrict W)) (hDJW : MemLp DJ p (volume.restrict W))
    (hξW : MemLp ξ q (volume.restrict W)) (hJξ : MemLpLoc q Ω (fun z => J z (ξ z)))
    (hJξW : MemLp (fun z => J z (ξ z)) q (volume.restrict W))
    (hJn_smooth : ∀ n, ContDiff ℝ ∞
      ((ρ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (W : Set ℂ).indicator J)) :
    -(∫ z, ⟪(∂_{(1 : ℂ)} Ψ : 𝓓(Ω, V)) z, J z (ξ z)⟫_ℝ) +
        ∫ z, ⟪(∂_{I} Ψ : 𝓓(Ω, V)) z, ξ z⟫_ℝ =
      -∫ z, ⟪(Ψ : ℂ → V) z,
        -J z (η z + DJ z I (ξ z) - S z (ξ z)) - DJ z 1 (ξ z) - DJ z I (J z (ξ z))⟫_ℝ := by
  have hq1 : 1 ≤ q := ENNReal.inv_le_one.1 (le_add_self.trans hpq)
  have hloc := Ω.isOpen.isLocallyClosed
  have hξloc := hsol.memLpLoc.locallyIntegrableOn hq1 hloc
  have hJξloc := hJξ.locallyIntegrableOn hq1 hloc
  have hDJIξ : LocallyIntegrableOn (fun z => DJ z I (ξ z)) Ω volume :=
    (hc.memLpLoc_deriv.clm_comp
      (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) I)).locallyIntegrableOn_clm_apply
      hsol.memLpLoc hpq hloc
  have hSξ : LocallyIntegrableOn (fun z => S z (ξ z)) Ω volume :=
    hc.memLpLoc_zeroth.locallyIntegrableOn_clm_apply hsol.memLpLoc hpq hloc
  have hJn_cont (n : ℕ) : Continuous
      ((ρ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (W : Set ℂ).indicator J) :=
    (hJn_smooth n).continuous
  have hlim_lhs := (((((tendsto_integral_inner_clm_of_uniform (∂_{(1 : ℂ)} Ψ) hξloc hJn_cont
      hJcont (hunif.mono (Ψ.tsupport_lineDerivOp_subset 1))).neg.sub
      (tendsto_integral_inner_convolution_of_memLp hp hpq hWc Ψ hΨW hDJW 1 hξW hρ0)).sub
      (tendsto_integral_inner_clm_of_uniform (∂_{I} Ψ) hJξloc hJn_cont hJcont
        (hunif.mono (Ψ.tsupport_lineDerivOp_subset I)))).sub
      (tendsto_integral_inner_convolution_of_memLp hp hpq hWc Ψ hΨW hDJW I hJξW hρ0)).sub
      (tendsto_integral_inner_clm_of_uniform Ψ hDJIξ hJn_cont hJcont hunif)).add
      (tendsto_integral_inner_clm_of_uniform Ψ hSξ hJn_cont hJcont hunif)
  have hlim_rhs := tendsto_integral_inner_clm_of_uniform Ψ hsol.locallyIntegrableOn hJn_cont
    hJcont hunif
  have hlim := tendsto_nhds_unique hlim_lhs (hlim_rhs.congr fun n =>
    (integral_inner_mollified_adjoint_eq hpq hc hJcont hsol Ψ hWΩ (ρ n) (hball n)
      hJW hDJW (hJn_smooth n)).symm)
  have hJJ : ∫ z, ⟪(∂_{I} Ψ : 𝓓(Ω, V)) z, J z (J z (ξ z))⟫_ℝ =
      -∫ z, ⟪(∂_{I} Ψ : 𝓓(Ω, V)) z, ξ z⟫_ℝ := by
    rw [← integral_neg]
    refine integral_congr_ae (.of_forall fun z => ?_)
    dsimp only
    by_cases hzΩ : z ∈ (Ω : Set ℂ)
    · rw [show J z (J z (ξ z)) = (J z * J z) (ξ z) from rfl, hJsq z hzΩ,
        neg_apply, one_apply_eq_self, inner_neg_right]
    · simp [image_eq_zero_of_notMem_tsupport fun h => hzΩ ((∂_{I} Ψ).tsupport_subset h)]
  rw [hJJ] at hlim
  linarith [hlim, integral_inner_adjoint_rhs_eq hpq hc hJcont hsol hJξ Ψ]

/-- Passing `ψ_n = J_n† Ψ` to the limit in the weak Cauchy–Riemann equation yields the adjoint
identity for `-Jᵀ` against arbitrary test functions `Ψ : 𝓓(Ω, V)` when `J² = -1` on `Ω`. -/
private theorem IsSobolevCRCoefficients.integral_inner_adjoint_limit (hp : p ≠ ⊤)
    (hpq : p⁻¹ + q⁻¹ ≤ 1) (hc : IsSobolevCRCoefficients p Ω J DJ S) (hJcont : ContinuousOn J Ω)
    (hJsq : ∀ z ∈ (Ω : Set ℂ), J z * J z = -1) (hsol : IsWeakCRSolution q Ω J DJ S ξ η)
    (Ψ : 𝓓(Ω, V)) :
    -(∫ z, ⟪(∂_{(1 : ℂ)} Ψ : 𝓓(Ω, V)) z, J z (ξ z)⟫_ℝ) +
        ∫ z, ⟪(∂_{I} Ψ : 𝓓(Ω, V)) z, ξ z⟫_ℝ =
      -∫ z, ⟪(Ψ : ℂ → V) z,
        -J z (η z + DJ z I (ξ z) - S z (ξ z)) - DJ z 1 (ξ z) - DJ z I (J z (ξ z))⟫_ℝ := by
  have hp1 : 1 ≤ p := ENNReal.inv_le_one.1 (le_self_add.trans hpq)
  obtain ⟨W, hΨW, hWΩ, hWc⟩ :=
    Opens.exists_between_and_isCompact_closure Ψ.hasCompactSupport Ψ.tsupport_subset
  obtain ⟨ρ, hρ0, hball, hunif⟩ :=
    exists_mollifier_tendstoUniformlyOn (hJcont.mono (subset_closure.trans hWΩ))
      Ψ.hasCompactSupport hΨW
  have hJW : MemLp J p (volume.restrict W) := hc.memLpLoc_coeff.memLp_of_closure_subset hWc hWΩ
  have hDJW : MemLp DJ p (volume.restrict W) := hc.memLpLoc_deriv.memLp_of_closure_subset hWc hWΩ
  have hξW : MemLp ξ q (volume.restrict W) := hsol.memLpLoc.memLp_of_closure_subset hWc hWΩ
  have hJξ : MemLpLoc q Ω (fun z => J z (ξ z)) := hsol.memLpLoc.clm_apply_of_continuousOn hJcont
  have hJξW : MemLp (fun z => J z (ξ z)) q (volume.restrict W) :=
    hJξ.memLp_of_closure_subset hWc hWΩ
  have hJWext : MemLp ((W : Set ℂ).indicator J) p volume :=
    (memLp_indicator_iff_restrict W.isOpen.measurableSet.nullMeasurableSet).2 hJW
  have hJn_smooth (n : ℕ) : ContDiff ℝ ∞
      ((ρ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (W : Set ℂ).indicator J) :=
    (ρ n).hasCompactSupport_normed.contDiff_convolution_left _ (ρ n).contDiff_normed
      (hJWext.locallyIntegrable hp1)
  exact integral_inner_adjoint_limit_aux hp hpq hc hJcont hJsq hsol Ψ hWc hWΩ hΨW hρ0 hball hunif
    hJW hDJW hξW hJξ hJξW hJn_smooth

/-- Testing the weak Cauchy–Riemann equation against `(∂_1 φ) • w` isolates the `∂_1²` and
mixed `∂_I ∂_1` terms in the divergence-form Laplace identity. -/
private theorem IsSobolevCRCoefficients.integral_inner_lineDeriv_one_smul_eq (hpq : p⁻¹ + q⁻¹ ≤ 1)
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hsol : IsWeakCRSolution q Ω J DJ S ξ η)
    (φ : 𝓓(Ω, ℝ)) (w : V) :
    -(∫ z, ⟪(∂_{(1 : ℂ)} (∂_{(1 : ℂ)} φ) : 𝓓(Ω, ℝ)) z • w, ξ z⟫_ℝ) -
        (∫ z, ⟪(∂_{I} (∂_{(1 : ℂ)} φ) : 𝓓(Ω, ℝ)) z • w, J z (ξ z)⟫_ℝ) =
      ∫ z, ⟪(∂_{(1 : ℂ)} φ : 𝓓(Ω, ℝ)) z • w, η z + DJ z I (ξ z) - S z (ξ z)⟫_ℝ := by
  have hloc := Ω.isOpen.isLocallyClosed
  have hq1 : 1 ≤ q := ENNReal.inv_le_one.1 (le_add_self.trans hpq)
  have hξloc := hsol.memLpLoc.locallyIntegrableOn hq1 hloc
  let Lw : ℝ →L[ℝ] V := (ContinuousLinearMap.id ℝ ℝ).smulRight w
  let smulTest : 𝓓(Ω, ℝ) → 𝓓(Ω, V) := TestFunction.postcompCLM Lw
  have hsmul_apply (θ : 𝓓(Ω, ℝ)) (z : ℂ) : (smulTest θ : ℂ → V) z = (θ : ℂ → ℝ) z • w := rfl
  have hsmul_op (θ : 𝓓(Ω, ℝ)) (u : ℂ) :
      (∂_{u} (smulTest θ) : 𝓓(Ω, V)) = smulTest (∂_{u} θ) :=
    TestFunction.lineDerivCLM_postcompCLM Lw u θ
  set Ψ₁ := smulTest (∂_{(1 : ℂ)} φ)
  have hDJI_loc : LocallyIntegrableOn (fun z => DJ z I (ξ z)) Ω volume :=
    (hc.memLpLoc_deriv.clm_comp
      (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) I)).locallyIntegrableOn_clm_apply
      hsol.memLpLoc hpq hloc
  have hS_loc : LocallyIntegrableOn (fun z => S z (ξ z)) Ω volume :=
    hc.memLpLoc_zeroth.locallyIntegrableOn_clm_apply hsol.memLpLoc hpq hloc
  have i1 : Integrable (fun z => ⟪fderiv ℝ (Ψ₁ : ℂ → V) z 1, ξ z⟫_ℝ) :=
    Ψ₁.integrable_inner_fderiv hξloc 1
  have i2 : Integrable (fun z => ⟪fderiv ℝ (Ψ₁ : ℂ → V) z I, J z (ξ z)⟫_ℝ) :=
    Ψ₁.integrable_inner_fderiv
      (hc.memLpLoc_coeff.locallyIntegrableOn_clm_apply hsol.memLpLoc hpq hloc) I
  have iDJ : Integrable (fun z => ⟪(Ψ₁ : ℂ → V) z, DJ z I (ξ z)⟫_ℝ) :=
    Ψ₁.integrable_inner hDJI_loc
  have iS : Integrable (fun z => ⟪(Ψ₁ : ℂ → V) z, S z (ξ z)⟫_ℝ) :=
    Ψ₁.integrable_inner hS_loc
  have iη : Integrable (fun z => ⟪(Ψ₁ : ℂ → V) z, η z⟫_ℝ) :=
    Ψ₁.integrable_inner hsol.locallyIntegrableOn
  have hsplit : ∫ z, ⟪crFormalAdjoint J DJ S Ψ₁ z, ξ z⟫_ℝ =
      -(∫ z, ⟪fderiv ℝ (Ψ₁ : ℂ → V) z 1, ξ z⟫_ℝ) -
        (∫ z, ⟪fderiv ℝ (Ψ₁ : ℂ → V) z I, J z (ξ z)⟫_ℝ) -
        (∫ z, ⟪(Ψ₁ : ℂ → V) z, DJ z I (ξ z)⟫_ℝ) +
        ∫ z, ⟪(Ψ₁ : ℂ → V) z, S z (ξ z)⟫_ℝ := by
    simp only [inner_crFormalAdjoint]
    rw [integral_add _ iS, integral_sub _ iDJ, integral_sub _ i2, integral_neg]
    exacts [i1.neg, i1.neg.sub i2, (i1.neg.sub i2).sub iDJ]
  have h1 := hsol.integral_inner_crFormalAdjoint Ψ₁
  rw [hsplit] at h1
  simp only [← TestFunction.lineDerivOp_apply_eq_fderiv, Ψ₁, hsmul_op, hsmul_apply] at h1
  have hrhs : ∫ z, ⟪(Ψ₁ : ℂ → V) z, η z + DJ z I (ξ z) - S z (ξ z)⟫_ℝ =
      (∫ z, ⟪(Ψ₁ : ℂ → V) z, η z⟫_ℝ) + (∫ z, ⟪(Ψ₁ : ℂ → V) z, DJ z I (ξ z)⟫_ℝ) -
        ∫ z, ⟪(Ψ₁ : ℂ → V) z, S z (ξ z)⟫_ℝ := by
    simp only [inner_sub_right, inner_add_right]
    rw [integral_sub _ iS, integral_add iη iDJ]
    exact iη.add iDJ
  simp only [Ψ₁, hsmul_apply] at hrhs
  linarith

/-- **Divergence-form Laplace reduction** for weak Cauchy–Riemann solutions with Sobolev
coefficients. Suppose `p < ∞`, `p⁻¹ + q⁻¹ ≤ 1` (allowing `q = ∞`), `J` is continuous on `Ω` with
`J² = -1` everywhere on `Ω`, and `ξ` solves `∂_s ξ + J ∂_t ξ + S ξ = η` weakly on `Ω`. Then `ξ`
solves `Δξ = ∂_s f + ∂_t g` weakly on `Ω`, where `f = η + (∂_t J) ξ - S ξ` and
`g = -J f - (∂_s J) ξ - (∂_t J)(J ξ)`. -/
theorem IsSobolevCRCoefficients.integral_laplacian_smul_eq (hp : p ≠ ⊤) (hpq : p⁻¹ + q⁻¹ ≤ 1)
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hJcont : ContinuousOn J Ω)
    (hJsq : ∀ z ∈ (Ω : Set ℂ), J z * J z = -1) (hsol : IsWeakCRSolution q Ω J DJ S ξ η)
    (φ : 𝓓(Ω, ℝ)) :
    ∫ z, Δ (φ : ℂ → ℝ) z • ξ z =
      -∫ z, (fderiv ℝ (φ : ℂ → ℝ) z 1 • (η z + DJ z I (ξ z) - S z (ξ z)) +
        fderiv ℝ (φ : ℂ → ℝ) z I •
          (-J z (η z + DJ z I (ξ z) - S z (ξ z)) - DJ z 1 (ξ z) - DJ z I (J z (ξ z)))) := by
  have hloc := Ω.isOpen.isLocallyClosed
  have hq1 : 1 ≤ q := ENNReal.inv_le_one.1 (le_add_self.trans hpq)
  have hξloc := hsol.memLpLoc.locallyIntegrableOn hq1 hloc
  obtain ⟨hf, hg⟩ := hc.locallyIntegrableOn_laplace_aux hpq hJcont hsol
  refine ext_inner_left ℝ fun w => ?_
  let Lw : ℝ →L[ℝ] V := (ContinuousLinearMap.id ℝ ℝ).smulRight w
  let smulTest : 𝓓(Ω, ℝ) → 𝓓(Ω, V) := TestFunction.postcompCLM Lw
  have hsmul_apply (θ : 𝓓(Ω, ℝ)) (z : ℂ) : (smulTest θ : ℂ → V) z = (θ : ℂ → ℝ) z • w := rfl
  have hsmul_op (θ : 𝓓(Ω, ℝ)) (u : ℂ) :
      (∂_{u} (smulTest θ) : 𝓓(Ω, V)) = smulTest (∂_{u} θ) :=
    TestFunction.lineDerivCLM_postcompCLM Lw u θ
  have eq1 := hc.integral_inner_lineDeriv_one_smul_eq hpq hsol φ w
  have eq2 := hc.integral_inner_adjoint_limit hp hpq hJcont hJsq hsol (smulTest (∂_{I} φ))
  simp only [hsmul_op, hsmul_apply] at eq2
  rw [TestFunction.lineDerivOp_comm φ 1 I] at eq2
  have hΔ (z : ℂ) : Δ (φ : ℂ → ℝ) z =
      (∂_{(1 : ℂ)} (∂_{(1 : ℂ)} φ)) z + (∂_{I} (∂_{I} φ)) z := by
    rw [← TestFunction.laplacianCLM_apply]
    simp [laplacianCLM_eq_sum Complex.orthonormalBasisOneI, Fin.sum_univ_two]
  have hint11 := (∂_{(1 : ℂ)} (∂_{(1 : ℂ)} φ)).integrable_smul hξloc
  have hintII := (∂_{I} (∂_{I} φ)).integrable_smul hξloc
  have hintf := integrable_fderiv_smul_of_locallyIntegrableOn hf φ 1
  have hintg := integrable_fderiv_smul_of_locallyIntegrableOn hg φ I
  have hpull (θ : 𝓓(Ω, ℝ)) {u : ℂ → V} (hu : Integrable (fun z => (θ : ℂ → ℝ) z • u z)) :
      ⟪w, ∫ z, (θ : ℂ → ℝ) z • u z⟫_ℝ = ∫ z, ⟪(θ : ℂ → ℝ) z • w, u z⟫_ℝ := by
    rw [← integral_inner hu w]
    exact integral_congr_ae (.of_forall fun z => by simp [inner_smul_left, inner_smul_right])
  have hlhs : ⟪w, ∫ z, Δ (φ : ℂ → ℝ) z • ξ z⟫_ℝ =
      (∫ z, ⟪(∂_{(1 : ℂ)} (∂_{(1 : ℂ)} φ) : 𝓓(Ω, ℝ)) z • w, ξ z⟫_ℝ) +
        ∫ z, ⟪(∂_{I} (∂_{I} φ) : 𝓓(Ω, ℝ)) z • w, ξ z⟫_ℝ := by
    simp_rw [hΔ, add_smul]
    rw [integral_add hint11 hintII, inner_add_right, hpull _ hint11, hpull _ hintII]
  have hrhs : ⟪w, -∫ z, (fderiv ℝ (φ : ℂ → ℝ) z 1 • (η z + DJ z I (ξ z) - S z (ξ z)) +
        fderiv ℝ (φ : ℂ → ℝ) z I •
          (-J z (η z + DJ z I (ξ z) - S z (ξ z)) - DJ z 1 (ξ z) - DJ z I (J z (ξ z))))⟫_ℝ =
      -(∫ z, ⟪(∂_{(1 : ℂ)} φ : 𝓓(Ω, ℝ)) z • w, η z + DJ z I (ξ z) - S z (ξ z)⟫_ℝ) -
        ∫ z, ⟪(∂_{I} φ : 𝓓(Ω, ℝ)) z • w,
          -J z (η z + DJ z I (ξ z) - S z (ξ z)) - DJ z 1 (ξ z) - DJ z I (J z (ξ z))⟫_ℝ := by
    rw [inner_neg_right, integral_add hintf hintg, inner_add_right]
    simp only [← TestFunction.lineDerivOp_apply_eq_fderiv] at hintf hintg ⊢
    rw [hpull _ hintf, hpull _ hintg]
    ring
  linarith

end LaplaceReduction

section OrderZeroRegularity

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Ω : Opens ℂ} {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}

/-- **Single-step interior Sobolev gain** (McDuff–Salamon, Lemma B.4.6). Suppose `2 < p < ∞`,
`1 < r < ∞`, `p⁻¹ + q⁻¹ ≤ r⁻¹` (allowing `q = ∞`), `J ∈ W^{1,p}_loc(Ω)` with `J² = -1` almost
everywhere on `Ω`, `S ∈ Lᵖ_loc(Ω)` and `η ∈ Lʳ_loc(Ω)`. Every weak solution `ξ ∈ L^q_loc(Ω)` of
`∂_s ξ + J ∂_t ξ + S ξ = η` lies in `W^{1,r}_loc(Ω)`. -/
theorem IsWeakCRSolution.memWkpLoc_one_of_inv_add_inv_le {p q r : ℝ≥0∞} (hp2 : 2 < p) (hp : p ≠ ⊤)
    (hr1 : 1 < r) (hr : r ≠ ⊤) (hpqr : p⁻¹ + q⁻¹ ≤ r⁻¹)
    (hc : IsSobolevCRCoefficients p Ω J DJ S)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1) (hη : MemLpLoc r Ω η)
    (hsol : IsWeakCRSolution q Ω J DJ S ξ η) :
    MemWkpLoc r Ω 1 ξ := by
  have hpq : p⁻¹ + q⁻¹ ≤ 1 := hpqr.trans (ENNReal.inv_le_one.2 hr1.le)
  have hq1 : 1 ≤ q := ENNReal.inv_le_one.1 (le_add_self.trans hpq)
  have hJW1p : MemWkpLoc p Ω 1 J := memWkpLoc_succ_iff_of_isOpen.2
    ⟨hc.memLpLoc_coeff, DJ, hc.hasWeakFDerivOn, memWkpLoc_zero_iff.2 hc.memLpLoc_deriv⟩
  set J' := TauCeti.MeasureTheory.preciseRepresentative volume J
  have hJ'cont : ContinuousOn J' Ω := hJW1p.continuousOn_preciseRepresentative hp2
  have hJJ' : J =ᵐ[volume.restrict Ω] J' :=
    hc.memLpLoc_coeff.ae_eq_preciseRepresentative (one_le_two.trans hp2.le)
  have hc' : IsSobolevCRCoefficients p Ω J' DJ S :=
    ⟨hc.hasWeakFDerivOn.congr_ae hJJ', hc.memLpLoc_coeff.congr_ae hJJ',
      hc.memLpLoc_deriv, hc.memLpLoc_zeroth⟩
  have hsol' : IsWeakCRSolution q Ω J' DJ S ξ η :=
    (isWeakCRSolution_congr_ae hJJ' .rfl .rfl .rfl .rfl).1 hsol
  have hJ'sq_ae : (fun z => J' z * J' z) =ᵐ[volume.restrict Ω] fun _ => -1 := by
    filter_upwards [hJsq, hJJ'] with z hsq hJ' using by rw [← hJ', hsq]
  have hJ'sq : ∀ z ∈ (Ω : Set ℂ), J' z * J' z = -1 :=
    Measure.eqOn_open_of_ae_eq hJ'sq_ae Ω.isOpen (hJ'cont.mul hJ'cont) continuousOn_const
  have hDJ1 : MemLpLoc p Ω (fun z => DJ z 1) :=
    hc.memLpLoc_deriv.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) 1)
  have hDJI : MemLpLoc p Ω (fun z => DJ z I) :=
    hc.memLpLoc_deriv.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) I)
  have hJ'ξ : MemLpLoc q Ω (fun z => J' z (ξ z)) := hsol'.memLpLoc.clm_apply_of_continuousOn hJ'cont
  have hf : MemLpLoc r Ω (fun z => η z + DJ z I (ξ z) - S z (ξ z)) :=
    (hη.add (hDJI.clm_apply_of_inv_add_inv_le hsol'.memLpLoc hpqr)).sub
      (hc'.memLpLoc_zeroth.clm_apply_of_inv_add_inv_le hsol'.memLpLoc hpqr)
  have hg : MemLpLoc r Ω
      (fun z => -J' z (η z + DJ z I (ξ z) - S z (ξ z)) - DJ z 1 (ξ z) - DJ z I (J' z (ξ z))) :=
    ((hf.clm_apply_of_continuousOn hJ'cont).neg.sub
      (hDJ1.clm_apply_of_inv_add_inv_le hsol'.memLpLoc hpqr)).sub
      (hDJI.clm_apply_of_inv_add_inv_le hJ'ξ hpqr)
  exact memWkpLoc_one_of_forall_integral_laplacian_smul_eq hr1 hr
    (hsol'.memLpLoc.locallyIntegrableOn hq1 Ω.isOpen.isLocallyClosed) hf hg
    (hc'.integral_laplacian_smul_eq hp hpq hJ'cont hJ'sq hsol')

/-- Upgrading `MemLpLoc` membership of `ξ` upgrades the exponent of `IsWeakCRSolution`. -/
private theorem IsWeakCRSolution.of_memLpLoc {q q' : ℝ≥0∞}
    (hsol : IsWeakCRSolution q Ω J DJ S ξ η) (hξ : MemLpLoc q' Ω ξ) :
    IsWeakCRSolution q' Ω J DJ S ξ η :=
  isWeakCRSolution_iff.2 ⟨hξ, hsol.locallyIntegrableOn, fun φ =>
    ⟨hsol.integrable_inner_crFormalAdjoint φ, hsol.integral_inner_crFormalAdjoint φ⟩⟩

/-- Subcritical Sobolev-embedding step: when `m = (p⁻¹ + q₀⁻¹)⁻¹` satisfies `1 < m ≤ 2` and
`2 < p`, `MemWkpLoc m Ω 1 ξ` embeds into `MemLpLoc s Ω ξ` with
`s⁻¹ = q₀⁻¹ - (2⁻¹ - p⁻¹) / 2`. -/
private theorem memLpLoc_step_of_memWkpLoc_le_two {p q₀ m : ℝ≥0} (hp : 2 < p) (hm1 : 1 < m)
    (hm2 : ¬ 2 < m) (hm_inv : (m : ℝ)⁻¹ = (p : ℝ)⁻¹ + (q₀ : ℝ)⁻¹)
    (hξm : MemWkpLoc m Ω 1 ξ) :
    ∃ s : ℝ≥0, 0 < s ∧ (s : ℝ)⁻¹ = (q₀ : ℝ)⁻¹ - (2⁻¹ - (p : ℝ)⁻¹) / 2 ∧
      MemLpLoc s Ω ξ := by
  have hp2 : (2 : ℝ) < p := by exact_mod_cast hp
  have hp_inv_pos : 0 < (p : ℝ)⁻¹ := by positivity
  have hp_inv_lt : (p : ℝ)⁻¹ < 2⁻¹ := (inv_lt_inv₀ (by positivity) two_pos).2 hp2
  have hm2_le : (m : ℝ) ≤ 2 := by exact_mod_cast not_lt.1 hm2
  have hm_inv_ge : 2⁻¹ ≤ (p : ℝ)⁻¹ + (q₀ : ℝ)⁻¹ := by
    rw [← hm_inv]
    exact (inv_le_inv₀ two_pos (zero_lt_one.trans (by exact_mod_cast hm1))).2 hm2_le
  have hsinv_pos : 0 < (q₀ : ℝ)⁻¹ - (2⁻¹ - (p : ℝ)⁻¹) / 2 := by linarith
  let s : ℝ≥0 := ⟨((q₀ : ℝ)⁻¹ - (2⁻¹ - (p : ℝ)⁻¹) / 2)⁻¹, by positivity⟩
  have hs_pos : 0 < s := by exact_mod_cast inv_pos.2 hsinv_pos
  have hs_inv : (s : ℝ)⁻¹ = (q₀ : ℝ)⁻¹ - (2⁻¹ - (p : ℝ)⁻¹) / 2 := inv_inv _
  have hms : m ≤ s := by
    have : (m : ℝ) ≤ s :=
      (inv_le_inv₀ (by exact_mod_cast hs_pos)
        (zero_lt_one.trans (by exact_mod_cast hm1))).1 (by rw [hm_inv, hs_inv]; linarith)
    exact_mod_cast this
  have hgap : (m : ℝ)⁻¹ - (s : ℝ)⁻¹ ≤ 2⁻¹ := by
    rw [hm_inv, hs_inv]
    linarith
  exact ⟨s, hs_pos, hs_inv, hξm.memLpLoc_of_inv_sub_inv_le hm1.le hms hgap⟩

/-- Inductive exponent-climbing loop for `IsWeakCRSolution.memWkpLoc_one_of_memLpLoc`: each step
decreases `(q₀ : ℝ)⁻¹` by `(2⁻¹ - (p : ℝ)⁻¹) / 2 > 0` until either `(p : ℝ)⁻¹ + q₀⁻¹ ≤ r⁻¹` or the
intermediate Sobolev exponent exceeds `2`. -/
private theorem memWkpLoc_one_bootstrap_aux {p r : ℝ≥0} (hp : 2 < p) (hr : 1 < r) (hrp : r ≤ p)
    (hc : IsSobolevCRCoefficients p Ω J DJ S)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1) (hη : MemLpLoc r Ω η) :
    ∀ (N : ℕ) {q₀ : ℝ≥0}, 0 < q₀ → (p : ℝ)⁻¹ + (q₀ : ℝ)⁻¹ < 1 →
      (q₀ : ℝ)⁻¹ ≤ (N : ℝ) * ((2⁻¹ - (p : ℝ)⁻¹) / 2) →
      IsWeakCRSolution q₀ Ω J DJ S ξ η → MemWkpLoc r Ω 1 ξ
  | 0, q₀, hq0, _, hN, _ => by
      have hq_pos : 0 < (q₀ : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast hq0)
      simp only [Nat.cast_zero, zero_mul] at hN
      linarith
  | N + 1, q₀, hq0, hpq, hN, hsol => by
      have hp2 : (2 : ℝ) < p := by exact_mod_cast hp
      have hr_pos : (0 : ℝ) < r := zero_lt_one.trans (by exact_mod_cast hr)
      have hp_inv_lt : (p : ℝ)⁻¹ < 2⁻¹ := (inv_lt_inv₀ (by positivity) two_pos).2 hp2
      by_cases hle : (p : ℝ)⁻¹ + (q₀ : ℝ)⁻¹ ≤ (r : ℝ)⁻¹
      · have hle' : (p : ℝ≥0∞)⁻¹ + (q₀ : ℝ≥0∞)⁻¹ ≤ (r : ℝ≥0∞)⁻¹ := by
          rw [← ENNReal.coe_inv (zero_lt_two.trans hp).ne', ← ENNReal.coe_inv hq0.ne',
            ← ENNReal.coe_inv (zero_lt_one.trans hr).ne', ← ENNReal.coe_add]
          exact_mod_cast hle
        exact hsol.memWkpLoc_one_of_inv_add_inv_le (by exact_mod_cast hp) ENNReal.coe_ne_top
          (by exact_mod_cast hr) ENNReal.coe_ne_top hle' hc hJsq hη
      · rw [not_le] at hle
        set m : ℝ≥0 := (p⁻¹ + q₀⁻¹)⁻¹
        have hm_inv : (m : ℝ)⁻¹ = (p : ℝ)⁻¹ + (q₀ : ℝ)⁻¹ := by
          simp [m, NNReal.coe_inv, NNReal.coe_add]
        have hm1 : 1 < m := by
          have : 1 < (m : ℝ) := by
            rw [← inv_inv (m : ℝ), hm_inv]
            exact (one_lt_inv₀ (by positivity)).2 hpq
          exact_mod_cast this
        have hmr : m ≤ r := by
          have : (m : ℝ) ≤ r := (inv_le_inv₀ hr_pos
            (zero_lt_one.trans (by exact_mod_cast hm1))).1 (by linarith)
          exact_mod_cast this
        have hpqm : (p : ℝ≥0∞)⁻¹ + (q₀ : ℝ≥0∞)⁻¹ ≤ (m : ℝ≥0∞)⁻¹ := by
          rw [← ENNReal.coe_inv (zero_lt_two.trans hp).ne', ← ENNReal.coe_inv hq0.ne',
            ← ENNReal.coe_inv (zero_lt_one.trans hm1).ne', ← ENNReal.coe_add]
          exact le_of_eq (by simp [m])
        have hξm : MemWkpLoc m Ω 1 ξ :=
          hsol.memWkpLoc_one_of_inv_add_inv_le (by exact_mod_cast hp) ENNReal.coe_ne_top
            (by exact_mod_cast hm1) ENNReal.coe_ne_top hpqm hc hJsq
            (hη.mono_exponent (by exact_mod_cast hmr))
        by_cases hm2 : 2 < m
        · have : Fact (1 ≤ (m : ℝ≥0∞)) := ⟨by exact_mod_cast hm1.le⟩
          have : ENNReal.HolderTriple (m : ℝ≥0∞) (⊤ : ℝ≥0∞) m := ⟨by simp⟩
          have hξ_top : MemLpLoc ⊤ Ω ξ := hξm.memLpLoc_of_holderTriple hm2 le_rfl
          have hpr : (p : ℝ≥0∞)⁻¹ + (⊤ : ℝ≥0∞)⁻¹ ≤ (r : ℝ≥0∞)⁻¹ := by
            simpa using ENNReal.inv_le_inv.2 (ENNReal.coe_le_coe.2 hrp)
          exact (hsol.of_memLpLoc hξ_top).memWkpLoc_one_of_inv_add_inv_le
            (by exact_mod_cast hp) ENNReal.coe_ne_top (by exact_mod_cast hr) ENNReal.coe_ne_top
            hpr hc hJsq hη
        · obtain ⟨s, hs_pos, hs_inv, hξs⟩ :=
            memLpLoc_step_of_memWkpLoc_le_two hp hm1 hm2 hm_inv hξm
          refine memWkpLoc_one_bootstrap_aux hp hr hrp hc hJsq hη N hs_pos ?_ ?_
            (hsol.of_memLpLoc hξs)
          · rw [hs_inv]
            linarith
          · rw [hs_inv]
            push_cast at hN
            linarith

/-- **Order-zero interior regularity with general right-hand side** (McDuff–Salamon, Proposition
B.4.9 at `k = 0`). Let `2 < p`, `1 < r ≤ p`, and `(p : ℝ≥0∞)⁻¹ + q⁻¹ < 1` (allowing `q = ∞`). If
`J ∈ W^{1,p}_loc(Ω)` with `J² = -1` almost everywhere on `Ω`, `S ∈ Lᵖ_loc(Ω)`, and
`η ∈ Lʳ_loc(Ω)`, then every weak solution `ξ ∈ L^q_loc(Ω)` of `∂_s ξ + J ∂_t ξ + S ξ = η` lies in
`W^{1,r}_loc(Ω)`. -/
theorem IsWeakCRSolution.memWkpLoc_one_of_memLpLoc {p r : ℝ≥0} {q : ℝ≥0∞} (hp : 2 < p)
    (hr : 1 < r) (hrp : r ≤ p) (hpq : (p : ℝ≥0∞)⁻¹ + q⁻¹ < 1)
    (hc : IsSobolevCRCoefficients p Ω J DJ S)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1) (hη : MemLpLoc r Ω η)
    (hsol : IsWeakCRSolution q Ω J DJ S ξ η) :
    MemWkpLoc r Ω 1 ξ := by
  rcases eq_or_ne q ⊤ with rfl | hqt
  · have hpr : (p : ℝ≥0∞)⁻¹ + (⊤ : ℝ≥0∞)⁻¹ ≤ (r : ℝ≥0∞)⁻¹ := by
      simpa using ENNReal.inv_le_inv.2 (ENNReal.coe_le_coe.2 hrp)
    exact hsol.memWkpLoc_one_of_inv_add_inv_le (by exact_mod_cast hp) ENNReal.coe_ne_top
      (by exact_mod_cast hr) ENNReal.coe_ne_top hpr hc hJsq hη
  have hq0 : q ≠ 0 := by
    rintro rfl
    simp at hpq
  lift q to ℝ≥0 using hqt
  have hq_pos : 0 < q := pos_iff_ne_zero.2 (by exact_mod_cast hq0)
  have hp_pos : 0 < p := zero_lt_two.trans hp
  have hpq' : (p : ℝ)⁻¹ + (q : ℝ)⁻¹ < 1 := by
    rw [← ENNReal.coe_inv hp_pos.ne', ← ENNReal.coe_inv hq_pos.ne', ← ENNReal.coe_add] at hpq
    exact_mod_cast hpq
  have hp2 : (2 : ℝ) < p := by exact_mod_cast hp
  have hp_inv_lt : (p : ℝ)⁻¹ < 2⁻¹ := (inv_lt_inv₀ (by positivity) two_pos).2 hp2
  have hδ : 0 < (2⁻¹ - (p : ℝ)⁻¹) / 2 := by linarith
  refine memWkpLoc_one_bootstrap_aux hp hr hrp hc hJsq hη
    ⌈(q : ℝ)⁻¹ / ((2⁻¹ - (p : ℝ)⁻¹) / 2)⌉₊ hq_pos hpq' ?_ hsol
  exact (div_le_iff₀ hδ).1 (Nat.le_ceil _)

/-- **Order-zero interior regularity** (McDuff–Salamon, Proposition B.4.9, `k = 0`). Let `2 < p`,
`1 < q ≤ p`, and `(p : ℝ≥0∞)⁻¹ + (q : ℝ≥0∞)⁻¹ < 1`. If `J ∈ W^{1,p}_loc(Ω)` with `J² = -1` almost
everywhere on `Ω`, `S ∈ Lᵖ_loc(Ω)`, and `η ∈ L^q_loc(Ω)`, then every weak solution
`ξ ∈ L^q_loc(Ω)` of `∂_s ξ + J ∂_t ξ + S ξ = η` lies in `W^{1,q}_loc(Ω)`. -/
theorem IsWeakCRSolution.memWkpLoc_one {p q : ℝ≥0} (hp : 2 < p) (hq : 1 < q) (hqp : q ≤ p)
    (hpq : (p : ℝ≥0∞)⁻¹ + (q : ℝ≥0∞)⁻¹ < 1) (hc : IsSobolevCRCoefficients p Ω J DJ S)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1) (hη : MemLpLoc q Ω η)
    (hsol : IsWeakCRSolution q Ω J DJ S ξ η) :
    MemWkpLoc q Ω 1 ξ :=
  hsol.memWkpLoc_one_of_memLpLoc hp hq hqp hpq hc hJsq hη

end OrderZeroRegularity

section Counterexample

/-- Horizontal-line fundamental theorem of calculus for `(∂_1 φ)(s + i t)`: integrating in `s : ℝ`
vanishes for every fixed `t : ℝ`. -/
private theorem integral_lineDerivOp_one_slice_eq_zero {Ω : Opens ℂ} (φ : 𝓓(Ω, ℝ)) (t : ℝ) :
    (∫ s : ℝ, (∂_{(1 : ℂ)} φ : 𝓓(Ω, ℝ)) ((s : ℂ) + t * I)) = 0 := by
  let emb : ℝ → ℂ := fun s => (s : ℂ) + t * I
  let g : ℝ → ℝ := fun s => (φ : ℂ → ℝ) (emb s)
  let g' : ℝ → ℝ := fun s => (∂_{(1 : ℂ)} φ : 𝓓(Ω, ℝ)) (emb s)
  have hg_deriv (s : ℝ) : HasDerivAt g (g' s) s := by
    have hemb : HasFDerivAt emb Complex.ofRealCLM s :=
      (Complex.ofRealCLM.hasFDerivAt (x := s)).add_const ((t : ℂ) * I)
    have hd := ((φ.contDiff.differentiable (by simp) (emb s)).hasFDerivAt.comp s hemb).hasDerivAt
    simpa only [g, g', Function.comp_def, TestFunction.lineDerivOp_apply_eq_fderiv,
      ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, Complex.ofReal_one] using hd
  obtain ⟨R, hR⟩ := φ.hasCompactSupport.isCompact.isBounded.subset_closedBall (0 : ℂ)
  have hcs (θ : 𝓓(Ω, ℝ)) (hθ : tsupport (θ : ℂ → ℝ) ⊆ tsupport (φ : ℂ → ℝ)) :
      Integrable (fun s : ℝ => (θ : ℂ → ℝ) (emb s)) := by
    refine (θ.continuous.comp (Complex.continuous_ofReal.add
      continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -R) (b := R))
        fun s hs => ?_)
    have hz : emb s ∈ closedBall (0 : ℂ) R := hR (hθ (subset_tsupport _ hs))
    rw [mem_closedBall_zero_iff] at hz
    have hre : (emb s).re = s := by simp [emb]
    exact abs_le.1 (hre ▸ (Complex.abs_re_le_norm (emb s)).trans hz)
  exact integral_eq_zero_of_hasDerivAt_of_integrable hg_deriv
    (hcs (∂_{(1 : ℂ)} φ) (φ.tsupport_lineDerivOp_subset 1)) (hcs φ subset_rfl)

/-- The indicator of the upper half-plane solves `∂_s ξ = 0` weakly in `L^∞_loc(Ω)` on every open
planar domain `Ω`. -/
private theorem isWeakCRSolution_upperHalfPlaneIndicator (Ω : Opens ℂ) :
    IsWeakCRSolution ⊤ Ω 0 0 0 ({z : ℂ | 0 < z.im}.indicator fun _ => (1 : ℝ)) 0 := by
  set ξ : ℂ → ℝ := {z : ℂ | 0 < z.im}.indicator fun _ => 1
  have hmeas : MeasurableSet {z : ℂ | 0 < z.im} := measurableSet_lt measurable_const measurable_im
  have hξ_top : MemLpLoc ⊤ Ω ξ := memLpLoc_iff.2 fun K _ hK => by
    have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
    exact memLp_indicator_const ⊤ hmeas.nullMeasurableSet 1 (Or.inr (measure_ne_top _ _))
  refine isWeakCRSolution_iff.2 ⟨hξ_top, locallyIntegrableOn_zero, fun φ => ?_⟩
  have hloc := hξ_top.locallyIntegrableOn le_top Ω.isOpen.isLocallyClosed
  have hint₀ : Integrable (fun z => fderiv ℝ (φ : ℂ → ℝ) z 1 * ξ z) := by
    simpa [mul_comm] using φ.integrable_inner_fderiv hloc 1
  have hadj (z : ℂ) : ⟪crFormalAdjoint 0 0 0 φ z, ξ z⟫_ℝ = -(fderiv ℝ (φ : ℂ → ℝ) z 1 * ξ z) := by
    rw [inner_crFormalAdjoint]; simp [mul_comm]
  simp_rw [hadj]
  refine ⟨hint₀.neg, ?_⟩
  simp only [Pi.zero_apply, inner_zero_right, integral_zero, integral_neg, neg_eq_zero]
  rw [← (Complex.volume_preserving_equiv_real_prod.symm _).integral_comp'
    (fun z => fderiv ℝ (φ : ℂ → ℝ) z 1 * ξ z), Measure.volume_eq_prod]
  have hp_int : Integrable (fun p : ℝ × ℝ =>
      fderiv ℝ (φ : ℂ → ℝ) (Complex.measurableEquivRealProd.symm p) 1 *
        ξ (Complex.measurableEquivRealProd.symm p)) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact ((Complex.volume_preserving_equiv_real_prod.symm _).integrable_comp_emb
      Complex.measurableEquivRealProd.symm.measurableEmbedding).2 hint₀
  rw [integral_prod_symm _ hp_int]
  refine integral_eq_zero_of_ae (.of_forall fun t => ?_)
  simp only [Pi.zero_apply]
  by_cases ht : 0 < t
  · have hξt (s : ℝ) : ξ (Complex.measurableEquivRealProd.symm (s, t)) = 1 :=
      indicator_of_mem ht _
    have hsymm (s : ℝ) : Complex.measurableEquivRealProd.symm (s, t) = (s : ℂ) + t * I := by
      apply Complex.ext <;> simp
    simp_rw [hξt, mul_one, hsymm, ← TestFunction.lineDerivOp_apply_eq_fderiv]
    exact integral_lineDerivOp_one_slice_eq_zero φ t
  · have hξt (s : ℝ) : ξ (Complex.measurableEquivRealProd.symm (s, t)) = 0 :=
      indicator_of_notMem ht _
    simp_rw [hξt, mul_zero, integral_zero]

/-- Any continuous function `g` on `Ω` agreeing almost everywhere on `Ω` with the upper-half-plane
indicator equals `1` on `ball z₀ ε ∩ {z | 0 < z.im}` and `0` on `ball z₀ ε ∩ {z | z.im < 0}`
whenever `ball z₀ ε ⊆ Ω`. -/
private theorem eqOn_ball_inter_upper_lower {Ω : Opens ℂ} {g : ℂ → ℝ} (hg_cont : ContinuousOn g Ω)
    (hg_ae : ({z : ℂ | 0 < z.im}.indicator fun _ => (1 : ℝ)) =ᵐ[volume.restrict Ω] g)
    {z₀ : ℂ} {ε : ℝ} (hball : ball z₀ ε ⊆ Ω) :
    EqOn (fun _ => (1 : ℝ)) g (ball z₀ ε ∩ {z | 0 < z.im}) ∧
      EqOn (fun _ => (0 : ℝ)) g (ball z₀ ε ∩ {z | z.im < 0}) := by
  set Up : Set ℂ := ball z₀ ε ∩ {z | 0 < z.im}
  set Un : Set ℂ := ball z₀ ε ∩ {z | z.im < 0}
  have hUp_open : IsOpen Up := isOpen_ball.inter (isOpen_lt continuous_const continuous_im)
  have hUn_open : IsOpen Un := isOpen_ball.inter (isOpen_lt continuous_im continuous_const)
  have hgp_ae : (fun _ : ℂ => (1 : ℝ)) =ᵐ[volume.restrict Up] g := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (inter_subset_left.trans hball) hg_ae,
      ae_restrict_mem hUp_open.measurableSet] with z hzg hz
    exact hzg ▸ (indicator_of_mem hz.2 (fun _ => (1 : ℝ))).symm
  have hgn_ae : (fun _ : ℂ => (0 : ℝ)) =ᵐ[volume.restrict Un] g := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (inter_subset_left.trans hball) hg_ae,
      ae_restrict_mem hUn_open.measurableSet] with z hzg hz
    have hzim : z ∉ {w : ℂ | 0 < w.im} := fun hpos =>
      ((mem_ofPred.1 hz.2).trans (mem_ofPred.1 hpos)).false
    exact hzg ▸ (indicator_of_notMem hzim (fun _ => (1 : ℝ))).symm
  exact ⟨Measure.eqOn_open_of_ae_eq hgp_ae hUp_open continuousOn_const
      (hg_cont.mono (inter_subset_left.trans hball)),
    Measure.eqOn_open_of_ae_eq hgn_ae hUn_open continuousOn_const
      (hg_cont.mono (inter_subset_left.trans hball))⟩

/-- On an open set `Ω` meeting the real axis, the indicator of the upper half-plane does not belong
to `W^{1,q}_loc(Ω)` for any `q > 2`. -/
private theorem not_memWkpLoc_one_upperHalfPlaneIndicator {Ω : Opens ℂ} {z₀ : ℂ} (hz₀ : z₀ ∈ Ω)
    (him : z₀.im = 0) {q : ℝ≥0∞} (hq : 2 < q) :
    ¬ MemWkpLoc q Ω 1 ({z : ℂ | 0 < z.im}.indicator fun _ => (1 : ℝ)) := by
  intro hW
  set ξ : ℂ → ℝ := {z : ℂ | 0 < z.im}.indicator fun _ => 1
  set g := TauCeti.MeasureTheory.preciseRepresentative volume ξ
  have hg_cont : ContinuousOn g Ω := hW.continuousOn_preciseRepresentative hq
  have hg_ae : ξ =ᵐ[volume.restrict Ω] g :=
    hW.memLpLoc.ae_eq_preciseRepresentative (one_le_two.trans hq.le)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 Ω.isOpen z₀ hz₀
  obtain ⟨hgp, hgn⟩ := eqOn_ball_inter_upper_lower hg_cont hg_ae hball
  let δ : ℕ → ℝ := fun n => ε / ((n : ℝ) + 2)
  have hδ_pos (n : ℕ) : 0 < δ n := div_pos hε (by positivity)
  have hδ_lt (n : ℕ) : δ n < ε := div_lt_self hε (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hseq : Tendsto (fun n : ℕ => (δ n : ℂ) * I) atTop (𝓝 0) := by
    simpa [δ] using (Complex.continuous_ofReal.tendsto 0).comp
      ((tendsto_const_nhds (x := ε)).div_atTop
        (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)) |>.mul_const I
  have hlim_p : Tendsto (fun n : ℕ => z₀ + (δ n : ℂ) * I) atTop (𝓝 z₀) := by
    simpa using tendsto_const_nhds.add hseq
  have hlim_n : Tendsto (fun n : ℕ => z₀ - (δ n : ℂ) * I) atTop (𝓝 z₀) := by
    simpa using tendsto_const_nhds.sub hseq
  have hmem_p (n : ℕ) : z₀ + (δ n : ℂ) * I ∈ ball z₀ ε ∩ {z | 0 < z.im} := by
    refine ⟨?_, by simp [him, hδ_pos n]⟩
    rw [mem_ball, dist_self_add_left, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_of_nonneg (hδ_pos n).le]
    exact hδ_lt n
  have hmem_n (n : ℕ) : z₀ - (δ n : ℂ) * I ∈ ball z₀ ε ∩ {z | z.im < 0} := by
    refine ⟨?_, by simp [him, hδ_pos n]⟩
    rw [mem_ball, sub_eq_add_neg, dist_self_add_left, norm_neg, norm_mul, Complex.norm_I,
      mul_one, Complex.norm_real, Real.norm_of_nonneg (hδ_pos n).le]
    exact hδ_lt n
  have hc_z₀ := (hg_cont z₀ hz₀).continuousAt (Ω.isOpen.mem_nhds hz₀)
  have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (g z₀)) :=
    (hc_z₀.tendsto.comp hlim_p).congr fun n => (hgp (hmem_p n)).symm
  have h0 : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (g z₀)) :=
    (hc_z₀.tendsto.comp hlim_n).congr fun n => (hgn (hmem_n n)).symm
  have h10 : (1 : ℝ) = 0 :=
    (tendsto_nhds_unique tendsto_const_nhds h1).trans (tendsto_nhds_unique h0 tendsto_const_nhds)
  norm_num at h10

/-- **Sharpness of `J² = -1`.** With `J = 0` and `S = 0` (smooth coefficients violating
`J² = -1`), the indicator of the upper half-plane is a bounded weak solution of `∂_s ξ = 0` on
every open set `Ω`, yet on any `Ω` meeting the real axis it fails to lie in `W^{1,q}_loc(Ω)` for
every `q > 2`. -/
theorem exists_isWeakCRSolution_zero_not_memWkpLoc_one {Ω : Opens ℂ} {z₀ : ℂ} (hz₀ : z₀ ∈ Ω)
    (him : z₀.im = 0) {q : ℝ≥0∞} (hq : 2 < q) :
    ∃ ξ : ℂ → ℝ, IsWeakCRSolution ⊤ Ω 0 0 0 ξ 0 ∧ ¬ MemWkpLoc q Ω 1 ξ :=
  ⟨_, isWeakCRSolution_upperHalfPlaneIndicator Ω,
    not_memWkpLoc_one_upperHalfPlaneIndicator hz₀ him hq⟩

end Counterexample

end TauCeti
