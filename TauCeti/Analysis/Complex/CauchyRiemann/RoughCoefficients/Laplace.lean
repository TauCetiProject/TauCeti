/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Weak
public import TauCeti.Analysis.Complex.Wirtinger.DivergenceLaplace
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.MetricSpace.Thickening
import TauCeti.Analysis.Distribution.TestFunction.Inner
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Sobolev.Mollification.Interior
import TauCeti.Analysis.Sobolev.WeakDeriv.Bilinear.Holder
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
import TauCeti.MeasureTheory.Function.Lp.Holder

/-!
# Divergence-form Laplace reduction for Cauchy–Riemann operators with Sobolev coefficients

Let `Ω ⊆ ℂ` be open, write `z = s + i t`, and let `V` be a real Hilbert space. For Sobolev
coefficients `J ∈ W^{1,p}_loc(Ω; V →L[ℝ] V)` and `S ∈ Lᵖ_loc(Ω; V →L[ℝ] V)` with `p < ∞`, assume
`J` is continuous on `Ω` with `J² = -1` everywhere on `Ω`, and let `ξ ∈ L^q_loc(Ω)` weakly solve

`∂_s ξ + J ∂_t ξ + S ξ = η`

in the sense of `TauCeti.IsWeakCRSolution q Ω J DJ S ξ η` with `p⁻¹ + q⁻¹ ≤ 1` (allowing `q = ∞`).

This file proves the divergence-form Laplace reduction
(`TauCeti.IsSobolevCRCoefficients.integral_laplacian_smul_eq`, the analytic core of
McDuff–Salamon Lemma B.4.6): `ξ` weakly solves `Δξ = ∂_s f + ∂_t g` on `Ω` with
`f = η + (∂_t J) ξ - S ξ` and `g = -J f - (∂_s J) ξ - (∂_t J)(J ξ)`. Because `J` is only
`W^{1,p}_loc`, `Jᵀ ∂_t φ` is not a test function; the proof mollifies `J` on a relatively compact
subdomain so that `J_n → J` uniformly on `tsupport φ` while `DJ_n → DJ` in `Lᵖ`, tests the weak
equation against `J_nᵀ ∂_t(φ • w)`, and passes to the limit.

## Main declarations

* `TauCeti.MemLpLoc.clm_apply_of_inv_add_inv_le` and `TauCeti.MemLpLoc.continuousOn_clm_apply`:
  Hölder and continuous-operator bounds for pointwise evaluation of operator fields on `MemLpLoc`.
* `TauCeti.IsSobolevCRCoefficients.integral_laplacian_smul_eq`: the weak divergence-form Laplace
  identity `Δξ = ∂_s f + ∂_t g`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4 (Lemma B.4.6).
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
theorem MemLpLoc.clm_apply_of_inv_add_inv_le {A : ℂ → F →L[ℝ] G} {w : ℂ → F}
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

/-- Applying an operator field continuous on `U` to a locally `L^q` vector field preserves local
`L^q` membership on `U`. -/
theorem MemLpLoc.continuousOn_clm_apply {A : ℂ → F →L[ℝ] G} {w : ℂ → F}
    (hw : MemLpLoc q U w) (hA : ContinuousOn A U) : MemLpLoc q U (fun z => A z (w z)) :=
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
    Θ.integrable_inner ((hu1.continuousOn_clm_apply hB).locallyIntegrableOn le_rfl hloc)
  have hintA (n : ℕ) : Integrable (fun z => ⟪(Θ : ℂ → V) z, A n z (u z)⟫_ℝ) :=
    Θ.integrable_inner
      ((hu1.continuousOn_clm_apply (hA n).continuousOn).locallyIntegrableOn le_rfl hloc)
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
  refine Θ.tendsto_integral_inner_of_tendsto_lintegral_enorm_sub hΘW (.of_forall hint_n)
    hint_lim.aestronglyMeasurable
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
  have hJξ : MemLpLoc q Ω (fun z => J z (ξ z)) := hsol.memLpLoc.continuousOn_clm_apply hJcont
  have hf : LocallyIntegrableOn (fun z => η z + DJ z I (ξ z) - S z (ξ z)) Ω volume :=
    (hsol.locallyIntegrableOn.add
      (hDJI.locallyIntegrableOn_clm_apply hsol.memLpLoc hpq hloc)).sub
      (hc.memLpLoc_zeroth.locallyIntegrableOn_clm_apply hsol.memLpLoc hpq hloc)
  have hf1 : MemLpLoc 1 Ω (fun z => η z + DJ z I (ξ z) - S z (ξ z)) :=
    (memLpLoc_one_iff_locallyIntegrableOn hloc).2 hf
  have hJf : LocallyIntegrableOn (fun z => J z (η z + DJ z I (ξ z) - S z (ξ z))) Ω volume :=
    (hf1.continuousOn_clm_apply hJcont).locallyIntegrableOn le_rfl hloc
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
  have hJξloc := (hsol.memLpLoc.continuousOn_clm_apply hJcont).locallyIntegrableOn hq1 hloc
  have hi (Θ : 𝓓(Ω, V)) {A : ℂ → V →L[ℝ] V} (hA : Continuous A) {w : ℂ → V}
      (hw : LocallyIntegrableOn w Ω volume) :
      Integrable (fun z => ⟪(Θ : ℂ → V) z, A z (w z)⟫_ℝ) :=
    Θ.integrable_inner ((((memLpLoc_one_iff_locallyIntegrableOn hloc).2
      hw).continuousOn_clm_apply hA.continuousOn).locallyIntegrableOn le_rfl hloc)
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
      hw).continuousOn_clm_apply hJcont).locallyIntegrableOn le_rfl hloc)
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
  have hJξ : MemLpLoc q Ω (fun z => J z (ξ z)) := hsol.memLpLoc.continuousOn_clm_apply hJcont
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
  have iDJ : Integrable (fun z => ⟪(Ψ₁ : ℂ → V) z, DJ z I (ξ z)⟫_ℝ) :=
    Ψ₁.integrable_inner hDJI_loc
  have iS : Integrable (fun z => ⟪(Ψ₁ : ℂ → V) z, S z (ξ z)⟫_ℝ) :=
    Ψ₁.integrable_inner hS_loc
  have iη : Integrable (fun z => ⟪(Ψ₁ : ℂ → V) z, η z⟫_ℝ) :=
    Ψ₁.integrable_inner hsol.locallyIntegrableOn
  have h1 := hsol.integral_inner_crFormalAdjoint Ψ₁
  rw [hc.integral_inner_crFormalAdjoint_eq_terms hpq hsol.memLpLoc Ψ₁] at h1
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

end TauCeti
