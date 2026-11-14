/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Differentiated
public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.OrderZero
public import TauCeti.Analysis.Sobolev.Local.Morrey.Higher
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Thickening
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.TargetChange
import TauCeti.Analysis.Distribution.TestFunction.Inner
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Normed.Operator.Basic
import TauCeti.Analysis.Sobolev.Local.Coordinates
import TauCeti.Analysis.Sobolev.Local.Multiplication.Higher
import TauCeti.Analysis.Sobolev.Mollification.Interior
import TauCeti.Analysis.Sobolev.WeakDeriv.Bilinear.Holder
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
import TauCeti.MeasureTheory.Function.Lp.Holder

/-!
# Higher-order interior regularity for Cauchy–Riemann operators with Sobolev coefficients

Let `Ω ⊆ ℂ` be open, write `z = s + i t`, and let `V` be a finite-dimensional real inner product
space. Consider the real linear Cauchy–Riemann operator

`D ξ = ∂_s ξ + J ∂_t ξ + S ξ`

with Sobolev coefficients `J ∈ W^{max 1 k, p}_loc(Ω; V →L[ℝ] V)` satisfying `J² = -1` almost
everywhere on `Ω` and `S ∈ W^{k,p}_loc(Ω; V →L[ℝ] V)` for `2 < p < ∞`.

Building on the order-zero regularity theorem `TauCeti.IsWeakCRSolution.memWkpLoc_one` of
`TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.OrderZero`, this file proves higher-order
interior regularity (McDuff–Salamon, Proposition B.4.9):

1. **The weak differentiated system** (`TauCeti.isWeakCRSolution_differentiated`). When `ξ` and
   `η` lie only in `W^{1,q}_loc(Ω)` with `2 < p`, `1 < q ≤ p`, `p⁻¹ + q⁻¹ ≤ 1`, and
   `∂_s ξ + J ∂_t ξ + S ξ = η` almost everywhere on `Ω`, the pair `Ξ = (∂_s ξ, ∂_t ξ)` valued in
   `WithLp 2 (V × V)` is a *weak* solution (`TauCeti.IsWeakCRSolution`) of
   `∂_s Ξ + diag(J, J) ∂_t Ξ + S₂ Ξ = (∂_s η - (∂_s S) ξ, ∂_t η - (∂_t S) ξ)` with
   `S₂ = TauCeti.differentiatedCRCoefficient S DJ`. Neither second weak derivatives of `ξ` nor
   second weak derivatives of `J` are assumed: the `∂_s` row uses a distributional commutator
   identity established by interior mollification of `ξ`.
2. **Higher-order interior regularity** (`TauCeti.IsWeakCRSolution.memWkpLoc_succ`). By induction
   on `k`, if `2 < p`, `1 < q ≤ p`, `(p : ℝ≥0∞)⁻¹ + (q : ℝ≥0∞)⁻¹ < 1`, `J ∈ W^{max 1 k, p}_loc(Ω)`
   with `J² = -1` almost everywhere, `S ∈ W^{k,p}_loc(Ω)`, and `η ∈ W^{k,q}_loc(Ω)`, then every
   weak solution `ξ ∈ L^q_loc(Ω)` belongs to `W^{k+1,q}_loc(Ω)`.
3. **Regularity on general finite-dimensional normed spaces**
   (`TauCeti.IsWeakLinearCauchyRiemannOn.memWkpLoc_succ_of_memWkpLoc`,
   `TauCeti.IsWeakLinearCauchyRiemannOn.contDiffOn`, and
   `TauCeti.IsWeakLinearCauchyRiemannOn.contDiffOn_top`). Transporting along a continuous linear
   equivalence to Euclidean space removes the inner-product structure from the hypotheses for
   `TauCeti.IsWeakLinearCauchyRiemannOn`.

## Main declarations

* `TauCeti.isWeakCRSolution_differentiated`: `Ξ = (∂_s ξ, ∂_t ξ)` weakly solves the differentiated
  Cauchy–Riemann system when `ξ ∈ W^{1,q}_loc(Ω)`.
* `TauCeti.IsWeakCRSolution.memWkpLoc_succ`: McDuff–Salamon Proposition B.4.9 (`ξ ∈ W^{k+1,q}_loc`).
* `TauCeti.IsWeakCRSolution.memWkpLoc_succ_of_memWkpLoc` and
  `TauCeti.IsWeakCRSolution.memWkpLoc_succ_self`: exponent-raising forms when `η ∈ W^{k,r}_loc` or
  `η ∈ W^{k,p}_loc` and `(p : ℝ≥0∞)⁻¹ + q⁻¹ < 1`.
* `TauCeti.IsWeakCRSolution.exists_contDiffOn_ae_eq`: `C^k` representative almost everywhere on `Ω`.
* `TauCeti.IsWeakLinearCauchyRiemannOn.memWkpLoc_succ_of_memWkpLoc`,
  `TauCeti.IsWeakLinearCauchyRiemannOn.contDiffOn`, and
  `TauCeti.IsWeakLinearCauchyRiemannOn.contDiffOn_top`: `W^{k+1,p}_loc`, `C^k`, and `C^∞`
  regularity of continuous weak linear Cauchy–Riemann solutions valued in any finite-dimensional
  real normed space.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4 (Proposition B.4.9).
-/

public noncomputable section

open Complex Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Convolution Distributions ENNReal InnerProductSpace LineDeriv NNReal Topology

namespace TauCeti

/-! ### Weak differentiated system -/

section WeakDifferentiated

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {Ω : Opens ℂ}

private local instance : NormedAddCommGroup (V →L[ℝ] V) := inferInstance
private local instance : NormedSpace ℝ (V →L[ℝ] V) := inferInstance
private local instance : NormedAddCommGroup (ℂ →L[ℝ] V) := inferInstance
private local instance : NormedSpace ℝ (ℂ →L[ℝ] V) := inferInstance
private local instance : NormedAddCommGroup (V × V →L[ℝ] V × V) := inferInstance
private local instance : NormedSpace ℝ (V × V →L[ℝ] V × V) := inferInstance
private local instance :
    NormedAddCommGroup (WithLp 2 (V × V) →L[ℝ] WithLp 2 (V × V)) := inferInstance
private local instance :
    NormedSpace ℝ (WithLp 2 (V × V) →L[ℝ] WithLp 2 (V × V)) := inferInstance

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
  · simp [indicator_of_notMem hzW,
      image_eq_zero_of_notMem_tsupport fun h => hzW (hΘW h)]

/-- Pairing a test function supported in `W` against `A z (((ρ_n ⋆ 1_W D) z) v)` passes to the
limit when `A ∈ Lᵖ(W)` and `D ∈ L^q(W)` with `q < ∞` and `p⁻¹ + q⁻¹ ≤ 1`. -/
private theorem tendsto_integral_inner_clm_convolution {p q : ℝ≥0∞} (hq : q ≠ ⊤)
    (hpq : p⁻¹ + q⁻¹ ≤ 1) {W : Opens ℂ} (hWc : IsCompact (closure (W : Set ℂ))) (Θ : 𝓓(Ω, V))
    (hΘW : tsupport (Θ : ℂ → V) ⊆ W) {A : ℂ → V →L[ℝ] V}
    (hA : MemLp A p (volume.restrict W)) {D : ℂ → ℂ →L[ℝ] V}
    (hD : MemLp D q (volume.restrict W)) (v : ℂ) {ρ : ℕ → ContDiffBump (0 : ℂ)}
    (hρ : Tendsto (fun n => (ρ n).rOut) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z, ⟪(Θ : ℂ → V) z,
        A z (((ρ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          (W : Set ℂ).indicator D) z v)⟫_ℝ)
      atTop (𝓝 (∫ z, ⟪(Θ : ℂ → V) z, A z (D z v)⟫_ℝ)) := by
  have : Fact (1 ≤ p) := ⟨ENNReal.inv_le_one.1 (le_self_add.trans hpq)⟩
  have : Fact (1 ≤ q) := ⟨ENNReal.inv_le_one.1 (le_add_self.trans hpq)⟩
  set r := (p⁻¹ + q⁻¹)⁻¹
  have : Fact (1 ≤ r) := ⟨ENNReal.one_le_inv.2 hpq⟩
  have : ENNReal.HolderTriple p q r := ⟨(inv_inv _).symm⟩
  have : ENNReal.HolderTriple p ⊤ p := ⟨by simp⟩
  have hWm := W.isOpen.measurableSet.nullMeasurableSet (μ := volume)
  have hAext : MemLp ((W : Set ℂ).indicator A) p volume := (memLp_indicator_iff_restrict hWm).2 hA
  have hDext : MemLp ((W : Set ℂ).indicator D) q volume := (memLp_indicator_iff_restrict hWm).2 hD
  have hWfin : volume (W : Set ℂ) < ⊤ := (measure_mono subset_closure).trans_lt hWc.measure_lt_top
  let B : (V →L[ℝ] V) →L[ℝ] (ℂ →L[ℝ] V) →L[ℝ] V :=
    ((ContinuousLinearMap.compL ℝ (ℂ →L[ℝ] V) (ℂ →L[ℝ] V) V)
      (ContinuousLinearMap.apply ℝ V v)).comp (ContinuousLinearMap.compL ℝ ℂ V V)
  have hB (L : V →L[ℝ] V) (M : ℂ →L[ℝ] V) : B L M = L (M v) := by simp [B]
  have hL1 := tendsto_setLIntegral_enorm_bilin_sub (r := r) B hWfin
    tendsto_const_nhds (tendsto_normedBumpLp hq hρ (hDext.toLp _))
    (fun _ => hAext.coeFn_toLp)
    (hAext.coeFn_toLp_indicator_restrict W.isOpen.measurableSet subset_rfl)
    (fun n => normedBumpLp_ae_eq_convolution hq (ρ n) hDext)
    (hDext.coeFn_toLp_indicator_restrict W.isOpen.measurableSet subset_rfl)
  let ΘW : 𝓓(W, V) := ⟨Θ, Θ.contDiff, Θ.hasCompactSupport, hΘW⟩
  have : IsFiniteMeasure (volume.restrict (W : Set ℂ)) := isFiniteMeasure_restrict.2 hWfin.ne
  have hint_lim : Integrable (fun z => ⟪(Θ : ℂ → V) z, A z (D z v)⟫_ℝ) := by
    simpa [ΘW, hB] using ΘW.integrable_inner (IntegrableOn.locallyIntegrableOn
      ((B.memLp_of_bilin r hA hD).integrable Fact.out))
  have hint_n (n : ℕ) : Integrable (fun z => ⟪(Θ : ℂ → V) z,
      A z (((ρ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (W : Set ℂ).indicator D) z v)⟫_ℝ) := by
    have hc := ((ρ n).hasCompactSupport_normed (μ := volume)).continuous_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ →L[ℝ] V))
      ((ρ n).continuous_normed (μ := volume)) (hDext.locallyIntegrable Fact.out)
    obtain ⟨C, hC⟩ := hWc.exists_bound_of_continuousOn hc.continuousOn
    have hmem := B.memLp_of_bilin p hA (memLp_top_of_bound hc.aestronglyMeasurable C
      ((ae_restrict_iff' W.isOpen.measurableSet).2
        (.of_forall fun z hz => hC z (subset_closure hz))))
    simpa [ΘW, hB] using ΘW.integrable_inner
      (IntegrableOn.locallyIntegrableOn (hmem.integrable Fact.out))
  refine tendsto_integral_inner_of_setLIntegral Θ hΘW hint_lim hint_n
    (hL1.congr fun n => setLIntegral_congr_fun W.isOpen.measurableSet fun z hz => ?_)
  rw [indicator_of_mem hz, hB, hB]

/-- Commutator identity for a smooth field `ψ` and a `W^{1,p}_loc` coefficient `J`: symmetry of the
second Fréchet derivative of `ψ` cancels the second-derivative terms in the weak Leibniz rules for
`∂_t(J ∂_s ψ)` and `∂_s(J ∂_t ψ)`. -/
private theorem integral_commutator_of_contDiff [FiniteDimensional ℝ V] {p q : ℝ≥0∞}
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hpq : p⁻¹ + q⁻¹ ≤ 1)
    {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V}
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (φ : 𝓓(Ω, V)) {ψ : ℂ → V}
    (hψ : ContDiff ℝ ∞ ψ) :
    -(∫ z, ⟪fderiv ℝ (φ : ℂ → V) z I, J z (fderiv ℝ ψ z 1)⟫_ℝ) -
        (∫ z, ⟪(φ : ℂ → V) z, DJ z I (fderiv ℝ ψ z 1)⟫_ℝ) +
        ∫ z, ⟪(φ : ℂ → V) z, DJ z 1 (fderiv ℝ ψ z I)⟫_ℝ =
      -(∫ z, ⟪fderiv ℝ (φ : ℂ → V) z 1, J z (fderiv ℝ ψ z I)⟫_ℝ) := by
  have : Fact (1 ≤ p) := ⟨ENNReal.inv_le_one.1 (le_self_add.trans hpq)⟩
  have : Fact (1 ≤ q) := ⟨ENNReal.inv_le_one.1 (le_add_self.trans hpq)⟩
  have : Fact (1 ≤ (p⁻¹ + q⁻¹)⁻¹) := ⟨ENNReal.one_le_inv.2 hpq⟩
  have : ENNReal.HolderTriple p q (p⁻¹ + q⁻¹)⁻¹ := ⟨(inv_inv _).symm⟩
  let u : ℂ → ℂ → V := fun v z => fderiv ℝ ψ z v
  have hu_smooth (v : ℂ) : ContDiff ℝ ∞ (u v) :=
    (hψ.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  have hu_weak (v : ℂ) : HasWeakFDerivOn volume Ω (u v) (fderiv ℝ (u v)) :=
    ((hu_smooth v).contDiffOn.of_le (by simp)).hasWeakFDerivOn_fderiv
  have hu_q (v : ℂ) : MemLpLoc q Ω (u v) := (hu_smooth v).continuous.continuousOn.memLpLoc
  have hdu_q (v w : ℂ) : MemLpLoc q Ω (fun z => fderiv ℝ (u v) z w) :=
    (((hu_smooth v).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply
      contDiff_const).continuous.continuousOn.memLpLoc
  have hDJw (w : ℂ) : MemLpLoc p Ω (fun z => DJ z w) :=
    hc.memLpLoc_deriv.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) w)
  have hJu (v w : ℂ) : HasWeakLineDerivOn volume Ω (fun z => J z (u v z))
      (fun z => DJ z w (u v z) + J z (fderiv ℝ (u v) z w)) w := by
    simpa using (hc.hasWeakFDerivOn.hasWeakLineDerivOn w).bilin_of_memLp
      (ContinuousLinearMap.id ℝ (V →L[ℝ] V)) hp hp hq hq hpq hpq hpq
      ((hu_weak v).hasWeakLineDerivOn w)
      (fun K hK hKΩ => memLpLoc_iff.1 hc.memLpLoc_coeff K hKΩ hK)
      (fun K hK hKΩ => memLpLoc_iff.1 (hDJw w) K hKΩ hK)
      (fun K hK hKΩ => memLpLoc_iff.1 (hu_q v) K hKΩ hK)
      (fun K hK hKΩ => memLpLoc_iff.1 (hdu_q v w) K hKΩ hK)
  have hloc := Ω.isOpen.isLocallyClosed
  have hibp (v w : ℂ) : ∫ z, ⟪fderiv ℝ (φ : ℂ → V) z w, J z (u v z)⟫_ℝ =
      -((∫ z, ⟪(φ : ℂ → V) z, DJ z w (u v z)⟫_ℝ) +
        ∫ z, ⟪(φ : ℂ → V) z, J z (fderiv ℝ (u v) z w)⟫_ℝ) := by
    have h := (hJu v w).integral_inner_lineDeriv_eq_neg φ
    simp only [TestFunction.lineDeriv_eq_fderiv, inner_add_right] at h
    exact h.trans (congrArg Neg.neg (integral_add
      (φ.integrable_inner ((hDJw w).locallyIntegrableOn_clm_apply (hu_q v) hpq hloc))
      (φ.integrable_inner (hc.memLpLoc_coeff.locallyIntegrableOn_clm_apply (hdu_q v w) hpq hloc))))
  have hsymm (z : ℂ) : fderiv ℝ (u 1) z I = fderiv ℝ (u I) z 1 := by
    have hd : DifferentiableAt ℝ (fderiv ℝ ψ) z :=
      (hψ.fderiv_right (m := 1) (by simp)).differentiable one_ne_zero z
    simpa [u, fderiv_clm_apply hd (differentiableAt_const _)] using
      ((hψ.contDiffAt (x := z)).isSymmSndFDerivAt (by simp)).eq I 1
  have h1 := hibp 1 I
  have h2 := hibp I 1
  simp_rw [hsymm] at h1
  linarith

omit [CompleteSpace V] in
/-- On the support of `Θ`, if every `ρ.rOut`-ball around `tsupport Θ` lies in `W ⊆ Ω`, the Fréchet
derivative of `ρ.normed ⋆ 1_W ξ` agrees with `ρ.normed ⋆ 1_W Dξ`, so their inner-product pairings
against `z ↦ A z (· v)` are equal. -/
private theorem integral_inner_clm_mollified_fderiv_eq {q : ℝ≥0∞} (hq1 : 1 ≤ q)
    {W : Opens ℂ} (hWΩ : closure (W : Set ℂ) ⊆ Ω) {ξ : ℂ → V} {Dξ : ℂ → ℂ →L[ℝ] V}
    (hDξ : HasWeakFDerivOn volume Ω ξ Dξ)
    (hξW : MemLp ξ q (volume.restrict W)) (hDξW : MemLp Dξ q (volume.restrict W))
    (ρ : ContDiffBump (0 : ℂ)) (Θ : 𝓓(Ω, V))
    (hball : ∀ z ∈ tsupport (Θ : ℂ → V), closedBall z ρ.rOut ⊆ W)
    (A : ℂ → V →L[ℝ] V) (v : ℂ) :
    (∫ z, ⟪(Θ : ℂ → V) z, A z (fderiv ℝ
        (ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (W : Set ℂ).indicator ξ)
        z v)⟫_ℝ) =
      ∫ z, ⟪(Θ : ℂ → V) z, A z
        ((ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (W : Set ℂ).indicator Dξ)
          z v)⟫_ℝ := by
  refine integral_congr_ae (.of_forall fun z => ?_)
  dsimp only
  by_cases hz : z ∈ tsupport (Θ : ℂ → V)
  · have hd := (hDξ.mono (subset_closure.trans hWΩ)).fderiv_indicator_convolution_normed
      hξW hDξW hq1 hq1 ρ z (hball z hz)
    have hd' : fderiv ℝ (ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (W : Set ℂ).indicator ξ) z =
      (ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (W : Set ℂ).indicator Dξ) z := by
      simpa only [convolution_flip] using hd
    rw [hd']
  · simp [image_eq_zero_of_notMem_tsupport hz]

/-- Constructs a sequence of bump radii `ρ n → 0` whose closed balls around points of a compact set
`K ⊆ W` remain inside `W`. -/
private theorem exists_mollifier_radii {W : Opens ℂ} {K : Set ℂ}
    (hK : IsCompact K) (hKW : K ⊆ W) :
    ∃ ρ : ℕ → ContDiffBump (0 : ℂ), Tendsto (fun n => (ρ n).rOut) atTop (𝓝 0) ∧
      ∀ n, ∀ z ∈ K, closedBall z (ρ n).rOut ⊆ W := by
  obtain ⟨δ, hδ, hδW⟩ := hK.exists_cthickening_subset_open W.isOpen hKW
  refine ⟨fun n => ⟨(δ / ((n : ℝ) + 2)) / 2, δ / ((n : ℝ) + 2),
      by positivity, half_lt_self (by positivity)⟩,
    (tendsto_const_nhds (x := δ)).div_atTop
      (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop), fun n z hz => ?_⟩
  exact (closedBall_subset_closedBall (div_lt_self hδ
    (by linarith [Nat.cast_nonneg (α := ℝ) n])).le).trans
      ((closedBall_subset_cthickening hz δ).trans hδW)

/-- Distributional commutator identity for `J ∈ W^{1,p}_loc(Ω)` and `ξ ∈ W^{1,q}_loc(Ω)` when
`p⁻¹ + q⁻¹ ≤ 1`, proved by interior mollification of `ξ` on a precompact open neighbourhood of
`tsupport φ`. -/
private theorem integral_commutator_of_hasWeakFDerivOn [FiniteDimensional ℝ V] {p q : ℝ≥0∞}
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hpq : p⁻¹ + q⁻¹ ≤ 1)
    {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ : ℂ → V} {Dξ : ℂ → ℂ →L[ℝ] V}
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hDξ : HasWeakFDerivOn volume Ω ξ Dξ)
    (hξq : MemLpLoc q Ω ξ) (hDξq : MemLpLoc q Ω Dξ) (φ : 𝓓(Ω, V)) :
    -(∫ z, ⟪fderiv ℝ (φ : ℂ → V) z I, J z (Dξ z 1)⟫_ℝ) -
        (∫ z, ⟪(φ : ℂ → V) z, DJ z I (Dξ z 1)⟫_ℝ) +
        ∫ z, ⟪(φ : ℂ → V) z, DJ z 1 (Dξ z I)⟫_ℝ =
      -(∫ z, ⟪fderiv ℝ (φ : ℂ → V) z 1, J z (Dξ z I)⟫_ℝ) := by
  have hq1 : 1 ≤ q := ENNReal.inv_le_one.1 (le_add_self.trans hpq)
  obtain ⟨W, hφW, hWΩ, hWc⟩ :=
    Opens.exists_between_and_isCompact_closure φ.hasCompactSupport φ.tsupport_subset
  obtain ⟨ρ, hρ0, hball⟩ := exists_mollifier_radii φ.hasCompactSupport hφW
  have hμW : volume.restrict (W : Set ℂ) ≤ volume.restrict (closure (W : Set ℂ)) :=
    Measure.restrict_mono subset_closure le_rfl
  have hξW : MemLp ξ q (volume.restrict W) := (memLpLoc_iff.1 hξq _ hWΩ hWc).mono_measure hμW
  have hDξW : MemLp Dξ q (volume.restrict W) := (memLpLoc_iff.1 hDξq _ hWΩ hWc).mono_measure hμW
  have hJW : MemLp J p (volume.restrict W) :=
    (memLpLoc_iff.1 hc.memLpLoc_coeff _ hWΩ hWc).mono_measure hμW
  have hDJW (w : ℂ) : MemLp (fun z => DJ z w) p (volume.restrict W) :=
    ((memLpLoc_iff.1 hc.memLpLoc_deriv _ hWΩ hWc).mono_measure hμW).continuousLinearMap_comp
      (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) w)
  have hξext : MemLp ((W : Set ℂ).indicator ξ) q volume :=
    (memLp_indicator_iff_restrict W.isOpen.measurableSet.nullMeasurableSet).2 hξW
  let Dψ (n : ℕ) : ℂ → ℂ →L[ℝ] V :=
    (ρ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (W : Set ℂ).indicator Dξ
  have hid (n : ℕ) : -(∫ z, ⟪(∂_{I} φ : 𝓓(Ω, V)) z, J z (Dψ n z 1)⟫_ℝ) -
      (∫ z, ⟪(φ : ℂ → V) z, DJ z I (Dψ n z 1)⟫_ℝ) +
      (∫ z, ⟪(φ : ℂ → V) z, DJ z 1 (Dψ n z I)⟫_ℝ) =
      -(∫ z, ⟪(∂_{(1 : ℂ)} φ : 𝓓(Ω, V)) z, J z (Dψ n z I)⟫_ℝ) := by
    have hψ_smooth : ContDiff ℝ ∞
        ((ρ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (W : Set ℂ).indicator ξ) :=
      ((ρ n).hasCompactSupport_normed (μ := volume)).contDiff_convolution_left
        (ContinuousLinearMap.lsmul ℝ ℝ) ((ρ n).contDiff_normed (μ := volume))
        (hξext.locallyIntegrable hq1)
    have hc_n := integral_commutator_of_contDiff hp hq hpq hc φ hψ_smooth
    simp_rw [← TestFunction.lineDerivOp_apply_eq_fderiv] at hc_n
    rwa [integral_inner_clm_mollified_fderiv_eq hq1 hWΩ hDξ hξW hDξW (ρ n) (∂_{I} φ)
        (fun z hz => hball n z (φ.tsupport_lineDerivOp_subset I hz)) J 1,
      integral_inner_clm_mollified_fderiv_eq hq1 hWΩ hDξ hξW hDξW (ρ n) φ (hball n)
        (fun z => DJ z I) 1,
      integral_inner_clm_mollified_fderiv_eq hq1 hWΩ hDξ hξW hDξW (ρ n) φ (hball n)
        (fun z => DJ z 1) I,
      integral_inner_clm_mollified_fderiv_eq hq1 hWΩ hDξ hξW hDξW (ρ n) (∂_{(1 : ℂ)} φ)
        (fun z hz => hball n z (φ.tsupport_lineDerivOp_subset 1 hz)) J I] at hc_n
  have ht1 := tendsto_integral_inner_clm_convolution hq hpq hWc (∂_{I} φ)
    ((φ.tsupport_lineDerivOp_subset I).trans hφW) hJW hDξW 1 hρ0
  have ht2 := tendsto_integral_inner_clm_convolution hq hpq hWc φ hφW (hDJW I) hDξW 1 hρ0
  have ht3 := tendsto_integral_inner_clm_convolution hq hpq hWc φ hφW (hDJW 1) hDξW I hρ0
  have ht4 := tendsto_integral_inner_clm_convolution hq hpq hWc (∂_{(1 : ℂ)} φ)
    ((φ.tsupport_lineDerivOp_subset 1).trans hφW) hJW hDξW I hρ0
  simpa only [TestFunction.lineDerivOp_apply_eq_fderiv] using
    tendsto_nhds_unique ((ht1.neg.sub ht2).add ht3) (ht4.neg.congr fun n => (hid n).symm)

/-- Common weak directional differentiation of `∂_s ξ + J ∂_t ξ + S ξ = η` along `v ∈ ℂ` against a
test function `θ ∈ 𝓓(Ω, V)`. -/
private theorem integral_lineDeriv_crEquation [FiniteDimensional ℝ V] {p q : ℝ≥0} (hp : 2 < p)
    (hq : 1 < q) (hqp : q ≤ p) (hpq : (p : ℝ≥0∞)⁻¹ + (q : ℝ≥0∞)⁻¹ ≤ 1)
    {J S : ℂ → V →L[ℝ] V} {DJ DS : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}
    {Dξ Dη : ℂ → ℂ →L[ℝ] V} (hc : IsSobolevCRCoefficients p Ω J DJ S)
    (hS : MemWkpLoc p Ω 1 S) (hDS : HasWeakFDerivOn volume Ω S DS)
    (hξ : MemWkpLoc q Ω 1 ξ) (hDξ : HasWeakFDerivOn volume Ω ξ Dξ)
    (hη : MemWkpLoc q Ω 1 η) (hDη : HasWeakFDerivOn volume Ω η Dη)
    (heq : ∀ᵐ z ∂volume.restrict Ω, Dξ z 1 + J z (Dξ z I) + S z (ξ z) = η z)
    (v : ℂ) (θ : 𝓓(Ω, V)) :
    -(∫ z, ⟪fderiv ℝ (θ : ℂ → V) z v, Dξ z 1⟫_ℝ) -
        (∫ z, ⟪fderiv ℝ (θ : ℂ → V) z v, J z (Dξ z I)⟫_ℝ) +
        ∫ z, ⟪(θ : ℂ → V) z, S z (Dξ z v)⟫_ℝ =
      ∫ z, ⟪(θ : ℂ → V) z, Dη z v - DS z v (ξ z)⟫_ℝ := by
  have : Fact (1 ≤ (p : ℝ≥0∞)) := ⟨by exact_mod_cast hq.le.trans hqp⟩
  have hq1 : (1 : ℝ≥0∞) ≤ q := by exact_mod_cast hq.le
  have : Fact (1 ≤ (q : ℝ≥0∞)) := ⟨hq1⟩
  have hloc := Ω.isOpen.isLocallyClosed
  have hDξq : MemLpLoc q Ω Dξ := memWkpLoc_zero_iff.1 (hξ.memWkpLoc_of_hasWeakFDerivOn hDξ)
  have hDSp : MemLpLoc p Ω DS := memWkpLoc_zero_iff.1 (hS.memWkpLoc_of_hasWeakFDerivOn hDS)
  have hDηq : MemLpLoc q Ω Dη := memWkpLoc_zero_iff.1 (hη.memWkpLoc_of_hasWeakFDerivOn hDη)
  have hSξ : HasWeakLineDerivOn volume Ω (fun z => S z (ξ z))
      (fun z => DS z v (ξ z) + S z (Dξ z v)) v := by
    simpa using (hDS.bilin_of_memLpLoc (ContinuousLinearMap.id ℝ (V →L[ℝ] V)) hp hq hqp
      ((hS.memLpLoc_of_holderTriple hp le_rfl).mono_exponent le_top)
      hDSp hDξ hξ.memLpLoc hDξq).hasWeakLineDerivOn v
  have iD1 : Integrable (fun z => ⟪fderiv ℝ (θ : ℂ → V) z v, Dξ z 1⟫_ℝ) := by
    simpa using θ.integrable_inner_fderiv
      ((hDξq.clm_comp (ContinuousLinearMap.apply ℝ V 1)).locallyIntegrableOn hq1 hloc) v
  have iJD : Integrable (fun z => ⟪fderiv ℝ (θ : ℂ → V) z v, J z (Dξ z I)⟫_ℝ) := by
    simpa using θ.integrable_inner_fderiv (hc.memLpLoc_coeff.locallyIntegrableOn_clm_apply
      (hDξq.clm_comp (ContinuousLinearMap.apply ℝ V I)) hpq hloc) v
  have iSξ := θ.integrable_inner_fderiv
    (hc.memLpLoc_zeroth.locallyIntegrableOn_clm_apply hξ.memLpLoc hpq hloc) v
  have iDSξ : Integrable (fun z => ⟪(θ : ℂ → V) z, DS z v (ξ z)⟫_ℝ) := by
    simpa using θ.integrable_inner ((MemLpLoc.bilin_of_memWkpLoc
      (ContinuousLinearMap.id ℝ (V →L[ℝ] V)) hp hqp
      (hDSp.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) v)) hξ).locallyIntegrableOn hq1 hloc)
  have iSD : Integrable (fun z => ⟪(θ : ℂ → V) z, S z (Dξ z v)⟫_ℝ) := by
    simpa using θ.integrable_inner (hc.memLpLoc_zeroth.locallyIntegrableOn_clm_apply
      (hDξq.clm_comp (ContinuousLinearMap.apply ℝ V v)) hpq hloc)
  have iDη : Integrable (fun z => ⟪(θ : ℂ → V) z, Dη z v⟫_ℝ) := by
    simpa using θ.integrable_inner
      ((hDηq.clm_comp (ContinuousLinearMap.apply ℝ V v)).locallyIntegrableOn hq1 hloc)
  have hpde : (∫ z, ⟪fderiv ℝ (θ : ℂ → V) z v, Dξ z 1⟫_ℝ) +
      (∫ z, ⟪fderiv ℝ (θ : ℂ → V) z v, J z (Dξ z I)⟫_ℝ) +
      (∫ z, ⟪fderiv ℝ (θ : ℂ → V) z v, S z (ξ z)⟫_ℝ) =
      ∫ z, ⟪fderiv ℝ (θ : ℂ → V) z v, η z⟫_ℝ := by
    rw [← integral_add iD1 iJD]
    refine (integral_add (iD1.add iJD) iSξ).symm.trans
      (integral_congr_ae ((ae_imp_of_ae_restrict heq).mono fun z hz => ?_))
    by_cases hzΩ : z ∈ (Ω : Set ℂ)
    · simp only [Pi.add_apply, ← inner_add_right, hz hzΩ]
    · simp [fderiv_of_notMem_tsupport ℝ fun h => hzΩ (θ.tsupport_subset h)]
  have hS_ibp := hSξ.integral_inner_lineDeriv_eq_neg θ
  simp only [TestFunction.lineDeriv_eq_fderiv, inner_add_right, integral_add iDSξ iSD] at hS_ibp
  have hη_ibp := (hDη.hasWeakLineDerivOn v).integral_inner_lineDeriv_eq_neg θ
  simp only [TestFunction.lineDeriv_eq_fderiv] at hη_ibp
  simp_rw [inner_sub_right, integral_sub iDη iDSξ]
  linarith

/-- Continuous linear map sending `A : W →L[ℝ] W` to `diag(A, A)` on `WithLp 2 (W × W)`. -/
private def diagWithLpCLM (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℝ W] :
    (W →L[ℝ] W) →L[ℝ] WithLp 2 (W × W) →L[ℝ] WithLp 2 (W × W) :=
  let e := (WithLp.prodContinuousLinearEquiv 2 ℝ W W).symm
  (e.arrowCongr e).toContinuousLinearMap.comp
    ((ContinuousLinearMap.prodMapL ℝ W W W W).comp
      ((ContinuousLinearMap.id ℝ (W →L[ℝ] W)).prod (ContinuousLinearMap.id ℝ (W →L[ℝ] W))))

/-- Action of `diagWithLpCLM` as a block-diagonal operator on `WithLp 2 (W × W)`. -/
@[simp]
private theorem diagWithLpCLM_apply {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (A : W →L[ℝ] W) :
    diagWithLpCLM W A =
      (WithLp.prodContinuousLinearEquiv 2 ℝ W W).symm.arrowCongr
        (WithLp.prodContinuousLinearEquiv 2 ℝ W W).symm (A.prodMap A) := by
  simp [diagWithLpCLM]

/-- Pointwise decomposition of the formal adjoint pairing on `WithLp 2 (V × V)` into the two
coordinate test functions `φ₁ = fst ∘ Φ` and `φ₂ = snd ∘ Φ`. -/
private theorem inner_crFormalAdjoint_withLp_eq
    {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V}
    (Φ : 𝓓(Ω, WithLp 2 (V × V))) (z : ℂ) (u₁ u₂ : V) :
    let e := (WithLp.prodContinuousLinearEquiv 2 ℝ V V).symm
    let φ₁ : 𝓓(Ω, V) := TestFunction.postcompCLM (WithLp.fstL 2 ℝ V V) Φ
    let φ₂ : 𝓓(Ω, V) := TestFunction.postcompCLM (WithLp.sndL 2 ℝ V V) Φ
    ⟪crFormalAdjoint (fun w => diagWithLpCLM V (J w)) (fun w => (diagWithLpCLM V).comp (DJ w))
        (fun w => e.arrowCongr e (differentiatedCRCoefficient (S w) (DJ w))) Φ z,
        WithLp.toLp 2 (u₁, u₂)⟫_ℝ =
      (⟪crFormalAdjoint J DJ S φ₁ z, u₁⟫_ℝ + ⟪(φ₁ : ℂ → V) z, DJ z 1 u₂⟫_ℝ) +
        (⟪crFormalAdjoint J DJ S φ₂ z, u₂⟫_ℝ + ⟪(φ₂ : ℂ → V) z, DJ z I u₂⟫_ℝ) := by
  intro e φ₁ φ₂
  have hf1 (v : ℂ) : (fderiv ℝ (Φ : ℂ → WithLp 2 (V × V)) z v).fst =
      fderiv ℝ (φ₁ : ℂ → V) z v := by
    rw [← TestFunction.lineDerivOp_apply_eq_fderiv, ← TestFunction.lineDerivOp_apply_eq_fderiv]
    simpa [φ₁, TestFunction.lineDerivOp_eq_lineDerivCLM ℝ] using
      congr_fun (congrArg DFunLike.coe
        (TestFunction.lineDerivCLM_postcompCLM (n := ⊤) (k := ⊤) (WithLp.fstL 2 ℝ V V) v Φ)).symm z
  have hf2 (v : ℂ) : (fderiv ℝ (Φ : ℂ → WithLp 2 (V × V)) z v).snd =
      fderiv ℝ (φ₂ : ℂ → V) z v := by
    rw [← TestFunction.lineDerivOp_apply_eq_fderiv, ← TestFunction.lineDerivOp_apply_eq_fderiv]
    simpa [φ₂, TestFunction.lineDerivOp_eq_lineDerivCLM ℝ] using
      congr_fun (congrArg DFunLike.coe
        (TestFunction.lineDerivCLM_postcompCLM (n := ⊤) (k := ⊤) (WithLp.sndL 2 ℝ V V) v Φ)).symm z
  have hφ1 : ((Φ : ℂ → WithLp 2 (V × V)) z).fst = (φ₁ : ℂ → V) z := by simp [φ₁]
  have hφ2 : ((Φ : ℂ → WithLp 2 (V × V)) z).snd = (φ₂ : ℂ → V) z := by simp [φ₂]
  rw [inner_crFormalAdjoint, inner_crFormalAdjoint, inner_crFormalAdjoint]
  simp [e, ContinuousLinearMap.coe_prodMap', hf1 1, hf1 I, hf2 1, hf2 I, hφ1, hφ2, inner_add_right]
  ring

/-- Splits `∫ ⟪crFormalAdjoint J DJ S φ, u⟫` into its four additive terms under Sobolev
coefficients and `p⁻¹ + q⁻¹ ≤ 1`. -/
private theorem integral_inner_crFormalAdjoint_split {p q : ℝ≥0∞}
    {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {u : ℂ → V}
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hpq : p⁻¹ + q⁻¹ ≤ 1)
    (hu : MemLpLoc q Ω u) (φ : 𝓓(Ω, V)) :
    ∫ z, ⟪crFormalAdjoint J DJ S φ z, u z⟫_ℝ =
      -(∫ z, ⟪fderiv ℝ (φ : ℂ → V) z 1, u z⟫_ℝ) -
        (∫ z, ⟪fderiv ℝ (φ : ℂ → V) z I, J z (u z)⟫_ℝ) -
        (∫ z, ⟪(φ : ℂ → V) z, DJ z I (u z)⟫_ℝ) + ∫ z, ⟪(φ : ℂ → V) z, S z (u z)⟫_ℝ := by
  have hloc := Ω.isOpen.isLocallyClosed
  have hDJI := hc.memLpLoc_deriv.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) I)
  have h₁ := φ.integrable_inner_fderiv
    (hu.locallyIntegrableOn (ENNReal.inv_le_one.1 (le_add_self.trans hpq)) hloc) 1
  have h₂ := φ.integrable_inner_fderiv (hc.memLpLoc_coeff.locallyIntegrableOn_clm_apply hu hpq hloc)
    I
  have h₃ : Integrable (fun z => ⟪(φ : ℂ → V) z, DJ z I (u z)⟫_ℝ) :=
    φ.integrable_inner (hDJI.locallyIntegrableOn_clm_apply hu hpq hloc)
  have h₄ := φ.integrable_inner (hc.memLpLoc_zeroth.locallyIntegrableOn_clm_apply hu hpq hloc)
  simp only [inner_crFormalAdjoint]
  rw [integral_add _ h₄, integral_sub _ h₃, integral_sub _ h₂, integral_neg]
  exacts [h₁.neg, h₁.neg.sub h₂, (h₁.neg.sub h₂).sub h₃]

omit [CompleteSpace V] in
/-- Symmetry of mixed weak first derivatives against a test function:
`∫ ⟪∂_s φ, ∂_t ξ⟫ = ∫ ⟪∂_t φ, ∂_s ξ⟫`. -/
private theorem integral_inner_fderiv_comm_of_hasWeakFDerivOn [FiniteDimensional ℝ V]
    {ξ : ℂ → V} {Dξ : ℂ → ℂ →L[ℝ] V}
    (hDξ : HasWeakFDerivOn volume Ω ξ Dξ) (φ : 𝓓(Ω, V)) :
    ∫ z, ⟪fderiv ℝ (φ : ℂ → V) z 1, Dξ z I⟫_ℝ =
      ∫ z, ⟪fderiv ℝ (φ : ℂ → V) z I, Dξ z 1⟫_ℝ := by
  have a1 := (hDξ.hasWeakLineDerivOn I).integral_inner_lineDeriv_eq_neg (∂_{(1 : ℂ)} φ)
  have a2 := (hDξ.hasWeakLineDerivOn 1).integral_inner_lineDeriv_eq_neg (∂_{I} φ)
  simp_rw [TestFunction.lineDeriv_lineDerivOp_comm φ 1 I,
    TestFunction.lineDerivOp_apply_eq_fderiv] at a1
  simp_rw [TestFunction.lineDerivOp_apply_eq_fderiv] at a2
  linarith

/-- Evaluates `∫ ⟪crFormalAdjoint J₂ DJ₂ S₂ Φ, Ξ⟫` on `WithLp 2 (V × V)` by splitting into the
two coordinate rows and combining `integral_commutator_of_hasWeakFDerivOn` (row 1) and symmetry
of test-function directional derivatives (row 2) with `integral_lineDeriv_crEquation`. -/
private theorem integral_inner_crFormalAdjoint_differentiated_aux [FiniteDimensional ℝ V]
    {p q : ℝ≥0} (hp : 2 < p) (hq : 1 < q) (hqp : q ≤ p) (hpq : (p : ℝ≥0∞)⁻¹ + (q : ℝ≥0∞)⁻¹ ≤ 1)
    {J S : ℂ → V →L[ℝ] V} {DJ DS : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}
    {Dξ Dη : ℂ → ℂ →L[ℝ] V} (hc : IsSobolevCRCoefficients p Ω J DJ S)
    (hS : MemWkpLoc p Ω 1 S) (hDS : HasWeakFDerivOn volume Ω S DS)
    (hξ : MemWkpLoc q Ω 1 ξ) (hDξ : HasWeakFDerivOn volume Ω ξ Dξ)
    (hη : MemWkpLoc q Ω 1 η) (hDη : HasWeakFDerivOn volume Ω η Dη)
    (heq : ∀ᵐ z ∂volume.restrict Ω, Dξ z 1 + J z (Dξ z I) + S z (ξ z) = η z)
    (Φ : 𝓓(Ω, WithLp 2 (V × V))) :
    let e := (WithLp.prodContinuousLinearEquiv 2 ℝ V V).symm
    ∫ z, ⟪crFormalAdjoint (fun w => diagWithLpCLM V (J w))
        (fun w => (diagWithLpCLM V).comp (DJ w))
        (fun w => e.arrowCongr e (differentiatedCRCoefficient (S w) (DJ w))) Φ z,
        WithLp.toLp 2 (Dξ z 1, Dξ z I)⟫_ℝ =
      ∫ z, ⟪(Φ : ℂ → WithLp 2 (V × V)) z,
        WithLp.toLp 2 (Dη z 1 - DS z 1 (ξ z), Dη z I - DS z I (ξ z))⟫_ℝ := by
  intro e
  let φ₁ : 𝓓(Ω, V) := TestFunction.postcompCLM (WithLp.fstL 2 ℝ V V) Φ
  let φ₂ : 𝓓(Ω, V) := TestFunction.postcompCLM (WithLp.sndL 2 ℝ V V) Φ
  have hq1 : (1 : ℝ≥0∞) ≤ q := by exact_mod_cast hq.le
  have hloc := Ω.isOpen.isLocallyClosed
  have hDξq : MemLpLoc q Ω Dξ := memWkpLoc_zero_iff.1 (hξ.memWkpLoc_of_hasWeakFDerivOn hDξ)
  have hDξv (v : ℂ) : MemLpLoc q Ω (fun z => Dξ z v) :=
    hDξq.clm_comp (ContinuousLinearMap.apply ℝ V v)
  have iA (v : ℂ) (φ : 𝓓(Ω, V)) := hc.integrable_inner_crFormalAdjoint hpq (hDξv v) φ
  have iB (v : ℂ) (φ : 𝓓(Ω, V)) : Integrable (fun z => ⟪(φ : ℂ → V) z, DJ z v (Dξ z I)⟫_ℝ) :=
    φ.integrable_inner ((hc.memLpLoc_deriv.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) v)
      ).locallyIntegrableOn_clm_apply (hDξv I) hpq hloc)
  have hlhs : ∫ z, ⟪crFormalAdjoint (fun w => diagWithLpCLM V (J w))
        (fun w => (diagWithLpCLM V).comp (DJ w))
        (fun w => e.arrowCongr e (differentiatedCRCoefficient (S w) (DJ w))) Φ z,
        WithLp.toLp 2 (Dξ z 1, Dξ z I)⟫_ℝ =
      ((∫ z, ⟪crFormalAdjoint J DJ S φ₁ z, Dξ z 1⟫_ℝ) +
        ∫ z, ⟪(φ₁ : ℂ → V) z, DJ z 1 (Dξ z I)⟫_ℝ) +
      ((∫ z, ⟪crFormalAdjoint J DJ S φ₂ z, Dξ z I⟫_ℝ) +
        ∫ z, ⟪(φ₂ : ℂ → V) z, DJ z I (Dξ z I)⟫_ℝ) := by
    exact (integral_congr_ae (.of_forall fun z =>
      inner_crFormalAdjoint_withLp_eq Φ z (Dξ z 1) (Dξ z I))).trans
      ((integral_add ((iA 1 φ₁).add (iB 1 φ₁)) ((iA I φ₂).add (iB I φ₂))).trans
        (congrArg₂ (· + ·) (integral_add (iA 1 φ₁) (iB 1 φ₁))
          (integral_add (iA I φ₂) (iB I φ₂))))
  have hrow1 : (∫ z, ⟪crFormalAdjoint J DJ S φ₁ z, Dξ z 1⟫_ℝ) +
      (∫ z, ⟪(φ₁ : ℂ → V) z, DJ z 1 (Dξ z I)⟫_ℝ) =
      ∫ z, ⟪(φ₁ : ℂ → V) z, Dη z 1 - DS z 1 (ξ z)⟫_ℝ := by
    rw [integral_inner_crFormalAdjoint_split hc hpq (hDξv 1) φ₁]
    linarith [integral_commutator_of_hasWeakFDerivOn ENNReal.coe_ne_top ENNReal.coe_ne_top
        hpq hc hDξ hξ.memLpLoc hDξq φ₁,
      integral_lineDeriv_crEquation hp hq hqp hpq hc hS hDS hξ hDξ hη hDη heq 1 φ₁]
  have hrow2 : (∫ z, ⟪crFormalAdjoint J DJ S φ₂ z, Dξ z I⟫_ℝ) +
      (∫ z, ⟪(φ₂ : ℂ → V) z, DJ z I (Dξ z I)⟫_ℝ) =
      ∫ z, ⟪(φ₂ : ℂ → V) z, Dη z I - DS z I (ξ z)⟫_ℝ := by
    rw [integral_inner_crFormalAdjoint_split hc hpq (hDξv I) φ₂,
      integral_inner_fderiv_comm_of_hasWeakFDerivOn hDξ φ₂]
    linarith [integral_lineDeriv_crEquation hp hq hqp hpq hc hS hDS hξ hDξ hη hDη heq I φ₂]
  have hH := memLpLoc_differentiatedCR_rightSide hp hq.le hqp hS hDS hξ hη hDη
  have hpt (z : ℂ) : ⟪(Φ : ℂ → WithLp 2 (V × V)) z,
        WithLp.toLp 2 (Dη z 1 - DS z 1 (ξ z), Dη z I - DS z I (ξ z))⟫_ℝ =
      ⟪(φ₁ : ℂ → V) z, Dη z 1 - DS z 1 (ξ z)⟫_ℝ +
        ⟪(φ₂ : ℂ → V) z, Dη z I - DS z I (ξ z)⟫_ℝ := by simp [φ₁, φ₂]
  rw [hlhs, hrow1, hrow2]
  simp_rw [hpt]
  exact (integral_add
    (φ₁.integrable_inner ((hH.clm_comp (.fst ℝ V V)).locallyIntegrableOn hq1 hloc))
    (φ₂.integrable_inner ((hH.clm_comp (.snd ℝ V V)).locallyIntegrableOn hq1 hloc))).symm

/-- **The weak differentiated Cauchy–Riemann system.** Let `2 < p`, `1 < q ≤ p`, and
`p⁻¹ + q⁻¹ ≤ 1`. If `J, S ∈ W^{1,p}_loc(Ω)` with weak derivatives `DJ, DS` and
`ξ, η ∈ W^{1,q}_loc(Ω)` with weak derivatives `Dξ, Dη` satisfy
`∂_s ξ + J ∂_t ξ + S ξ = η` almost everywhere on `Ω`, then `Ξ = (∂_s ξ, ∂_t ξ)` valued in the
Hilbert product `WithLp 2 (V × V)` is a weak solution (`TauCeti.IsWeakCRSolution`) of
`∂_s Ξ + diag(J, J) ∂_t Ξ + S₂ Ξ = (∂_s η - (∂_s S) ξ, ∂_t η - (∂_t S) ξ)` with
`S₂ = TauCeti.differentiatedCRCoefficient S DJ`. -/
theorem isWeakCRSolution_differentiated [FiniteDimensional ℝ V] {p q : ℝ≥0} (hp : 2 < p)
    (hq : 1 < q) (hqp : q ≤ p) (hpq : (p : ℝ≥0∞)⁻¹ + (q : ℝ≥0∞)⁻¹ ≤ 1)
    {J S : ℂ → V →L[ℝ] V} {DJ DS : ℂ → ℂ →L[ℝ] V →L[ℝ] V}
    {DJ₂ : ℂ → ℂ →L[ℝ] WithLp 2 (V × V) →L[ℝ] WithLp 2 (V × V)}
    {ξ η : ℂ → V} {Dξ Dη : ℂ → ℂ →L[ℝ] V}
    (hJ : MemWkpLoc p Ω 1 J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hS : MemWkpLoc p Ω 1 S) (hDS : HasWeakFDerivOn volume Ω S DS)
    (hξ : MemWkpLoc q Ω 1 ξ) (hDξ : HasWeakFDerivOn volume Ω ξ Dξ)
    (hη : MemWkpLoc q Ω 1 η) (hDη : HasWeakFDerivOn volume Ω η Dη)
    (heq : ∀ᵐ z ∂volume.restrict Ω, Dξ z 1 + J z (Dξ z I) + S z (ξ z) = η z)
    (hDJ₂ : HasWeakFDerivOn volume Ω
      (fun z => (WithLp.prodContinuousLinearEquiv 2 ℝ V V).symm.arrowCongr
        (WithLp.prodContinuousLinearEquiv 2 ℝ V V).symm ((J z).prodMap (J z))) DJ₂) :
    IsWeakCRSolution q Ω
      (fun z => (WithLp.prodContinuousLinearEquiv 2 ℝ V V).symm.arrowCongr
        (WithLp.prodContinuousLinearEquiv 2 ℝ V V).symm ((J z).prodMap (J z)))
      DJ₂
      (fun z => (WithLp.prodContinuousLinearEquiv 2 ℝ V V).symm.arrowCongr
        (WithLp.prodContinuousLinearEquiv 2 ℝ V V).symm
        (differentiatedCRCoefficient (S z) (DJ z)))
      (fun z => WithLp.toLp 2 (Dξ z 1, Dξ z I))
      (fun z => WithLp.toLp 2 (Dη z 1 - DS z 1 (ξ z), Dη z I - DS z I (ξ z))) := by
  let e := (WithLp.prodContinuousLinearEquiv 2 ℝ V V).symm
  have hJ₂_eq : (fun z => diagWithLpCLM V (J z)) =
      fun z => e.arrowCongr e ((J z).prodMap (J z)) := funext fun z => diagWithLpCLM_apply (J z)
  have hDJ₂_diag : HasWeakFDerivOn volume Ω (fun z => diagWithLpCLM V (J z))
      (fun z => (diagWithLpCLM V).comp (DJ z)) := hDJ.clm_comp (diagWithLpCLM V)
  have hDJ₂_ae := (hJ₂_eq ▸ hDJ₂_diag).ae_eq hDJ₂
  rw [← hJ₂_eq]
  refine (isWeakCRSolution_congr_ae .rfl hDJ₂_ae .rfl .rfl .rfl).1 ?_
  have hq1 : (1 : ℝ≥0∞) ≤ q := by exact_mod_cast hq.le
  have hloc := Ω.isOpen.isLocallyClosed
  have hDJp : MemLpLoc p Ω DJ := memWkpLoc_zero_iff.1 (hJ.memWkpLoc_of_hasWeakFDerivOn hDJ)
  have hc : IsSobolevCRCoefficients p Ω J DJ S := ⟨hDJ, hJ.memLpLoc, hDJp, hS.memLpLoc⟩
  have hc₂ : IsSobolevCRCoefficients p Ω (fun z => diagWithLpCLM V (J z))
      (fun z => (diagWithLpCLM V).comp (DJ z))
      (fun z => e.arrowCongr e (differentiatedCRCoefficient (S z) (DJ z))) :=
    ⟨hDJ₂_diag, hJ.memLpLoc.clm_comp (diagWithLpCLM V),
      memWkpLoc_zero_iff.1
        ((hJ.clm_comp (diagWithLpCLM V)).memWkpLoc_of_hasWeakFDerivOn hDJ₂_diag),
      (memWkpLoc_zero_iff.1 ((memWkpLoc_zero_iff.2 hS.memLpLoc).differentiatedCRCoefficient
        hJ hDJ)).clm_comp (e.arrowCongr e).toContinuousLinearMap⟩
  have hΞq : MemLpLoc q Ω (fun z => WithLp.toLp 2 (Dξ z 1, Dξ z I)) :=
    e.comp_memLpLoc_iff.2 (memWkpLoc_zero_iff.1 (hξ.memWkpLoc_partials_of_hasWeakFDerivOn hDξ))
  have hHq : MemLpLoc q Ω
      (fun z => WithLp.toLp 2 (Dη z 1 - DS z 1 (ξ z), Dη z I - DS z I (ξ z))) :=
    e.comp_memLpLoc_iff.2
      (memLpLoc_differentiatedCR_rightSide hp hq.le hqp hS hDS hξ hη hDη)
  exact isWeakCRSolution_iff.2 ⟨hΞq, hHq.locallyIntegrableOn hq1 hloc, fun Φ =>
    ⟨hc₂.integrable_inner_crFormalAdjoint hpq hΞq Φ,
      integral_inner_crFormalAdjoint_differentiated_aux hp hq hqp hpq hc hS hDS hξ hDξ hη hDη
        heq Φ⟩⟩

end WeakDifferentiated

/-! ### Higher-order interior regularity -/

section HigherRegularity

/-- Right-hand side regularity for the differentiated system at every order `m`: if
`S ∈ W^{m+1,p}_loc(Ω)`, `ξ ∈ W^{m+1,q}_loc(Ω)`, and `η ∈ W^{m+1,q}_loc(Ω)` with `2 < p` and
`1 < q ≤ p`, then `(∂_s η - (∂_s S) ξ, ∂_t η - (∂_t S) ξ) ∈ W^{m,q}_loc(Ω)`. -/
private theorem memWkpLoc_differentiatedCR_rightSide {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] {Ω : Opens ℂ} {p q : ℝ≥0} (hp : 2 < p)
    (hq : 1 < q) (hqp : q ≤ p) {m : ℕ} {S : ℂ → V →L[ℝ] V} {DS : ℂ → ℂ →L[ℝ] V →L[ℝ] V}
    {ξ η : ℂ → V} {Dη : ℂ → ℂ →L[ℝ] V}
    (hS : MemWkpLoc p Ω (m + 1) S) (hDS : HasWeakFDerivOn volume Ω S DS)
    (hξ : MemWkpLoc q Ω (m + 1) ξ) (hη : MemWkpLoc q Ω (m + 1) η)
    (hDη : HasWeakFDerivOn volume Ω η Dη) :
    MemWkpLoc q Ω m (fun z => (Dη z 1 - DS z 1 (ξ z), Dη z I - DS z I (ξ z))) := by
  cases m with
  | zero =>
    exact memWkpLoc_zero_iff.2 (memLpLoc_differentiatedCR_rightSide hp hq.le hqp hS hDS hξ hη hDη)
  | succ n =>
    have hDSn : MemWkpLoc p Ω (n + 1) DS := hS.memWkpLoc_of_hasWeakFDerivOn hDS
    have hDηn : MemWkpLoc q Ω (n + 1) Dη := hη.memWkpLoc_of_hasWeakFDerivOn hDη
    have hcomp (v : ℂ) : MemWkpLoc q Ω (n + 1) (fun z => Dη z v - DS z v (ξ z)) :=
      (hDηn.clm_comp (ContinuousLinearMap.apply ℝ V v)).sub
        ((hDSn.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) v)).clm_apply_succ
          hp hq hqp hξ.of_succ)
    exact (hcomp 1).prodMk (hcomp I)

section Step

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Ω : Opens ℂ}

private local instance : NormedAddCommGroup (V →L[ℝ] V) := inferInstance
private local instance : NormedSpace ℝ (V →L[ℝ] V) := inferInstance
private local instance : NormedAddCommGroup (V × V →L[ℝ] V × V) := inferInstance
private local instance : NormedSpace ℝ (V × V →L[ℝ] V × V) := inferInstance
private local instance :
    NormedAddCommGroup (WithLp 2 (V × V) →L[ℝ] WithLp 2 (V × V)) := inferInstance
private local instance :
    NormedSpace ℝ (WithLp 2 (V × V) →L[ℝ] WithLp 2 (V × V)) := inferInstance

/-- Inductive step of `IsWeakCRSolution.memWkpLoc_succ`: upgrades `ξ ∈ W^{m+1,q}_loc(Ω)` to
`ξ ∈ W^{m+2,q}_loc(Ω)` by applying the order-`m` hypothesis to the weak differentiated system on
`WithLp 2 (V × V)`. -/
private theorem memWkpLoc_succ_step {p q : ℝ≥0} {m : ℕ}
    {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}
    (hp : 2 < p) (hq : 1 < q) (hqp : q ≤ p) (hpq : (p : ℝ≥0∞)⁻¹ + (q : ℝ≥0∞)⁻¹ < 1)
    (hJm1 : MemWkpLoc p Ω (m + 1) J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1)
    (hS : MemWkpLoc p Ω (m + 1) S) (hη : MemWkpLoc q Ω (m + 1) η)
    (hsol : IsWeakCRSolution q Ω J DJ S ξ η) (hξm : MemWkpLoc q Ω (m + 1) ξ)
    (ih_prod : ∀ {J₂ S₂ : ℂ → WithLp 2 (V × V) →L[ℝ] WithLp 2 (V × V)}
      {DJ₂ : ℂ → ℂ →L[ℝ] WithLp 2 (V × V) →L[ℝ] WithLp 2 (V × V)}
      {Ξ H : ℂ → WithLp 2 (V × V)},
      MemWkpLoc p Ω (max 1 m) J₂ → HasWeakFDerivOn volume Ω J₂ DJ₂ →
      (∀ᵐ z ∂volume.restrict Ω, J₂ z * J₂ z = -1) →
      MemWkpLoc p Ω m S₂ → MemWkpLoc q Ω m H →
      IsWeakCRSolution q Ω J₂ DJ₂ S₂ Ξ H → MemWkpLoc q Ω (m + 1) Ξ) :
    MemWkpLoc q Ω (m + 2) ξ := by
  have h1le : 1 ≤ m + 1 := Nat.succ_le_succ (Nat.zero_le m)
  have hmax : max 1 m ≤ m + 1 := max_le h1le (Nat.le_succ m)
  obtain ⟨Dξ, hDξ, hDξm⟩ := hξm.exists_weakFDeriv_of_isOpen
  obtain ⟨DS, hDS, -⟩ := hS.exists_weakFDeriv_of_isOpen
  obtain ⟨Dη, hDη, -⟩ := hη.exists_weakFDeriv_of_isOpen
  have hc : IsSobolevCRCoefficients p Ω J DJ S :=
    ⟨hDJ, (hJm1.of_le h1le).memLpLoc,
      memWkpLoc_zero_iff.1 ((hJm1.of_le h1le).memWkpLoc_of_hasWeakFDerivOn hDJ), hS.memLpLoc⟩
  have heq : ∀ᵐ z ∂volume.restrict Ω, Dξ z 1 + J z (Dξ z I) + S z (ξ z) = η z :=
    (hc.isWeakCRSolution_iff_ae hpq.le ENNReal.coe_ne_top ENNReal.coe_ne_top hDξ hsol.memLpLoc
      hDξm.memLpLoc hsol.locallyIntegrableOn).1 hsol
  let e := (WithLp.prodContinuousLinearEquiv 2 ℝ V V).symm
  have hJ₂_eq : (fun z => diagWithLpCLM V (J z)) =
      fun z => e.arrowCongr e ((J z).prodMap (J z)) := funext fun z => diagWithLpCLM_apply (J z)
  have hDJ₂ : HasWeakFDerivOn volume Ω (fun z => e.arrowCongr e ((J z).prodMap (J z)))
      (fun z => (diagWithLpCLM V).comp (DJ z)) := by
    rw [← hJ₂_eq]; exact hDJ.clm_comp (diagWithLpCLM V)
  have hsol₂ := isWeakCRSolution_differentiated hp hq hqp hpq.le (hJm1.of_le h1le) hDJ
    (hS.of_le h1le) hDS (hξm.of_le h1le) hDξ (hη.of_le h1le) hDη heq hDJ₂
  have hJ₂sq : ∀ᵐ z ∂volume.restrict Ω,
      e.arrowCongr e ((J z).prodMap (J z)) * e.arrowCongr e ((J z).prodMap (J z)) = -1 := by
    filter_upwards [hJsq] with z hz
    refine ContinuousLinearMap.ext fun w => ?_
    simpa [ContinuousLinearMap.mul_def] using
      congrArg e (congr($(prodMap_mul_self_eq_neg_one hz) (e.symm w)))
  have hJ₂ : MemWkpLoc p Ω (max 1 m) (fun z => e.arrowCongr e ((J z).prodMap (J z))) := by
    rw [← hJ₂_eq]; exact (hJm1.of_le hmax).clm_comp (diagWithLpCLM V)
  have hS₂ : MemWkpLoc p Ω m
      (fun z => e.arrowCongr e (differentiatedCRCoefficient (S z) (DJ z))) :=
    (hS.of_succ.differentiatedCRCoefficient hJm1 hDJ).clm_comp
      (e.arrowCongr e).toContinuousLinearMap
  have hH₂ : MemWkpLoc q Ω m
      (fun z => WithLp.toLp 2 (Dη z 1 - DS z 1 (ξ z), Dη z I - DS z I (ξ z))) :=
    (memWkpLoc_differentiatedCR_rightSide hp hq hqp hS hDS hξm hη hDη).clm_comp
      e.toContinuousLinearMap
  have hΞm := ih_prod hJ₂ hDJ₂ hJ₂sq hS₂ hH₂ hsol₂
  have hDξ' : HasWeakFDerivOn volume (Opens.interior (Ω : Set ℂ)) ξ Dξ := by
    rwa [Opens.interior_coe]
  exact hsol.memLpLoc.memWkpLoc_succ_of_hasWeakFDerivOn hDξ'
    (hΞm.clm_comp (WithLp.fstL 2 ℝ V V)) (hΞm.clm_comp (WithLp.sndL 2 ℝ V V))

end Step

/-- **Higher-order interior regularity** (McDuff–Salamon, Proposition B.4.9). Let `k : ℕ`,
`2 < p`, `1 < q ≤ p`, and `(p : ℝ≥0∞)⁻¹ + (q : ℝ≥0∞)⁻¹ < 1`. If `J ∈ W^{max 1 k, p}_loc(Ω)` has
weak derivative `DJ` with `J² = -1` almost everywhere on `Ω`, `S ∈ W^{k,p}_loc(Ω)`, and
`η ∈ W^{k,q}_loc(Ω)`, then every weak solution `ξ ∈ L^q_loc(Ω)` of `∂_s ξ + J ∂_t ξ + S ξ = η`
belongs to `W^{k+1,q}_loc(Ω)`. -/
theorem IsWeakCRSolution.memWkpLoc_succ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {Ω : Opens ℂ} {p q : ℝ≥0} {k : ℕ}
    {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}
    (hp : 2 < p) (hq : 1 < q) (hqp : q ≤ p) (hpq : (p : ℝ≥0∞)⁻¹ + (q : ℝ≥0∞)⁻¹ < 1)
    (hJ : MemWkpLoc p Ω (max 1 k) J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1)
    (hS : MemWkpLoc p Ω k S) (hη : MemWkpLoc q Ω k η)
    (hsol : IsWeakCRSolution q Ω J DJ S ξ η) :
    MemWkpLoc q Ω (k + 1) ξ := by
  induction k generalizing V with
  | zero =>
    have hc : IsSobolevCRCoefficients p Ω J DJ S :=
      ⟨hDJ, hJ.memLpLoc, memWkpLoc_zero_iff.1 (hJ.memWkpLoc_of_hasWeakFDerivOn hDJ),
        memWkpLoc_zero_iff.1 hS⟩
    exact hsol.memWkpLoc_one hp hq hqp hpq hc hJsq (memWkpLoc_zero_iff.1 hη)
  | succ m ih =>
    have hJm1 : MemWkpLoc p Ω (m + 1) J := by simpa using hJ
    have hmax : max 1 m ≤ m + 1 := max_le (Nat.succ_le_succ (Nat.zero_le m)) (Nat.le_succ m)
    exact memWkpLoc_succ_step hp hq hqp hpq hJm1 hDJ hJsq hS hη hsol
      (ih (hJm1.of_le hmax) hDJ hJsq hS.of_succ hη.of_succ hsol)
      fun hJ₂ hDJ₂ hJ₂sq hS₂ hH₂ hsol₂ => ih hJ₂ hDJ₂ hJ₂sq hS₂ hH₂ hsol₂

/-- **Higher-order interior regularity with exponent raising.** If `2 < p`, `1 < r ≤ p`,
`(p : ℝ≥0∞)⁻¹ + q⁻¹ < 1`, `(p : ℝ≥0∞)⁻¹ + (r : ℝ≥0∞)⁻¹ < 1`, `J ∈ W^{max 1 k, p}_loc(Ω)` with
`J² = -1` almost everywhere on `Ω`, `S ∈ W^{k,p}_loc(Ω)`, and `η ∈ W^{k,r}_loc(Ω)`, then every weak
solution `ξ ∈ L^q_loc(Ω)` (allowing `q = ∞`) lies in `W^{k+1,r}_loc(Ω)`. -/
theorem IsWeakCRSolution.memWkpLoc_succ_of_memWkpLoc {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] {Ω : Opens ℂ} {p r : ℝ≥0} {q : ℝ≥0∞} {k : ℕ}
    {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}
    (hp : 2 < p) (hr : 1 < r) (hrp : r ≤ p)
    (hpq : (p : ℝ≥0∞)⁻¹ + q⁻¹ < 1) (hpr : (p : ℝ≥0∞)⁻¹ + (r : ℝ≥0∞)⁻¹ < 1)
    (hJ : MemWkpLoc p Ω (max 1 k) J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1)
    (hS : MemWkpLoc p Ω k S) (hη : MemWkpLoc r Ω k η)
    (hsol : IsWeakCRSolution q Ω J DJ S ξ η) :
    MemWkpLoc r Ω (k + 1) ξ := by
  have hJ1 : MemWkpLoc p Ω 1 J := hJ.of_le (le_max_left 1 k)
  have hc : IsSobolevCRCoefficients p Ω J DJ S :=
    ⟨hDJ, hJ1.memLpLoc, memWkpLoc_zero_iff.1 (hJ1.memWkpLoc_of_hasWeakFDerivOn hDJ), hS.memLpLoc⟩
  have hξ1 : MemWkpLoc r Ω 1 ξ :=
    hsol.memWkpLoc_one_of_memLpLoc hp hr hrp hpq hc hJsq hη.memLpLoc
  have hsol_r : IsWeakCRSolution r Ω J DJ S ξ η :=
    isWeakCRSolution_iff.2 ⟨hξ1.memLpLoc, hsol.locallyIntegrableOn,
      (isWeakCRSolution_iff.1 hsol).2.2⟩
  exact hsol_r.memWkpLoc_succ hp hr hrp hpr hJ hDJ hJsq hS hη

/-- **Higher-order interior regularity at the coefficient exponent `p`.** When `2 < p`,
`(p : ℝ≥0∞)⁻¹ + q⁻¹ < 1`, `J ∈ W^{max 1 k, p}_loc(Ω)` with `J² = -1` almost everywhere,
`S ∈ W^{k,p}_loc(Ω)`, and `η ∈ W^{k,p}_loc(Ω)`, every weak solution `ξ ∈ L^q_loc(Ω)` lies in
`W^{k+1,p}_loc(Ω)`. -/
theorem IsWeakCRSolution.memWkpLoc_succ_self {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] {Ω : Opens ℂ} {p : ℝ≥0} {q : ℝ≥0∞} {k : ℕ}
    {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}
    (hp : 2 < p) (hpq : (p : ℝ≥0∞)⁻¹ + q⁻¹ < 1)
    (hJ : MemWkpLoc p Ω (max 1 k) J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1)
    (hS : MemWkpLoc p Ω k S) (hη : MemWkpLoc p Ω k η)
    (hsol : IsWeakCRSolution q Ω J DJ S ξ η) :
    MemWkpLoc p Ω (k + 1) ξ := by
  have hp2 : (2 : ℝ) < p := by exact_mod_cast hp
  have hpp_real : (p : ℝ)⁻¹ + (p : ℝ)⁻¹ < 1 := by
    have : (p : ℝ)⁻¹ < 2⁻¹ := (inv_lt_inv₀ (by positivity) two_pos).2 hp2
    linarith
  have hpp : (p : ℝ≥0∞)⁻¹ + (p : ℝ≥0∞)⁻¹ < 1 := by
    rw [← ENNReal.coe_inv (zero_lt_two.trans hp).ne', ← ENNReal.coe_add]
    exact_mod_cast hpp_real
  exact hsol.memWkpLoc_succ_of_memWkpLoc hp (one_lt_two.trans hp) le_rfl hpq hpp hJ hDJ hJsq hS hη

/-- **Existence of a `C^k` representative.** Under the hypotheses of
`TauCeti.IsWeakCRSolution.memWkpLoc_succ_self`, every weak solution `ξ ∈ L^q_loc(Ω)` agrees almost
everywhere on `Ω` with a `C^k` map on `Ω`. -/
theorem IsWeakCRSolution.exists_contDiffOn_ae_eq {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] {Ω : Opens ℂ} {p : ℝ≥0} {q : ℝ≥0∞} {k : ℕ}
    {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}
    (hp : 2 < p) (hpq : (p : ℝ≥0∞)⁻¹ + q⁻¹ < 1)
    (hJ : MemWkpLoc p Ω (max 1 k) J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1)
    (hS : MemWkpLoc p Ω k S) (hη : MemWkpLoc p Ω k η)
    (hsol : IsWeakCRSolution q Ω J DJ S ξ η) :
    ∃ g : ℂ → V, ContDiffOn ℝ k g Ω ∧ ξ =ᵐ[volume.restrict Ω] g :=
  (hsol.memWkpLoc_succ_self hp hpq hJ hDJ hJsq hS hη).exists_contDiffOn_ae_eq (by exact_mod_cast hp)

end HigherRegularity

/-! ### Weak linear Cauchy–Riemann solutions in finite-dimensional normed spaces -/

section NormedSpace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Ω : Opens ℂ}

/-- **Interior Sobolev regularity for `TauCeti.IsWeakLinearCauchyRiemannOn` on a finite-dimensional
real normed space.** If `2 < p`, `(p : ℝ≥0∞)⁻¹ + q⁻¹ < 1`, `J ∈ W^{max 1 k, p}_loc(Ω)` with
`J² = -1` almost everywhere on `Ω`, and `S ∈ W^{k,p}_loc(Ω)`, then every weak solution `ξ` of
`∂_s ξ + J ∂_t ξ + S ξ = 0` on `Ω` at exponent `q` lies in `W^{k+1,p}_loc(Ω)`. -/
theorem IsWeakLinearCauchyRiemannOn.memWkpLoc_succ_of_memWkpLoc {p : ℝ≥0} {q : ℝ≥0∞} {k : ℕ}
    {J S : ℂ → V →L[ℝ] V} {ξ : ℂ → V} (hp : 2 < p) (hpq : (p : ℝ≥0∞)⁻¹ + q⁻¹ < 1)
    (hJ : MemWkpLoc p Ω (max 1 k) J) (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1)
    (hS : MemWkpLoc p Ω k S) (h : IsWeakLinearCauchyRiemannOn q Ω J S ξ) :
    MemWkpLoc p Ω (k + 1) ξ := by
  let q₀ : ℝ≥0∞ := min q p
  have hq₀_t : q₀ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right q p)
  have hpp : (p : ℝ≥0∞)⁻¹ + (p : ℝ≥0∞)⁻¹ < 1 := by
    have hp2 : (2 : ℝ) < p := by exact_mod_cast hp
    have h1 : (p : ℝ)⁻¹ < 2⁻¹ := (inv_lt_inv₀ (by positivity) two_pos).2 hp2
    rw [← ENNReal.coe_inv (zero_lt_two.trans hp).ne', ← ENNReal.coe_add]
    exact_mod_cast (by linarith : (p : ℝ)⁻¹ + (p : ℝ)⁻¹ < 1)
  have hpq₀ : (p : ℝ≥0∞)⁻¹ + q₀⁻¹ < 1 := by
    rcases min_cases q (p : ℝ≥0∞) with ⟨hmin, _⟩ | ⟨hmin, _⟩ <;> · dsimp only [q₀]; rwa [hmin]
  let E := EuclideanSpace ℝ (Fin (Module.finrank ℝ V))
  let A : V ≃L[ℝ] E := (LinearEquiv.ofFinrankEq V E (by simp [E])).toContinuousLinearEquiv
  let conjA : (V →L[ℝ] V) ≃L[ℝ] E →L[ℝ] E := A.arrowCongr A
  have hE : IsWeakLinearCauchyRiemannOn q₀ Ω (fun z => conjA (J z)) (fun z => conjA (S z))
      (fun z => A (ξ z)) := by
    have hcomp := A.isWeakCauchyRiemannOn_iff_comp.1 (h.mono_exponent (min_le_left q p))
    have hJeq : (fun z (_ : E) => (A : V →L[ℝ] E).comp ((J z).comp (A.symm : E →L[ℝ] V))) =
        fun z _ => conjA (J z) :=
      funext fun _ => funext fun _ => ContinuousLinearMap.ext fun _ => rfl
    have hSeq : (fun z (y : E) => A (-S z (A.symm y))) = fun z y => -conjA (S z) y :=
      funext fun _ => funext fun _ => map_neg A _
    simpa only [IsWeakLinearCauchyRiemannOn, hJeq, hSeq] using hcomp
  have hJ' : MemWkpLoc p Ω (max 1 k) (fun z => conjA (J z)) := conjA.comp_memWkpLoc_iff.2 hJ
  have hS' : MemWkpLoc p Ω k (fun z => conjA (S z)) := conjA.comp_memWkpLoc_iff.2 hS
  obtain ⟨DJ', hDJ', hDJ'0⟩ := (hJ'.of_le (le_max_left 1 k)).exists_weakFDeriv_of_isOpen
  have hc' : IsSobolevCRCoefficients p Ω (fun z => conjA (J z)) DJ' (fun z => conjA (S z)) :=
    ⟨hDJ', hJ'.memLpLoc, memWkpLoc_zero_iff.1 hDJ'0, hS'.memLpLoc⟩
  have hsol' : IsWeakCRSolution q₀ Ω (fun z => conjA (J z)) DJ' (fun z => conjA (S z))
      (fun z => A (ξ z)) 0 :=
    ((hc'.isWeakLinearCauchyRiemannOn_iff hpq₀.le ENNReal.coe_ne_top hq₀_t).1 hE).2.1
  have hJsq' : ∀ᵐ z ∂volume.restrict Ω, conjA (J z) * conjA (J z) = -1 := by
    filter_upwards [hJsq] with z hz
    refine ContinuousLinearMap.ext fun y => ?_
    have hy : J z (J z (A.symm y)) = -A.symm y := by simpa using congr($hz (A.symm y))
    simp [conjA, ContinuousLinearMap.mul_def, hy]
  exact A.comp_memWkpLoc_iff.1
    (hsol'.memWkpLoc_succ_self hp hpq₀ hJ' hDJ' hJsq' hS' memWkpLoc_zero_fun)

/-- **`C^k` interior regularity for `TauCeti.IsWeakLinearCauchyRiemannOn`.** Under the hypotheses
of `TauCeti.IsWeakLinearCauchyRiemannOn.memWkpLoc_succ_of_memWkpLoc`, a continuous weak solution `ξ`
of `∂_s ξ + J ∂_t ξ + S ξ = 0` on `Ω` is of class `C^k` on `Ω`. -/
theorem IsWeakLinearCauchyRiemannOn.contDiffOn {p : ℝ≥0} {q : ℝ≥0∞} {k : ℕ}
    {J S : ℂ → V →L[ℝ] V} {ξ : ℂ → V} (hp : 2 < p) (hpq : (p : ℝ≥0∞)⁻¹ + q⁻¹ < 1)
    (hJ : MemWkpLoc p Ω (max 1 k) J) (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1)
    (hS : MemWkpLoc p Ω k S) (h : IsWeakLinearCauchyRiemannOn q Ω J S ξ) :
    ContDiffOn ℝ k ξ Ω := by
  have hW : MemWkpLoc p Ω (k + 1) ξ := h.memWkpLoc_succ_of_memWkpLoc hp hpq hJ hJsq hS
  obtain ⟨g, hg, hae⟩ := hW.exists_contDiffOn_ae_eq (by exact_mod_cast hp)
  exact hg.congr (Measure.eqOn_open_of_ae_eq hae Ω.isOpen h.continuousOn hg.continuousOn)

/-- **`C^∞` interior regularity for `TauCeti.IsWeakLinearCauchyRiemannOn` with smooth
coefficients.** If `1 < q ≤ ∞`, `J` and `S` are `C^∞` on `Ω`, and `J² = -1` almost everywhere on
`Ω`, then every weak solution `ξ` of `∂_s ξ + J ∂_t ξ + S ξ = 0` at exponent `q` is `C^∞` on `Ω`. -/
theorem IsWeakLinearCauchyRiemannOn.contDiffOn_top {q : ℝ≥0∞} (hq : 1 < q)
    {J S : ℂ → V →L[ℝ] V} {ξ : ℂ → V} (hJ : ContDiffOn ℝ ∞ J Ω)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1) (hS : ContDiffOn ℝ ∞ S Ω)
    (h : IsWeakLinearCauchyRiemannOn q Ω J S ξ) :
    ContDiffOn ℝ ∞ ξ Ω := by
  have hq_inv : q⁻¹ < 1 := ENNReal.inv_lt_one.2 hq
  let a : ℝ≥0 := q⁻¹.toNNReal
  have ha_coe : (a : ℝ≥0∞) = q⁻¹ := ENNReal.coe_toNNReal (ne_top_of_lt hq_inv)
  have ha1 : (a : ℝ) < 1 := by exact_mod_cast ha_coe.trans_lt hq_inv
  obtain ⟨n, hn⟩ := exists_nat_gt ((1 - (a : ℝ))⁻¹)
  let p : ℝ≥0 := max (3 : ℝ≥0) (n : ℝ≥0)
  have hp : 2 < p := (by norm_num : (2 : ℝ≥0) < 3).trans_le (le_max_left (3 : ℝ≥0) (n : ℝ≥0))
  have hp_inv : (p : ℝ)⁻¹ < 1 - (a : ℝ) := by
    have hn_pos : (0 : ℝ) < n := (inv_pos.2 (sub_pos.2 ha1)).trans hn
    have hp_ge : (n : ℝ) ≤ p := by
      simpa only [NNReal.coe_natCast] using NNReal.coe_le_coe.2 (le_max_right (3 : ℝ≥0) (n : ℝ≥0))
    exact ((inv_le_inv₀ (by positivity) hn_pos).2 hp_ge).trans_lt
      ((inv_lt_comm₀ (sub_pos.2 ha1) hn_pos).1 hn)
  have hpq : (p : ℝ≥0∞)⁻¹ + q⁻¹ < 1 := by
    have hpq_nn : p⁻¹ + a < 1 := by exact_mod_cast (by linarith : (p : ℝ)⁻¹ + (a : ℝ) < 1)
    rw [← ha_coe, ← ENNReal.coe_inv (zero_lt_two.trans hp).ne', ← ENNReal.coe_add]
    exact_mod_cast hpq_nn
  refine contDiffOn_infty.2 fun k => ?_
  exact h.contDiffOn hp hpq ((hJ.of_le (by simp)).memWkpLoc subset_rfl) hJsq
    ((hS.of_le (by simp)).memWkpLoc subset_rfl)

end NormedSpace

end TauCeti
