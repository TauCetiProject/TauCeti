/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Weak
public import TauCeti.Analysis.Sobolev.Local.Norm
import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.DivergenceForm
import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.OrderZero
import TauCeti.Analysis.Complex.Wirtinger.DivergenceLaplace.Estimate
import TauCeti.Analysis.Sobolev.Local.SobolevEmbedding
import TauCeti.Data.ENNReal.Holder
import TauCeti.MeasureTheory.Function.Holder
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.Topology.Sets.Opens

/-!
# The order-zero estimate for real Cauchy–Riemann equations with Sobolev coefficients

Let `Ω ⊆ ℂ` be open, write `z = s + i t`, and let `V` be a finite-dimensional real inner product
space. For coefficients `J ∈ W^{1,p}(Ω; End V)` with `J² = -1` and `S ∈ Lᵖ(Ω; End V)`, `p > 2`,
let `ξ ∈ L^q_loc` be a weak solution of

`∂_s ξ + J ∂_t ξ + S ξ = η`

in the sense of `TauCeti.IsWeakCRSolution`, with `η ∈ Lʳ_loc`, `1 < r < ∞` and
`1/p + 1/q ≤ 1/r`. The order-zero lemma `TauCeti.IsWeakCRSolution.memWkpLoc_one` shows
`ξ ∈ W^{1,r}_loc(Ω)`. This file proves the accompanying estimate (McDuff–Salamon, Lemma B.4.6):
for every set `U` with compact closure in `Ω`,

`‖ξ‖_{W^{1,r}(U)} ≤ C (‖η‖_{Lʳ(Ω)} + ‖ξ‖_{L^q(Ω)})`,

where `C` depends only on `p`, `q`, `r`, `U`, `Ω`, `V` and a bound `M` for `‖J‖_{W^{1,p}(Ω)}`
and `‖S‖_{Lᵖ(Ω)}` (`TauCeti.exists_eLpNormWkp_one_le_of_isWeakCRSolution`). The constant is
chosen before the coefficients, so a single constant serves every pair `(J, S)` in a bounded set:
this is the uniformity clause of the estimate at order zero.

## The argument

Shrink `Ω` to an open set `W` with `closure U ⊆ W` and compact closure `closure W ⊆ Ω`. On `W` the
solution satisfies the divergence-form Laplace equation `Δξ = ∂_s f + ∂_t g` with the data
`f = η + (∂_t J) ξ - S ξ` and `g = -J f - (∂_s J) ξ - (∂_t J) (J ξ)`
(`TauCeti.IsWeakCRSolution.integral_laplacian_smul_eq`), so the interior estimate for that
equation (`TauCeti.exists_eLpNormWkp_one_le_of_integral_laplacian_smul_eq`) bounds
`‖ξ‖_{W^{1,r}(U)}` by `‖f‖_{Lʳ(W)} + ‖g‖_{Lʳ(W)} + ‖ξ‖_{L^q(W)}`. Each term of `f` and `g` is a
product of `η` or `ξ` with factors among `J`, `DJ` and `S`. Hölder's inequality bounds it by
`‖J‖_{L^∞(W)}`, `‖DJ‖_{Lᵖ(Ω)}` and `‖S‖_{Lᵖ(Ω)}` times `‖η‖_{Lʳ(Ω)}` or `‖ξ‖_{L^{q'}(W)}`, where
`1/p + 1/q' = 1/r` and `q' ≤ q`, so that `‖ξ‖_{L^{q'}(W)}` is at most a multiple of
`‖ξ‖_{L^q(Ω)}` because `W` has finite measure. Morrey's embedding bounds `‖J‖_{L^∞(W)}` by a
multiple of `‖J‖_{W^{1,p}(Ω)}` (`TauCeti.exists_eLpNorm_top_le_mul_eLpNormWkp_one`).

## Main results

* `TauCeti.exists_eLpNormWkp_one_le_of_isWeakCRSolution`: the order-zero interior estimate, with
  a constant uniform over coefficients bounded in `W^{1,p} × Lᵖ`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4, Lemma B.4.6 and its proof.
-/

public section

open MeasureTheory TopologicalSpace Complex Set
open scoped ENNReal NNReal

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {Ω : Opens ℂ} {p q r : ℝ≥0∞}

/-- On an open set, a weak derivative of `f` has `Lᵖ` norm at most `‖f‖_{W^{1,p}}`. -/
private theorem eLpNorm_le_eLpNormWkp_one {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℂ → F} {D : ℂ → ℂ →L[ℝ] F}
    (hD : HasWeakFDerivOn volume Ω f D) :
    eLpNorm D p (volume.restrict Ω) ≤ eLpNormWkp p Ω 1 f := by
  rw [eLpNormWkp_succ_eq_of_hasWeakFDerivOn (k := 0) hD, eLpNormWkp_zero]
  exact le_add_self

/-- The final bookkeeping of the order-zero estimate:
`C ((1 + k) a + 3 (1 + k) m (c b) + b) ≤ C (2 + k + 3 (1 + k) m c) (a + b)`. -/
private theorem mul_add_le_mul_mul_add (C k m c a b : ℝ≥0∞) :
    C * ((1 + k) * a + 3 * (1 + k) * m * (c * b) + b) ≤
      C * (2 + k + 3 * (1 + k) * m * c) * (a + b) :=
  calc C * ((1 + k) * a + 3 * (1 + k) * m * (c * b) + b)
      ≤ C * ((1 + k) * a + 3 * (1 + k) * m * (c * b) + b +
          ((3 * (1 + k) * m * c + 1) * a + (1 + k) * b)) := mul_le_mul_right le_self_add _
    _ = C * (2 + k + 3 * (1 + k) * m * c) * (a + b) := by ring

section DivergenceData

variable {μ : Measure ℂ} [ENNReal.HolderTriple p q r] {J S : ℂ → V →L[ℝ] V}
  {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}

omit [CompleteSpace V] in
/-- Hölder's inequality for `z ↦ DJ z c (w z)` with `‖c‖ = 1`, `DJ ∈ Lᵖ` and `w ∈ L^q`. -/
private theorem eLpNorm_apply_apply_le {c : ℂ} (hc : ‖c‖ = 1) {w : ℂ → V}
    (hDJ : AEStronglyMeasurable DJ μ) (hw : AEStronglyMeasurable w μ) :
    eLpNorm (fun z => DJ z c (w z)) r μ ≤ eLpNorm DJ p μ * eLpNorm w q μ :=
  (eLpNorm_clm_apply_le (a := p) (b := q)
    ((ContinuousLinearMap.apply ℝ (V →L[ℝ] V) c).continuous.comp_aestronglyMeasurable hDJ)
    hw).trans (mul_le_mul_left ((eLpNorm_clm_apply_const_le (p := p) (f := DJ) c).trans_eq
      (by rw [show ‖c‖₊ = 1 from Subtype.ext hc, ENNReal.coe_one, one_mul])) _)

omit [CompleteSpace V] in
/-- The `Lʳ` bound for the divergence-form data `f = η + (∂_t J) ξ - S ξ` and
`g = -J f - (∂_s J) ξ - (∂_t J) (J ξ)` together, in terms of bounds `k` for `‖J‖_{L^∞}`, `m` for
`‖DJ‖_{Lᵖ}` and `‖S‖_{Lᵖ}`, `a` for `‖η‖_{Lʳ}` and `x` for `‖ξ‖_{L^q}`. -/
private theorem eLpNorm_divergenceForm_add_le (hr : 1 ≤ r) (hJ : AEStronglyMeasurable J μ)
    (hDJ : AEStronglyMeasurable DJ μ) (hS : AEStronglyMeasurable S μ)
    (hξ : AEStronglyMeasurable ξ μ) (hη : AEStronglyMeasurable η μ) {k m a x : ℝ≥0∞}
    (hJk : eLpNorm J ∞ μ ≤ k) (hDJm : eLpNorm DJ p μ ≤ m) (hSm : eLpNorm S p μ ≤ m)
    (hηa : eLpNorm η r μ ≤ a) (hξx : eLpNorm ξ q μ ≤ x) :
    eLpNorm (fun z => η z + DJ z I (ξ z) - S z (ξ z)) r μ +
      eLpNorm (fun z => -J z (η z + DJ z I (ξ z) - S z (ξ z)) - DJ z 1 (ξ z) -
        DJ z I (J z (ξ z))) r μ ≤ (1 + k) * a + 3 * (1 + k) * m * x := by
  have hA : Continuous fun y : (V →L[ℝ] V) × V => y.1 y.2 := isBoundedBilinearMap_apply.continuous
  have hJξm : AEStronglyMeasurable (fun z => J z (ξ z)) μ :=
    hA.comp_aestronglyMeasurable (hJ.prodMk hξ)
  have hDJIm : AEStronglyMeasurable (fun z => DJ z I) μ :=
    (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) I).continuous.comp_aestronglyMeasurable hDJ
  have hFm : AEStronglyMeasurable (fun z => η z + DJ z I (ξ z) - S z (ξ z)) μ :=
    (hη.add (hA.comp_aestronglyMeasurable (hDJIm.prodMk hξ))).sub
      (hA.comp_aestronglyMeasurable (hS.prodMk hξ))
  have hF : eLpNorm (fun z => η z + DJ z I (ξ z) - S z (ξ z)) r μ ≤ a + m * x + m * x :=
    (eLpNorm_sub_le hr).trans (add_le_add ((eLpNorm_add_le hr).trans (add_le_add hηa
      ((eLpNorm_apply_apply_le (q := q) norm_I hDJ hξ).trans (mul_le_mul' hDJm hξx))))
      ((eLpNorm_clm_apply_le (a := p) (b := q) hS hξ).trans (mul_le_mul' hSm hξx)))
  have hJF : eLpNorm (fun z => -J z (η z + DJ z I (ξ z) - S z (ξ z))) r μ ≤
      k * (a + m * x + m * x) := by
    refine (eLpNorm_neg (fun z => J z (η z + DJ z I (ξ z) - S z (ξ z))) r μ).le.trans ?_
    exact (eLpNorm_clm_apply_le (a := ∞) (b := r) hJ hFm).trans (mul_le_mul' hJk hF)
  have hG := (eLpNorm_sub_le hr).trans (add_le_add ((eLpNorm_sub_le hr).trans (add_le_add hJF
    ((eLpNorm_apply_apply_le (q := q) norm_one hDJ hξ).trans (mul_le_mul' hDJm hξx))))
    ((eLpNorm_apply_apply_le (q := q) norm_I hDJ hJξm).trans (mul_le_mul' hDJm
      ((eLpNorm_clm_apply_le (a := ∞) (b := q) hJ hξ).trans (mul_le_mul' hJk hξx)))))
  refine (add_le_add hF hG).trans_eq ?_
  ring

end DivergenceData

/-- **The order-zero interior estimate for real Cauchy–Riemann equations with Sobolev
coefficients** (McDuff–Salamon, Lemma B.4.6). Let `V` be finite-dimensional, `p > 2`,
`1 < r < ∞` and `1/p + 1/q ≤ 1/r`, let `U` have compact closure in `Ω`, and let `M ≥ 0`. There is
a constant `C` such that for all coefficients `J ∈ W^{1,p}(Ω)` with `J² = -1` almost everywhere
and `S ∈ Lᵖ(Ω)`, in the sense of `TauCeti.IsSobolevCRCoefficients`, with
`‖J‖_{W^{1,p}(Ω)} ≤ M` and `‖S‖_{Lᵖ(Ω)} ≤ M`, every weak solution `ξ ∈ L^q_loc` of
`∂_s ξ + J ∂_t ξ + S ξ = η` on `Ω` with `η ∈ Lʳ_loc` satisfies
`‖ξ‖_{W^{1,r}(U)} ≤ C (‖η‖_{Lʳ(Ω)} + ‖ξ‖_{L^q(Ω)})`.

The constant depends only on `p`, `q`, `r`, `U`, `Ω`, `V` and `M`, and not on `(J, S)`: one
constant serves every pair of coefficients in a bounded set. -/
theorem exists_eLpNormWkp_one_le_of_isWeakCRSolution [FiniteDimensional ℝ V] (hp : 2 < p)
    (hpqr : p⁻¹ + q⁻¹ ≤ r⁻¹) (hr : 1 < r) (hr_top : r ≠ ⊤) {U : Set ℂ}
    (hUc : IsCompact (closure U)) (hUΩ : closure U ⊆ Ω) (M : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (J S : ℂ → V →L[ℝ] V) (DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V) (ξ η : ℂ → V),
      IsWeakCRSolution q Ω J DJ S ξ η → IsSobolevCRCoefficients p Ω J DJ S →
      (∀ᵐ z ∂volume.restrict Ω, J z * J z = -1) → eLpNormWkp p Ω 1 J ≤ M →
      eLpNorm S p (volume.restrict Ω) ≤ M → MemLpLoc r Ω η →
      eLpNormWkp r U 1 ξ ≤ C * (eLpNorm η r (volume.restrict Ω) +
        eLpNorm ξ q (volume.restrict Ω)) := by
  have hr1 : 1 ≤ r := hr.le
  have hpq1 : p⁻¹ + q⁻¹ ≤ 1 := hpqr.trans (ENNReal.inv_le_one.2 hr1)
  have hq1 : 1 ≤ q := ENNReal.one_le_right_of_inv_add_inv_le_one hpq1
  obtain ⟨q', _, hq'q⟩ := ENNReal.HolderTriple.exists_le_of_inv_add_inv_le hpqr
  -- An intermediate open set `W` with `closure U ⊆ W` and `closure W` compact in `Ω`.
  obtain ⟨W, hUW, hWΩ, hWc⟩ := Opens.exists_between_and_isCompact_closure hUc hUΩ
  have hWle : W ≤ Ω := subset_closure.trans hWΩ
  -- The Laplace estimate and Morrey bound on `W`, and `L^{q'}(W)` against `L^q(W)`.
  obtain ⟨CL, hCL⟩ := exists_eLpNormWkp_one_le_of_integral_laplacian_smul_eq (V := V) hr hr_top
    hq1 hUc hUW
  obtain ⟨Cm, hCm⟩ := exists_eLpNorm_top_le_mul_eLpNormWkp_one (F := V →L[ℝ] V) hp hWc hWΩ
  have : IsFiniteMeasure (volume.restrict (W : Set ℂ)) := isFiniteMeasure_restrict.2
    ((measure_mono subset_closure).trans_lt hWc.measure_lt_top).ne
  obtain ⟨c, hc⟩ := exists_eLpNorm_le_mul_eLpNorm_of_le (μ := volume.restrict (W : Set ℂ))
    (E := V) hq'q
  refine ⟨CL * (2 + Cm * M + 3 * (1 + Cm * M) * M * c),
    fun J S DJ ξ η h hco hJ2 hJM hSM hη => ?_⟩
  set μ := volume.restrict (W : Set ℂ)
  have hμ : μ ≤ volume.restrict Ω := Measure.restrict_mono hWle le_rfl
  have hW : IsWeakCRSolution q W J DJ S ξ η := h.mono hWle
  have hcW : IsSobolevCRCoefficients p W J DJ S :=
    ⟨hco.hasWeakFDerivOn.mono hWle, hco.memLpLoc_coeff.mono_set hWle,
      hco.memLpLoc_deriv.mono_set hWle, hco.memLpLoc_zeroth.mono_set hWle⟩
  have hJb := hcW.memLpLoc_top_coeff hp
  have : ENNReal.HolderTriple p q (p⁻¹ + q⁻¹)⁻¹ := .of p q
  have hrt : r ≤ (p⁻¹ + q⁻¹)⁻¹ := ENNReal.le_inv_iff_le_inv.2 hpqr
  have hmain := hCL ξ _ _ (hW.memLpLoc.locallyIntegrableOn hq1 W.isOpen.isLocallyClosed)
    (hW.memLpLoc_divergenceForm_fst hcW hrt (hη.mono_set hWle))
    (hW.memLpLoc_divergenceForm_snd hcW hJb hrt (hη.mono_set hWle))
    (hW.integral_laplacian_smul_eq hcW hJb (ae_mono hμ hJ2) hpq1)
  -- Bounds for the factors on `W`.
  have hm {s : ℝ≥0∞} {u : ℂ → V →L[ℝ] V} (hu : MemLpLoc s Ω u) : AEStronglyMeasurable u μ :=
    (hu.memLp_restrict_of_isCompact_closure hWc hWΩ).aestronglyMeasurable
  have hmV {s : ℝ≥0∞} {u : ℂ → V} (hu : MemLpLoc s Ω u) : AEStronglyMeasurable u μ :=
    (hu.memLp_restrict_of_isCompact_closure hWc hWΩ).aestronglyMeasurable
  have hJk : eLpNorm J ∞ μ ≤ (Cm * M : ℝ≥0) := (hCm J).trans (by rw [ENNReal.coe_mul]; gcongr)
  have hDJM : eLpNorm DJ p μ ≤ M := (eLpNorm_mono_measure _ hμ).trans
    ((eLpNorm_le_eLpNormWkp_one hco.hasWeakFDerivOn).trans hJM)
  have hdata := eLpNorm_divergenceForm_add_le (q := q') hr1 (hm hco.memLpLoc_coeff)
    (hco.memLpLoc_deriv.memLp_restrict_of_isCompact_closure hWc hWΩ).aestronglyMeasurable
    (hm hco.memLpLoc_zeroth) (hmV h.memLpLoc) (hmV hη) hJk hDJM
    ((eLpNorm_mono_measure _ hμ).trans hSM) (eLpNorm_mono_measure _ hμ)
    ((hc ξ).trans (mul_le_mul_right (eLpNorm_mono_measure _ hμ) _))
  -- Collect the terms.
  refine hmain.trans ((mul_le_mul_right (add_le_add hdata (eLpNorm_mono_measure _ hμ)) _).trans ?_)
  convert mul_add_le_mul_mul_add CL _ M c _ _ using 2
  push_cast
  ring

end TauCeti
