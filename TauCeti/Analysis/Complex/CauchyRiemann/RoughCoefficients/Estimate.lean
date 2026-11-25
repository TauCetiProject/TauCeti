/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Weak
public import TauCeti.Analysis.Sobolev.Local.Norm
import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.DivergenceForm
import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Interior
import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.OrderZero
import TauCeti.Analysis.Complex.Wirtinger.DivergenceLaplace.Estimate
import TauCeti.Analysis.Sobolev.Local.SobolevEmbedding
import TauCeti.Data.ENNReal.Holder
import TauCeti.MeasureTheory.Function.Holder
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.Topology.Sets.Opens

/-!
# Interior estimates for real Cauchy–Riemann equations with Sobolev coefficients

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

Climbing the exponent ladder of `TauCeti.IsWeakCRSolution.memWkpLoc_one_of_le` with this estimate
gives, for `1/p + 1/q < 1` and any `1 < r < ∞` with `r ≤ p`, the same bound
`‖ξ‖_{W^{1,r}(U)} ≤ C (‖η‖_{Lʳ(Ω)} + ‖ξ‖_{L^q(Ω)})` without any relation between `q` and `r`
(`TauCeti.exists_eLpNormWkp_one_le_of_isWeakCRSolution_of_le`), again uniformly in bounded
`(J, S)`. Each rung applies the order-zero estimate at `1/r' = 1/p + 1/s` and then the local
Sobolev or Morrey estimate
(`TauCeti.exists_inv_le_inv_sub_and_eLpNorm_le_mul_eLpNormWkp_one`) on a smaller open
set, so the rungs run through nested open sets `U ⋐ ⋯ ⋐ Ω`.

## The argument at order zero

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
* `TauCeti.exists_eLpNormWkp_one_le_of_isWeakCRSolution_of_le`: the interior `W^{1,r}` estimate
  for every `r ≤ p` from a solution in `L^q_loc`, with the same uniformity.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4, Lemmas B.4.4 and B.4.6 and the proof of Lemma B.4.6.
-/

public section

open MeasureTheory TopologicalSpace Complex Set
open scoped ENNReal NNReal

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {Ω : Opens ℂ} {p q r : ℝ≥0∞}

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
      (by rw [show ‖c‖₊ = 1 from NNReal.eq (by simpa using hc), ENNReal.coe_one, one_mul])) _)

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
  have hcW : IsSobolevCRCoefficients p W J DJ S := hco.mono hWle
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
    ((eLpNormWkp_zero (f := DJ) ▸
      eLpNormWkp_le_eLpNormWkp_succ_of_hasWeakFDerivOn (k := 0) hco.hasWeakFDerivOn).trans hJM)
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

/-- The bookkeeping of one rung of the estimate ladder:
`x (a + y (z a + b)) ≤ x (1 + y z + y) (a + b)`. -/
private theorem mul_add_mul_le_mul_mul_add (x y z a b : ℝ≥0∞) :
    x * (a + y * (z * a + b)) ≤ x * (1 + y * z + y) * (a + b) :=
  calc x * (a + y * (z * a + b)) ≤ x * (a + y * (z * a + b) + (b + y * z * b + y * a)) :=
        mul_le_mul_right le_self_add _
    _ = x * (1 + y * z + y) * (a + b) := by ring

variable (V) in
/-- The interior `W^{1,r}(U)` estimate for weak solutions in `Lˢ_loc(Ω)`, with a constant
uniform over coefficients bounded by `M`. -/
private def HasCREstimate (p r s : ℝ≥0∞) (M : ℝ≥0) (Ω : Opens ℂ) (U : Set ℂ) : Prop :=
  ∃ C : ℝ≥0, ∀ (J S : ℂ → V →L[ℝ] V) (DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V) (ξ η : ℂ → V),
    IsWeakCRSolution s Ω J DJ S ξ η → IsSobolevCRCoefficients p Ω J DJ S →
    (∀ᵐ z ∂volume.restrict Ω, J z * J z = -1) → eLpNormWkp p Ω 1 J ≤ M →
    eLpNorm S p (volume.restrict Ω) ≤ M → MemLpLoc r Ω η →
    eLpNormWkp r U 1 ξ ≤ C * (eLpNorm η r (volume.restrict Ω) + eLpNorm ξ s (volume.restrict Ω))

/-- One rung of the estimate ladder. Let `1/r' = 1/p + 1/s` with `1 < r' ≤ r < ∞`, and let `s'`
be an exponent with `W^{1,r'}_loc ⊂ L^{s'}_loc` and the local Sobolev estimate. If the estimate
holds for solutions in `L^{s'}_loc` on every open set, it holds for solutions in `Lˢ_loc`: the
order-zero estimate bounds `ξ` in `W^{1,r'}`, and the Sobolev estimate bounds it in `L^{s'}`, on
nested open sets `U ⋐ W₁ ⋐ W ⋐ W₀ ⋐ Ω`. -/
private theorem hasCREstimate_of_rung [FiniteDimensional ℝ V] (hp : 2 < p) (hr_top : r ≠ ⊤)
    (M : ℝ≥0) {s s' : ℝ≥0∞} (hr'1 : 1 < (p⁻¹ + s⁻¹)⁻¹) (hr'r : (p⁻¹ + s⁻¹)⁻¹ ≤ r)
    (hest : ∀ {U : Set ℂ} {W : Opens ℂ}, IsCompact (closure U) → closure U ⊆ W →
      ∃ C : ℝ≥0, ∀ u : ℂ → V,
        eLpNorm u s' (volume.restrict U) ≤ C * eLpNormWkp (p⁻¹ + s⁻¹)⁻¹ W 1 u)
    (ih : ∀ (Ω : Opens ℂ) (U : Set ℂ), IsCompact (closure U) → closure U ⊆ Ω →
      HasCREstimate V p r s' M Ω U)
    {U : Set ℂ} (hUc : IsCompact (closure U)) (hUΩ : closure U ⊆ Ω) :
    HasCREstimate V p r s M Ω U := by
  have hr'_top : (p⁻¹ + s⁻¹)⁻¹ ≠ ⊤ := ne_top_of_le_ne_top hr_top hr'r
  obtain ⟨W₁, hUW₁, hW₁Ω, hW₁c⟩ := Opens.exists_between_and_isCompact_closure hUc hUΩ
  obtain ⟨W, hW₁W, hWΩ, hWc⟩ := Opens.exists_between_and_isCompact_closure hW₁c hW₁Ω
  obtain ⟨W₀, hWW₀, hW₀Ω, hW₀c⟩ := Opens.exists_between_and_isCompact_closure hWc hWΩ
  have hW₀le : W₀ ≤ Ω := subset_closure.trans hW₀Ω
  have hW₁W₀ : W₁ ≤ W₀ := subset_closure.trans (hW₁W.trans (subset_closure.trans hWW₀))
  obtain ⟨C₁, hC₁⟩ := ih W₁ U hUc hUW₁
  obtain ⟨CS, hCS⟩ := hest hW₁c hW₁W
  obtain ⟨C₀, hC₀⟩ := exists_eLpNormWkp_one_le_of_isWeakCRSolution (V := V) (Ω := W₀) (q := s)
    hp (by rw [inv_inv]) hr'1 hr'_top hWc hWW₀ M
  have : IsFiniteMeasure (volume.restrict (W₀ : Set ℂ)) := isFiniteMeasure_restrict.2
    ((measure_mono subset_closure).trans_lt hW₀c.measure_lt_top).ne
  obtain ⟨c, hc⟩ := exists_eLpNorm_le_mul_eLpNorm_of_le (μ := volume.restrict (W₀ : Set ℂ))
    (E := V) hr'r
  refine ⟨C₁ * (1 + CS * C₀ * c + CS * C₀), fun J S DJ ξ η h hco hJ2 hJM hSM hη => ?_⟩
  have hμ₀ : volume.restrict (W₀ : Set ℂ) ≤ volume.restrict Ω := Measure.restrict_mono hW₀le le_rfl
  have hμ₁ : volume.restrict (W₁ : Set ℂ) ≤ volume.restrict Ω :=
    Measure.restrict_mono (hW₁W₀.trans hW₀le) le_rfl
  have hηr' : MemLpLoc (p⁻¹ + s⁻¹)⁻¹ W₀ η := (hη.mono_set hW₀le).mono_exponent hr'r
  -- The solution is in `L^{s'}_loc` on `W₀`, by the qualitative order-zero lemma.
  have hξs' : MemLpLoc s' W₀ ξ := MemWkpLoc.memLpLoc_of_forall_exists_eLpNorm_le
    ((h.mono hW₀le).memWkpLoc_one (hco.mono hW₀le) hp
    (ae_mono hμ₀ hJ2) hr'1 hr'_top (by rw [inv_inv]) hηr') hest
  have h₁ := hC₁ J S DJ ξ η ((h.mono (hW₁W₀.trans hW₀le)).of_memLpLoc (hξs'.mono_set hW₁W₀))
    (hco.mono (hW₁W₀.trans hW₀le)) (ae_mono hμ₁ hJ2)
    ((eLpNormWkp_mono_set (hW₁W₀.trans hW₀le)).trans hJM)
    ((eLpNorm_mono_measure _ hμ₁).trans hSM) (hη.mono_set (hW₁W₀.trans hW₀le))
  have h₀ := hC₀ J S DJ ξ η (h.mono hW₀le) (hco.mono hW₀le) (ae_mono hμ₀ hJ2)
    ((eLpNormWkp_mono_set hW₀le).trans hJM) ((eLpNorm_mono_measure _ hμ₀).trans hSM) hηr'
  set a := eLpNorm η r (volume.restrict Ω)
  set b := eLpNorm ξ s (volume.restrict Ω)
  calc eLpNormWkp r U 1 ξ
      ≤ C₁ * (eLpNorm η r (volume.restrict W₁) + eLpNorm ξ s' (volume.restrict W₁)) := h₁
    -- the Sobolev or Morrey estimate on `W₁ ⋐ W`
    _ ≤ C₁ * (a + CS * eLpNormWkp (p⁻¹ + s⁻¹)⁻¹ W 1 ξ) := by
      gcongr
      exacts [eLpNorm_mono_measure _ hμ₁, hCS ξ]
    -- the order-zero estimate on `W ⋐ W₀`
    _ ≤ C₁ * (a + CS * (C₀ * (eLpNorm η (p⁻¹ + s⁻¹)⁻¹ (volume.restrict W₀) +
          eLpNorm ξ s (volume.restrict W₀)))) := by gcongr
    -- the comparison of `L^{r'}(W₀)` with `Lʳ(W₀)`
    _ ≤ C₁ * (a + CS * (C₀ * (c * a + b))) := by
      gcongr
      exacts [(hc η).trans (by gcongr; exact eLpNorm_mono_measure _ hμ₀),
        eLpNorm_mono_measure _ hμ₀]
    _ = C₁ * (a + CS * C₀ * (c * a + b)) := by ring
    _ ≤ C₁ * (1 + CS * C₀ * c + CS * C₀) * (a + b) := mul_add_mul_le_mul_mul_add _ _ _ _ _
    _ = ↑(C₁ * (1 + CS * C₀ * c + CS * C₀)) * (a + b) := by push_cast; ring

/-- The estimate ladder, by induction on the number `n` of rungs: if `1/s ≤ 1/q` and
`1/s ≤ 1/r - 1/p + n d` with `d = (1/2 - 1/p) / 2`, the estimate holds for solutions in
`Lˢ_loc`. -/
private theorem hasCREstimate_of_inv_le_add_mul [FiniteDimensional ℝ V] (hp : 2 < p)
    (hpq : p⁻¹ + q⁻¹ < 1) (hr : 1 < r) (hr_top : r ≠ ⊤) (hrp : r ≤ p) (M : ℝ≥0) (n : ℕ) :
    ∀ (Ω : Opens ℂ) (s : ℝ≥0∞) (U : Set ℂ), s⁻¹ ≤ q⁻¹ →
      s⁻¹ ≤ r⁻¹ - p⁻¹ + n * ((2⁻¹ - p⁻¹) / 2) → IsCompact (closure U) → closure U ⊆ Ω →
      HasCREstimate V p r s M Ω U := by
  set d : ℝ≥0∞ := (2⁻¹ - p⁻¹) / 2
  induction n with
  | zero =>
    intro Ω s U _ hsn hUc hUΩ
    rw [Nat.cast_zero, zero_mul, add_zero] at hsn
    exact exists_eLpNormWkp_one_le_of_isWeakCRSolution hp
      (add_le_of_le_tsub_left_of_le (ENNReal.inv_le_inv.2 hrp) hsn) hr hr_top hUc hUΩ M
  | succ n ih =>
    intro Ω s U hsq hsn hUc hUΩ
    by_cases hsr : p⁻¹ + s⁻¹ ≤ r⁻¹
    · exact exists_eLpNormWkp_one_le_of_isWeakCRSolution hp hsr hr hr_top hUc hUΩ M
    rw [not_le] at hsr
    have hr'1 : 1 < (p⁻¹ + s⁻¹)⁻¹ := ENNReal.one_lt_inv.2 ((add_le_add le_rfl hsq).trans_lt hpq)
    obtain ⟨s', hs's, hest⟩ :=
      exists_inv_le_inv_sub_and_eLpNorm_le_mul_eLpNormWkp_one (F := V) hp hr'1.le
    refine hasCREstimate_of_rung hp hr_top M hr'1
      (ENNReal.inv_le_inv.1 (by rw [inv_inv]; exact hsr.le)) hest
      (fun Ω' U' hU'c hU'Ω' => ih Ω' s' U' (hs's.trans (tsub_le_self.trans hsq)) ?_ hU'c hU'Ω')
      hUc hUΩ
    refine hs's.trans ?_
    rw [tsub_le_iff_right]
    calc s⁻¹ ≤ r⁻¹ - p⁻¹ + ↑(n + 1) * d := hsn
      _ = r⁻¹ - p⁻¹ + ↑n * d + d := by push_cast; ring

/-- **The interior `W^{1,r}` estimate** (McDuff–Salamon, Lemmas B.4.4 and B.4.6). Let `V` be
finite-dimensional, `p > 2`, `1/p + 1/q < 1`, `1 < r < ∞` and `r ≤ p`, let `U` have compact
closure in `Ω`, and let `M ≥ 0`. There is a constant `C` such that for all coefficients
`J ∈ W^{1,p}(Ω)` with `J² = -1` almost everywhere and `S ∈ Lᵖ(Ω)` with `‖J‖_{W^{1,p}(Ω)} ≤ M` and
`‖S‖_{Lᵖ(Ω)} ≤ M`, every weak solution `ξ ∈ L^q_loc` of `∂_s ξ + J ∂_t ξ + S ξ = η` on `Ω` with
`η ∈ Lʳ_loc` satisfies `‖ξ‖_{W^{1,r}(U)} ≤ C (‖η‖_{Lʳ(Ω)} + ‖ξ‖_{L^q(Ω)})`.

This is the estimate accompanying `TauCeti.IsWeakCRSolution.memWkpLoc_one_of_le`: taking `r = q`
when `q ≤ p` and `q < ∞` gives `‖ξ‖_{W^{1,q}(U)} ≤ C (‖η‖_{L^q(Ω)} + ‖ξ‖_{L^q(Ω)})`. The constant
depends only on `p`, `q`, `r`, `U`, `Ω`, `V` and `M`, so one constant serves every pair `(J, S)`
in a bounded set. -/
theorem exists_eLpNormWkp_one_le_of_isWeakCRSolution_of_le [FiniteDimensional ℝ V] (hp : 2 < p)
    (hpq : p⁻¹ + q⁻¹ < 1) (hr : 1 < r) (hr_top : r ≠ ⊤) (hrp : r ≤ p) {U : Set ℂ}
    (hUc : IsCompact (closure U)) (hUΩ : closure U ⊆ Ω) (M : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (J S : ℂ → V →L[ℝ] V) (DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V) (ξ η : ℂ → V),
      IsWeakCRSolution q Ω J DJ S ξ η → IsSobolevCRCoefficients p Ω J DJ S →
      (∀ᵐ z ∂volume.restrict Ω, J z * J z = -1) → eLpNormWkp p Ω 1 J ≤ M →
      eLpNorm S p (volume.restrict Ω) ≤ M → MemLpLoc r Ω η →
      eLpNormWkp r U 1 ξ ≤ C * (eLpNorm η r (volume.restrict Ω) +
        eLpNorm ξ q (volume.restrict Ω)) := by
  have hd : 0 < (2⁻¹ - p⁻¹) / 2 :=
    ENNReal.div_pos (tsub_pos_of_lt (ENNReal.inv_lt_inv.2 hp)).ne' ENNReal.ofNat_ne_top
  have hq_top : q⁻¹ ≠ ⊤ := ((le_add_self.trans_lt hpq).trans ENNReal.one_lt_top).ne
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (ENNReal.div_ne_top hq_top hd.ne')
  exact hasCREstimate_of_inv_le_add_mul hp hpq hr hr_top hrp M n Ω q U le_rfl
    (((ENNReal.div_le_iff hd.ne' (ENNReal.div_ne_top (by finiteness) two_ne_zero)).1
      hn.le).trans le_add_self) hUc hUΩ

end TauCeti
