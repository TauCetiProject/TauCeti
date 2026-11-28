/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import TauCeti.MeasureTheory.Function.BoundedMeanOscillation

import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.WeakDeriv
import TauCeti.MeasureTheory.Function.LpSeminorm.Ball

/-!
# The borderline embedding `W^{1,n} ⊆ VMO ⊆ BMO` for weakly differentiable functions

Let `E` be a finite-dimensional real normed space of positive dimension `n` with an additive Haar
measure `μ`, let `F` be a real Banach space, and let `u : E → F` be globally weakly differentiable
(`TauCeti.HasWeakFDerivOn μ ⊤ u Du`). By the scale-invariant Poincaré–Wirtinger inequality at the
borderline exponent `p = n` (`TauCeti.HasWeakFDerivOn.setLAverage_enorm_sub_setAverage_ball_le`),
the mean oscillation of `u` on every ball `B(c, r)` is controlled by `‖Du‖_{Lⁿ(B(c, r))}` with a
constant independent of the radius `r`. Consequently, if `Du ∈ Lⁿ(μ)`, then `u` has bounded mean
oscillation (`TauCeti.HasWeakFDerivOn.memBMO`) and, by uniform vanishing of
`sup_c ‖Du‖_{Lⁿ(B(c, r))}` as `r → 0`
(`TauCeti.tendsto_zero_of_eventually_le_mul_iSup_eLpNorm_restrict_ball`), vanishing mean
oscillation (`TauCeti.HasWeakFDerivOn.memVMO`).

For the scalar inner-product-space `W^{1,p}(Ω)` version on arbitrary open sets `Ω` (including local
John–Nirenberg exponential integrability), see
`TauCeti.Analysis.Sobolev.W1p.BoundedMeanOscillation`.

## Main declarations

* `TauCeti.HasWeakFDerivOn.bmoSeminorm_le`: BMO seminorm bound for globally weakly differentiable
  functions in terms of `‖Du‖_{Lⁿ(μ)}`.
* `TauCeti.HasWeakFDerivOn.memBMO`: borderline embedding `W^{1,n} ⊆ BMO`.
* `TauCeti.HasWeakFDerivOn.vmoModulus_le`: VMO modulus bound at scale `r` in terms of
  `⨆ c, ‖Du‖_{Lⁿ(B(c, r))}`.
* `TauCeti.HasWeakFDerivOn.memVMO`: borderline embedding `W^{1,n} ⊆ VMO`.

## References

* H. Brezis, L. Nirenberg, *Degree theory and BMO; Part I: Compact manifolds without boundaries*,
  Selecta Math. (N.S.) **1** (1995), 197–263.
-/

public section

noncomputable section

namespace TauCeti

open Filter _root_.MeasureTheory Metric Module Set
open scoped ENNReal Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {u : E → F} {Du : E → E →L[ℝ] F}

/-- **BMO bound for globally weakly differentiable functions at the borderline exponent `p = n`.**
For any globally weakly differentiable function `u : E → F` in positive dimension `n`,
`bmoSeminorm u μ ≤ 2 ^ (n + 1) * ω ^ (-1 / n) * ‖Du‖_{Lⁿ(μ)}`. -/
theorem HasWeakFDerivOn.bmoSeminorm_le [Nontrivial E] (hu : HasWeakFDerivOn μ ⊤ u Du) :
    bmoSeminorm u μ ≤
      ENNReal.ofReal (2 ^ (finrank ℝ E + 1) * μ.real (ball 0 1) ^ (-(finrank ℝ E : ℝ)⁻¹)) *
        eLpNorm Du (finrank ℝ E) μ :=
  TauCeti.bmoSeminorm_le fun c r =>
    (hu.setLAverage_enorm_sub_setAverage_ball_le (x := c) (r := r) (subset_univ _)).trans
      (mul_le_mul_right (eLpNorm_mono_measure _ Measure.restrict_le_self) _)

/-- **Borderline embedding `W^{1,n} ⊆ BMO`.** A globally weakly differentiable function whose weak
derivative has finite `Lⁿ` seminorm has bounded mean oscillation. -/
theorem HasWeakFDerivOn.memBMO [Nontrivial E] (hu : HasWeakFDerivOn μ ⊤ u Du)
    (hDu : eLpNorm Du (finrank ℝ E) μ ≠ ∞) :
    MemBMO u μ :=
  memBMO_iff.2 ⟨locallyIntegrableOn_univ.1 hu.locallyIntegrableOn,
    hu.bmoSeminorm_le.trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 hDu))⟩

/-- **VMO modulus bound at the borderline exponent `p = n`.** For every radius `r`, the VMO modulus
of `u` at scale `r` is controlled by the supremum over all centres `c` of `‖Du‖_{Lⁿ(B(c, r))}`. -/
theorem HasWeakFDerivOn.vmoModulus_le [Nontrivial E] (hu : HasWeakFDerivOn μ ⊤ u Du) (r : ℝ) :
    vmoModulus u μ r ≤
      ENNReal.ofReal (2 ^ (finrank ℝ E + 1) * μ.real (ball 0 1) ^ (-(finrank ℝ E : ℝ)⁻¹)) *
        ⨆ c : E, eLpNorm Du (finrank ℝ E) (μ.restrict (ball c r)) :=
  TauCeti.vmoModulus_le fun c s hs =>
    (hu.setLAverage_enorm_sub_setAverage_ball_le (x := c) (r := s) (subset_univ _)).trans <|
      mul_le_mul_right
        ((eLpNorm_mono_measure _ (Measure.restrict_mono (ball_subset_ball hs) le_rfl)).trans
          (le_iSup (fun c' => eLpNorm Du (finrank ℝ E) (μ.restrict (ball c' r))) c)) _

/-- **Borderline embedding `W^{1,n} ⊆ VMO`.** A globally weakly differentiable function whose weak
derivative has finite `Lⁿ` seminorm has vanishing mean oscillation. -/
theorem HasWeakFDerivOn.memVMO [Nontrivial E] (hu : HasWeakFDerivOn μ ⊤ u Du)
    (hDu : eLpNorm Du (finrank ℝ E) μ ≠ ∞) :
    MemVMO u μ :=
  memVMO_iff_tendsto.2 ⟨hu.memBMO hDu,
    tendsto_zero_of_eventually_le_mul_iSup_eLpNorm_restrict_ball
      (Nat.cast_ne_zero.2 finrank_pos.ne') (ENNReal.natCast_ne_top _) hDu
      (tendsto_id.mono_left nhdsWithin_le_nhds) (.of_forall hu.vmoModulus_le)
      ENNReal.ofReal_ne_top⟩

end TauCeti

end
