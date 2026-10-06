/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Basic
public import TauCeti.MeasureTheory.Integral.IntegralEqImproper

/-!
# Tail integrals of completely monotone functions

If `f` is completely monotone on `(0, ∞)` and its integral over one positive tail is finite,
then `t ↦ ∫ s in Ioi t, f s` is completely monotone on `(0, ∞)`. Its derivative is `-f`, so
integration shifts the alternating derivative signs by one order. This gives an integral
closure operation that complements the closure under negated derivatives.

Integrability over `(0, ∞)` further makes the tail integral continuous on `[0, ∞)`, including
when `f` itself has a singularity at the origin. The open-ray result only needs integrability
of one positive tail, so it also applies to functions such as `t ↦ t⁻²`.

## Main declarations

* `TauCeti.IsCompletelyMonotoneOnIoi.integral_Ioi`: complete monotonicity of positive tail
  integrals.
* `TauCeti.IsCompletelyMonotoneOnIoi.isContinuousCompletelyMonotoneOnIoi_integral_Ioi`:
  integrability at the origin gives the closed-half-line continuity clause.

The derivatives are given by `MeasureTheory.IntegrableOn.hasDerivAt_integral_Ioi` and
`MeasureTheory.IntegrableOn.iteratedDeriv_integral_Ioi`. Continuity at the origin comes from
Mathlib's `MeasureTheory.IntegrableOn.continuousOn_Ici_primitive_Ioi`.

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*
  (de Gruyter, 2nd ed. 2012), Chapter 1.
-/

public section

open Set Filter MeasureTheory intervalIntegral
open scoped ContDiff Topology

namespace TauCeti.IsCompletelyMonotoneOnIoi

variable {f : ℝ → ℝ}

/-- Positive tail integration preserves complete monotonicity on `(0, ∞)` whenever one
positive tail is integrable. Integrability or continuity at the origin is unnecessary. -/
theorem integral_Ioi (hf : IsCompletelyMonotoneOnIoi f)
    (hint : ∃ a > 0, IntegrableOn f (Ioi a)) :
    IsCompletelyMonotoneOnIoi (fun t ↦ ∫ s in Ioi t, f s) := by
  obtain ⟨a, _, hinta⟩ := hint
  have hint : ∀ t > 0, IntegrableOn f (Ioi t) := by
    intro t ht
    have hcont : ContinuousOn f (Ici t) :=
      hf.contDiffOn.continuousOn.mono (Ici_subset_Ioi.mpr ht)
    exact (integrableOn_Ici_iff_integrableAtFilter_atTop.mpr
      ⟨⟨Ioi a, Ioi_mem_atTop a, hinta⟩,
        hcont.locallyIntegrableOn measurableSet_Ici⟩).mono_set Ioi_subset_Ici_self
  have hderiv : ∀ t > 0, HasDerivAt (fun u ↦ ∫ s in Ioi u, f s) (-f t) t := by
    intro t ht
    exact (hint (t / 2) (by linarith)).hasDerivAt_integral_Ioi
      (hf.contDiffOn.continuousOn.continuousAt (isOpen_Ioi.mem_nhds ht)) (by linarith)
  refine ⟨?_, fun n t ht ↦ ?_⟩
  · rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun t ht ↦
      (hderiv t ht).differentiableAt.differentiableWithinAt, ?_⟩
    exact hf.contDiffOn.neg.congr fun t ht ↦ (hderiv t ht).deriv
  · cases n with
    | zero =>
        simp only [pow_zero, one_mul, iteratedDeriv_zero]
        exact integral_nonneg_of_ae
          ((ae_restrict_mem measurableSet_Ioi).mono fun s hs ↦ hf.nonneg (ht.trans hs))
    | succ n =>
        rw [(hint (t / 2) (by linarith)).iteratedDeriv_integral_Ioi
          (hf.contDiffOn.continuousOn.mono (Ioi_subset_Ioi (by linarith))) n
          (by linarith : t / 2 < t), pow_succ]
        simpa using hf.neg_one_pow_mul_iteratedDeriv_nonneg n ht

/-- If a completely monotone function on `(0, ∞)` is integrable there, its tail integral is
continuous on `[0, ∞)` and completely monotone on `(0, ∞)`. The integrand need not be
continuous or bounded at the origin. -/
theorem isContinuousCompletelyMonotoneOnIoi_integral_Ioi
    (hf : IsCompletelyMonotoneOnIoi f) (hint : IntegrableOn f (Ioi 0)) :
    IsContinuousCompletelyMonotoneOnIoi (fun t ↦ ∫ s in Ioi t, f s) :=
  isContinuousCompletelyMonotoneOnIoi_iff.mpr
    ⟨hint.continuousOn_Ici_primitive_Ioi,
      hf.integral_Ioi ⟨1, zero_lt_one, hint.mono_set (Ioi_subset_Ioi zero_le_one)⟩⟩

end TauCeti.IsCompletelyMonotoneOnIoi
