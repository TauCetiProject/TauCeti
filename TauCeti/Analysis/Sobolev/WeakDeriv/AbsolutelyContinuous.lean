/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Interval

/-!
# Weak derivatives of absolutely continuous curves

An absolutely continuous curve in a finite-dimensional real normed space has its classical
almost-everywhere derivative as a weak derivative on the open interval. Together with the
continuous-representative theorem, this gives the one-dimensional identification of weakly
differentiable functions with absolutely continuous representatives.

The proof uses the finite-dimensional fundamental theorem of calculus in
`TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun` and the existing
weak derivative of an integral primitive.

## References

* G. Leoni, *A First Course in Sobolev Spaces*, Theorem 7.13.
-/

public section

open MeasureTheory Set Filter

namespace AbsolutelyContinuousOnInterval

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {a b : ℝ} {f : ℝ → F}

/-- The classical derivative of an absolutely continuous finite-dimensional curve is its
weak derivative on the open interval. No integrability hypothesis beyond absolute continuity
is needed. -/
theorem hasWeakLineDerivOn (hf : AbsolutelyContinuousOnInterval f a b) :
    TauCeti.HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ f (deriv f) 1 := by
  rcases le_or_gt b a with hba | hab
  · have h0 : volume.restrict (Ioo a b) = 0 := by simp [Ioo_eq_empty_of_le hba]
    exact (TauCeti.hasWeakLineDerivOn_zero.congr_ae (by simp [h0, EventuallyEq])).congr_ae_deriv
      (by simp [h0, EventuallyEq])
  have hint := hf.intervalIntegrable_deriv_of_finiteDimensional
  have h := (TauCeti.hasWeakLineDerivOn_const
    (μ := volume) (Ω := ⟨Ioo a b, isOpen_Ioo⟩) (v := 1) (f a)).add
      (TauCeti.hasWeakLineDerivOn_intervalIntegral_left
        ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).1 hint))
  refine (h.congr_ae ?_).congr_ae_deriv (EventuallyEq.of_eq (zero_add _))
  apply (ae_restrict_iff' measurableSet_Ioo).2
  exact Eventually.of_forall fun t ht ↦ by
    have hsub : uIcc a t ⊆ uIcc a b :=
      uIcc_subset_uIcc left_mem_uIcc (Icc_subset_uIcc (Ioo_subset_Icc_self ht))
    simp only [Pi.add_apply]
    rw [(hf.mono hsub).integral_deriv_eq_sub_of_finiteDimensional]
    exact add_sub_cancel _ _

end AbsolutelyContinuousOnInterval
