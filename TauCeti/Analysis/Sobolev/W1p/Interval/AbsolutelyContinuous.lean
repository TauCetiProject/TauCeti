/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Interval.Representative
public import TauCeti.Analysis.Sobolev.W1p.Interval.Trace
public import TauCeti.Analysis.Sobolev.WeakDeriv.AbsolutelyContinuous
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# The absolutely continuous characterization of interval Sobolev classes

An absolutely continuous real function on `[a,b]` whose classical derivative belongs to `Lᵖ`
defines an element of `W1p volume (Ioo a b) p`, for every `1 ≤ p ≤ ∞`. Its value and gradient
agree almost everywhere with the function and its derivative. This is the converse to the
existing construction of absolutely continuous representatives of interval Sobolev classes.

The range of `W1p.intervalRepresentativeL` is exactly the continuous functions whose extension
by endpoint projection is absolutely continuous and has derivative in `Lᵖ(a,b)`. In
particular the characterization retains derivative integrability at `p = 2`; absolute
continuity alone does not characterize `H¹`. For finite `p`, such a function that vanishes at
both endpoints defines an element of `W^{1,p}_0(a,b)`.

## References

* G. Leoni, *A First Course in Sobolev Spaces*, Theorem 7.13.
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Theorem 8.2.
-/

public section

noncomputable section

open MeasureTheory Set Filter TopologicalSpace
open scoped ENNReal

namespace AbsolutelyContinuousOnInterval

variable {a b : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {f : ℝ → ℝ}

/-- An absolutely continuous function with classical derivative in `Lᵖ(a,b)` represents a
Sobolev class, including at `p = ∞`; the recorded weak gradient is its classical derivative
almost everywhere. -/
theorem exists_w1p_value_gradient_ae_eq (hf : AbsolutelyContinuousOnInterval f a b)
    (hdf : MemLp (deriv f) p (volume.restrict (Ioo a b))) :
    ∃ u : TauCeti.W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p,
      TauCeti.W1p.value u =ᵐ[volume.restrict (Ioo a b)] f ∧
      TauCeti.W1p.gradient u =ᵐ[volume.restrict (Ioo a b)] deriv f := by
  have hv : MemLp f p (volume.restrict (Ioo a b)) :=
    hf.continuousOn.memLp_restrict_of_subset_isCompact
      isCompact_uIcc measurableSet_Ioo (Ioo_subset_Icc_self.trans Icc_subset_uIcc) p
  have hw : TauCeti.HasWeakFDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ f
      (fun t ↦ innerSL ℝ (deriv f t)) := by
    apply TauCeti.hasWeakFDerivOn_iff.2
    intro v
    simpa [Pi.smul_def, smul_eq_mul, real_inner_comm, mul_comm] using
      hf.hasWeakLineDerivOn.smul_direction v
  refine ⟨TauCeti.W1p.mk (hv.toLp f) (hdf.toLp (deriv f))
    ((hw.congr_ae hv.coeFn_toLp.symm).congr_ae_deriv ?_), ?_, ?_⟩
  · filter_upwards [hdf.coeFn_toLp] with t ht
    rw [ht]
  · simpa only [TauCeti.W1p.value_mk] using hv.coeFn_toLp
  · simpa only [TauCeti.W1p.gradient_mk] using hdf.coeFn_toLp

end AbsolutelyContinuousOnInterval

namespace TauCeti.W1p

variable {a b : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every absolutely continuous real function with `Lᵖ` derivative is the representative of
exactly one interval Sobolev class. The equality includes both endpoint values. -/
theorem existsUnique_intervalRepresentativeL_eq (hab : a < b) {f : ℝ → ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hdf : MemLp (deriv f) p (volume.restrict (Ioo a b))) :
    ∃! u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p,
      ∀ t : Icc a b, intervalRepresentativeL hab u t = f t := by
  obtain ⟨u, hu, -⟩ := hf.exists_w1p_value_gradient_ae_eq hdf
  let w : C(Icc a b, ℝ) := ⟨fun t ↦ f t,
    (uIcc_of_le hab.le ▸ hf.continuousOn).domRestrict⟩
  have heq : intervalRepresentativeL hab u = w := by
    apply (intervalRepresentativeL_eq_iff hab u w).2
    filter_upwards [hu, ae_restrict_mem measurableSet_Ioo] with t ht hmem
    rw [projIcc_of_mem hab.le (Ioo_subset_Icc_self hmem)]
    exact ht
  refine ⟨u, fun t ↦ congrArg (fun g : C(Icc a b, ℝ) ↦ g t) heq, ?_⟩
  intro v hv
  apply intervalRepresentativeL_injective hab
  ext t
  exact (hv t).trans ((congrArg (fun g : C(Icc a b, ℝ) ↦ g t) heq).symm)

/-- Characterization of the range of the continuous-representative map. The projection
extends a function on `[a,b]` by constants outside the interval and imposes no extra endpoint
differentiability requirement. -/
-- Rewrite before simplification of range membership and the open-set coercion in the carrier.
@[simp↓]
theorem mem_range_intervalRepresentativeL_iff (hab : a < b) (w : C(Icc a b, ℝ)) :
    w ∈ Set.range (intervalRepresentativeL (p := p) hab) ↔
      AbsolutelyContinuousOnInterval (fun t ↦ w (projIcc a b hab.le t)) a b ∧
      MemLp (deriv (fun t ↦ w (projIcc a b hab.le t))) p
        (volume.restrict (Ioo a b)) := by
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨absolutelyContinuousOnInterval_intervalRepresentativeL hab u, ?_⟩
    apply (Lp.memLp (gradient u)).ae_eq
    apply (ae_restrict_iff' measurableSet_Ioo).2
    filter_upwards [ae_hasDerivAt_intervalRepresentativeL hab u] with t ht hmem
    exact (ht (uIoc_of_le hab.le ▸ Ioo_subset_Ioc_self hmem)).deriv.symm
  · rintro ⟨hw, hdw⟩
    obtain ⟨u, hu, -⟩ := existsUnique_intervalRepresentativeL_eq hab hw hdw
    refine ⟨u, ?_⟩
    ext t
    simpa only [projIcc_of_mem hab.le t.property] using hu t

end TauCeti.W1p

namespace AbsolutelyContinuousOnInterval

variable {a b : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {f : ℝ → ℝ}

/-- For `p < ∞`, an absolutely continuous function with classical derivative in `Lᵖ(a,b)` that
vanishes at both endpoints defines an element of `W^{1,p}_0(a,b)`, whose value and gradient agree
almost everywhere with the function and its derivative. -/
theorem exists_w1p0_value_gradient_ae_eq (hp : p ≠ ∞) (hab : a < b)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hdf : MemLp (deriv f) p (volume.restrict (Ioo a b))) (ha : f a = 0) (hb : f b = 0) :
    ∃ v : TauCeti.W1p0 volume ⟨Ioo a b, isOpen_Ioo⟩ p,
      TauCeti.W1p.value (v : TauCeti.W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p)
          =ᵐ[volume.restrict (Ioo a b)] f ∧
        TauCeti.W1p.gradient (v : TauCeti.W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p)
          =ᵐ[volume.restrict (Ioo a b)] deriv f := by
  obtain ⟨u, hu, hgu⟩ := hf.exists_w1p_value_gradient_ae_eq hdf
  let w : C(Icc a b, ℝ) := ⟨fun t ↦ f t, (uIcc_of_le hab.le ▸ hf.continuousOn).domRestrict⟩
  have heq : TauCeti.W1p.intervalRepresentativeL hab u = w := by
    refine (TauCeti.W1p.intervalRepresentativeL_eq_iff hab u w).2 ?_
    filter_upwards [hu, ae_restrict_mem measurableSet_Ioo] with t ht hmem
    rw [projIcc_of_mem hab.le (Ioo_subset_Icc_self hmem)]
    exact ht
  have hmem : u ∈ TauCeti.w1p0Submodule volume ⟨Ioo a b, isOpen_Ioo⟩ p := by
    rw [TauCeti.W1p.mem_w1p0Submodule_iff_intervalTraceL_eq_zero hp hab,
      TauCeti.W1p.intervalTraceL_apply, heq]
    exact Prod.ext ha hb
  exact ⟨⟨u, hmem⟩, hu, hgu⟩

end AbsolutelyContinuousOnInterval
