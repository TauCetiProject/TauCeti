/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.RowCompact
public import TauCeti.RingTheory.PowerSeries.Entire.Eval

/-!
# Entire functions of row-compact operators

An entire power series with zero constant coefficient takes row-compact operators to
row-compact operators. More generally, its value differs from its constant scalar operator by
a row-compact operator. On an infinite model space the constant coefficient must vanish:
`B(u)` is row compact if and only if `B(0) = 0`. In particular, the constant function one
cannot be used in compact spectral mapping on an infinite model space.

The evaluation is the existing `PowerSeries.evalAt` in the complete endomorphism algebra,
with the ring-scalar operator norm. No new operator functional calculus is introduced.
The limit criterion `ContinuousLinearMap.IsRowCompact.of_tendsto_opNorm_sum_pow` also applies
to power series known to converge at the operator without being entire.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127**
  (1997), 417–479, Appendix A3–A4.
-/

public section

open Filter Finset Topology
open scoped ZeroAtInfty TauCeti.RingOpNorm PowerSeries

namespace ContinuousLinearMap

variable {I R : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [NormedCommRing R] [IsUltrametricDist R] [TauCeti.NormedRing.IsTate R]
  {u : C₀(I, R) →L[R] C₀(I, R)}

variable [CompleteSpace R] {B : R⟦X⟧}

/-- Evaluating an entire series with zero constant term at a row-compact operator preserves
row compactness, over complete ultrametric Tate rings. -/
theorem IsRowCompact.evalAt (hu : u.IsRowCompact) (hB : B.IsEntire)
    (hB0 : PowerSeries.constantCoeff B = 0) :
    (B.evalAt u).IsRowCompact := by
  apply hu.of_tendsto_opNorm_sum_pow (b := fun n ↦ PowerSeries.coeff n B)
    ((PowerSeries.coeff_zero_eq_constantCoeff_apply B).trans hB0)
  simpa only [norm_sub_rev] using
    tendsto_iff_norm_sub_tendsto_zero.mp (hB.hasSum_evalAt u).tendsto_sum_nat

/-- The nonconstant part of an entire function of a row-compact operator is row compact. -/
theorem IsRowCompact.evalAt_sub_constantCoeff (hu : u.IsRowCompact) (hB : B.IsEntire) :
    (B.evalAt u - PowerSeries.constantCoeff B • (1 : C₀(I, R) →L[R] C₀(I, R))).IsRowCompact := by
  have h := hu.evalAt (hB.sub (PowerSeries.isEntire_C (PowerSeries.constantCoeff B)))
    (by simp)
  have heq : (B - PowerSeries.C (PowerSeries.constantCoeff B)).evalAt u =
      B.evalAt u - PowerSeries.constantCoeff B • (1 : C₀(I, R) →L[R] C₀(I, R)) :=
    (hB.evalAt_sub (PowerSeries.isEntire_C _) u).trans
      (congrArg (fun t ↦ B.evalAt u - t) (PowerSeries.evalAt_C _ u))
  rwa [heq] at h

/-- An entire function of a row-compact operator is row compact exactly when its constant
scalar operator is row compact. This also covers finite and empty model spaces. -/
theorem IsRowCompact.isRowCompact_evalAt_iff (hu : u.IsRowCompact) (hB : B.IsEntire) :
    (B.evalAt u).IsRowCompact ↔
      (PowerSeries.constantCoeff B • (1 : C₀(I, R) →L[R] C₀(I, R))).IsRowCompact := by
  have h := hu.evalAt_sub_constantCoeff hB
  constructor
  · intro hv
    have heq : B.evalAt u - (B.evalAt u - PowerSeries.constantCoeff B • 1) =
        PowerSeries.constantCoeff B • (1 : C₀(I, R) →L[R] C₀(I, R)) :=
      sub_sub_cancel (B.evalAt u) (PowerSeries.constantCoeff B • 1)
    simpa only [heq] using hv.sub h
  · intro hc
    have heq : B.evalAt u - PowerSeries.constantCoeff B • 1 +
        PowerSeries.constantCoeff B • (1 : C₀(I, R) →L[R] C₀(I, R)) = B.evalAt u :=
      sub_add_cancel (B.evalAt u) (PowerSeries.constantCoeff B • 1)
    simpa only [heq] using h.add hc

/-- On an infinite model space the zero constant coefficient condition for compact entire
functional calculus is necessary as well as sufficient. This holds even for nonunit scalars
and coefficient rings with nilpotents. -/
theorem IsRowCompact.isRowCompact_evalAt_iff_constantCoeff_eq_zero [Infinite I]
    (hu : u.IsRowCompact) (hB : B.IsEntire) :
    (B.evalAt u).IsRowCompact ↔ PowerSeries.constantCoeff B = 0 := by
  rw [hu.isRowCompact_evalAt_iff hB]
  exact isRowCompact_smul_id_iff _

end ContinuousLinearMap
