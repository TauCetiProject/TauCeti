/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Bounded
public import TauCeti.RingTheory.PowerSeries.OpenDisc.Eval

/-!
# Bounded series on the open disc

A power series whose weighted coefficient norms `‖aₙ‖ R₀ⁿ` are bounded lies on the open disc of
radius `R₀`, so the bounded series of `TauCeti.RingTheory.PowerSeries.Bounded` sit between their
two neighbouring coefficient algebras:

`IsRestricted.subring R₀ ≤ HasGaussNorm.subring R R₀ ≤ OnOpenDisc.subring R R₀`.

The second inclusion is uniformly continuous for the topology of the Gauss norms at all radii
below `R₀`, each of which is bounded by the Gauss norm at `R₀`. Composing with evaluation of
series on the open disc, a bounded series is evaluated continuously at every point `b` with
`‖b‖ < R₀` of a complete normed algebra, and in an ultrametric algebra with `‖1‖ = 1` its value is
bounded by its Gauss norm. The inclusion is not onto in general: over `ℚ_p` the series
`log (1 + X)` lies on the open unit disc (`PowerSeries.onOpenDisc_log`) but has unbounded
coefficients (`TauCeti.not_bddAbove_norm_coeff_log`).

## Main results

* `PowerSeries.HasGaussNorm.subring_le_onOpenDiscSubring`: the inclusion into series on the open
  disc.
* `TauCeti.PowerSeries.HasGaussNorm.uniformContinuous_inclusion_onOpenDiscSubring`: the inclusion
  into series on the open disc is uniformly continuous.
* `TauCeti.PowerSeries.HasGaussNorm.norm_evalAt_le` and
  `TauCeti.PowerSeries.HasGaussNorm.continuous_evalAtHom_comp_inclusion`: evaluation at a point of
  the open disc is bounded by the Gauss norm in an ultrametric algebra, and continuous in any
  complete normed algebra.

## References

* Y. Amice, *Interpolation p-adique*, Bull. Soc. Math. France 92 (1964), 117–180.
* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4.
-/

public section

namespace PowerSeries

variable {R : Type*} [NormedRing R] [IsUltrametricDist R] {R₀ : ℝ} [Fact (0 < R₀)]

/-- A series with bounded weighted coefficient norms at the radius `R₀` lies on the open disc of
radius `R₀`. -/
theorem HasGaussNorm.subring_le_onOpenDiscSubring :
    HasGaussNorm.subring R R₀ ≤ OnOpenDisc.subring R R₀ :=
  fun _ hf ↦ OnOpenDisc.mem_subring.mpr (HasGaussNorm.mem_subring.mp hf).onOpenDisc

end PowerSeries

namespace TauCeti.PowerSeries.HasGaussNorm

open _root_.PowerSeries

section NormedRing

variable {R : Type*} [NormedRing R] [IsUltrametricDist R] {R₀ : ℝ} [Fact (0 < R₀)]

-- Supply the positivity witness used by the Gauss-norm instances on each smaller closed disc.
attribute [local instance] TauCeti.PowerSeries.OnOpenDisc.radius_pos

/-- The inclusion of bounded series into series on the open disc of the same radius is uniformly
continuous: the Gauss norm at each smaller radius is bounded by the Gauss norm at `R₀`. -/
theorem uniformContinuous_inclusion_onOpenDiscSubring :
    UniformContinuous (Subring.inclusion
      (HasGaussNorm.subring_le_onOpenDiscSubring (R := R) (R₀ := R₀))) := by
  refine OnOpenDisc.uniformContinuous_iff.mpr fun r ↦ ?_
  refine AddMonoidHomClass.uniformContinuous_of_bound ((OnOpenDisc.restrict r).toAddMonoidHom.comp
    (Subring.inclusion HasGaussNorm.subring_le_onOpenDiscSubring).toAddMonoidHom) 1 fun f ↦ ?_
  rw [one_mul, TauCeti.PowerSeries.norm_eq_gaussNorm, norm_eq_gaussNorm]
  simpa using TauCeti.PowerSeries.gaussNorm_le_gaussNorm_of_le (fun _ ↦ norm_nonneg _)
    r.2.1.le r.2.2.le (HasGaussNorm.mem_subring.mp f.2)

/-- The inclusion of bounded series into series on the open disc of the same radius is
continuous. -/
theorem continuous_inclusion_onOpenDiscSubring :
    Continuous (Subring.inclusion
      (HasGaussNorm.subring_le_onOpenDiscSubring (R := R) (R₀ := R₀))) :=
  uniformContinuous_inclusion_onOpenDiscSubring.continuous

end NormedRing

section NormedCommRing

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] {R₀ : ℝ} [Fact (0 < R₀)]
  {A : Type*} [NormedRing A] [Algebra R A] [IsBoundedSMul R A] {b : A}

/-- In an ultrametric normed algebra with `‖1‖ = 1`, the value of a bounded series at a point `b`
with `‖b‖ ≤ R₀` is bounded by its Gauss norm. -/
theorem norm_evalAt_le [IsUltrametricDist A] [NormOneClass A] (f : HasGaussNorm.subring R R₀)
    (hb : ‖b‖ ≤ R₀) : ‖(f : R⟦X⟧).evalAt b‖ ≤ ‖f‖ :=
  norm_evalAt_le_gaussNorm (HasGaussNorm.mem_subring.mp f.2) hb

/-- Evaluation of bounded series at a point `b` with `‖b‖ < R₀` of a complete normed algebra,
through the series on the open disc of radius `R₀`, is continuous for the Gauss norm. -/
theorem continuous_evalAtHom_comp_inclusion [CompleteSpace A] (hb : ‖b‖ < R₀) :
    Continuous ((OnOpenDisc.evalAtHom R hb).comp
      (Subring.inclusion HasGaussNorm.subring_le_onOpenDiscSubring)) :=
  (TauCeti.PowerSeries.OnOpenDisc.continuous_evalAtHom hb).comp
    continuous_inclusion_onOpenDiscSubring

end NormedCommRing

end TauCeti.PowerSeries.HasGaussNorm
