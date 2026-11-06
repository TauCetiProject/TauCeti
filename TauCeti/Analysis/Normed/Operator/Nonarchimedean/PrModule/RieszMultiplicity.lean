/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszProjection.Multiplicity
public import TauCeti.LinearAlgebra.End.Retract

/-!
# Multiplicity of Fredholm zeros on modules with property (Pr)

For a row-compact endomorphism `u` of a module with property (Pr), a good zero `a` of
order `h` of its Fredholm series has a stabilized generalized eigenspace of constant
rank `h`. Over a field, its dimension is `h`. The same formulas apply to the range of
any Riesz projection at that zero.

These statements transport the model-space multiplicity theorem
`ContinuousLinearMap.IsRieszProjection.rankAtStalk_range` through a continuous linear
retract. The kernel comparison uses only the inclusion and retraction, not a basis or a
finite free complement. Computing ranks at prime ideals retains coefficient rings with
nilpotents. Order zero, exponent zero, and the zero module are included.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §7, Proposition 12.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.2, Theorem 2.2.2.
-/

public section

open scoped ZeroAtInfty

namespace ContinuousLinearMap

section Ring

variable {R M : Type*} [NormedCommRing R] [NormOneClass R] [IsUltrametricDist R]
  [CompleteSpace R] [TauCeti.NormedRing.IsTate R]
  [SeminormedAddCommGroup M] [Module R M] [ContinuousConstSMul R M]
  {u E : M →L[R] M} {a : R} {h n : ℕ}

/-- At a good Fredholm zero of order `h`, every stabilized generalized eigenspace on a
module with property (Pr) has rank `h` at every prime ideal of the coefficient ring.
No Noetherianity or reducedness hypothesis is imposed. -/
theorem IsPrCompact.rankAtStalk_ker_pow (hu : u.IsPrCompact)
    (hH : u.charPowerSeries.IsGoodZero a h) (hn : h ≤ n) (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R)
      (LinearMap.ker (((1 - a • u) ^ n : M →L[R] M) : M →ₗ[R] M)) p = h := by
  classical
  obtain ⟨J, _, _, i, r, hri⟩ := (TauCeti.hasPr_def R M).mp hu.hasPr_source
  have hv := hu.isRowCompact_comp i r
  rw [hu.charPowerSeries_eq hri] at hH
  obtain ⟨hzero, hunit⟩ := PowerSeries.isGoodZero_iff.mp hH
  have hF := hv.isRieszProjection_rieszProjection hzero hunit
  -- Extension adds a zero block, so it does not change these spectral kernels.
  have hri' : r.toLinearMap.comp i.toLinearMap = LinearMap.id := by
    simpa only [toLinearMap_comp, coe_id] using
      congrArg ContinuousLinearMap.toLinearMap hri
  have hleft : LinearMap.ker (((1 - a • u) ^ n : M →L[R] M) : M →ₗ[R] M) =
      LinearMap.ker ((1 - a • u.toLinearMap) ^ n) := by
    simp only [toLinearMap_pow, toLinearMap_sub, toLinearMap_one, toLinearMap_smul]
  have hright : LinearMap.ker (((1 - a • i.comp (u.comp r)) ^ n :
        C₀(J, R) →L[R] C₀(J, R)) : C₀(J, R) →ₗ[R] C₀(J, R)) =
      LinearMap.ker ((1 - i.toLinearMap.comp ((a • u.toLinearMap).comp r.toLinearMap)) ^ n) := by
    simp only [toLinearMap_pow, toLinearMap_sub, toLinearMap_one, toLinearMap_smul,
      toLinearMap_comp, LinearMap.comp_smul, LinearMap.smul_comp]
  let heq := (LinearEquiv.ofEq _ _ hleft).trans
    ((LinearMap.kerOneSubPowEquivOfRetract (a • u.toLinearMap) hri' n).trans
      (LinearEquiv.ofEq _ _ hright).symm)
  have hker : Module.rankAtStalk (R := R)
      (LinearMap.ker (((1 - a • u) ^ n : M →L[R] M) : M →ₗ[R] M)) =
      Module.rankAtStalk (R := R)
        (LinearMap.ker (((1 - a • i.comp (u.comp r)) ^ n :
          C₀(J, R) →L[R] C₀(J, R)) : C₀(J, R) →ₗ[R] C₀(J, R))) := by
    -- Fixing the additive groups selects the submodule, rather than normed, structures.
    let : AddCommGroup (LinearMap.ker (((1 - a • u) ^ n : M →L[R] M) : M →ₗ[R] M)) :=
      inferInstance
    let : AddCommGroup (LinearMap.ker (((1 - a • i.comp (u.comp r)) ^ n :
        C₀(J, R) →L[R] C₀(J, R)) : C₀(J, R) →ₗ[R] C₀(J, R))) := inferInstance
    exact Module.rankAtStalk_eq_of_equiv heq
  rw [hker, hF.ker_pow_eq hn, ← hF.range_eq_ker]
  exact hF.rankAtStalk_range hv hH p

/-- The range of any Riesz projection at a good Fredholm zero on a module with property
(Pr) has constant rank equal to the order of that zero. -/
theorem IsRieszProjection.rankAtStalk_range_of_isPrCompact [IsBoundedSMul R M]
    (hE : IsRieszProjection u a h E) (hu : u.IsPrCompact)
    (hH : u.charPowerSeries.IsGoodZero a h) (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) E.range p = h := by
  rw [hE.range_eq_ker]
  exact hu.rankAtStalk_ker_pow hH le_rfl p

end Ring

section Field

variable {K M : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [SeminormedAddCommGroup M] [Module K M] [ContinuousConstSMul K M]
  {u E : M →L[K] M} {a : K} {h n : ℕ}

/-- Over a complete ultrametric field, a good Fredholm zero of order `h` on a module
with property (Pr) has stabilized generalized eigenspaces of dimension `h`. -/
theorem IsPrCompact.finrank_ker_pow (hu : u.IsPrCompact)
    (hH : u.charPowerSeries.IsGoodZero a h) (hn : h ≤ n) :
    Module.finrank K (LinearMap.ker (((1 - a • u) ^ n : M →L[K] M) : M →ₗ[K] M)) = h := by
  have hr := hu.rankAtStalk_ker_pow hH hn ⟨⊥, Ideal.isPrime_bot⟩
  simpa using hr

/-- The range of a Riesz projection on a module with property (Pr) has dimension equal
to the order of the good Fredholm zero. This includes order zero. -/
theorem IsRieszProjection.finrank_range_of_isPrCompact [IsBoundedSMul K M]
    (hE : IsRieszProjection u a h E) (hu : u.IsPrCompact)
    (hH : u.charPowerSeries.IsGoodZero a h) : Module.finrank K E.range = h := by
  rw [hE.range_eq_ker]
  exact hu.finrank_ker_pow hH le_rfl

end Field

end ContinuousLinearMap
