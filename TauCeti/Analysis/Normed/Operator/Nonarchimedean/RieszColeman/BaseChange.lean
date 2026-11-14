/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.BaseChange
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszColeman.Factorization
import TauCeti.RingTheory.Polynomial.Resultant.Coleman

/-!
# Coefficientwise base change of Riesz–Coleman projections

Let `f : R →+* S` be a bounded unital homomorphism of ultrametric normed commutative rings with Tate
scalars (`TauCeti.NormedRing.IsTate`), with `S` complete, and let `u_S = u.mapCoeffs f hf` be the
coefficientwise extension of an endomorphism `u` of `C₀(I, R)`. Whenever `Q : R[X]` preserves its
degree under `f` (in particular whenever `IsUnit Q.leadingCoeff`), `(Q.map f).reverse =
Q.reverse.map f`, so any Riesz–Coleman projection `E` of `u` for `Q` extends to `E.mapCoeffs f hf`
for `Q.map f` without compactness. Under a coprime Fredholm factorization `H_u = Q * S₀` over a
complete `R`, the explicit projector `rieszColemanProjection` commutes with `mapCoeffs`, and bounded
field extensions preserve `finrank K (ker Q*(u))`.

## Main results

* `ContinuousLinearMap.IsRieszColemanProjection.mapCoeffs`,
  `ContinuousLinearMap.IsRieszColemanProjection.mapCoeffs_of_isUnit_leadingCoeff`: Riesz–Coleman
  projections commute with bounded coefficient extension without compactness.
* `ContinuousLinearMap.IsRowCompact.rieszColemanProjection_mapCoeffs`: the explicit projector
  commutes with bounded coefficient extension under a coprime Fredholm factorization.
* `ContinuousLinearMap.IsRowCompact.finrank_ker_aeval_reverse_mapCoeffs`: bounded field extension
  preserves the dimension of `ker Q*(u)`.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127** (1997),
  417–479, Appendix A4.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*, Algebra
  Number Theory **13** (2019), 93–158, §2.2.
-/

public section

open Polynomial
open PowerSeries (IsEntire)
open scoped ZeroAtInfty NNReal TauCeti.RingOpNorm PowerSeries

namespace ContinuousLinearMap

section Ring

variable {I R S : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [NormedCommRing R] [TauCeti.NormedRing.IsTate R]
  [NormedCommRing S] [TauCeti.NormedRing.IsTate S] [IsUltrametricDist S] [CompleteSpace S]

/-- **Riesz–Coleman projections under bounded base change.** Whenever `Q` preserves its degree under
a bounded ring homomorphism `f : R →+* S`, `E.mapCoeffs f hf` is a Riesz–Coleman projection of
`u.mapCoeffs f hf` for `Q.map f`, with no compactness of `u` or completeness of `R` needed. -/
theorem IsRieszColemanProjection.mapCoeffs
    {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]} (hE : IsRieszColemanProjection u Q E)
    (f : R →+* S) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖)
    (hdeg : (Q.map f).natDegree = Q.natDegree) :
    IsRieszColemanProjection (u.mapCoeffs f hf) (Q.map f) (E.mapCoeffs f hf) := by
  have hrev : (Q.map f).reverse = Q.reverse.map f := by rw [reverse, hdeg, reflect_map, ← reverse]
  obtain ⟨w, hw₁, hw₂, hw₃, hw₄, hw⟩ := hE.exists_inverse
  refine ⟨?_, ?_, mapCoeffs_mem_closure_adjoin f hf hE.mem_closure_adjoin, ?_,
    ⟨w.mapCoeffs f hf, ?_, ?_, ?_, ?_, mapCoeffs_mem_closure_adjoin f hf hw⟩⟩
  · simpa [IsIdempotentElem] using congrArg (fun v ↦ v.mapCoeffs f hf) hE.isIdempotentElem.eq
  · simpa [Commute, SemiconjBy] using congrArg (fun v ↦ v.mapCoeffs f hf) hE.commute.eq
  · rw [hrev, ← mapCoeffs_aeval]
    simpa using congrArg (fun v ↦ v.mapCoeffs f hf) hE.aeval_reverse_mul_eq_zero
  · rw [hrev, ← mapCoeffs_aeval]; simpa using congrArg (fun v ↦ v.mapCoeffs f hf) hw₁
  · rw [hrev, ← mapCoeffs_aeval]; simpa using congrArg (fun v ↦ v.mapCoeffs f hf) hw₂
  · simpa using congrArg (fun v ↦ v.mapCoeffs f hf) hw₃
  · simpa using congrArg (fun v ↦ v.mapCoeffs f hf) hw₄

/-- When `IsUnit Q.leadingCoeff`, any Riesz–Coleman projection of `u` for `Q` extends along `f`. -/
theorem IsRieszColemanProjection.mapCoeffs_of_isUnit_leadingCoeff
    {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]} (hE : IsRieszColemanProjection u Q E)
    (hQ : IsUnit Q.leadingCoeff) (f : R →+* S) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) :
    IsRieszColemanProjection (u.mapCoeffs f hf) (Q.map f) (E.mapCoeffs f hf) := by
  have := NormOneClass.nontrivial (G := S)
  exact hE.mapCoeffs f hf (natDegree_map_eq_of_isUnit_leadingCoeff f hQ)

/-- **Bounded base change of the explicit Riesz–Coleman projector.** Under a coprime Fredholm
factorization `H_u = Q * S₀` with `IsUnit Q.leadingCoeff`, `rieszColemanProjection` commutes with
`mapCoeffs`. -/
theorem IsRowCompact.rieszColemanProjection_mapCoeffs [IsUltrametricDist R] [CompleteSpace R]
    {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact) (f : R →+* S)
    (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) {Q : R[X]} {S₀ : R⟦X⟧} (hQ : IsUnit Q.leadingCoeff)
    (hS₀ : S₀.IsEntire) (hfac : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S₀)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S₀, IsEntire.mem_subring.mpr hS₀⟩) :
    (u.mapCoeffs f hf).rieszColemanProjection (Q.map f) =
      (u.rieszColemanProjection Q).mapCoeffs f hf := by
  have := NormOneClass.nontrivial (G := S)
  have hdeg : (Q.map f).natDegree = Q.natDegree := natDegree_map_eq_of_isUnit_leadingCoeff f hQ
  have hrev : (Q.map f).reverse = Q.reverse.map f := by rw [reverse, hdeg, reflect_map, ← reverse]
  have hlc : (Q.map f).leadingCoeff = f Q.leadingCoeff := by
    rw [leadingCoeff, hdeg, coeff_map, ← leadingCoeff]
  set B := 1 - C (Ring.inverse Q.leadingCoeff) * Q.reverse with hB_def
  have hB_map : 1 - C (Ring.inverse (Q.map f).leadingCoeff) * (Q.map f).reverse = B.map f := by
    rw [hlc, ← hQ.map_ringInverse f, hrev, hB_def, Polynomial.map_sub, Polynomial.map_one,
      Polynomial.map_mul, map_C]
  have hB0 : B.coeff 0 = 0 := coeff_zero_one_sub_C_mul_reverse (Ring.inverse_mul_cancel _ hQ)
  have hGood := hu.isGoodZero_charPowerSeries_aeval_one_sub_C_mul_reverse hQ hS₀ hfac hcop
  rw [rieszColemanProjection_def, rieszColemanProjection_def, hdeg, hB_map, ← hB_def,
    ← mapCoeffs_aeval]
  rw [← hB_def] at hGood
  simpa only [map_one] using
    (hu.aeval hB0).rieszProjection_mapCoeffs f hf hGood.isUnit_evalAt_hasseDeriv

end Ring

section Field

variable {I K L : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]

/-- Bounded field extension preserves the dimension of `ker Q*(u)` under a coprime Fredholm
factorization `H_u = Q * S₀`. -/
theorem IsRowCompact.finrank_ker_aeval_reverse_mapCoeffs
    {u : C₀(I, K) →L[K] C₀(I, K)} (hu : u.IsRowCompact) (f : K →+* L)
    (hf : ∃ C : ℝ≥0, ∀ x, ‖f x‖ ≤ C * ‖x‖) {Q : K[X]} {S₀ : K⟦X⟧} (hS₀ : S₀.IsEntire)
    (hfac : u.matrixCoeff.charPowerSeries = (Q : K⟦X⟧) * S₀)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring K)
      ⟨S₀, IsEntire.mem_subring.mpr hS₀⟩) :
    Module.finrank L (LinearMap.ker
      (Polynomial.aeval (u.mapCoeffs f hf) (Q.map f).reverse : Module.End L C₀(I, L))) =
    Module.finrank K (LinearMap.ker (Polynomial.aeval u Q.reverse : Module.End K C₀(I, K))) := by
  have hQ : IsUnit Q.leadingCoeff := (leadingCoeff_ne_zero.mpr fun h0 ↦ by
    simpa [h0, u.matrixCoeff.constantCoeff_charPowerSeries] using
      congrArg (PowerSeries.constantCoeff (R := K)) hfac).isUnit
  have hE := hu.isRieszColemanProjection_rieszColemanProjection hQ hS₀ hfac hcop
  have hEf := hE.mapCoeffs_of_isUnit_leadingCoeff hQ f hf
  set B := 1 - C (Ring.inverse Q.leadingCoeff) * Q.reverse with hB_def
  have hB0 : B.coeff 0 = 0 := coeff_zero_one_sub_C_mul_reverse (Ring.inverse_mul_cancel _ hQ)
  have hv := hu.aeval hB0
  have hGood := hu.isGoodZero_charPowerSeries_aeval_one_sub_C_mul_reverse hQ hS₀ hfac hcop
  rw [← hB_def] at hGood
  have hEv : IsRieszProjection (Polynomial.aeval u B) 1 Q.natDegree
      (u.rieszColemanProjection Q) := by
    rw [rieszColemanProjection_def, ← hB_def]
    exact hv.isRieszProjection_rieszProjection (fun _ ↦ hGood.evalAt_hasseDeriv_eq_zero)
      hGood.isUnit_evalAt_hasseDeriv
  have hEvf : IsRieszProjection ((Polynomial.aeval u B).mapCoeffs f hf) 1 Q.natDegree
      ((u.rieszColemanProjection Q).mapCoeffs f hf) := by
    simpa only [map_one] using hEv.mapCoeffs f hf
  have hGoodf := by simpa only [map_one] using hv.isGoodZero_charPowerSeries_mapCoeffs f hf hGood
  rw [← hEf.range_eq_ker, hEvf.finrank_range (hv.mapCoeffs f hf) hGoodf,
    hE.finrank_ker_aeval_reverse hu hS₀ hfac hcop]

end Field

end ContinuousLinearMap
