/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.RowCompact.BaseChange
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.FredholmDet
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszProjection.Basic
public import TauCeti.RingTheory.PowerSeries.Entire.GoodZero

/-!
# Coefficientwise base change of Fredholm series, resolvents and Riesz projectors

Let `f : R →+* S` be a bounded unital homomorphism of complete ultrametric normed commutative
rings, with `R` Tate (`TauCeti.NormedRing.IsTate R`), and let `u_S = u.mapCoeffs f hf` be the
coefficientwise extension of an endomorphism `u` of the model space `C₀(I, R)`. The Fredholm
series of `u_S` is the coefficientwise image of that of `u`, by continuity of `f` on the
convergent principal-minor sums
(`ContinuousLinearMap.IsRowCompact.charPowerSeries_map`).

For row-compact `u` the whole spectral calculus at a scalar `a` follows, at the scalar `f a`:

* the values of the Hasse derivatives of the Fredholm series, hence the Fredholm determinant and
  good zeros (`ContinuousLinearMap.IsRowCompact.fredholmDet_mapCoeffs`,
  `ContinuousLinearMap.IsRowCompact.isGoodZero_charPowerSeries_mapCoeffs`);
* the coefficients of the Fredholm resolvent
  (`ContinuousLinearMap.IsRowCompact.resolventCoeff_mapCoeffs`) and, when `S` is also Tate
  (`TauCeti.NormedRing.IsTate S`), the values of its Hasse derivatives
  (`ContinuousLinearMap.IsRowCompact.resolventHasseDerivAt_mapCoeffs`), since coefficient
  extension is a continuous ring homomorphism on endomorphisms;
* when `S` is Tate, Riesz projections, which need no compactness at all
  (`ContinuousLinearMap.IsRieszProjection.mapCoeffs`), and the explicit Riesz projector
  (`ContinuousLinearMap.IsRowCompact.rieszProjection_mapCoeffs`).

This comparison allows coefficient rings without a common ground field and does not require
Noetherianity, flatness or a completed tensor product. Over rings with nilpotents it retains the
coefficient information that evaluation at field-valued points would lose.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §§3–7.
* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127**
  (1997), 417–479, Appendix A.
-/

public section

open Filter Topology
open scoped ZeroAtInfty NNReal TauCeti.RingOpNorm

namespace ContinuousLinearMap

variable {I J R S : Type*}
  [TopologicalSpace I] [DiscreteTopology I]
  [TopologicalSpace J] [DiscreteTopology J] [DecidableEq J]
  [NormedCommRing R] [TauCeti.NormedRing.IsTate R]
  [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S]

/-- The Fredholm series commutes with bounded coefficient extension. This is an equality of
power series over the coefficient ring, including when that ring has nilpotents. -/
theorem IsRowCompact.charPowerSeries_map [DecidableEq I] [IsUltrametricDist R] [CompleteSpace R]
    {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact)
    (f : R →+* S) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) :
    (u.mapCoeffs f hf).matrixCoeff.charPowerSeries =
      PowerSeries.map f u.matrixCoeff.charPowerSeries := by
  obtain ⟨C, hC⟩ := hf
  rw [matrixCoeff_mapCoeffs]
  exact Matrix.charPowerSeries_map f (AddMonoidHomClass.continuous_of_bound f C hC)
    hu.summable_principalMinor

section Spectral

variable [DecidableEq I] [IsUltrametricDist R] [CompleteSpace R]
  {u : C₀(I, R) →L[R] C₀(I, R)}

/-- The values at `f a` of the Hasse derivatives of the Fredholm series of the extension are the
images of their values at `a`. -/
theorem IsRowCompact.evalAt_hasseDeriv_charPowerSeries_mapCoeffs (hu : u.IsRowCompact)
    (f : R →+* S) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) (k : ℕ) (a : R) :
    (PowerSeries.hasseDeriv k (u.mapCoeffs f hf).matrixCoeff.charPowerSeries).evalAt (f a) =
      f ((PowerSeries.hasseDeriv k u.matrixCoeff.charPowerSeries).evalAt a) := by
  have hcont : Continuous f := by
    obtain ⟨C, hC⟩ := hf
    exact AddMonoidHomClass.continuous_of_bound f C hC
  rw [hu.charPowerSeries_map f hf, PowerSeries.hasseDeriv_map,
    (hu.isEntire_charPowerSeries.hasseDeriv k).evalAt_map f hcont]

/-- The value `H_u(a)` of the Fredholm series at a scalar commutes with bounded coefficient
extension. -/
theorem IsRowCompact.evalAt_charPowerSeries_mapCoeffs (hu : u.IsRowCompact)
    (f : R →+* S) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) (a : R) :
    (u.mapCoeffs f hf).matrixCoeff.charPowerSeries.evalAt (f a) =
      f (u.matrixCoeff.charPowerSeries.evalAt a) := by
  simpa using hu.evalAt_hasseDeriv_charPowerSeries_mapCoeffs f hf 0 a

/-- **Bounded base change of the Fredholm determinant.** For row-compact `u`,
`det (1 - u_S) = f (det (1 - u))`. -/
theorem IsRowCompact.fredholmDet_mapCoeffs (hu : u.IsRowCompact)
    (f : R →+* S) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) :
    (u.mapCoeffs f hf).fredholmDet = f u.fredholmDet := by
  simpa [fredholmDet_def] using hu.evalAt_charPowerSeries_mapCoeffs f hf 1

/-- A good zero `a` of order `h` of the Fredholm series of a row-compact `u` gives the good zero
`f a` of the same order of the Fredholm series of its extension. -/
theorem IsRowCompact.isGoodZero_charPowerSeries_mapCoeffs (hu : u.IsRowCompact)
    (f : R →+* S) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) {a : R} {h : ℕ}
    (ha : u.matrixCoeff.charPowerSeries.IsGoodZero a h) :
    (u.mapCoeffs f hf).matrixCoeff.charPowerSeries.IsGoodZero (f a) h := by
  obtain ⟨C, hC⟩ := hf
  rw [hu.charPowerSeries_map]
  exact ha.map hu.isEntire_charPowerSeries f (AddMonoidHomClass.continuous_of_bound f C hC)

/-- The coefficients of the Fredholm resolvent commute with bounded coefficient extension. -/
theorem IsRowCompact.resolventCoeff_mapCoeffs (hu : u.IsRowCompact)
    (f : R →+* S) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) (m : ℕ) :
    (u.mapCoeffs f hf).resolventCoeff m = (u.resolventCoeff m).mapCoeffs f hf := by
  have hc (k : ℕ) :
      (u.mapCoeffs f hf).matrixCoeff.charCoeff k = f (u.matrixCoeff.charCoeff k) := by
    simpa [Matrix.coeff_charPowerSeries] using
      congrArg (PowerSeries.coeff k) (hu.charPowerSeries_map f hf)
  simp only [resolventCoeff_def, mapCoeffs_sum, mapCoeffs_smul, mapCoeffs_pow, hc]

variable [TauCeti.NormedRing.IsTate S]

/-- **Bounded base change of the Fredholm resolvent.** For row-compact `u`, the value at `f a` of
the `k`-th Hasse derivative of the Fredholm resolvent of the extension is the extension of its
value at `a`. -/
theorem IsRowCompact.resolventHasseDerivAt_mapCoeffs (hu : u.IsRowCompact)
    (f : R →+* S) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) (k : ℕ) (a : R) :
    (u.mapCoeffs f hf).resolventHasseDerivAt k (f a) =
      (u.resolventHasseDerivAt k a).mapCoeffs f hf := by
  refine ((hu.mapCoeffs f hf).hasSum_resolventHasseDerivAt k (f a)).unique ?_
  simpa [hu.resolventCoeff_mapCoeffs] using
    (hu.hasSum_resolventHasseDerivAt k a).mapCoeffs f hf

/-- The value `V(a)` of the Fredholm resolvent of a row-compact operator commutes with bounded
coefficient extension. -/
theorem IsRowCompact.resolventAt_mapCoeffs (hu : u.IsRowCompact)
    (f : R →+* S) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) (a : R) :
    (u.mapCoeffs f hf).resolventAt (f a) = (u.resolventAt a).mapCoeffs f hf := by
  simpa using hu.resolventHasseDerivAt_mapCoeffs f hf 0 a

/-- **Bounded base change of the Riesz projector.** If `ΔʰH_u(a)` is a unit, the Riesz projector
of the extension of a row-compact `u` at `f a` is the extension of the Riesz projector of `u`
at `a`. -/
theorem IsRowCompact.rieszProjection_mapCoeffs (hu : u.IsRowCompact)
    (f : R →+* S) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) {a : R} {h : ℕ}
    (hc : IsUnit ((PowerSeries.hasseDeriv h u.matrixCoeff.charPowerSeries).evalAt a)) :
    (u.mapCoeffs f hf).rieszProjection (f a) h = (u.rieszProjection a h).mapCoeffs f hf := by
  rw [rieszProjection_def, rieszProjection_def, hu.evalAt_hasseDeriv_charPowerSeries_mapCoeffs,
    hu.resolventHasseDerivAt_mapCoeffs, ← hc.map_ringInverse f]
  simp only [mapCoeffs_sub, mapCoeffs_one, mapCoeffs_pow, mapCoeffs_mul, mapCoeffs_smul]

end Spectral

/-- **Riesz projections under bounded base change.** The coefficientwise extension of a Riesz
projection of `u` at `a` of order `h` is a Riesz projection of the extension of `u` at `f a` of
the same order. No compactness is needed. -/
theorem IsRieszProjection.mapCoeffs [TauCeti.NormedRing.IsTate S]
    {u E : C₀(J, R) →L[R] C₀(J, R)} {a : R} {h : ℕ} (hE : IsRieszProjection u a h E)
    (f : R →+* S) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) :
    IsRieszProjection (u.mapCoeffs f hf) (f a) h (E.mapCoeffs f hf) := by
  obtain ⟨w, hw₁, hw₂, hw₃, hw₄, hw⟩ := hE.exists_inverse
  refine ⟨?_, ?_, mapCoeffs_mem_closure_adjoin f hf hE.mem_closure_adjoin, ?_,
    ⟨w.mapCoeffs f hf, ?_, ?_, ?_, ?_, mapCoeffs_mem_closure_adjoin f hf hw⟩⟩
  · simpa [IsIdempotentElem] using congrArg (fun v ↦ v.mapCoeffs f hf) hE.isIdempotentElem.eq
  · simpa [Commute, SemiconjBy] using congrArg (fun v ↦ v.mapCoeffs f hf) hE.commute.eq
  · simpa using congrArg (fun v ↦ v.mapCoeffs f hf) hE.pow_mul_eq_zero
  · simpa using congrArg (fun v ↦ v.mapCoeffs f hf) hw₁
  · simpa using congrArg (fun v ↦ v.mapCoeffs f hf) hw₂
  · simpa using congrArg (fun v ↦ v.mapCoeffs f hf) hw₃
  · simpa using congrArg (fun v ↦ v.mapCoeffs f hf) hw₄

end ContinuousLinearMap
