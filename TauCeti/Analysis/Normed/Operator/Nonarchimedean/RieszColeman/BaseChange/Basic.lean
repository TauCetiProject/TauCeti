/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.BaseChange
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszColeman.Decomposition
import TauCeti.RingTheory.PowerSeries.Dvd
import TauCeti.RingTheory.PowerSeries.Entire.Coprime

/-!
# Coefficientwise base change of Riesz–Coleman projections

This file records the behaviour of Riesz–Coleman projections, complementary inverses, explicit
Riesz–Coleman projectors, and spectral-summand ranks and dimensions on model spaces `C₀(I, R)`
under bounded coefficient-ring homomorphisms `mapCoeffs`.

## Main results

* `ContinuousLinearMap.IsRieszColemanProjection.mapCoeffs`,
  `ContinuousLinearMap.IsRieszColemanProjection.inverse_mapCoeffs`, and
  `ContinuousLinearMap.IsRowCompact.rieszColemanProjection_mapCoeffs`: compatibility of
  Riesz–Coleman projections, complementary inverses, and explicit Riesz–Coleman projectors with
  bounded coefficientwise extension `mapCoeffs` on `C₀(I, R)`.
* `ContinuousLinearMap.IsRieszColemanProjection.rankAtStalk_range_mapCoeffs` and
  `ContinuousLinearMap.IsRowCompact.finrank_ker_aeval_reverse_mapCoeffs`: invariance of stalk rank
  and field kernel dimension under bounded base change on `C₀(I, R)`.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127** (1997),
  417–479, Appendix A, A4.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.2.
* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §7.
-/

public section

open Polynomial
open PowerSeries (IsEntire)
open scoped PowerSeries ZeroAtInfty NNReal TauCeti.RingOpNorm

namespace ContinuousLinearMap

section BaseChange

variable {I R S : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [NormedCommRing R] [TauCeti.NormedRing.IsTate R]
  [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S]
  [TauCeti.NormedRing.IsTate S]

/-- **Riesz–Coleman projections under bounded base change.** When `Q.leadingCoeff` is a unit, the
coefficientwise extension of a Riesz–Coleman projection of `u` for `Q` is a Riesz–Coleman
projection of `u.mapCoeffs f hf` for `Q.map f`. No compactness is needed. -/
theorem IsRieszColemanProjection.mapCoeffs {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]}
    (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff)
    (f : R →+* S) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) :
    IsRieszColemanProjection (u.mapCoeffs f hf) (Q.map f) (E.mapCoeffs f hf) := by
  simpa only [mapCoeffsRingHom_apply] using
    hE.map (mapCoeffsRingHom f hf)
      (by
        simp only [mapCoeffsRingHom_apply]
        rw [reverse_map_of_isUnit_leadingCoeff hQ f, aeval_mapCoeffs])
      (fun {v} hv ↦ by
        simpa only [mapCoeffsRingHom_apply] using mapCoeffs_mem_closure_adjoin f hf hv)

/-- The complementary inverse of a Riesz–Coleman projection commutes with bounded base change when
`Q.leadingCoeff` is a unit. -/
@[simp]
theorem IsRieszColemanProjection.inverse_mapCoeffs {u E : C₀(I, R) →L[R] C₀(I, R)}
    {Q : R[X]} (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff)
    (f : R →+* S) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) :
    (hE.mapCoeffs hQ f hf).inverse = hE.inverse.mapCoeffs f hf := by
  have hinv := hE.inverse_map (mapCoeffsRingHom f hf)
    (by
      simp only [mapCoeffsRingHom_apply]
      rw [reverse_map_of_isUnit_leadingCoeff hQ f, aeval_mapCoeffs])
    (fun {v} hv ↦ by
      simpa only [mapCoeffsRingHom_apply] using mapCoeffs_mem_closure_adjoin f hf hv)
  simpa only [mapCoeffsRingHom_apply] using hinv

/-- **Bounded base change of the explicit Riesz–Coleman projector.** For a row-compact operator `u`
with a coprime factorisation `H_u = Q * S'`, where `IsUnit Q.leadingCoeff` and `S'` is entire, the
explicit Riesz–Coleman projector of `u.mapCoeffs f hf` for `Q.map f` is the coefficientwise
extension of `u.rieszColemanProjection Q`. -/
theorem IsRowCompact.rieszColemanProjection_mapCoeffs [IsUltrametricDist R]
    [CompleteSpace R] {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact) {Q : R[X]} {S' : R⟦X⟧}
    (hQ : IsUnit Q.leadingCoeff) (hS' : S'.IsEntire)
    (hQS' : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S')
    (hcop : IsCoprime (IsEntire.polynomialHom Q) ⟨S', IsEntire.mem_subring.mpr hS'⟩)
    (f : R →+* S) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) :
    (u.mapCoeffs f hf).rieszColemanProjection (Q.map f) =
      (u.rieszColemanProjection Q).mapCoeffs f hf := by
  rcases subsingleton_or_nontrivial S with hS | hS
  · ext x i; exact Subsingleton.elim _ _
  obtain ⟨-, hQlc, hFS, hHS, hcopS⟩ :=
    IsEntire.map_factorization hQ hS' hQS' hcop f hf.choose_spec
  rw [← hu.charPowerSeries_map f hf] at hHS
  exact (((hu.isRieszColemanProjection_rieszColemanProjection hQ hS' hQS' hcop).mapCoeffs
    hQ f hf).eq_rieszColemanProjection (hu.mapCoeffs f hf) hQlc hFS hHS hcopS).symm

/-- **Constant stalk rank after bounded base change.** For a row-compact operator `u` on
`C₀(I, R)` with a Riesz–Coleman projection `E` for a coprime factorisation `H_u = Q * S'`, where
`IsUnit Q.leadingCoeff` and `S'` is entire, the base-changed summand `(E.mapCoeffs f hf).range`
has constant stalk rank `Q.natDegree` at every prime ideal of `S`. -/
theorem IsRieszColemanProjection.rankAtStalk_range_mapCoeffs [IsUltrametricDist R] [CompleteSpace R]
    {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]} {S' : R⟦X⟧}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact)
    (hQ : IsUnit Q.leadingCoeff) (hS' : S'.IsEntire)
    (hQS' : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S')
    (hcop : IsCoprime (IsEntire.polynomialHom Q) ⟨S', IsEntire.mem_subring.mpr hS'⟩)
    (f : R →+* S) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) (q : PrimeSpectrum S) :
    Module.rankAtStalk (R := S) (E.mapCoeffs f hf).range q = Q.natDegree := by
  have : Nontrivial S := q.nontrivial
  obtain ⟨hQdeg, hQlc, hFS, hHS, hcopS⟩ :=
    IsEntire.map_factorization hQ hS' hQS' hcop f hf.choose_spec
  rw [← hu.charPowerSeries_map f hf] at hHS
  rw [← hQdeg]
  exact (hE.mapCoeffs hQ f hf).rankAtStalk_range (hu.mapCoeffs f hf) hQlc hFS hHS hcopS q

end BaseChange

section FieldBaseChange

variable {I K L : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]

/-- **Bounded field extension preserves `dim ker Q*(u)`.** For a coprime factorisation `H_u = Q * S`
of the Fredholm series of a row-compact operator `u` on `C₀(I, K)`, bounded coefficient extension
along `f : K →+* L` preserves the dimension of `ker Q*(u)`. -/
theorem IsRowCompact.finrank_ker_aeval_reverse_mapCoeffs {u : C₀(I, K) →L[K] C₀(I, K)}
    (hu : u.IsRowCompact) (f : K →+* L) (hf : ∃ C : ℝ≥0, ∀ x, ‖f x‖ ≤ C * ‖x‖)
    {Q : K[X]} {S : K⟦X⟧} (hS : S.IsEntire)
    (hQS : u.matrixCoeff.charPowerSeries = (Q : K⟦X⟧) * S)
    (hcop : IsCoprime (IsEntire.polynomialHom Q) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    Module.finrank L (Polynomial.aeval (u.mapCoeffs f hf) (Q.map f).reverse :
        C₀(I, L) →L[L] C₀(I, L)).ker =
      Module.finrank K (Polynomial.aeval u Q.reverse : C₀(I, K) →L[K] C₀(I, K)).ker := by
  have hQ := PowerSeries.isUnit_leadingCoeff_of_eq_coe_mul
    (Matrix.constantCoeff_charPowerSeries _) hQS
  obtain ⟨hQdeg, -, hLS, hHS, hcopL⟩ :=
    IsEntire.map_factorization hQ hS hQS hcop f hf.choose_spec
  rw [← hu.charPowerSeries_map f hf] at hHS
  rw [(hu.mapCoeffs f hf).finrank_ker_aeval_reverse hLS hHS hcopL, hQdeg,
    hu.finrank_ker_aeval_reverse hS hQS hcop]

end FieldBaseChange

end ContinuousLinearMap
