/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.PrModule.BaseChange
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszColeman.Decomposition
import TauCeti.Algebra.Polynomial.Reverse

/-!
# Base change of Riesz–Coleman projections

This file records the behaviour of Riesz–Coleman projections, complementary inverses, explicit
Riesz–Coleman projectors, and spectral-summand ranks and dimensions under completed-tensor base
change on `(Pr)` modules and bounded coefficient-ring homomorphisms on model spaces `C₀(I, R)`.

## Main results

* `ContinuousLinearMap.IsRieszColemanProjection.completedBaseChange` and
  `ContinuousLinearMap.IsRieszColemanProjection.inverse_completedBaseChange`: transport of
  Riesz–Coleman projections and their complementary inverses along completed-tensor base change on
  `(Pr)` modules.
* `ContinuousLinearMap.IsRieszColemanProjection.mapCoeffs`,
  `ContinuousLinearMap.IsRieszColemanProjection.inverse_mapCoeffs`, and
  `ContinuousLinearMap.IsRowCompact.rieszColemanProjection_mapCoeffs`: compatibility of
  Riesz–Coleman projections, complementary inverses, and explicit Riesz–Coleman projectors with
  bounded coefficientwise extension `mapCoeffs` on `C₀(I, R)`.
* `ContinuousLinearMap.IsRieszColemanProjection.rankAtStalk_range_mapCoeffs` and
  `ContinuousLinearMap.IsRowCompact.finrank_ker_aeval_reverse_mapCoeffs`: invariance of stalk rank
  and field kernel dimension under bounded base change.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127** (1997),
  417–479, Appendix A, A4.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.2.
* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §7.
-/

public section

open Polynomial TauCeti
open PowerSeries (IsEntire)
open scoped PowerSeries ZeroAtInfty NNReal TauCeti.RingOpNorm

local notation:70 S:71 " ⊗̂[" R "] " M:71 => (TauCeti.Huber.BanachModule.CompletedTensor R S M)

namespace ContinuousLinearMap

section PrBaseChange

universe u

variable {R S : Type*} [NormedCommRing R] [TauCeti.NormedRing.IsTate R]
  [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S] [Algebra R S]
  [TauCeti.NormedRing.IsTate S]
  {M N : Type u} [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  [SeminormedAddCommGroup N] [Module S N] [IsBoundedSMul S N]
  (hS : ∃ C : ℝ≥0, ∀ (r : R) (s : S), ‖r • s‖ ≤ C * ‖r‖ * ‖s‖)

include hS in
/-- **Riesz–Coleman projections under completed-tensor base change.** On a `(Pr)` module `M` over
`R`, when `Q.leadingCoeff` is a unit, `completedBaseChange` transports a Riesz–Coleman projection of
`u` for `Q` to one of `u.completedBaseChange α α` for `Q.map (algebraMap R S)` (no compactness
needed). -/
theorem IsRieszColemanProjection.completedBaseChange (hM : HasPr R M) (α : S ⊗̂[R] M ≃L[S] N)
    {u E : M →L[R] M} {Q : R[X]} (hE : IsRieszColemanProjection u Q E)
    (hQ : IsUnit Q.leadingCoeff) :
    IsRieszColemanProjection (u.completedBaseChange α α) (Polynomial.map (algebraMap R S) Q)
      (E.completedBaseChange α α) := by
  let Φ := completedBaseChangeRingHom α
  have haeval : Polynomial.aeval (u.completedBaseChange α α)
      (Polynomial.map (algebraMap R S) Q).reverse = Φ (Polynomial.aeval u Q.reverse) := by
    rw [Polynomial.reverse_map_of_isUnit_leadingCoeff hQ (algebraMap R S),
      aeval_completedBaseChange, completedBaseChangeRingHom_apply]
  obtain ⟨w, hw₁, hw₂, hw₃, hw₄, hw⟩ := hE.exists_inverse
  refine ⟨by simpa [IsIdempotentElem, Φ] using congrArg Φ hE.isIdempotentElem.eq,
    by simpa [Commute, SemiconjBy, Φ] using congrArg Φ hE.commute.eq,
    completedBaseChange_mem_closure_adjoin hS hM α hE.mem_closure_adjoin,
    by simpa [Φ, haeval, map_mul] using congrArg Φ hE.aeval_reverse_mul_eq_zero,
    ⟨w.completedBaseChange α α,
      by simpa [Φ, haeval, map_mul, map_sub, map_one] using congrArg Φ hw₁,
      by simpa [Φ, haeval, map_mul, map_sub, map_one] using congrArg Φ hw₂,
      by simpa [Φ, map_mul] using congrArg Φ hw₃,
      by simpa [Φ, map_mul] using congrArg Φ hw₄,
      completedBaseChange_mem_closure_adjoin hS hM α hw⟩⟩

include hS in
/-- The complementary inverse of a Riesz–Coleman projection on a `(Pr)` module commutes with
completed-tensor base change when `Q.leadingCoeff` is a unit. -/
theorem IsRieszColemanProjection.inverse_completedBaseChange (hM : HasPr R M)
    (α : S ⊗̂[R] M ≃L[S] N) {u E : M →L[R] M} {Q : R[X]}
    (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff) :
    (hE.completedBaseChange hS hM α hQ).inverse = hE.inverse.completedBaseChange α α := by
  let Φ := completedBaseChangeRingHom α
  have haeval : Polynomial.aeval (u.completedBaseChange α α)
      (Polynomial.map (algebraMap R S) Q).reverse = Φ (Polynomial.aeval u Q.reverse) := by
    rw [Polynomial.reverse_map_of_isUnit_leadingCoeff hQ (algebraMap R S),
      aeval_completedBaseChange, completedBaseChangeRingHom_apply]
  refine ((hE.completedBaseChange hS hM α hQ).eq_inverse ?_ ?_).symm
  · rw [haeval, ← completedBaseChangeRingHom_apply, ← map_mul, hE.aeval_reverse_mul_inverse,
      map_sub, map_one, completedBaseChangeRingHom_apply]
  · rw [← completedBaseChangeRingHom_apply, ← completedBaseChangeRingHom_apply, ← map_mul,
      hE.mul_inverse_eq_zero, map_zero]

end PrBaseChange

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
  have hrev := reverse_map_of_isUnit_leadingCoeff hQ f
  obtain ⟨w, hw₁, hw₂, hw₃, hw₄, hw⟩ := hE.exists_inverse
  refine ⟨?_, ?_, mapCoeffs_mem_closure_adjoin f hf hE.mem_closure_adjoin, ?_,
    ⟨w.mapCoeffs f hf, ?_, ?_, ?_, ?_, mapCoeffs_mem_closure_adjoin f hf hw⟩⟩
  · simpa [IsIdempotentElem] using congrArg (fun v ↦ v.mapCoeffs f hf) hE.isIdempotentElem.eq
  · simpa [Commute, SemiconjBy] using congrArg (fun v ↦ v.mapCoeffs f hf) hE.commute.eq
  · rw [hrev, aeval_mapCoeffs, ← mapCoeffs_mul, hE.aeval_reverse_mul_eq_zero, mapCoeffs_zero]
  · rw [hrev, aeval_mapCoeffs, ← mapCoeffs_mul, hw₁, mapCoeffs_sub, mapCoeffs_one]
  · rw [hrev, aeval_mapCoeffs, ← mapCoeffs_mul, hw₂, mapCoeffs_sub, mapCoeffs_one]
  · rw [← mapCoeffs_mul, hw₃, mapCoeffs_zero]
  · rw [← mapCoeffs_mul, hw₄, mapCoeffs_zero]

/-- The complementary inverse of a Riesz–Coleman projection commutes with bounded base change. -/
theorem IsRieszColemanProjection.inverse_mapCoeffs {u E : C₀(I, R) →L[R] C₀(I, R)}
    {Q : R[X]} (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff)
    (f : R →+* S) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) :
    (hE.mapCoeffs hQ f hf).inverse = hE.inverse.mapCoeffs f hf := by
  have hrev := reverse_map_of_isUnit_leadingCoeff hQ f
  refine ((hE.mapCoeffs hQ f hf).eq_inverse ?_ ?_).symm
  · rw [hrev, aeval_mapCoeffs, ← mapCoeffs_mul, hE.aeval_reverse_mul_inverse, mapCoeffs_sub,
      mapCoeffs_one]
  · rw [← mapCoeffs_mul, hE.mul_inverse_eq_zero, mapCoeffs_zero]

omit [TauCeti.NormedRing.IsTate S] in
/-- Transports a coprime polynomial factorisation `H_u = Q * S'` along a bounded ring homomorphism
`f : R →+* S` into a nontrivial target ring. -/
private theorem mapCoeffs_factorisation [IsUltrametricDist R] [CompleteSpace R] [Nontrivial S]
    {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact) {Q : R[X]} {S' : R⟦X⟧}
    (hQ : IsUnit Q.leadingCoeff) (hS' : S'.IsEntire)
    (hQS' : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S')
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S', IsEntire.mem_subring.mpr hS'⟩)
    (f : R →+* S) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) :
    (Q.map f).natDegree = Q.natDegree ∧
      IsUnit (Q.map f).leadingCoeff ∧
      (PowerSeries.map f S').IsEntire ∧
      (u.mapCoeffs f hf).matrixCoeff.charPowerSeries =
        ((Q.map f : S[X]) : S⟦X⟧) * PowerSeries.map f S' ∧
      IsCoprime (⟨Q.map f, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe (Q.map f))⟩ :
        IsEntire.subring S)
        ⟨PowerSeries.map f S', IsEntire.mem_subring.mpr (hS'.map f hf.choose_spec)⟩ := by
  have hQdeg : (Q.map f).natDegree = Q.natDegree :=
    natDegree_map_of_leadingCoeff_ne_zero f (hQ.map f).ne_zero
  have hQlc : IsUnit (Q.map f).leadingCoeff := by
    rw [leadingCoeff_map_of_leadingCoeff_ne_zero f (hQ.map f).ne_zero]
    exact hQ.map f
  have hFS : (PowerSeries.map f S').IsEntire := hS'.map f hf.choose_spec
  have hHS : (u.mapCoeffs f hf).matrixCoeff.charPowerSeries =
      ((Q.map f : S[X]) : S⟦X⟧) * PowerSeries.map f S' := by
    rw [hu.charPowerSeries_map f hf, hQS', map_mul, Polynomial.polynomial_map_coe]
  have hcopS : IsCoprime
      (⟨Q.map f, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe (Q.map f))⟩ :
        IsEntire.subring S)
      ⟨PowerSeries.map f S', IsEntire.mem_subring.mpr hFS⟩ := by
    have hQeq :
        (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R) =
          IsEntire.polynomialHom Q :=
      Subtype.ext (IsEntire.coe_polynomialHom Q).symm
    have hQfeq :
        (⟨Q.map f, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe (Q.map f))⟩ :
          IsEntire.subring S) = IsEntire.polynomialHom (Q.map f) :=
      Subtype.ext (IsEntire.coe_polynomialHom (Q.map f)).symm
    have h1 : IsEntire.mapHom f hf.choose_spec
        ⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ =
        ⟨Q.map f, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe (Q.map f))⟩ := by
      rw [hQeq, IsEntire.mapHom_polynomialHom, hQfeq]
    have h2 : IsEntire.mapHom f hf.choose_spec ⟨S', IsEntire.mem_subring.mpr hS'⟩ =
        ⟨PowerSeries.map f S', IsEntire.mem_subring.mpr hFS⟩ :=
      Subtype.ext (IsEntire.coe_mapHom f hf.choose_spec _)
    have h := hcop.map (IsEntire.mapHom f hf.choose_spec)
    rwa [h1, h2] at h
  exact ⟨hQdeg, hQlc, hFS, hHS, hcopS⟩

/-- **Bounded base change of the explicit Riesz–Coleman projector.** For a row-compact operator `u`
with a coprime factorisation `H_u = Q * S'`, where `IsUnit Q.leadingCoeff` and `S'` is entire, the
explicit Riesz–Coleman projector of `u.mapCoeffs f hf` for `Q.map f` is the coefficientwise
extension of `u.rieszColemanProjection Q`. -/
theorem IsRowCompact.rieszColemanProjection_mapCoeffs [IsUltrametricDist R]
    [CompleteSpace R] {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact) {Q : R[X]} {S' : R⟦X⟧}
    (hQ : IsUnit Q.leadingCoeff) (hS' : S'.IsEntire)
    (hQS' : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S')
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S', IsEntire.mem_subring.mpr hS'⟩)
    (f : R →+* S) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) :
    (u.mapCoeffs f hf).rieszColemanProjection (Q.map f) =
      (u.rieszColemanProjection Q).mapCoeffs f hf := by
  rcases subsingleton_or_nontrivial S with hS | hS
  · ext x i; exact Subsingleton.elim _ _
  obtain ⟨-, hQlc, hFS, hHS, hcopS⟩ := mapCoeffs_factorisation hu hQ hS' hQS' hcop f hf
  exact (((hu.isRieszColemanProjection_rieszColemanProjection hQ hS' hQS' hcop).mapCoeffs
    hQ f hf).eq_rieszColemanProjection (hu.mapCoeffs f hf) hQlc hFS hHS hcopS).symm

/-- After bounded base change, the Riesz–Coleman summand of a coprime factorisation `H_u = Q * S'`
has constant stalk rank `Q.natDegree` at every prime ideal of `S`. -/
theorem IsRieszColemanProjection.rankAtStalk_range_mapCoeffs [IsUltrametricDist R] [CompleteSpace R]
    {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]} {S' : R⟦X⟧}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact)
    (hQ : IsUnit Q.leadingCoeff) (hS' : S'.IsEntire)
    (hQS' : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S')
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S', IsEntire.mem_subring.mpr hS'⟩)
    (f : R →+* S) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) (q : PrimeSpectrum S) :
    Module.rankAtStalk (R := S) (E.mapCoeffs f hf).range q = Q.natDegree := by
  have : Nontrivial S :=
    ⟨⟨1, 0, fun h ↦ q.isPrime.ne_top ((Ideal.eq_top_iff_one q.asIdeal).2 (h ▸ q.asIdeal.zero_mem))⟩⟩
  obtain ⟨hQdeg, hQlc, hFS, hHS, hcopS⟩ := mapCoeffs_factorisation hu hQ hS' hQS' hcop f hf
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
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring K) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    Module.finrank L (Polynomial.aeval (u.mapCoeffs f hf) (Q.map f).reverse :
        C₀(I, L) →L[L] C₀(I, L)).ker =
      Module.finrank K (Polynomial.aeval u Q.reverse : C₀(I, K) →L[K] C₀(I, K)).ker := by
  have hQ := PowerSeries.isUnit_leadingCoeff_of_eq_coe_mul
    (Matrix.constantCoeff_charPowerSeries _) hQS
  have hE := hu.isRieszColemanProjection_rieszColemanProjection hQ hS hQS hcop
  have hr := hE.rankAtStalk_range_mapCoeffs hu hQ hS hQS hcop f hf ⟨⊥, Ideal.isPrime_bot⟩
  let : AddCommGroup ((u.rieszColemanProjection Q).mapCoeffs f hf).range := inferInstance
  rw [Module.rankAtStalk_eq_finrank_of_free, Pi.natCast_apply, Nat.cast_id] at hr
  rw [← (hE.mapCoeffs hQ f hf).range_eq_ker, hr, ← hE.finrank_range hu hS hQS hcop,
    hE.range_eq_ker]

end FieldBaseChange

end ContinuousLinearMap
