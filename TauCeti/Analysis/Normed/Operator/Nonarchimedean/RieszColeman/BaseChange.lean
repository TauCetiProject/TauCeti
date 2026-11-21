/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.PrModule.BaseChange
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszColeman.PrModule
import TauCeti.Algebra.Polynomial.Reverse
import TauCeti.RingTheory.PowerSeries.Dvd

/-!
# Base change of Riesz–Coleman projections

This file records the behaviour of Riesz–Coleman projections, complementary inverses, explicit
Riesz–Coleman projectors, and spectral-summand ranks and dimensions under bounded completed-tensor
base change on `(Pr)` modules and bounded coefficient-ring homomorphisms on model spaces
`C₀(I, R)`.

## Main results

* `ContinuousLinearMap.IsRieszColemanProjection.completedBaseChange`,
  `ContinuousLinearMap.IsRieszColemanProjection.inverse_completedBaseChange`,
  `ContinuousLinearMap.IsRieszColemanProjection.rankAtStalk_range_completedBaseChange`, and
  `ContinuousLinearMap.IsPrCompact.finrank_ker_aeval_reverse_completedBaseChange`: transport of
  Riesz–Coleman projections, complementary inverses, stalk ranks, and field kernel dimensions along
  completed-tensor base change on `(Pr)` modules for bounded scalar extensions.
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

open Polynomial TauCeti
open PowerSeries (IsEntire)
open scoped PowerSeries ZeroAtInfty NNReal TauCeti.RingOpNorm

local notation:70 S:71 " ⊗̂[" R "] " M:71 => (TauCeti.Huber.BanachModule.CompletedTensor R S M)

namespace ContinuousLinearMap

/-- Transports a Riesz–Coleman projection and its complementary inverse along an endomorphism ring
homomorphism `Φ` that matches reversed-polynomial evaluation and preserves the adjoin closure. -/
private theorem isRieszColemanProjection_map_and_inverse
    {R₁ R₂ : Type*} [NormedCommRing R₁] [TauCeti.NormedRing.IsTate R₁]
    [NormedCommRing R₂] [TauCeti.NormedRing.IsTate R₂]
    {M₁ M₂ : Type*} [SeminormedAddCommGroup M₁] [Module R₁ M₁] [IsBoundedSMul R₁ M₁]
    [SeminormedAddCommGroup M₂] [Module R₂ M₂] [IsBoundedSMul R₂ M₂]
    (Φ : (M₁ →L[R₁] M₁) →+* (M₂ →L[R₂] M₂))
    {u E : M₁ →L[R₁] M₁} {Q : R₁[X]} {Q' : R₂[X]}
    (hE : IsRieszColemanProjection u Q E)
    (haeval : Polynomial.aeval (Φ u) Q'.reverse = Φ (Polynomial.aeval u Q.reverse))
    (hclosure : ∀ {v : M₁ →L[R₁] M₁},
      v ∈ closure (Algebra.adjoin R₁ {u} : Set (M₁ →L[R₁] M₁)) →
      Φ v ∈ closure (Algebra.adjoin R₂ {Φ u} : Set (M₂ →L[R₂] M₂))) :
    ∃ hE' : IsRieszColemanProjection (Φ u) Q' (Φ E), hE'.inverse = Φ hE.inverse := by
  have hinv₁ : Polynomial.aeval (Φ u) Q'.reverse * Φ hE.inverse = 1 - Φ E := by
    rw [haeval, ← map_mul, hE.aeval_reverse_mul_inverse, map_sub, map_one]
  have hinv₂ : Φ hE.inverse * Polynomial.aeval (Φ u) Q'.reverse = 1 - Φ E := by
    rw [haeval, ← map_mul, hE.inverse_mul_aeval_reverse, map_sub, map_one]
  have hinv₃ : Φ E * Φ hE.inverse = 0 := by
    rw [← map_mul, hE.mul_inverse_eq_zero, map_zero]
  have hinv₄ : Φ hE.inverse * Φ E = 0 := by
    rw [← map_mul, hE.inverse_mul_eq_zero, map_zero]
  have hE' : IsRieszColemanProjection (Φ u) Q' (Φ E) :=
    ⟨by simpa [IsIdempotentElem] using congrArg Φ hE.isIdempotentElem.eq,
      by simpa [Commute, SemiconjBy] using congrArg Φ hE.commute.eq,
      hclosure hE.mem_closure_adjoin,
      by rw [haeval, ← map_mul, hE.aeval_reverse_mul_eq_zero, map_zero],
      ⟨Φ hE.inverse, hinv₁, hinv₂, hinv₃, hinv₄, hclosure hE.inverse_mem_closure_adjoin⟩⟩
  exact ⟨hE', (hE'.eq_inverse hinv₁ hinv₃).symm⟩

section PrBaseChange

universe u

variable {R S : Type*} [NormedCommRing R] [TauCeti.NormedRing.IsTate R]
  [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S] [Algebra R S]
  [TauCeti.NormedRing.IsTate S]
  {M N : Type u} [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  [SeminormedAddCommGroup N] [Module S N] [IsBoundedSMul S N]
  (hS : ∃ C : ℝ≥0, ∀ (r : R) (s : S), ‖r • s‖ ≤ C * ‖r‖ * ‖s‖)

include hS in
private theorem isRieszColemanProjection_completedBaseChange_aux (hM : HasPr R M)
    (α : S ⊗̂[R] M ≃L[S] N) {u E : M →L[R] M} {Q : R[X]}
    (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff) :
    ∃ hE' : IsRieszColemanProjection (u.completedBaseChange α α)
        (Polynomial.map (algebraMap R S) Q) (E.completedBaseChange α α),
      hE'.inverse = hE.inverse.completedBaseChange α α := by
  obtain ⟨hE', hinv⟩ := isRieszColemanProjection_map_and_inverse (completedBaseChangeRingHom α) hE
    (by rw [completedBaseChangeRingHom_apply,
      Polynomial.reverse_map_of_isUnit_leadingCoeff hQ (algebraMap R S), aeval_completedBaseChange,
      completedBaseChangeRingHom_apply])
    (fun hv ↦ by
      simpa only [completedBaseChangeRingHom_apply] using
        completedBaseChange_mem_closure_adjoin hS hM α hv)
  simp only [completedBaseChangeRingHom_apply] at hE' hinv
  exact ⟨hE', hinv⟩

include hS in
/-- **Riesz–Coleman projections under bounded completed-tensor base change.** On a `(Pr)` module
`M` over `R`, for a bounded scalar extension `S` satisfying `‖r • s‖ ≤ C * ‖r‖ * ‖s‖` and
`IsUnit Q.leadingCoeff`, `completedBaseChange` transports a Riesz–Coleman projection of `u` for `Q`
to one of `u.completedBaseChange α α` for `Q.map (algebraMap R S)` (no compactness needed). -/
theorem IsRieszColemanProjection.completedBaseChange (hM : HasPr R M) (α : S ⊗̂[R] M ≃L[S] N)
    {u E : M →L[R] M} {Q : R[X]} (hE : IsRieszColemanProjection u Q E)
    (hQ : IsUnit Q.leadingCoeff) :
    IsRieszColemanProjection (u.completedBaseChange α α) (Polynomial.map (algebraMap R S) Q)
      (E.completedBaseChange α α) :=
  (isRieszColemanProjection_completedBaseChange_aux hS hM α hE hQ).1

include hS in
/-- The complementary inverse of a Riesz–Coleman projection on a `(Pr)` module commutes with
completed-tensor base change for a bounded scalar extension `S` satisfying
`‖r • s‖ ≤ C * ‖r‖ * ‖s‖` when `Q.leadingCoeff` is a unit. -/
theorem IsRieszColemanProjection.inverse_completedBaseChange (hM : HasPr R M)
    (α : S ⊗̂[R] M ≃L[S] N) {u E : M →L[R] M} {Q : R[X]}
    (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff) :
    (hE.completedBaseChange hS hM α hQ).inverse = hE.inverse.completedBaseChange α α :=
  (isRieszColemanProjection_completedBaseChange_aux hS hM α hE hQ).2

include hS in
/-- **Constant stalk rank after bounded completed-tensor base change.** For a `(Pr)`-compact
operator `u` on a module `M` over a complete ultrametric Tate ring `R` with a Riesz–Coleman
projection `E` for a coprime factorisation `H_u = Q * S'`, where `IsUnit Q.leadingCoeff` and `S'`
is entire, completed-tensor base change along a bounded scalar extension `S` satisfying
`‖r • s‖ ≤ C * ‖r‖ * ‖s‖` yields a summand `(E.completedBaseChange α α).range` of constant stalk
rank `Q.natDegree` at every prime ideal of `S`. -/
theorem IsRieszColemanProjection.rankAtStalk_range_completedBaseChange
    [IsUltrametricDist R] [CompleteSpace R] (α : S ⊗̂[R] M ≃L[S] N)
    {u E : M →L[R] M} {Q : R[X]} {S' : R⟦X⟧}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact)
    (hQ : IsUnit Q.leadingCoeff) (hS' : S'.IsEntire)
    (hQS' : u.charPowerSeries = (Q : R⟦X⟧) * S')
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S', IsEntire.mem_subring.mpr hS'⟩)
    (q : PrimeSpectrum S) :
    Module.rankAtStalk (R := S) (E.completedBaseChange α α).range q = Q.natDegree := by
  have : Nontrivial S := q.nontrivial
  obtain ⟨C, hC⟩ := exists_norm_algebraMap_le_of_norm_smul_le hS
  obtain ⟨hQdeg, hQlc, hFS, hHS, hcopS⟩ :=
    IsEntire.map_factorisation hQ hS' hQS' hcop (algebraMap R S) hC
  rw [← hu.charPowerSeries_completedBaseChange hS α] at hHS
  rw [← hQdeg]
  exact (hE.completedBaseChange hS hu.hasPr_source α hQ).rankAtStalk_range_of_isPrCompact
    (hu.completedBaseChange hS α α) hQlc hFS hHS hcopS q

end PrBaseChange

section BaseChange

variable {I R S : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [NormedCommRing R] [TauCeti.NormedRing.IsTate R]
  [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S]
  [TauCeti.NormedRing.IsTate S]

private theorem isRieszColemanProjection_mapCoeffs_aux
    {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]}
    (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff)
    (f : R →+* S) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) :
    ∃ hE' : IsRieszColemanProjection (u.mapCoeffs f hf) (Q.map f) (E.mapCoeffs f hf),
      hE'.inverse = hE.inverse.mapCoeffs f hf := by
  obtain ⟨hE', hinv⟩ := isRieszColemanProjection_map_and_inverse (mapCoeffsRingHom f hf) hE
    (by
      simp only [mapCoeffsRingHom_apply]
      rw [reverse_map_of_isUnit_leadingCoeff hQ f, aeval_mapCoeffs])
    (fun hv ↦ by
      simpa only [mapCoeffsRingHom_apply] using mapCoeffs_mem_closure_adjoin f hf hv)
  simp only [mapCoeffsRingHom_apply] at hE' hinv
  exact ⟨hE', hinv⟩

/-- **Riesz–Coleman projections under bounded base change.** When `Q.leadingCoeff` is a unit, the
coefficientwise extension of a Riesz–Coleman projection of `u` for `Q` is a Riesz–Coleman
projection of `u.mapCoeffs f hf` for `Q.map f`. No compactness is needed. -/
theorem IsRieszColemanProjection.mapCoeffs {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]}
    (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff)
    (f : R →+* S) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) :
    IsRieszColemanProjection (u.mapCoeffs f hf) (Q.map f) (E.mapCoeffs f hf) :=
  (isRieszColemanProjection_mapCoeffs_aux hE hQ f hf).1

/-- The complementary inverse of a Riesz–Coleman projection commutes with bounded base change when
`Q.leadingCoeff` is a unit. -/
theorem IsRieszColemanProjection.inverse_mapCoeffs {u E : C₀(I, R) →L[R] C₀(I, R)}
    {Q : R[X]} (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff)
    (f : R →+* S) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) :
    (hE.mapCoeffs hQ f hf).inverse = hE.inverse.mapCoeffs f hf :=
  (isRieszColemanProjection_mapCoeffs_aux hE hQ f hf).2

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
  obtain ⟨-, hQlc, hFS, hHS, hcopS⟩ :=
    IsEntire.map_factorisation hQ hS' hQS' hcop f hf.choose_spec
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
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S', IsEntire.mem_subring.mpr hS'⟩)
    (f : R →+* S) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) (q : PrimeSpectrum S) :
    Module.rankAtStalk (R := S) (E.mapCoeffs f hf).range q = Q.natDegree := by
  have : Nontrivial S := q.nontrivial
  obtain ⟨hQdeg, hQlc, hFS, hHS, hcopS⟩ :=
    IsEntire.map_factorisation hQ hS' hQS' hcop f hf.choose_spec
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
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring K) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    Module.finrank L (Polynomial.aeval (u.mapCoeffs f hf) (Q.map f).reverse :
        C₀(I, L) →L[L] C₀(I, L)).ker =
      Module.finrank K (Polynomial.aeval u Q.reverse : C₀(I, K) →L[K] C₀(I, K)).ker := by
  have hQ := PowerSeries.isUnit_leadingCoeff_of_eq_coe_mul
    (Matrix.constantCoeff_charPowerSeries _) hQS
  obtain ⟨hQdeg, -, hLS, hHS, hcopL⟩ :=
    IsEntire.map_factorisation hQ hS hQS hcop f hf.choose_spec
  rw [← hu.charPowerSeries_map f hf] at hHS
  rw [(hu.mapCoeffs f hf).finrank_ker_aeval_reverse hLS hHS hcopL, hQdeg,
    hu.finrank_ker_aeval_reverse hS hQS hcop]

end FieldBaseChange

section PrFieldBaseChange

universe u

variable {K L : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L] [Algebra K L]
  {M N : Type u} [SeminormedAddCommGroup M] [Module K M] [ContinuousConstSMul K M]
  [SeminormedAddCommGroup N] [Module L N] [ContinuousConstSMul L N]

/-- **Completed-tensor field extension preserves `dim ker Q*(u)`.** For a coprime factorisation
`H_u = Q * S` of the Fredholm series of a `(Pr)`-compact operator `u` on `M` into a polynomial `Q`
and an entire series `S`, completed-tensor base change along a bounded field extension `L / K`
preserves the dimension of `ker Q*(u)`. -/
theorem IsPrCompact.finrank_ker_aeval_reverse_completedBaseChange
    (hL : ∃ C : ℝ≥0, ∀ (k : K) (l : L), ‖k • l‖ ≤ C * ‖k‖ * ‖l‖) (α : L ⊗̂[K] M ≃L[L] N)
    {u : M →L[K] M} (hu : u.IsPrCompact) {Q : K[X]} {S : K⟦X⟧} (hS : S.IsEntire)
    (hQS : u.charPowerSeries = (Q : K⟦X⟧) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring K) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    Module.finrank L (Polynomial.aeval (u.completedBaseChange α α)
        (Q.map (algebraMap K L)).reverse : N →L[L] N).ker =
      Module.finrank K (Polynomial.aeval u Q.reverse : M →L[K] M).ker := by
  have hQ := PowerSeries.isUnit_leadingCoeff_of_eq_coe_mul u.constantCoeff_charPowerSeries hQS
  obtain ⟨C, hC⟩ := exists_norm_algebraMap_le_of_norm_smul_le hL
  obtain ⟨hQdeg, -, hLS, hHS, hcopL⟩ :=
    IsEntire.map_factorisation hQ hS hQS hcop (algebraMap K L) hC
  rw [← hu.charPowerSeries_completedBaseChange hL α] at hHS
  rw [(hu.completedBaseChange hL α α).finrank_ker_aeval_reverse hLS hHS hcopL, hQdeg,
    hu.finrank_ker_aeval_reverse hS hQS hcop]

end PrFieldBaseChange

end ContinuousLinearMap
