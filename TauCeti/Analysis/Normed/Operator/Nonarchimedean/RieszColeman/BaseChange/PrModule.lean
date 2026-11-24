/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.PrModule.BaseChange
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszColeman.PrModule
import TauCeti.RingTheory.PowerSeries.Dvd
import TauCeti.RingTheory.PowerSeries.Entire.Coprime

/-!
# Completed-tensor base change of Riesz–Coleman projections on `(Pr)` modules

This file records the behaviour of Riesz–Coleman projections, complementary inverses, and
spectral-summand ranks and dimensions under bounded completed-tensor base change on `(Pr)`
modules.

## Main results

* `ContinuousLinearMap.IsRieszColemanProjection.completedBaseChange`,
  `ContinuousLinearMap.IsRieszColemanProjection.inverse_completedBaseChange`,
  `ContinuousLinearMap.IsRieszColemanProjection.rankAtStalk_range_completedBaseChange`, and
  `ContinuousLinearMap.IsPrCompact.finrank_ker_aeval_reverse_completedBaseChange`: transport of
  Riesz–Coleman projections, complementary inverses, stalk ranks, and field kernel dimensions along
  completed-tensor base change on `(Pr)` modules for bounded scalar extensions.

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
/-- **Riesz–Coleman projections under bounded completed-tensor base change.** On a `(Pr)` module
`M` over `R`, for a bounded scalar extension `S` satisfying `‖r • s‖ ≤ C * ‖r‖ * ‖s‖` and
`IsUnit Q.leadingCoeff`, `completedBaseChange` transports a Riesz–Coleman projection of `u` for `Q`
to one of `u.completedBaseChange α α` for `Q.map (algebraMap R S)` (no compactness needed). -/
theorem IsRieszColemanProjection.completedBaseChange (hM : HasPr R M) (α : S ⊗̂[R] M ≃L[S] N)
    {u E : M →L[R] M} {Q : R[X]} (hE : IsRieszColemanProjection u Q E)
    (hQ : IsUnit Q.leadingCoeff) :
    IsRieszColemanProjection (u.completedBaseChange α α) (Polynomial.map (algebraMap R S) Q)
      (E.completedBaseChange α α) := by
  simpa only [completedBaseChangeRingHom_apply] using
    hE.map (completedBaseChangeRingHom α)
      (by
        rw [completedBaseChangeRingHom_apply,
          Polynomial.reverse_map_of_isUnit_leadingCoeff hQ (algebraMap R S),
          aeval_completedBaseChange, completedBaseChangeRingHom_apply])
      (fun {v} hv ↦ by
        simpa only [completedBaseChangeRingHom_apply] using
          completedBaseChange_mem_closure_adjoin hS hM α hv)

include hS in
/-- The complementary inverse of a Riesz–Coleman projection on a `(Pr)` module commutes with
completed-tensor base change for a bounded scalar extension `S` satisfying
`‖r • s‖ ≤ C * ‖r‖ * ‖s‖` when `Q.leadingCoeff` is a unit. -/
@[simp]
theorem IsRieszColemanProjection.inverse_completedBaseChange (hM : HasPr R M)
    (α : S ⊗̂[R] M ≃L[S] N) {u E : M →L[R] M} {Q : R[X]}
    (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff) :
    (hE.completedBaseChange hS hM α hQ).inverse = hE.inverse.completedBaseChange α α := by
  have hinv := hE.inverse_map (completedBaseChangeRingHom α)
    (by
      rw [completedBaseChangeRingHom_apply,
        Polynomial.reverse_map_of_isUnit_leadingCoeff hQ (algebraMap R S),
        aeval_completedBaseChange, completedBaseChangeRingHom_apply])
    (fun {v} hv ↦ by
      simpa only [completedBaseChangeRingHom_apply] using
        completedBaseChange_mem_closure_adjoin hS hM α hv)
  simpa only [completedBaseChangeRingHom_apply] using hinv

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
    (hcop : IsCoprime (IsEntire.polynomialHom Q) ⟨S', IsEntire.mem_subring.mpr hS'⟩)
    (q : PrimeSpectrum S) :
    Module.rankAtStalk (R := S) (E.completedBaseChange α α).range q = Q.natDegree := by
  have : Nontrivial S := q.nontrivial
  obtain ⟨C, hC⟩ := exists_norm_algebraMap_le_of_norm_smul_le hS
  obtain ⟨hQdeg, hQlc, hFS, hHS, hcopS⟩ :=
    IsEntire.map_factorization hQ hS' hQS' hcop (algebraMap R S) hC
  rw [← hu.charPowerSeries_completedBaseChange hS α] at hHS
  rw [← hQdeg]
  exact (hE.completedBaseChange hS hu.hasPr_source α hQ).rankAtStalk_range_of_isPrCompact
    (hu.completedBaseChange hS α α) hQlc hFS hHS hcopS q

end PrBaseChange

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
    (hcop : IsCoprime (IsEntire.polynomialHom Q) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    Module.finrank L (Polynomial.aeval (u.completedBaseChange α α)
        (Q.map (algebraMap K L)).reverse : N →L[L] N).ker =
      Module.finrank K (Polynomial.aeval u Q.reverse : M →L[K] M).ker := by
  have hQ := PowerSeries.isUnit_leadingCoeff_of_eq_coe_mul u.constantCoeff_charPowerSeries hQS
  obtain ⟨C, hC⟩ := exists_norm_algebraMap_le_of_norm_smul_le hL
  obtain ⟨hQdeg, -, hLS, hHS, hcopL⟩ :=
    IsEntire.map_factorization hQ hS hQS hcop (algebraMap K L) hC
  rw [← hu.charPowerSeries_completedBaseChange hL α] at hHS
  rw [(hu.completedBaseChange hL α α).finrank_ker_aeval_reverse hLS hHS hcopL, hQdeg,
    hu.finrank_ker_aeval_reverse hS hQS hcop]

end PrFieldBaseChange

end ContinuousLinearMap
