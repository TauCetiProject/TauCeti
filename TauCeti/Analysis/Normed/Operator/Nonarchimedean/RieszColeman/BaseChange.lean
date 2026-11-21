/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.PrModule.BaseChange
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszColeman.PrModule

/-!
# Riesz–Coleman projections under completed-tensor base change

Let `R` be a complete ultrametric Tate normed commutative ring, `S` a complete ultrametric Tate
normed commutative `R`-algebra with bounded scalar action, `M` a Banach `R`-module with property
`(Pr)`, and `α : S ⊗̂_R M ≃L[S] N` a realisation of its completed scalar extension. For an
operator `u` on `M` write `u_S = u.completedBaseChange α α` for its extension to `N`.

When `Q.leadingCoeff` is a unit, extending a Riesz–Coleman projection `E` of `u` for `Q` gives a
Riesz–Coleman projection `E_S` of `u_S` for `Q.map (algebraMap R S)`
(`ContinuousLinearMap.IsRieszColemanProjection.completedBaseChange`), and by uniqueness every
Riesz–Coleman projection of `u_S` for this polynomial is `E_S`
(`ContinuousLinearMap.IsRieszColemanProjection.eq_completedBaseChange`). Thus the projector onto
`ker (Q.map (algebraMap R S))*(u_S)` along its invariant complement is the extension of the
projector onto `ker Q*(u)`.

If moreover `u` is `(Pr)`-compact with a coprime factorisation `H_u = Q * F` as in the
Riesz–Coleman decomposition, the factorisation maps to a coprime factorisation of `H_(u_S)`, so the
extended summand `range E_S = ker (Q.map (algebraMap R S))*(u_S)` again has constant stalk rank
`Q.natDegree` on `Spec S`
(`ContinuousLinearMap.IsRieszColemanProjection.rankAtStalk_range_completedBaseChange`). Over a
complete extension `L` of a complete ultrametric field `K`, the dimension of the summand is
therefore unchanged
(`ContinuousLinearMap.IsRieszColemanProjection.finrank_range_completedBaseChange`).

## Main results

* `ContinuousLinearMap.IsRieszColemanProjection.completedBaseChange`: Riesz–Coleman projections
  extend along completed base change.
* `ContinuousLinearMap.IsRieszColemanProjection.eq_completedBaseChange`: the extended projection is
  the unique Riesz–Coleman projection of `u_S` for `Q.map (algebraMap R S)`.
* `ContinuousLinearMap.IsRieszColemanProjection.rankAtStalk_range_completedBaseChange` and
  `ContinuousLinearMap.IsRieszColemanProjection.finrank_range_completedBaseChange`: the extended
  summand has stalk rank, respectively dimension, `Q.natDegree`.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127** (1997),
  417–479, Appendix A, A4.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §§2.1–2.2.
-/

public section

open Polynomial TauCeti TauCeti.Huber.BanachModule
open PowerSeries (IsEntire)
open scoped PowerSeries NNReal

universe u

local notation:70 S:71 " ⊗̂[" R "] " M:71 => (CompletedTensor R S M)

namespace ContinuousLinearMap

section Projection

variable {R S : Type*} [NormedCommRing R] [TauCeti.NormedRing.IsTate R]
  [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S] [Algebra R S]
  [TauCeti.NormedRing.IsTate S]
  {M N : Type u} [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  [SeminormedAddCommGroup N] [Module S N] [IsBoundedSMul S N]
  (hS : ∃ C : ℝ≥0, ∀ (r : R) (s : S), ‖r • s‖ ≤ C * ‖r‖ * ‖s‖)

include hS

/-- **Riesz–Coleman projections under completed-tensor base change.** On a `(Pr)` module `M` over
`R`, when `Q.leadingCoeff` is a unit, `completedBaseChange` transports a Riesz–Coleman projection
of `u` for `Q` to one of `u.completedBaseChange α α` for `Q.map (algebraMap R S)`. No compactness is
needed. -/
theorem IsRieszColemanProjection.completedBaseChange (hM : HasPr R M) (α : S ⊗̂[R] M ≃L[S] N)
    {u E : M →L[R] M} {Q : R[X]} (hE : IsRieszColemanProjection u Q E)
    (hQ : IsUnit Q.leadingCoeff) :
    IsRieszColemanProjection (u.completedBaseChange α α) (Q.map (algebraMap R S))
      (E.completedBaseChange α α) := by
  let Φ := completedBaseChangeRingHom α
  have hrev : Polynomial.aeval (u.completedBaseChange α α) (Q.map (algebraMap R S)).reverse =
      (Polynomial.aeval u Q.reverse).completedBaseChange α α := by
    rw [reverse_map_of_isUnit_leadingCoeff hQ, aeval_completedBaseChange]
  obtain ⟨w, hw₁, hw₂, hw₃, hw₄, hw⟩ := hE.exists_inverse
  refine ⟨by simpa [IsIdempotentElem, Φ] using congrArg Φ hE.isIdempotentElem.eq,
    by simpa [Commute, SemiconjBy, Φ] using congrArg Φ hE.commute.eq,
    completedBaseChange_mem_closure_adjoin hS hM α hE.mem_closure_adjoin, ?_,
    ⟨w.completedBaseChange α α, ?_, ?_, ?_, ?_, completedBaseChange_mem_closure_adjoin hS hM α hw⟩⟩
  · simpa [hrev, Φ] using congrArg Φ hE.aeval_reverse_mul_eq_zero
  · simpa [hrev, Φ] using congrArg Φ hw₁
  · simpa [hrev, Φ] using congrArg Φ hw₂
  · simpa [Φ] using congrArg Φ hw₃
  · simpa [Φ] using congrArg Φ hw₄

/-- **Uniqueness of the extended Riesz–Coleman projection.** When `Q.leadingCoeff` is a unit, every
Riesz–Coleman projection of `u.completedBaseChange α α` for `Q.map (algebraMap R S)` is the
extension `E.completedBaseChange α α` of a Riesz–Coleman projection `E` of `u` for `Q`. -/
theorem IsRieszColemanProjection.eq_completedBaseChange (hM : HasPr R M) (α : S ⊗̂[R] M ≃L[S] N)
    {u E : M →L[R] M} {Q : R[X]} (hE : IsRieszColemanProjection u Q E)
    (hQ : IsUnit Q.leadingCoeff) {E' : N →L[S] N}
    (hE' : IsRieszColemanProjection (u.completedBaseChange α α) (Q.map (algebraMap R S)) E') :
    E' = E.completedBaseChange α α :=
  hE'.unique (hE.completedBaseChange hS hM α hQ)

end Projection

section Rank

variable {R S : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [TauCeti.NormedRing.IsTate R]
  [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S] [Algebra R S]
  [TauCeti.NormedRing.IsTate S]
  {M N : Type u} [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  [SeminormedAddCommGroup N] [Module S N] [IsBoundedSMul S N]
  (hS : ∃ C : ℝ≥0, ∀ (r : R) (s : S), ‖r • s‖ ≤ C * ‖r‖ * ‖s‖)

include hS

/-- **Stalk rank of the extended Riesz–Coleman summand.** Let `u` be a `(Pr)`-compact operator
with a coprime factorisation `H_u = Q * F`, where `Q(0) = 1`, `Q.leadingCoeff` is a unit and `F` is
entire. Then the range of the extension of a Riesz–Coleman projection of `u` for `Q` along
`α : S ⊗̂_R M ≃L[S] N` has rank `Q.natDegree` at every prime ideal of `S`. -/
theorem IsRieszColemanProjection.rankAtStalk_range_completedBaseChange {u E : M →L[R] M} {Q : R[X]}
    {F : R⟦X⟧} (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact)
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hF : F.IsEntire)
    (hQF : u.charPowerSeries = (Q : R⟦X⟧) * F)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨F, IsEntire.mem_subring.mpr hF⟩)
    (α : S ⊗̂[R] M ≃L[S] N) (p : PrimeSpectrum S) :
    Module.rankAtStalk (R := S) (E.completedBaseChange α α).range p = Q.natDegree := by
  obtain ⟨C, hC⟩ := exists_norm_algebraMap_le_of_norm_smul_le hS
  let f := algebraMap R S
  rcases subsingleton_or_nontrivial S with hSsub | hSnt
  · exact absurd (Subsingleton.elim p.asIdeal ⊤) p.isPrime.ne_top
  have hQS : IsUnit (Q.map f).leadingCoeff := by
    rw [leadingCoeff_map_of_leadingCoeff_ne_zero f (hQ.map f).ne_zero]; exact hQ.map f
  have hcopS : IsCoprime
      (⟨(Q.map f : S⟦X⟧), IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe _)⟩ :
        IsEntire.subring S) ⟨PowerSeries.map f F, IsEntire.mem_subring.mpr (hF.map f hC)⟩ := by
    convert hcop.map (IsEntire.mapHom f hC) <;> ext1 <;> simp [Polynomial.polynomial_map_coe]
  have hrank := (hE.completedBaseChange hS hu.hasPr_source α hQ).rankAtStalk_range_of_isPrCompact
    (hu.completedBaseChange hS α α) (by simp [hQ0]) hQS (hF.map f hC)
    (by rw [hu.charPowerSeries_completedBaseChange hS α, hQF, map_mul,
      Polynomial.polynomial_map_coe]) hcopS p
  rwa [natDegree_map_of_leadingCoeff_ne_zero f (hQ.map f).ne_zero] at hrank

end Rank

section Field

variable {K L : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]
  {M N : Type u} [SeminormedAddCommGroup M] [Module K M] [IsBoundedSMul K M]
  [SeminormedAddCommGroup N] [Module L N] [IsBoundedSMul L N]

/-- **Dimension of the Riesz–Coleman summand under complete field extension.** Let `u` be a
`(Pr)`-compact operator over a complete ultrametric field `K` with a coprime factorisation
`H_u = Q * F`, where `Q(0) = 1` and `F` is entire, and let `E` be a Riesz–Coleman projection of `u`
for `Q`. Over a complete ultrametric extension `L`, the extension of `E` along
`α : L ⊗̂_K M ≃L[L] N` has range of the same dimension `Q.natDegree` as `range E`. -/
theorem IsRieszColemanProjection.finrank_range_completedBaseChange {u E : M →L[K] M} {Q : K[X]}
    {F : K⟦X⟧} (hE : IsRieszColemanProjection u Q E) (hu : u.IsPrCompact)
    (hQ0 : Q.coeff 0 = 1) (hF : F.IsEntire)
    (hQF : u.charPowerSeries = (Q : K⟦X⟧) * F)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring K) ⟨F, IsEntire.mem_subring.mpr hF⟩)
    (α : L ⊗̂[K] M ≃L[L] N) :
    Module.finrank L (E.completedBaseChange α α).range = Module.finrank K E.range := by
  have hQ : IsUnit Q.leadingCoeff :=
    IsUnit.mk0 _ (leadingCoeff_ne_zero.mpr fun h ↦ by simp [h] at hQ0)
  have hS : ∃ C : ℝ≥0, ∀ (r : K) (s : L), ‖r • s‖ ≤ C * ‖r‖ * ‖s‖ :=
    ⟨1, fun r s ↦ by simpa using norm_smul_le r s⟩
  have hr := hE.rankAtStalk_range_completedBaseChange hS hu hQ0 hQ hF hQF hcop α
    ⟨⊥, Ideal.isPrime_bot⟩
  rw [Module.rankAtStalk_eq_finrank_of_free] at hr
  rwa [hE.finrank_range_of_isPrCompact hu hQ0 hF hQF hcop]

end Field

end ContinuousLinearMap
