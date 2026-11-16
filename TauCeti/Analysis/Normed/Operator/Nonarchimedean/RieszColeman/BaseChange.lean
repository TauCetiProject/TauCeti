/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.BaseChange
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszColeman.ModelSpace
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Coefficientwise base change of Riesz–Coleman projections

Let `f : R →+* S` be a bounded unital homomorphism of normed commutative rings, with `R` Tate and
`S` complete ultrametric Tate, and let `u_S = u.mapCoeffs f hf` be the coefficientwise extension of
an endomorphism `u` of a model space `C₀(J, R)`.

If `Q` is a polynomial over `R` with invertible leading coefficient, then `(Q.map f).reverse` is
`Q.reverse.map f`, so `(Q.map f)*(u_S) = (Q*(u))_S`. Consequently, the coefficientwise extension of
any Riesz–Coleman projection of `u` for `Q` is a Riesz–Coleman projection of `u_S` for `Q.map f`,
and the same holds for its complementary inverse
(`ContinuousLinearMap.IsRieszColemanProjection.mapCoeffs`,
`ContinuousLinearMap.IsRieszColemanProjection.inverse_mapCoeffs`). Neither statement requires
row compactness.

For row-compact `u` over complete ultrametric Tate rings, a coprime factorisation `H_u = Q * F`
pushes forward under `f` to a coprime factorisation `H_{u_S} = (Q.map f) * (PowerSeries.map f F)`,
so the base-changed Riesz–Coleman summand has constant stalk rank `deg Q` at every point of
`Spec S`. Over complete ultrametric fields, bounded field extension preserves the dimension of
`ker Q*(u)` (`ContinuousLinearMap.IsRowCompact.finrank_ker_aeval_reverse_mapCoeffs`).

## Main results

* `ContinuousLinearMap.IsRieszColemanProjection.mapCoeffs`: coefficientwise base change of
  Riesz–Coleman projections, without compactness.
* `ContinuousLinearMap.IsRieszColemanProjection.inverse_mapCoeffs`: compatibility of the
  complementary inverse with bounded base change.
* `ContinuousLinearMap.IsRieszColemanProjection.rankAtStalk_range_mapCoeffs`: stalk rank after
  bounded base change of a coprime factorisation.
* `ContinuousLinearMap.IsRowCompact.finrank_ker_aeval_reverse_mapCoeffs`: bounded field extension
  preserves `dim ker Q*(u)`.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127** (1997),
  417–479, Appendix A4.
* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §7, Proposition 12.
-/

public section

open scoped ZeroAtInfty NNReal TauCeti.RingOpNorm PowerSeries
open PowerSeries (IsEntire)

namespace ContinuousLinearMap

/-- Reversal commutes with ring homomorphisms on polynomials with invertible leading
coefficient. -/
private theorem reverse_map_of_isUnit_leadingCoeff {R S : Type*} [Semiring R] [Semiring S]
    {Q : Polynomial R} (hQ : IsUnit Q.leadingCoeff) (f : R →+* S) :
    (Q.map f).reverse = Q.reverse.map f := by
  rcases subsingleton_or_nontrivial S with hS | hS
  · exact Subsingleton.elim _ _
  · rw [Polynomial.reverse, Polynomial.reverse,
      Polynomial.natDegree_map_eq_of_isUnit_leadingCoeff f hQ, Polynomial.reflect_map]

/-- Bounded ring homomorphisms preserve coprimality in the ring of entire series. -/
private theorem isCoprime_map_entire {R S : Type*} [NormedCommRing R] [NormedCommRing S]
    {Q : Polynomial R} {F : R⟦X⟧} (hF : F.IsEntire)
    (f : R →+* S) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨F, IsEntire.mem_subring.mpr hF⟩) :
    IsCoprime
      (⟨Q.map f, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe (Q.map f))⟩ :
        IsEntire.subring S)
      ⟨PowerSeries.map f F,
        IsEntire.mem_subring.mpr (hF.map f (C := hf.choose) hf.choose_spec)⟩ := by
  obtain ⟨a, b, hab⟩ := hcop
  refine ⟨⟨PowerSeries.map f a.1,
      IsEntire.mem_subring.mpr ((IsEntire.mem_subring.mp a.2).map f hf.choose_spec)⟩,
    ⟨PowerSeries.map f b.1,
      IsEntire.mem_subring.mpr ((IsEntire.mem_subring.mp b.2).map f hf.choose_spec)⟩, ?_⟩
  apply Subtype.ext
  have hab' := congrArg (PowerSeries.map f ∘ Subtype.val) hab
  have hQmap : ((Q.map f : Polynomial S) : S⟦X⟧) = PowerSeries.map f (Q : R⟦X⟧) := by
    ext n
    simp
  simpa only [Function.comp_apply, Subring.coe_add, Subring.coe_mul, OneMemClass.coe_one,
    map_add, map_mul, map_one, hQmap] using hab'

section General

variable {J R S : Type*} [TopologicalSpace J] [DiscreteTopology J] [DecidableEq J]
  [NormedCommRing R] [TauCeti.NormedRing.IsTate R]
  [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S] [TauCeti.NormedRing.IsTate S]

/-- **Riesz–Coleman projections under bounded base change.** If `Q` has invertible leading
coefficient, the coefficientwise extension of a Riesz–Coleman projection of `u` for `Q` is a
Riesz–Coleman projection of `u.mapCoeffs f hf` for `Q.map f`. No compactness is needed. -/
theorem IsRieszColemanProjection.mapCoeffs {u E : C₀(J, R) →L[R] C₀(J, R)} {Q : Polynomial R}
    (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff)
    (f : R →+* S) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) :
    IsRieszColemanProjection (u.mapCoeffs f hf) (Q.map f) (E.mapCoeffs f hf) := by
  have hrev : (Q.map f).reverse = Q.reverse.map f := reverse_map_of_isUnit_leadingCoeff hQ f
  have haeval : Polynomial.aeval (u.mapCoeffs f hf) (Q.map f).reverse =
      (Polynomial.aeval u Q.reverse).mapCoeffs f hf := by
    rw [hrev, mapCoeffs_aeval]
  obtain ⟨w, hw₁, hw₂, hw₃, hw₄, hw⟩ := hE.exists_inverse
  refine ⟨?_, ?_, mapCoeffs_mem_closure_adjoin f hf hE.mem_closure_adjoin, ?_,
    ⟨w.mapCoeffs f hf, ?_, ?_, ?_, ?_, mapCoeffs_mem_closure_adjoin f hf hw⟩⟩
  · simpa [IsIdempotentElem] using congrArg (fun v ↦ v.mapCoeffs f hf) hE.isIdempotentElem.eq
  · simpa [Commute, SemiconjBy] using congrArg (fun v ↦ v.mapCoeffs f hf) hE.commute.eq
  · simpa [haeval] using congrArg (fun v ↦ v.mapCoeffs f hf) hE.aeval_reverse_mul_eq_zero
  · simpa [haeval] using congrArg (fun v ↦ v.mapCoeffs f hf) hw₁
  · simpa [haeval] using congrArg (fun v ↦ v.mapCoeffs f hf) hw₂
  · simpa using congrArg (fun v ↦ v.mapCoeffs f hf) hw₃
  · simpa using congrArg (fun v ↦ v.mapCoeffs f hf) hw₄

/-- The complementary inverse of a Riesz–Coleman projection commutes with bounded base change. -/
theorem IsRieszColemanProjection.inverse_mapCoeffs {u E : C₀(J, R) →L[R] C₀(J, R)}
    {Q : Polynomial R} (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff)
    (f : R →+* S) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) :
    (hE.mapCoeffs hQ f hf).inverse = hE.inverse.mapCoeffs f hf := by
  have hrev : (Q.map f).reverse = Q.reverse.map f := reverse_map_of_isUnit_leadingCoeff hQ f
  have haeval : Polynomial.aeval (u.mapCoeffs f hf) (Q.map f).reverse =
      (Polynomial.aeval u Q.reverse).mapCoeffs f hf := by
    rw [hrev, mapCoeffs_aeval]
  refine ((hE.mapCoeffs hQ f hf).eq_inverse ?_ ?_).symm
  · simpa [haeval] using congrArg (fun v ↦ v.mapCoeffs f hf) hE.aeval_reverse_mul_inverse
  · rw [← mapCoeffs_mul, hE.mul_inverse_eq_zero, mapCoeffs_zero]

end General

section RowCompact

variable {I R S : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R] [TauCeti.NormedRing.IsTate R]
  [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S] [TauCeti.NormedRing.IsTate S]

/-- After bounded base change, the Riesz–Coleman summand of a coprime factorisation `H_u = Q * F`
has constant stalk rank `deg Q` at every prime ideal of `S`. -/
theorem IsRieszColemanProjection.rankAtStalk_range_mapCoeffs
    {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : Polynomial R} {F : R⟦X⟧}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact)
    (hH : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * F) (hQ : IsUnit Q.leadingCoeff)
    (hF : F.IsEntire)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨F, IsEntire.mem_subring.mpr hF⟩)
    (f : R →+* S) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) (q : PrimeSpectrum S) :
    Module.rankAtStalk (R := S) (E.mapCoeffs f hf).range q = Q.natDegree := by
  have : Nontrivial S :=
    ⟨⟨1, 0, fun h ↦ q.isPrime.ne_top ((Ideal.eq_top_iff_one q.asIdeal).2 (h ▸ q.asIdeal.zero_mem))⟩⟩
  have hQdeg : (Q.map f).natDegree = Q.natDegree :=
    Polynomial.natDegree_map_eq_of_isUnit_leadingCoeff f hQ
  have hQlc : IsUnit (Q.map f).leadingCoeff := by
    have hlc : (Q.map f).leadingCoeff = f Q.leadingCoeff := by
      rw [Polynomial.leadingCoeff, Polynomial.leadingCoeff, hQdeg, Polynomial.coeff_map]
    rw [hlc]
    exact hQ.map f
  have hQmap : ((Q.map f : Polynomial S) : S⟦X⟧) = PowerSeries.map f (Q : R⟦X⟧) := by
    ext n
    simp
  have hHS : (u.mapCoeffs f hf).matrixCoeff.charPowerSeries =
      ((Q.map f : Polynomial S) : S⟦X⟧) * PowerSeries.map f F := by
    rw [hu.charPowerSeries_map f hf, hH, map_mul, hQmap]
  have hFS : (PowerSeries.map f F).IsEntire := hF.map f (C := hf.choose) hf.choose_spec
  rw [← hQdeg]
  exact (hE.mapCoeffs hQ f hf).rankAtStalk_range (hu.mapCoeffs f hf) hHS hQlc hFS
    (isCoprime_map_entire hF f hf hcop) q

end RowCompact

section Field

variable {I K L : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  {u : C₀(I, K) →L[K] C₀(I, K)}

/-- **Bounded field extension preserves `dim ker Q*(u)`.** For a coprime factorisation `H_u = Q * F`
of the Fredholm series of a row-compact operator `u` on `C₀(I, K)`, bounded coefficient extension
along `f : K →+* L` preserves the dimension of the Riesz–Coleman summand `ker Q*(u)`. -/
theorem IsRowCompact.finrank_ker_aeval_reverse_mapCoeffs (hu : u.IsRowCompact)
    (f : K →+* L) (hf : ∃ C : ℝ≥0, ∀ x, ‖f x‖ ≤ C * ‖x‖) {Q : Polynomial K} {F : K⟦X⟧}
    (hH : u.matrixCoeff.charPowerSeries = (Q : K⟦X⟧) * F) (hF : F.IsEntire)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring K)
      ⟨F, IsEntire.mem_subring.mpr hF⟩) :
    Module.finrank L (LinearMap.ker
      ((Polynomial.aeval (u.mapCoeffs f hf) (Q.map f).reverse : C₀(I, L) →L[L] C₀(I, L)) :
        Module.End L C₀(I, L))) =
    Module.finrank K (LinearMap.ker
      ((Polynomial.aeval u Q.reverse : C₀(I, K) →L[K] C₀(I, K)) : Module.End K C₀(I, K))) := by
  have hQne : Q ≠ 0 := by
    rintro rfl
    have h0 := congrArg PowerSeries.constantCoeff hH
    simp at h0
  have hQ : IsUnit Q.leadingCoeff := (Polynomial.leadingCoeff_ne_zero.2 hQne).isUnit
  have hQdeg : (Q.map f).natDegree = Q.natDegree :=
    Polynomial.natDegree_map_eq_of_isUnit_leadingCoeff f hQ
  have hQmap : ((Q.map f : Polynomial L) : L⟦X⟧) = PowerSeries.map f (Q : K⟦X⟧) := by
    ext n
    simp
  have hHL : (u.mapCoeffs f hf).matrixCoeff.charPowerSeries =
      ((Q.map f : Polynomial L) : L⟦X⟧) * PowerSeries.map f F := by
    rw [hu.charPowerSeries_map f hf, hH, map_mul, hQmap]
  have hFL : (PowerSeries.map f F).IsEntire := hF.map f (C := hf.choose) hf.choose_spec
  rw [(hu.mapCoeffs f hf).finrank_ker_aeval_reverse hHL hFL (isCoprime_map_entire hF f hf hcop),
    hu.finrank_ker_aeval_reverse hH hF hcop, hQdeg]

end Field

end ContinuousLinearMap
