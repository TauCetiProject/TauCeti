/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.BaseChange
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszColeman.Decomposition
import TauCeti.RingTheory.Polynomial.Resultant.Coleman

/-!
# Coefficientwise base change of Riesz–Coleman projections

Let `f : R →+* S` be a bounded unital homomorphism of normed commutative rings, with `R` Tate and
`S` complete ultrametric. Coefficientwise extension of endomorphisms of `C₀(J, R)` commutes with
polynomial evaluation (`ContinuousLinearMap.mapCoeffs_aeval`).

When `S` is also Tate, the coefficientwise extension of a Riesz–Coleman projection `E` of `u` at
`Q` is a Riesz–Coleman projection of `u.mapCoeffs f hf` at `Q.map f`, requiring no compactness and
only that `f` preserves the degree of `Q`: `(Q.map f).natDegree = Q.natDegree`
(`ContinuousLinearMap.IsRieszColemanProjection.mapCoeffs`). This degree-preservation hypothesis
ensures `(Q.map f).reverse = Q.reverse.map f`; it holds automatically whenever `Q` has unit leading
coefficient (`Polynomial.natDegree_map_eq_of_isUnit_leadingCoeff`) or `f` is injective
(`Polynomial.natDegree_map_eq_of_injective`).

For a row-compact `u` over complete ultrametric Tate rings `R, S`, when `Q` has invertible leading
coefficient and `Δ^(deg Q) H_(B(u))(1)` is a unit (where `B = 1 - lc(Q)⁻¹ Q*`), the explicit
projector commutes with base change
(`ContinuousLinearMap.IsRowCompact.rieszColemanProjection_mapCoeffs`). In particular, it holds for
any coprime polynomial factorisation `H_u = Q * S₀` with `lc(Q)` a unit and `S₀` entire
(`ContinuousLinearMap.IsRowCompact.rieszColemanProjection_mapCoeffs_of_eq_mul`).

Over a bounded field extension `f : K →+* L`, the coprime factorisation maps to a coprime
factorisation over `L`, and the dimension of `ker Q*(u)` is preserved
(`ContinuousLinearMap.IsRowCompact.finrank_ker_aeval_reverse_mapCoeffs`).

## Main results

* `ContinuousLinearMap.mapCoeffs_aeval`:
  `(aeval u p).mapCoeffs f hf = aeval (u.mapCoeffs f hf) (p.map f)`.
* `ContinuousLinearMap.IsRieszColemanProjection.mapCoeffs`: Riesz–Coleman projections transport
  along bounded base change whenever `deg (Q.map f) = deg Q`.
* `ContinuousLinearMap.IsRowCompact.rieszColemanProjection_mapCoeffs`: the explicit Riesz–Coleman
  projector commutes with bounded base change.
* `ContinuousLinearMap.IsRowCompact.rieszColemanProjection_mapCoeffs_of_eq_mul`: the same under a
  coprime factorisation `H_u = Q * S₀`.
* `ContinuousLinearMap.IsRowCompact.finrank_ker_aeval_reverse_mapCoeffs`: bounded field extension
  preserves `Module.finrank` of `ker Q*(u)`.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127** (1997),
  417–479, Appendix A4.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.2.
-/

public section

open Polynomial
open scoped ZeroAtInfty NNReal PowerSeries TauCeti.RingOpNorm

open PowerSeries (IsEntire)

namespace ContinuousLinearMap

section Ring

variable {J R S : Type*} [TopologicalSpace J] [DiscreteTopology J] [DecidableEq J]
  [NormedCommRing R] [TauCeti.NormedRing.IsTate R]
  [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S]

/-- Coefficientwise extension commutes with polynomial evaluation on endomorphisms of `C₀(J, R)`. -/
@[simp]
theorem mapCoeffs_aeval (u : C₀(J, R) →L[R] C₀(J, R)) (f : R →+* S)
    (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) (p : R[X]) :
    (Polynomial.aeval u p).mapCoeffs f hf = Polynomial.aeval (u.mapCoeffs f hf) (p.map f) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, Polynomial.map_add, mapCoeffs_add, hp, hq]
  | monomial n a =>
    simp only [Polynomial.map_monomial, aeval_monomial, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul, mapCoeffs_smul, mapCoeffs_pow]

/-- Mapping a polynomial commutes with `reverse` whenever the ring homomorphism preserves
`natDegree`. -/
private theorem reverse_map_of_natDegree_eq {A B : Type*} [Semiring A] [Semiring B]
    (f : A →+* B) {Q : A[X]} (hdeg : (Q.map f).natDegree = Q.natDegree) :
    (Q.map f).reverse = Q.reverse.map f := by
  rw [reverse, reverse, hdeg, reflect_map]

/-- **Riesz–Coleman projections under bounded base change.** The coefficientwise extension of a
Riesz–Coleman projection of `u` at `Q` is a Riesz–Coleman projection of the extension of `u` at
`Q.map f`, whenever `f` preserves `Q.natDegree` (in particular whenever `IsUnit Q.leadingCoeff`,
via `Polynomial.natDegree_map_eq_of_isUnit_leadingCoeff`, or when `f` is injective, via
`Polynomial.natDegree_map_eq_of_injective`). No compactness is needed. -/
theorem IsRieszColemanProjection.mapCoeffs [TauCeti.NormedRing.IsTate S]
    {u E : C₀(J, R) →L[R] C₀(J, R)} {Q : R[X]} (hE : IsRieszColemanProjection u Q E)
    (f : R →+* S) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖)
    (hdeg : (Q.map f).natDegree = Q.natDegree) :
    IsRieszColemanProjection (u.mapCoeffs f hf) (Q.map f) (E.mapCoeffs f hf) := by
  have hrev : (Q.map f).reverse = Q.reverse.map f := reverse_map_of_natDegree_eq f hdeg
  obtain ⟨w, hw₁, hw₂, hw₃, hw₄, hw⟩ := hE.exists_inverse
  refine ⟨?_, ?_, mapCoeffs_mem_closure_adjoin f hf hE.mem_closure_adjoin, ?_,
    ⟨w.mapCoeffs f hf, ?_, ?_, ?_, ?_, mapCoeffs_mem_closure_adjoin f hf hw⟩⟩
  · simpa [IsIdempotentElem] using congrArg (fun v ↦ v.mapCoeffs f hf) hE.isIdempotentElem.eq
  · simpa [Commute, SemiconjBy] using congrArg (fun v ↦ v.mapCoeffs f hf) hE.commute.eq
  · simpa [hrev] using congrArg (fun v ↦ v.mapCoeffs f hf) hE.aeval_reverse_mul_eq_zero
  · simpa [hrev] using congrArg (fun v ↦ v.mapCoeffs f hf) hw₁
  · simpa [hrev] using congrArg (fun v ↦ v.mapCoeffs f hf) hw₂
  · simpa using congrArg (fun v ↦ v.mapCoeffs f hf) hw₃
  · simpa using congrArg (fun v ↦ v.mapCoeffs f hf) hw₄

variable [IsUltrametricDist R] [CompleteSpace R] [TauCeti.NormedRing.IsTate S]

/-- **Bounded base change of the explicit Riesz–Coleman projector.** If `Q` has invertible leading
coefficient and `Δ^(deg Q) H_(B(u))(1)` is a unit (where `B = 1 - lc(Q)⁻¹ Q*`), then the explicit
Riesz–Coleman projector commutes with bounded coefficient extension. -/
theorem IsRowCompact.rieszColemanProjection_mapCoeffs {u : C₀(J, R) →L[R] C₀(J, R)}
    (hu : u.IsRowCompact) (f : R →+* S) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) {Q : R[X]}
    (hQ : IsUnit Q.leadingCoeff)
    (hc : IsUnit ((PowerSeries.hasseDeriv Q.natDegree
      ((Polynomial.aeval u
        (1 - C (Ring.inverse Q.leadingCoeff) * Q.reverse)).matrixCoeff.charPowerSeries)).evalAt
      (1 : R))) :
    (u.mapCoeffs f hf).rieszColemanProjection (Q.map f) =
      (u.rieszColemanProjection Q).mapCoeffs f hf := by
  rcases subsingleton_or_nontrivial S with hsub | hnontriv
  · ext x i
    exact Subsingleton.elim _ _
  have hdeg : (Q.map f).natDegree = Q.natDegree :=
    natDegree_map_eq_of_isUnit_leadingCoeff f hQ
  have hlc : (Q.map f).leadingCoeff = f Q.leadingCoeff :=
    leadingCoeff_map_eq_of_isUnit_leadingCoeff f hQ
  have hrev : (Q.map f).reverse = Q.reverse.map f := reverse_map_of_natDegree_eq f hdeg
  have hB0 : (1 - C (Ring.inverse Q.leadingCoeff) * Q.reverse).coeff 0 = 0 :=
    coeff_zero_one_sub_C_mul_reverse (Ring.inverse_mul_cancel Q.leadingCoeff hQ)
  have hinv : Ring.inverse (Q.map f).leadingCoeff = f (Ring.inverse Q.leadingCoeff) := by
    rw [hlc, hQ.map_ringInverse f]
  have hBmap :
      (1 - C (Ring.inverse Q.leadingCoeff) * Q.reverse).map f =
        1 - C (Ring.inverse (Q.map f).leadingCoeff) * (Q.map f).reverse := by
    simp [hinv, hrev]
  rw [rieszColemanProjection_def, rieszColemanProjection_def, hdeg, ← hBmap, ← mapCoeffs_aeval]
  simpa only [map_one] using (hu.aeval hB0).rieszProjection_mapCoeffs f hf hc

/-- **Bounded base change of the explicit Riesz–Coleman projector under a coprime factorisation.**
When `H_u = Q * S₀` with `lc(Q)` a unit, `S₀` entire, and `Q, S₀` coprime in `IsEntire.subring R`,
the explicit Riesz–Coleman projector commutes with bounded coefficient extension. -/
theorem IsRowCompact.rieszColemanProjection_mapCoeffs_of_eq_mul {u : C₀(J, R) →L[R] C₀(J, R)}
    (hu : u.IsRowCompact) (f : R →+* S) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖)
    {Q : R[X]} {S₀ : R⟦X⟧} (hH : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S₀)
    (hQ : IsUnit Q.leadingCoeff) (hS : S₀.IsEntire)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S₀, IsEntire.mem_subring.mpr hS⟩) :
    (u.mapCoeffs f hf).rieszColemanProjection (Q.map f) =
      (u.rieszColemanProjection Q).mapCoeffs f hf :=
  hu.rieszColemanProjection_mapCoeffs f hf hQ
    (hu.isGoodZero_charPowerSeries_aeval_one_sub_C_mul_reverse hH
      (Ring.inverse_mul_cancel Q.leadingCoeff hQ) hS hcop).isUnit_evalAt_hasseDeriv

end Ring

section Field

variable {I K L : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
  {u : C₀(I, K) →L[K] C₀(I, K)}

/-- Bounded field extension preserves the dimension of `ker Q*(u)` for every coprime polynomial
factor `Q` of `H_u = Q * S` with `S` entire. -/
theorem IsRowCompact.finrank_ker_aeval_reverse_mapCoeffs (hu : u.IsRowCompact)
    (f : K →+* L) (hf : ∃ C : ℝ≥0, ∀ x, ‖f x‖ ≤ C * ‖x‖) {Q : K[X]} {S : K⟦X⟧}
    (hH : u.matrixCoeff.charPowerSeries = (Q : K⟦X⟧) * S) (hS : S.IsEntire)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring K) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    Module.finrank L (LinearMap.ker ((Polynomial.aeval (u.mapCoeffs f hf) (Q.map f).reverse :
      C₀(I, L) →L[L] C₀(I, L)) : Module.End L C₀(I, L))) =
    Module.finrank K (LinearMap.ker ((Polynomial.aeval u Q.reverse :
      C₀(I, K) →L[K] C₀(I, K)) : Module.End K C₀(I, K))) := by
  obtain ⟨C, hC⟩ := hf
  have hS' : (PowerSeries.map f S).IsEntire := hS.map f hC
  have hH' : (u.mapCoeffs f ⟨C, hC⟩).matrixCoeff.charPowerSeries =
      ((Q.map f : L[X]) : L⟦X⟧) * PowerSeries.map f S := by
    rw [hu.charPowerSeries_map f ⟨C, hC⟩, hH, map_mul, Polynomial.polynomial_map_coe]
  have hcop' : IsCoprime
      (⟨Q.map f, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe (Q.map f))⟩ :
        IsEntire.subring L) ⟨PowerSeries.map f S, IsEntire.mem_subring.mpr hS'⟩ := by
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := hcop
    refine ⟨⟨PowerSeries.map f a, IsEntire.mem_subring.mpr ((IsEntire.mem_subring.mp ha).map f hC)⟩,
      ⟨PowerSeries.map f b, IsEntire.mem_subring.mpr ((IsEntire.mem_subring.mp hb).map f hC)⟩,
      Subtype.ext ?_⟩
    have hval := congrArg (PowerSeries.map f) (congrArg Subtype.val hab)
    simpa [Polynomial.polynomial_map_coe] using hval
  rw [(hu.mapCoeffs f ⟨C, hC⟩).finrank_ker_aeval_reverse hH' hS' hcop',
    hu.finrank_ker_aeval_reverse hH hS hcop,
    natDegree_map_eq_of_injective f.injective]

end Field

end ContinuousLinearMap
