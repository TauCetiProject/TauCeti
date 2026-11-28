/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Topology.Algebra.Module.Complement
public import TauCeti.Analysis.Normed.Operator.RingOpNorm.SpectralProjection
public import TauCeti.Analysis.Normed.Operator.RowCompact.Idempotent
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Smeval
import TauCeti.Algebra.Polynomial.AlgebraMap
import TauCeti.Algebra.Polynomial.Reverse
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.IdempotentRange
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Intertwining

/-!
# Riesz–Coleman projections and topological polynomial spectral splittings

Let `R` be a seminormed commutative ring with Tate scalars (`TauCeti.NormedRing.IsTate R`), `M` a
seminormed `R`-module with bounded scalar action, `u : M →L[R] M` a bounded endomorphism, and
`Q : R[X]` a polynomial with reversal `Q* = Q.reverse`.

A **Riesz–Coleman projection** of `u` for `Q` (`ContinuousLinearMap.IsRieszColemanProjection`) is
a spectral projection (`ContinuousLinearMap.IsSpectralProjection`) of `u` for `Q*(u)` of order `1`:
an idempotent `E` commuting with `u` and lying in the operator-norm closure of `R[u]`, such that
`Q*(u) * E = 0` and `Q*(u)` has a two-sided inverse `w` on the complementary summand `ker E =
range (1 - E)` with `w` again in the closure of `R[u]`. It yields a topological direct-sum
decomposition

  `M = ker Q*(u) ⊕ range Q*(u)`

into `u`-stable submodules (`ContinuousLinearMap.IsSpectralProjection.range_eq_ker_spectral`,
`ContinuousLinearMap.IsSpectralProjection.range_spectral_eq_ker`,
`ContinuousLinearMap.IsSpectralProjection.isTopCompl_ker_range_spectral`), on which
`Q*(u)` vanishes on the first summand and restricts to a continuous linear automorphism of the
second (`ContinuousLinearMap.IsSpectralProjection.equivKer`). Such a projection is unique
(`ContinuousLinearMap.IsSpectralProjection.unique`); for `Q = 1` it is zero
(`ContinuousLinearMap.isRieszColemanProjection_one_iff`,
`ContinuousLinearMap.IsRieszColemanProjection.eq_zero_of_one`,
`ContinuousLinearMap.isRieszColemanProjection_one_zero`), and scaling `Q` by a unit of `R` leaves
the predicate unchanged (`ContinuousLinearMap.IsRieszColemanProjection.C_mul`,
`ContinuousLinearMap.isRieszColemanProjection_C_mul_iff`).

When the leading coefficient of `Q` is a unit, the constant term of `Q*` is `Q.leadingCoeff`, so
dividing `Q* - Q*(0)` by `X` expresses `E = u * ((-lc(Q)⁻¹) • (Q*.divX)(u) * E)`, and
`Q*(u * (1 - E))` is invertible
(`ContinuousLinearMap.IsRieszColemanProjection.isUnit_aeval_mul_one_sub_reverse`). Consequently:

* `u` restricts to a continuous linear automorphism of `range E = ker Q*(u)`
  (`ContinuousLinearMap.IsRieszColemanProjection.equivRange`);
* on a model space `C₀(I, R)` over an ultrametric `R`, if `u` is row compact then `E` is row
  compact (`ContinuousLinearMap.IsRieszColemanProjection.isRowCompact`), and if `R` is also
  complete then `ker Q*(u)` is finitely generated and projective over `R`
  (`ContinuousLinearMap.IsRieszColemanProjection.finite_ker_aeval_reverse`,
  `ContinuousLinearMap.IsRieszColemanProjection.projective_ker_aeval_reverse`), without assuming
  `R` Noetherian or reduced;
* Riesz–Coleman projections compress along continuous linear retracts `r ∘ i = id`, and when
  `lc(Q)` is a unit the extension `i ∘ E ∘ r` recovers the ambient projection on `N` and `i`, `r`
  identify `range E` with `range E'`
  (`ContinuousLinearMap.IsRieszColemanProjection.comp_comp_of_retract`,
  `ContinuousLinearMap.IsRieszColemanProjection.comp_comp_eq_of_retract`,
  `ContinuousLinearMap.IsRieszColemanProjection.rangeEquivOfRetract`).

Finally, any linear map intertwining two endomorphisms intertwines their Riesz–Coleman projections
and complementary inverses for the same polynomial `Q` (via
`ContinuousLinearMap.IsSpectralProjection.semiconj`), so every bounded operator commuting with
`u` commutes with `E` and preserves both spectral summands
(`ContinuousLinearMap.IsRieszColemanProjection.commute_of_commute`), and ring homomorphisms
between endomorphism algebras matching reversed-polynomial evaluation and closure membership
transport Riesz–Coleman projections and their complementary inverses
(`ContinuousLinearMap.IsRieszColemanProjection.map`,
`ContinuousLinearMap.IsRieszColemanProjection.inverse_map`).

## Main definitions

* `ContinuousLinearMap.IsRieszColemanProjection`: the predicate characterising a spectral projector
  onto `ker Q*(u)` along a topological `u`-stable complement (closed when `M` is Hausdorff) on
  which `Q*(u)` is invertible, instantiating `ContinuousLinearMap.IsSpectralProjection` at
  `Q*(u)` with order `1`.
* `ContinuousLinearMap.IsRieszColemanProjection.equivRange`: when `IsUnit Q.leadingCoeff`, `u` as a
  continuous linear automorphism of `range E`.
* `ContinuousLinearMap.IsRieszColemanProjection.rangeEquivOfRetract`: when `IsUnit Q.leadingCoeff`,
  the continuous linear equivalence `E.range ≃L[R] E'.range` induced by a continuous linear retract
  `r ∘ i = id`.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127** (1997),
  417–479, Appendix A, A3–A4.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.2.
* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §7.
-/

public section

open Polynomial
open scoped ZeroAtInfty NNReal TauCeti.RingOpNorm

namespace ContinuousLinearMap

section Module

variable {R M : Type*} [SeminormedCommRing R] [TauCeti.NormedRing.IsTate R]
  [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]

/-- A **Riesz–Coleman projection** of an endomorphism `u` of a seminormed `R`-module `M` attached
to a polynomial `Q : R[X]`: a spectral projection (`ContinuousLinearMap.IsSpectralProjection`) of
`u` for the reversed polynomial `Q*(u)` of order `1`. -/
def IsRieszColemanProjection (u : M →L[R] M) (Q : R[X]) (E : M →L[R] M) : Prop :=
  IsSpectralProjection u (Polynomial.aeval u Q.reverse) 1 E

/-- Unfolding of `ContinuousLinearMap.IsRieszColemanProjection` as a spectral projection for
`Q*(u)` of order `1`. -/
theorem isRieszColemanProjection_def {u E : M →L[R] M} {Q : R[X]} :
    IsRieszColemanProjection u Q E ↔
      IsSpectralProjection u (Polynomial.aeval u Q.reverse) 1 E :=
  Iff.rfl

namespace IsRieszColemanProjection

variable {u E : M →L[R] M} {Q : R[X]}

/-- View a Riesz–Coleman projection as a `ContinuousLinearMap.IsSpectralProjection` for
`Q*(u)` of order `1`. -/
theorem toIsSpectralProjection (hE : IsRieszColemanProjection u Q E) :
    IsSpectralProjection u (Polynomial.aeval u Q.reverse) 1 E :=
  hE

omit [TauCeti.NormedRing.IsTate R] in
private theorem aeval_reverse_eq_algebraMap_leadingCoeff (u : M →L[R] M) {Q : R[X]}
    (hd : Q.natDegree = 0) :
    Polynomial.aeval u Q.reverse = algebraMap R (M →L[R] M) Q.leadingCoeff := by
  nth_rw 1 [Polynomial.eq_C_of_natDegree_eq_zero hd]
  rw [Polynomial.reverse_C, ← hd, Polynomial.coeff_natDegree, Polynomial.aeval_C]

omit [TauCeti.NormedRing.IsTate R] in
private theorem isUnit_aeval_reverse_of_natDegree_eq_zero (u : M →L[R] M) {Q : R[X]}
    (hd : Q.natDegree = 0) (hQ : IsUnit Q.leadingCoeff) :
    IsUnit (Polynomial.aeval u Q.reverse) :=
  aeval_reverse_eq_algebraMap_leadingCoeff u hd ▸ hQ.map (algebraMap R (M →L[R] M))

/-- A Riesz–Coleman projection for a degree-zero polynomial with invertible leading coefficient is
zero. -/
theorem eq_zero_of_natDegree_eq_zero (hE : IsRieszColemanProjection u Q E)
    (hd : Q.natDegree = 0) (hQ : IsUnit Q.leadingCoeff) : E = 0 :=
  hE.toIsSpectralProjection.eq_zero_of_isUnit
    (isUnit_aeval_reverse_of_natDegree_eq_zero u hd hQ)

/-- Zero is a Riesz–Coleman projection for any degree-zero polynomial with invertible leading
coefficient. -/
theorem zero_of_natDegree_eq_zero (u : M →L[R] M) {Q : R[X]}
    (hd : Q.natDegree = 0) (hQ : IsUnit Q.leadingCoeff) :
    IsRieszColemanProjection u Q 0 := by
  have hunit := isUnit_aeval_reverse_of_natDegree_eq_zero u hd hQ
  refine isRieszColemanProjection_def.mpr (IsSpectralProjection.zero_of_isUnit u hunit ?_)
  have hinv : ((hunit.unit⁻¹ : (M →L[R] M)ˣ) : M →L[R] M) =
      algebraMap R (M →L[R] M) (hQ.unit⁻¹ : Rˣ) := by
    apply hunit.mul_left_cancel
    simp [aeval_reverse_eq_algebraMap_leadingCoeff u hd, ← map_mul]
  rw [hinv]
  exact subset_closure (Subalgebra.algebraMap_mem _ _)

end IsRieszColemanProjection

/-- For `Q = 1`, the zero operator is a Riesz–Coleman projection of `u`. -/
theorem isRieszColemanProjection_one_zero (u : M →L[R] M) :
    IsRieszColemanProjection u 1 0 :=
  IsRieszColemanProjection.zero_of_natDegree_eq_zero u Polynomial.natDegree_one (by simp)

namespace IsRieszColemanProjection

variable {u E : M →L[R] M} {Q : R[X]}

/-- For `Q = 1`, the spectral summand is zero: any Riesz–Coleman projection for `1` is `0`. -/
theorem eq_zero_of_one (hE : IsRieszColemanProjection u 1 E) : E = 0 :=
  hE.eq_zero_of_natDegree_eq_zero Polynomial.natDegree_one (by simp)

end IsRieszColemanProjection

/-- For `Q = 1`, `E` is a Riesz–Coleman projection of `u` if and only if `E = 0`. -/
@[simp]
theorem isRieszColemanProjection_one_iff {u E : M →L[R] M} :
    IsRieszColemanProjection u 1 E ↔ E = 0 :=
  ⟨IsRieszColemanProjection.eq_zero_of_one, fun h ↦ h ▸ isRieszColemanProjection_one_zero u⟩

namespace IsRieszColemanProjection

variable {u E : M →L[R] M} {Q : R[X]}

omit [TauCeti.NormedRing.IsTate R] in
private theorem aeval_C_mul_reverse_eq_unit_smul (u : M →L[R] M) {c : R} (hc : IsUnit c)
    (Q : R[X]) :
    Polynomial.aeval u (Polynomial.C c * Q).reverse = hc.unit • Polynomial.aeval u Q.reverse := by
  rw [Polynomial.aeval_C_mul_reverse u hc Q, Units.smul_def, hc.unit_spec]

/-- A Riesz–Coleman projection commutes with every polynomial in `u`. -/
theorem commute_aeval (hE : IsRieszColemanProjection u Q E) (P : R[X]) :
    Commute (Polynomial.aeval u P) E := by
  simpa only [Polynomial.aeval_eq_smeval] using
    Polynomial.smeval_commute_left R P hE.toIsSpectralProjection.commute

/-- Every polynomial in `u` preserves `ker E`. -/
theorem mapsTo_ker_aeval (hE : IsRieszColemanProjection u Q E) (P : R[X]) :
    Set.MapsTo (Polynomial.aeval u P) E.ker E.ker := by
  intro x hx
  have hx' : E x = 0 := LinearMap.mem_ker.mp hx
  apply LinearMap.mem_ker.mpr
  simpa only [coe_coe, mul_apply_eq_comp, hx', map_zero] using
    congr($((hE.commute_aeval P).eq.symm) x)

/-- Every polynomial in `u` preserves `range E`. -/
theorem mapsTo_range_aeval (hE : IsRieszColemanProjection u Q E) (P : R[X]) :
    Set.MapsTo (Polynomial.aeval u P) E.range E.range := by
  rw [LinearMap.coe_range, coe_coe]
  exact Function.Semiconj.mapsTo_range fun x ↦ congr($((hE.commute_aeval P).eq.symm) x)

/-- Scaling `Q` by a unit scalar preserves Riesz–Coleman projections. -/
theorem C_mul (hE : IsRieszColemanProjection u Q E) {c : R} (hc : IsUnit c) :
    IsRieszColemanProjection u (Polynomial.C c * Q) E := by
  rw [isRieszColemanProjection_def, aeval_C_mul_reverse_eq_unit_smul u hc Q]
  exact hE.toIsSpectralProjection.units_smul_spectral hc.unit

/-- Rescaling `Q` by a unit scalar `c` scales the complementary inverse by `Ring.inverse c`. -/
theorem inverse_C_mul (hE : IsRieszColemanProjection u Q E) {c : R} (hc : IsUnit c) :
    (hE.C_mul hc).toIsSpectralProjection.inverse =
      Ring.inverse c • hE.toIsSpectralProjection.inverse := by
  rw [(hE.C_mul hc).toIsSpectralProjection.inverse_congr
      (hE.toIsSpectralProjection.units_smul_spectral hc.unit)
      (aeval_C_mul_reverse_eq_unit_smul u hc Q),
    hE.toIsSpectralProjection.inverse_units_smul_spectral hc.unit,
    Units.smul_def, ← Ring.inverse_unit hc.unit, hc.unit_spec]

end IsRieszColemanProjection

/-- Scaling `Q` by a unit scalar does not change the Riesz–Coleman projections of `u`. -/
@[simp]
theorem isRieszColemanProjection_C_mul_iff {u E : M →L[R] M} {Q : R[X]} {c : R}
    (hc : IsUnit c) :
    IsRieszColemanProjection u (Polynomial.C c * Q) E ↔ IsRieszColemanProjection u Q E := by
  rw [isRieszColemanProjection_def, isRieszColemanProjection_def,
    IsRieszColemanProjection.aeval_C_mul_reverse_eq_unit_smul u hc Q,
    IsSpectralProjection.units_smul_spectral_iff]

namespace IsRieszColemanProjection

variable {u E : M →L[R] M} {Q : R[X]}

/-- **Monotonicity in the polynomial.** If the leading coefficient of `Q` is a unit and `Q ∣ Q'`,
then the range `ker Q*(u)` of a Riesz–Coleman projection of `u` for `Q` lies in the range
`ker Q'*(u)` of any Riesz–Coleman projection of `u` for `Q'`. -/
theorem range_le_range_of_dvd {Q' : R[X]} {E' : M →L[R] M} (hE : IsRieszColemanProjection u Q E)
    (hE' : IsRieszColemanProjection u Q' E') (hQ : IsUnit Q.leadingCoeff) (hQQ' : Q ∣ Q') :
    LinearMap.range (E : M →ₗ[R] M) ≤ LinearMap.range (E' : M →ₗ[R] M) := by
  obtain ⟨A, rfl⟩ := hQQ'
  rw [hE.toIsSpectralProjection.range_eq_ker_spectral,
    hE'.toIsSpectralProjection.range_eq_ker_spectral]
  rcases eq_or_ne A 0 with rfl | hA
  · simp
  rw [reverse_mul (by rwa [Ne, hQ.mul_right_eq_zero, leadingCoeff_eq_zero]), toLinearMap_aeval,
    toLinearMap_aeval]
  exact le_sup_left.trans Polynomial.sup_ker_aeval_le_ker_aeval_mul

/-- When `Q.leadingCoeff` is a unit, `E` factors on the left through `u`: specifically,
`u * ((-lc(Q)⁻¹) • (Q*.divX)(u) * E) = E`. -/
theorem mul_smul_aeval_divX_reverse_mul (hE : IsRieszColemanProjection u Q E)
    (hQ : IsUnit Q.leadingCoeff) :
    u * ((-Ring.inverse Q.leadingCoeff) • Polynomial.aeval u Q.reverse.divX * E) = E := by
  -- Evaluating `X * Q*.divX + C (Q*(0)) = Q*` at `u` and right-multiplying by `E` kills the RHS.
  have hdiv : Polynomial.aeval u (X * Q.reverse.divX + C (Q.reverse.coeff 0)) * E = 0 := by
    rw [X_mul_divX_add, hE.toIsSpectralProjection.spectral_mul_eq_zero]
  rw [map_add, map_mul, aeval_X, aeval_C, coeff_zero_reverse, Algebra.algebraMap_eq_smul_one,
    add_mul, smul_mul_assoc, one_mul, add_eq_zero_iff_eq_neg] at hdiv
  calc u * ((-Ring.inverse Q.leadingCoeff) • Polynomial.aeval u Q.reverse.divX * E)
      = (-Ring.inverse Q.leadingCoeff) • (u * Polynomial.aeval u Q.reverse.divX * E) := by
        rw [smul_mul_assoc, mul_smul_comm, mul_assoc]
    _ = (Ring.inverse Q.leadingCoeff * Q.leadingCoeff) • E := by
        rw [hdiv, neg_smul, smul_neg, neg_neg, smul_smul]
    _ = E := by rw [Ring.inverse_mul_cancel _ hQ, one_smul]

/-- Symmetric form of `mul_smul_aeval_divX_reverse_mul`: `((-lc(Q)⁻¹) • (Q*.divX)(u) * E) * u =
E`. -/
theorem smul_aeval_divX_reverse_mul_mul (hE : IsRieszColemanProjection u Q E)
    (hQ : IsUnit Q.leadingCoeff) :
    ((-Ring.inverse Q.leadingCoeff) • Polynomial.aeval u Q.reverse.divX * E) * u = E := by
  have huP : Commute u (Polynomial.aeval u Q.reverse.divX) := by
    simpa only [Polynomial.aeval_eq_smeval] using
      (Polynomial.smeval_commute_left R Q.reverse.divX (Commute.refl u)).symm
  have hcomm : Commute u ((-Ring.inverse Q.leadingCoeff) • Polynomial.aeval u Q.reverse.divX * E) :=
    (huP.smul_right _).mul_right hE.toIsSpectralProjection.commute
  exact hcomm.eq.symm.trans (hE.mul_smul_aeval_divX_reverse_mul hQ)

/-- On `range E`, `(-lc(Q)⁻¹) • (Q*.divX)(u)` is a left inverse of `u`. -/
theorem neg_inverse_smul_aeval_divX_reverse_apply (hE : IsRieszColemanProjection u Q E)
    (hQ : IsUnit Q.leadingCoeff) {x : M} (hx : x ∈ E.range) :
    ((-Ring.inverse Q.leadingCoeff) • Polynomial.aeval u Q.reverse.divX) (u x) = x := by
  have hfix : E x = x :=
    (LinearMap.IsIdempotentElem.mem_range_iff
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap
        hE.toIsSpectralProjection.isIdempotentElem)).mp hx
  have hcomm : E (u x) = u (E x) :=
    congr($(hE.toIsSpectralProjection.commute.eq.symm) x)
  have h := congr($(hE.smul_aeval_divX_reverse_mul_mul hQ) x)
  simp only [mul_apply_eq_comp] at h
  rwa [hcomm, hfix] at h

/-- On `range E`, `(-lc(Q)⁻¹) • (Q*.divX)(u)` is a right inverse of `u`. -/
theorem apply_neg_inverse_smul_aeval_divX_reverse (hE : IsRieszColemanProjection u Q E)
    (hQ : IsUnit Q.leadingCoeff) {x : M} (hx : x ∈ E.range) :
    u (((-Ring.inverse Q.leadingCoeff) • Polynomial.aeval u Q.reverse.divX) x) = x := by
  have hfix : E x = x :=
    (LinearMap.IsIdempotentElem.mem_range_iff
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap
        hE.toIsSpectralProjection.isIdempotentElem)).mp hx
  have h := congr($(hE.mul_smul_aeval_divX_reverse_mul hQ) x)
  simp only [mul_apply_eq_comp] at h
  rwa [hfix] at h

/-- **Invertibility of `u` on `ker Q*(u) = range E`.** When the leading coefficient of `Q` is a
unit, `u` restricts to a continuous linear automorphism of `range E`. This includes `Q = 1`, when
`range E = 0`. -/
noncomputable def equivRange (hE : IsRieszColemanProjection u Q E)
    (hQ : IsUnit Q.leadingCoeff) : E.range ≃L[R] E.range :=
  ContinuousLinearEquiv.ofContinuousLinearMap
    (u.restrict hE.toIsSpectralProjection.mapsTo_range)
    (((-Ring.inverse Q.leadingCoeff) • Polynomial.aeval u Q.reverse.divX).restrict
      fun _ hx ↦ E.range.smul_mem _ (hE.mapsTo_range_aeval Q.reverse.divX hx))
    (ContinuousLinearMap.ext fun x ↦
      Subtype.ext (hE.apply_neg_inverse_smul_aeval_divX_reverse hQ x.property))
    (ContinuousLinearMap.ext fun x ↦
      Subtype.ext (hE.neg_inverse_smul_aeval_divX_reverse_apply hQ x.property))

/-- The spectral-summand automorphism `equivRange` acts by `u`. -/
@[simp]
theorem coe_equivRange_apply (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff)
    (x : E.range) : (hE.equivRange hQ x : M) = u x := by
  simp [equivRange, coe_restrict_apply hE.toIsSpectralProjection.mapsTo_range]

/-- The inverse spectral-summand automorphism `equivRange.symm` acts by `-lc(Q)⁻¹ • (Q*/X)(u)`. -/
@[simp]
theorem coe_equivRange_symm_apply (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff)
    (x : E.range) :
    ((hE.equivRange hQ).symm x : M) =
      ((-Ring.inverse Q.leadingCoeff) • Polynomial.aeval u Q.reverse.divX) x := by
  simp [equivRange]

/-- When `Q.leadingCoeff` is a unit, the restriction of `u` to `range E` is a unit of
`E.range →L[R] E.range`. -/
theorem isUnit_restrict_range (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff) :
    IsUnit (u.restrict hE.toIsSpectralProjection.mapsTo_range) :=
  (hE.equivRange hQ).toUnit.isUnit

/-- When `Q.leadingCoeff` is a unit, the `R`-linear restriction of `u` to `range E` is a unit of
`Module.End R E.range`. -/
theorem isUnit_toLinearMap_restrict_range (hE : IsRieszColemanProjection u Q E)
    (hQ : IsUnit Q.leadingCoeff) :
    IsUnit ((u : M →ₗ[R] M).restrict hE.toIsSpectralProjection.mapsTo_range) :=
  (hE.isUnit_restrict_range hQ).map toLinearMapRingHom

/-- When `Q.leadingCoeff` is a unit, `Q*(u * (1 - E))` is invertible on `M`. -/
theorem isUnit_aeval_mul_one_sub_reverse (hE : IsRieszColemanProjection u Q E)
    (hQ : IsUnit Q.leadingCoeff) :
    IsUnit (Polynomial.aeval (u * (1 - E)) Q.reverse) :=
  have hS := hE.toIsSpectralProjection
  Polynomial.isUnit_aeval_mul_one_sub_of_isIdempotentElem hS.isIdempotentElem hS.commute
    (Polynomial.coeff_zero_reverse Q ▸ hQ) hS.spectral_mul_inverse hS.inverse_mul_spectral

end IsRieszColemanProjection

end Module

section Intertwining

variable {R M N : Type*} [SeminormedCommRing R] [TauCeti.NormedRing.IsTate R]
  [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  [SeminormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]
  {u E : M →L[R] M} {v F : N →L[R] N} {Q : R[X]}

namespace IsRieszColemanProjection

/-- Every bounded operator commuting with `u` commutes with its Riesz–Coleman projection. -/
theorem commute_of_commute (hE : IsRieszColemanProjection u Q E) {g : M →L[R] M}
    (hg : Commute g u) : Commute g E :=
  ContinuousLinearMap.ext fun x ↦
    hE.toIsSpectralProjection.semiconj hE.toIsSpectralProjection
      g.toLinearMap
      (Function.Semiconj.aeval (f := g.toLinearMap) (fun y ↦ congr($(hg.eq) y)) Q.reverse) x

/-- Every bounded operator commuting with `u` commutes with the complementary inverse. -/
theorem commute_inverse_of_commute (hE : IsRieszColemanProjection u Q E) {g : M →L[R] M}
    (hg : Commute g u) : Commute g hE.toIsSpectralProjection.inverse :=
  ContinuousLinearMap.ext fun x ↦
    hE.toIsSpectralProjection.semiconj_inverse hE.toIsSpectralProjection
      g.toLinearMap
      (Function.Semiconj.aeval (f := g.toLinearMap) (fun y ↦ congr($(hg.eq) y)) Q.reverse) x

end IsRieszColemanProjection

end Intertwining

section Map

variable {R₁ R₂ : Type*} [NormedCommRing R₁] [TauCeti.NormedRing.IsTate R₁]
  [NormedCommRing R₂] [TauCeti.NormedRing.IsTate R₂]
  {M₁ M₂ : Type*} [SeminormedAddCommGroup M₁] [Module R₁ M₁] [IsBoundedSMul R₁ M₁]
  [SeminormedAddCommGroup M₂] [Module R₂ M₂] [IsBoundedSMul R₂ M₂]

/-- **Transport of Riesz–Coleman projections along a ring homomorphism.** If `Φ` is a ring
homomorphism between endomorphism algebras matching `Q'*(Φ u) = Φ (Q*(u))` and preserving the
operator-norm closure of polynomials in `u`, then `Φ E` is a Riesz–Coleman projection of `Φ u` for
`Q'`. -/
theorem IsRieszColemanProjection.map (Φ : (M₁ →L[R₁] M₁) →+* (M₂ →L[R₂] M₂))
    {u E : M₁ →L[R₁] M₁} {Q : R₁[X]} {Q' : R₂[X]}
    (hE : IsRieszColemanProjection u Q E)
    (haeval : Polynomial.aeval (Φ u) Q'.reverse = Φ (Polynomial.aeval u Q.reverse))
    (hclosure : ∀ {v : M₁ →L[R₁] M₁},
      v ∈ closure (Algebra.adjoin R₁ {u} : Set (M₁ →L[R₁] M₁)) →
      Φ v ∈ closure (Algebra.adjoin R₂ {Φ u} : Set (M₂ →L[R₂] M₂))) :
    IsRieszColemanProjection (Φ u) Q' (Φ E) :=
  isRieszColemanProjection_def.mpr <| by
    simpa only [← haeval] using hE.toIsSpectralProjection.map Φ hclosure

/-- **Transport of the complementary inverse along a ring homomorphism.** Under the hypotheses of
`IsRieszColemanProjection.map`, the complementary inverse of the transported projection `Φ E` is
`Φ hE.toIsSpectralProjection.inverse`. -/
theorem IsRieszColemanProjection.inverse_map (Φ : (M₁ →L[R₁] M₁) →+* (M₂ →L[R₂] M₂))
    {u E : M₁ →L[R₁] M₁} {Q : R₁[X]} {Q' : R₂[X]}
    (hE : IsRieszColemanProjection u Q E)
    (haeval : Polynomial.aeval (Φ u) Q'.reverse = Φ (Polynomial.aeval u Q.reverse))
    (hclosure : ∀ {v : M₁ →L[R₁] M₁},
      v ∈ closure (Algebra.adjoin R₁ {u} : Set (M₁ →L[R₁] M₁)) →
      Φ v ∈ closure (Algebra.adjoin R₂ {Φ u} : Set (M₂ →L[R₂] M₂))) :
    (hE.map Φ haeval hclosure).toIsSpectralProjection.inverse =
      Φ hE.toIsSpectralProjection.inverse :=
  hE.toIsSpectralProjection.inverse_map Φ
    (hE.map Φ haeval hclosure).toIsSpectralProjection haeval rfl

end Map

section Retract

variable {R M N : Type*} [NormedCommRing R] [TauCeti.NormedRing.IsTate R]
  [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  [SeminormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]
  {i : M →L[R] N} {r : N →L[R] M} {u : M →L[R] M} {Q : R[X]}

/-- **Compression of Riesz–Coleman projections along a retract.** Let `r ∘ i = id` present `M` as
a retract of a seminormed module `N`. If `E` is a Riesz–Coleman projection of `i ∘ u ∘ r` for `Q`,
then `r ∘ E ∘ i` is a Riesz–Coleman projection of `u` for `Q`. -/
theorem IsRieszColemanProjection.comp_comp_of_retract (hri : r.comp i = .id R M) {E : N →L[R] N}
    (hE : IsRieszColemanProjection (i.comp (u.comp r)) Q E) :
    IsRieszColemanProjection u Q (r.comp (E.comp i)) := by
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  have hr_semi : Function.Semiconj r.toLinearMap (i.comp (u.comp r)) u := fun y ↦ by simp [hri']
  have hi_semi : Function.Semiconj i.toLinearMap u (i.comp (u.comp r)) := fun x ↦ by simp [hri']
  exact isRieszColemanProjection_def.mpr
    (IsSpectralProjection.comp_comp_of_retract hri (hr_semi.aeval Q.reverse)
      (hi_semi.aeval Q.reverse) hE.toIsSpectralProjection)

/-- When `Q.leadingCoeff` is a unit, the Riesz–Coleman projection `E'` of the extension
`i ∘ u ∘ r` along a continuous linear retract `r ∘ i = id` vanishes on `ker r` and takes values in
`range i`, so extending any Riesz–Coleman projection `E` of `u` back to `N` recovers
`E' = i ∘ E ∘ r`. -/
theorem IsRieszColemanProjection.comp_comp_eq_of_retract (hri : r.comp i = .id R M)
    {E : M →L[R] M} {E' : N →L[R] N} (hE : IsRieszColemanProjection u Q E)
    (hE' : IsRieszColemanProjection (i.comp (u.comp r)) Q E') (hQ : IsUnit Q.leadingCoeff) :
    i.comp (E.comp r) = E' := by
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  have hr_semi : Function.Semiconj r.toLinearMap (i.comp (u.comp r)) u := fun y ↦ by simp [hri']
  have hfac := hE'.mul_smul_aeval_divX_reverse_mul hQ
  ext y
  -- Since `E' = (i ∘ u ∘ r) * (...)`, `E' y` already lies in `range i`, so `i (r (E' y)) = E' y`.
  have hirE : i (r (E' y)) = E' y := by
    have hy := congr($hfac y).symm
    simp only [mul_apply_eq_comp, comp_apply] at hy
    rw [hy, hri']
  calc (i.comp (E.comp r)) y = i (E (r y)) := by simp
    _ = i (r (E' y)) :=
      congrArg i (hE'.toIsSpectralProjection.semiconj
        hE.toIsSpectralProjection r.toLinearMap (hr_semi.aeval Q.reverse) y).symm
    _ = E' y := hirE

/-- When `Q.leadingCoeff` is a unit, along a continuous linear retract `r ∘ i = id`, `i` and `r`
restrict to a continuous linear equivalence between the ranges of the Riesz–Coleman projections of
`u` and `i ∘ u ∘ r`. -/
noncomputable def IsRieszColemanProjection.rangeEquivOfRetract (hri : r.comp i = .id R M)
    {E : M →L[R] M} {E' : N →L[R] N} (hE : IsRieszColemanProjection u Q E)
    (hE' : IsRieszColemanProjection (i.comp (u.comp r)) Q E')
    (hQ : IsUnit Q.leadingCoeff) : E.range ≃L[R] E'.range :=
  { toLinearEquiv :=
      (ContinuousLinearMap.rangeEquivOfRetract E hri).trans
        (LinearEquiv.ofEq _ _ (congrArg LinearMap.range
          (LinearMap.ext fun y ↦ by simp [← hE.comp_comp_eq_of_retract hri hE' hQ])))
    continuous_toFun := continuous_induced_rng.2 <|
      (i.continuous.comp continuous_subtypeVal).congr fun x ↦ by simp
    continuous_invFun := continuous_induced_rng.2 <|
      (r.continuous.comp continuous_subtypeVal).congr fun y ↦ by
        simp [LinearEquiv.ofEq_symm] }

/-- The retract range equivalence `rangeEquivOfRetract` acts in the forward direction by `i`. -/
@[simp]
theorem IsRieszColemanProjection.coe_rangeEquivOfRetract_apply (hri : r.comp i = .id R M)
    {E : M →L[R] M} {E' : N →L[R] N} (hE : IsRieszColemanProjection u Q E)
    (hE' : IsRieszColemanProjection (i.comp (u.comp r)) Q E')
    (hQ : IsUnit Q.leadingCoeff) (x : E.range) :
    ((hE.rangeEquivOfRetract hri hE' hQ x : N)) = i x := by
  simp [rangeEquivOfRetract]

/-- The inverse retract range equivalence `rangeEquivOfRetract.symm` acts by `r`. -/
@[simp]
theorem IsRieszColemanProjection.coe_rangeEquivOfRetract_symm_apply (hri : r.comp i = .id R M)
    {E : M →L[R] M} {E' : N →L[R] N} (hE : IsRieszColemanProjection u Q E)
    (hE' : IsRieszColemanProjection (i.comp (u.comp r)) Q E')
    (hQ : IsUnit Q.leadingCoeff) (y : E'.range) :
    (((hE.rangeEquivOfRetract hri hE' hQ).symm y : M)) = r y := by
  obtain ⟨x, rfl⟩ := (hE.rangeEquivOfRetract hri hE' hQ).surjective y
  rw [ContinuousLinearEquiv.symm_apply_apply, coe_rangeEquivOfRetract_apply]
  exact (DFunLike.congr_fun hri (x : M)).symm

end Retract

section RowCompact

variable {I R : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [NormedCommRing R] [TauCeti.NormedRing.IsTate R] [IsUltrametricDist R]
  {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]}

namespace IsRieszColemanProjection

/-- When `Q.leadingCoeff` is a unit, every Riesz–Coleman projection of a row-compact operator is
row compact, including when `Q = 1`. -/
theorem isRowCompact (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff)
    (hu : u.IsRowCompact) : E.IsRowCompact := by
  rw [← hE.mul_smul_aeval_divX_reverse_mul hQ, mul_def]
  exact hu.comp_clm _

variable [CompleteSpace R]

/-- When `Q.leadingCoeff` is a unit, the finite spectral summand `range E` of a row-compact
operator is finitely generated over `R`. -/
theorem finite_range (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff)
    (hu : u.IsRowCompact) : Module.Finite R E.range :=
  (hE.isRowCompact hQ hu).finite_range_of_isIdempotentElem
    hE.toIsSpectralProjection.isIdempotentElem

/-- When `Q.leadingCoeff` is a unit, the finite spectral summand `range E` of a row-compact
operator is projective over `R`. -/
theorem projective_range (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff)
    (hu : u.IsRowCompact) : Module.Projective R E.range :=
  (hE.isRowCompact hQ hu).projective_range_of_isIdempotentElem
    hE.toIsSpectralProjection.isIdempotentElem

/-- When `Q.leadingCoeff` is a unit, `ker Q*(u)` is finitely generated over `R`. -/
theorem finite_ker_aeval_reverse (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff)
    (hu : u.IsRowCompact) :
    Module.Finite R
      (LinearMap.ker ((Polynomial.aeval u Q.reverse : C₀(I, R) →L[R] C₀(I, R)) :
        C₀(I, R) →ₗ[R] C₀(I, R))) := by
  rw [← hE.toIsSpectralProjection.range_eq_ker_spectral]
  exact hE.finite_range hQ hu

/-- When `Q.leadingCoeff` is a unit, `ker Q*(u)` is projective over `R`. -/
theorem projective_ker_aeval_reverse (hE : IsRieszColemanProjection u Q E)
    (hQ : IsUnit Q.leadingCoeff) (hu : u.IsRowCompact) :
    Module.Projective R
      (LinearMap.ker ((Polynomial.aeval u Q.reverse : C₀(I, R) →L[R] C₀(I, R)) :
        C₀(I, R) →ₗ[R] C₀(I, R))) := by
  rw [← hE.toIsSpectralProjection.range_eq_ker_spectral]
  exact hE.projective_range hQ hu

end IsRieszColemanProjection

end RowCompact

end ContinuousLinearMap
