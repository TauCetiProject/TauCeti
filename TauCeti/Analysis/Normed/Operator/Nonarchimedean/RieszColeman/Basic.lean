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
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.BaseChange
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Smeval
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

into `u`-stable submodules (`ContinuousLinearMap.IsSpectralProjection.range_eq_ker`,
`ContinuousLinearMap.IsSpectralProjection.range_pow_eq_ker`,
`ContinuousLinearMap.IsSpectralProjection.isTopCompl_ker_range_pow`), on which
`Q*(u)` vanishes on the first summand and restricts to a continuous linear automorphism of the
second (`ContinuousLinearMap.IsSpectralProjection.equivKer`). Such a projection is unique
(`ContinuousLinearMap.IsSpectralProjection.unique`); for `Q = 1` it is zero
(`ContinuousLinearMap.isRieszColemanProjection_one_iff`,
`ContinuousLinearMap.IsRieszColemanProjection.eq_zero_of_one`,
`ContinuousLinearMap.isRieszColemanProjection_one_zero`), and scaling `Q` by a unit of `R` leaves
the predicate unchanged (`ContinuousLinearMap.IsRieszColemanProjection.units_smul_iff`).

When the leading coefficient of `Q` is a unit, the constant term of `Q*` is `Q.leadingCoeff`, so
dividing `Q* - Q*(0)` by `X` expresses `E = u * ((-lc(Q)⁻¹) • (Q*.divX)(u) * E)`. Consequently:

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
  `ContinuousLinearMap.IsRieszColemanProjection.rangeEquivOfRetract`);
* on model spaces `C₀(J, R)`, bounded coefficient extension preserves Riesz–Coleman projections and
  commutes with the complementary inverse whenever the homomorphism preserves the degree of `Q`
  (`ContinuousLinearMap.IsRieszColemanProjection.mapCoeffs`,
  `ContinuousLinearMap.IsRieszColemanProjection.inverse_mapCoeffs`).

Finally, any linear map intertwining two endomorphisms intertwines their Riesz–Coleman projections
and complementary inverses for the same polynomial `Q` (via
`ContinuousLinearMap.IsSpectralProjection.semiconj`), so every bounded operator commuting with
`u` commutes with `E` and preserves both spectral summands
(`ContinuousLinearMap.IsRieszColemanProjection.commute_of_commute`).

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

/-- A Riesz–Coleman projection for a degree-zero polynomial with invertible leading coefficient is
zero. -/
theorem eq_zero_of_natDegree_eq_zero (hE : IsRieszColemanProjection u Q E)
    (hd : Q.natDegree = 0) (hQ : IsUnit Q.leadingCoeff) : E = 0 := by
  have hrev : Q.reverse = C Q.leadingCoeff := by
    conv_lhs => rw [Polynomial.eq_C_of_natDegree_eq_zero hd]
    simp [Polynomial.leadingCoeff, hd]
  exact (isRieszColemanProjection_def.mp hE).eq_zero_of_isUnit <| by
    rw [hrev, Polynomial.aeval_C]
    exact hQ.map (algebraMap R (M →L[R] M))

/-- Zero is a Riesz–Coleman projection for any degree-zero polynomial with invertible leading
coefficient. -/
theorem zero_of_natDegree_eq_zero (u : M →L[R] M) {Q : R[X]}
    (hd : Q.natDegree = 0) (hQ : IsUnit Q.leadingCoeff) :
    IsRieszColemanProjection u Q 0 := by
  have hrev : Q.reverse = C Q.leadingCoeff := by
    conv_lhs => rw [Polynomial.eq_C_of_natDegree_eq_zero hd]
    simp [Polynomial.leadingCoeff, hd]
  have hunit : IsUnit (Polynomial.aeval u Q.reverse) := by
    rw [hrev, Polynomial.aeval_C]
    exact hQ.map (algebraMap R (M →L[R] M))
  refine isRieszColemanProjection_def.mpr (IsSpectralProjection.zero_of_isUnit u hunit ?_)
  have hinv : ((hunit.unit⁻¹ : (M →L[R] M)ˣ) : M →L[R] M) =
      algebraMap R (M →L[R] M) (hQ.unit⁻¹ : Rˣ) := by
    apply hunit.mul_left_cancel
    simp [hrev, ← map_mul]
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

/-- Scaling the polynomial `Q` by a unit of the coefficient ring does not change the Riesz–Coleman
projection. -/
theorem units_smul (hE : IsRieszColemanProjection u Q E) (c : Rˣ) :
    IsRieszColemanProjection u (c • Q) E := by
  rw [isRieszColemanProjection_def, Polynomial.reverse_units_smul, Units.smul_def, map_smul]
  simpa only [Units.smul_def] using (isRieszColemanProjection_def.mp hE).units_smul_spectral c

/-- Scaling the polynomial `Q` by a unit of the coefficient ring yields an equivalent Riesz–Coleman
projection predicate. -/
@[simp]
theorem units_smul_iff (c : Rˣ) :
    IsRieszColemanProjection u (c • Q) E ↔ IsRieszColemanProjection u Q E := by
  rw [isRieszColemanProjection_def, isRieszColemanProjection_def, Polynomial.reverse_units_smul,
    Units.smul_def, map_smul, ← Units.smul_def]
  exact IsSpectralProjection.units_smul_spectral_iff c

/-- Scaling `Q` by a unit `c : Rˣ` scales the complementary inverse of a Riesz–Coleman projection
by `c⁻¹`. -/
theorem inverse_units_smul (hE : IsRieszColemanProjection u Q E) (c : Rˣ) :
    (isRieszColemanProjection_def.mp (hE.units_smul c)).inverse =
      c⁻¹ • (isRieszColemanProjection_def.mp hE).inverse := by
  have hspec : Polynomial.aeval u (c • Q).reverse = c • Polynomial.aeval u Q.reverse := by
    rw [Polynomial.reverse_units_smul, Units.smul_def, map_smul, ← Units.smul_def]
  rw [← (isRieszColemanProjection_def.mp hE).inverse_units_smul_spectral c]
  have hcompat : ∀ {C'} (_ : C' = c • Polynomial.aeval u Q.reverse)
      (h : IsSpectralProjection u C' 1 E),
      h.inverse = ((isRieszColemanProjection_def.mp hE).units_smul_spectral c).inverse := by
    rintro _ rfl _
    rfl
  exact hcompat hspec _

/-- A Riesz–Coleman projection commutes with every polynomial in `u`. -/
theorem commute_aeval (hE : IsRieszColemanProjection u Q E) (P : R[X]) :
    Commute (Polynomial.aeval u P) E := by
  simpa only [Polynomial.aeval_eq_smeval] using
    Polynomial.smeval_commute_left R P (isRieszColemanProjection_def.mp hE).commute

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

/-- When `Q.leadingCoeff` is a unit, `E` factors on the left through `u`: specifically,
`u * ((-lc(Q)⁻¹) • (Q*.divX)(u) * E) = E`. -/
theorem mul_smul_aeval_divX_reverse_mul (hE : IsRieszColemanProjection u Q E)
    (hQ : IsUnit Q.leadingCoeff) :
    u * ((-Ring.inverse Q.leadingCoeff) • Polynomial.aeval u Q.reverse.divX * E) = E := by
  -- Evaluating `X * Q*.divX + C (Q*(0)) = Q*` at `u` and right-multiplying by `E` kills the RHS.
  have hdiv : Polynomial.aeval u (X * Q.reverse.divX + C (Q.reverse.coeff 0)) * E = 0 := by
    rw [X_mul_divX_add]
    simpa only [pow_one] using (isRieszColemanProjection_def.mp hE).pow_mul_eq_zero
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
    (huP.smul_right _).mul_right (isRieszColemanProjection_def.mp hE).commute
  exact hcomm.eq.symm.trans (hE.mul_smul_aeval_divX_reverse_mul hQ)

/-- On `range E`, `(-lc(Q)⁻¹) • (Q*.divX)(u)` is a left inverse of `u`. -/
theorem neg_inverse_smul_aeval_divX_reverse_apply (hE : IsRieszColemanProjection u Q E)
    (hQ : IsUnit Q.leadingCoeff) {x : M} (hx : x ∈ E.range) :
    ((-Ring.inverse Q.leadingCoeff) • Polynomial.aeval u Q.reverse.divX) (u x) = x := by
  have hfix : E x = x :=
    (LinearMap.IsIdempotentElem.mem_range_iff
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap
        (isRieszColemanProjection_def.mp hE).isIdempotentElem)).mp hx
  have hcomm : E (u x) = u (E x) :=
    congr($((isRieszColemanProjection_def.mp hE).commute.eq.symm) x)
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
        (isRieszColemanProjection_def.mp hE).isIdempotentElem)).mp hx
  have h := congr($(hE.mul_smul_aeval_divX_reverse_mul hQ) x)
  simp only [mul_apply_eq_comp] at h
  rwa [hfix] at h

/-- **Invertibility of `u` on `ker Q*(u) = range E`.** When the leading coefficient of `Q` is a
unit, `u` restricts to a continuous linear automorphism of `range E`. This includes `Q = 1`, when
`range E = 0`. -/
noncomputable def equivRange (hE : IsRieszColemanProjection u Q E)
    (hQ : IsUnit Q.leadingCoeff) : E.range ≃L[R] E.range :=
  ContinuousLinearEquiv.ofContinuousLinearMap
    (u.restrict (isRieszColemanProjection_def.mp hE).mapsTo_range)
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
  simp [equivRange, coe_restrict_apply (isRieszColemanProjection_def.mp hE).mapsTo_range]

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
    IsUnit (u.restrict (isRieszColemanProjection_def.mp hE).mapsTo_range) :=
  (hE.equivRange hQ).toUnit.isUnit

/-- When `Q.leadingCoeff` is a unit, the `R`-linear restriction of `u` to `range E` is a unit of
`Module.End R E.range`. -/
theorem isUnit_toLinearMap_restrict_range (hE : IsRieszColemanProjection u Q E)
    (hQ : IsUnit Q.leadingCoeff) :
    IsUnit ((u : M →ₗ[R] M).restrict (isRieszColemanProjection_def.mp hE).mapsTo_range) :=
  (hE.isUnit_restrict_range hQ).map toLinearMapRingHom

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
    (isRieszColemanProjection_def.mp hE).semiconj (isRieszColemanProjection_def.mp hE)
      g.toLinearMap
      (Function.Semiconj.aeval (f := g.toLinearMap) (fun y ↦ congr($(hg.eq) y)) Q.reverse) x

/-- Every bounded operator commuting with `u` commutes with the complementary inverse. -/
theorem commute_inverse_of_commute (hE : IsRieszColemanProjection u Q E) {g : M →L[R] M}
    (hg : Commute g u) : Commute g (isRieszColemanProjection_def.mp hE).inverse :=
  ContinuousLinearMap.ext fun x ↦
    (isRieszColemanProjection_def.mp hE).semiconj_inverse (isRieszColemanProjection_def.mp hE)
      g.toLinearMap
      (Function.Semiconj.aeval (f := g.toLinearMap) (fun y ↦ congr($(hg.eq) y)) Q.reverse) x

end IsRieszColemanProjection

end Intertwining

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
      (hi_semi.aeval Q.reverse) (isRieszColemanProjection_def.mp hE))

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
      congrArg i ((isRieszColemanProjection_def.mp hE').semiconj
        (isRieszColemanProjection_def.mp hE) r.toLinearMap (hr_semi.aeval Q.reverse) y).symm
    _ = E' y := hirE

/-- When `Q.leadingCoeff` is a unit, along a continuous linear retract `r ∘ i = id`, `i` and `r`
restrict to a continuous linear equivalence between the ranges of the Riesz–Coleman projections of
`u` and `i ∘ u ∘ r`. -/
noncomputable def IsRieszColemanProjection.rangeEquivOfRetract (hri : r.comp i = .id R M)
    {E : M →L[R] M} {E' : N →L[R] N} (hE : IsRieszColemanProjection u Q E)
    (hE' : IsRieszColemanProjection (i.comp (u.comp r)) Q E')
    (hQ : IsUnit Q.leadingCoeff) : E.range ≃L[R] E'.range :=
  let e₀ : E.range ≃ₗ[R] E'.range :=
    (ContinuousLinearMap.rangeEquivOfRetract E hri).trans
      (LinearEquiv.ofEq _ _ (congrArg LinearMap.range
        (LinearMap.ext fun y ↦ by simp [← hE.comp_comp_eq_of_retract hri hE' hQ])))
  { toLinearEquiv := e₀
    continuous_toFun := continuous_induced_rng.2 <|
      (i.continuous.comp continuous_subtypeVal).congr fun x ↦ by
        simp [e₀]
    continuous_invFun := continuous_induced_rng.2 <|
      (r.continuous.comp continuous_subtypeVal).congr fun y ↦ by
        simp [e₀, LinearEquiv.ofEq_symm] }

/-- The retract range equivalence `rangeEquivOfRetract` acts in the forward direction by `i`. -/
@[simp]
theorem IsRieszColemanProjection.coe_rangeEquivOfRetract_apply (hri : r.comp i = .id R M)
    {E : M →L[R] M} {E' : N →L[R] N} (hE : IsRieszColemanProjection u Q E)
    (hE' : IsRieszColemanProjection (i.comp (u.comp r)) Q E')
    (hQ : IsUnit Q.leadingCoeff) (x : E.range) :
    ((hE.rangeEquivOfRetract hri hE' hQ x : N)) = i x := by
  dsimp only [rangeEquivOfRetract]
  rw [ContinuousLinearEquiv.coe_mk, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
    ContinuousLinearMap.coe_rangeEquivOfRetract_apply]

/-- The inverse retract range equivalence `rangeEquivOfRetract.symm` acts by `r`. -/
@[simp]
theorem IsRieszColemanProjection.coe_rangeEquivOfRetract_symm_apply (hri : r.comp i = .id R M)
    {E : M →L[R] M} {E' : N →L[R] N} (hE : IsRieszColemanProjection u Q E)
    (hE' : IsRieszColemanProjection (i.comp (u.comp r)) Q E')
    (hQ : IsUnit Q.leadingCoeff) (y : E'.range) :
    (((hE.rangeEquivOfRetract hri hE' hQ).symm y : M)) = r y := by
  change (((hE.rangeEquivOfRetract hri hE' hQ).toLinearEquiv).symm y : M) = r y
  dsimp only [rangeEquivOfRetract]
  rw [LinearEquiv.symm_trans_apply, LinearEquiv.ofEq_symm,
    ContinuousLinearMap.coe_rangeEquivOfRetract_symm_apply, LinearEquiv.coe_ofEq_apply]

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
    (isRieszColemanProjection_def.mp hE).isIdempotentElem

/-- When `Q.leadingCoeff` is a unit, the finite spectral summand `range E` of a row-compact
operator is projective over `R`. -/
theorem projective_range (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff)
    (hu : u.IsRowCompact) : Module.Projective R E.range :=
  (hE.isRowCompact hQ hu).projective_range_of_isIdempotentElem
    (isRieszColemanProjection_def.mp hE).isIdempotentElem

/-- When `Q.leadingCoeff` is a unit, `ker Q*(u)` is finitely generated over `R`. -/
theorem finite_ker_aeval_reverse (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff)
    (hu : u.IsRowCompact) :
    Module.Finite R
      (LinearMap.ker ((Polynomial.aeval u Q.reverse : C₀(I, R) →L[R] C₀(I, R)) :
        C₀(I, R) →ₗ[R] C₀(I, R))) := by
  have hker := by simpa only [pow_one] using (isRieszColemanProjection_def.mp hE).range_eq_ker
  rw [← hker]
  exact hE.finite_range hQ hu

/-- When `Q.leadingCoeff` is a unit, `ker Q*(u)` is projective over `R`. -/
theorem projective_ker_aeval_reverse (hE : IsRieszColemanProjection u Q E)
    (hQ : IsUnit Q.leadingCoeff) (hu : u.IsRowCompact) :
    Module.Projective R
      (LinearMap.ker ((Polynomial.aeval u Q.reverse : C₀(I, R) →L[R] C₀(I, R)) :
        C₀(I, R) →ₗ[R] C₀(I, R))) := by
  have hker := by simpa only [pow_one] using (isRieszColemanProjection_def.mp hE).range_eq_ker
  rw [← hker]
  exact hE.projective_range hQ hu

end IsRieszColemanProjection

end RowCompact

section BaseChange

variable {J R S : Type*} [TopologicalSpace J] [DiscreteTopology J] [DecidableEq J]
  [NormedCommRing R] [TauCeti.NormedRing.IsTate R]
  [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S] [TauCeti.NormedRing.IsTate S]

/-- **Riesz–Coleman projections under bounded base change.** Coefficientwise extension along a
bounded unital ring homomorphism `f : R →+* S` carries a Riesz–Coleman projection of `u` for `Q`
to one of `u.mapCoeffs f hf` for `Q.map f`, whenever `f` preserves the degree of `Q` (in
particular, whenever `Q` has invertible leading coefficient, via
`Polynomial.natDegree_map_eq_of_isUnit_leadingCoeff`). No compactness is needed. -/
theorem IsRieszColemanProjection.mapCoeffs {u E : C₀(J, R) →L[R] C₀(J, R)} {Q : R[X]}
    (hE : IsRieszColemanProjection u Q E) (f : R →+* S)
    (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) (hdeg : (Q.map f).natDegree = Q.natDegree) :
    IsRieszColemanProjection (u.mapCoeffs f hf) (Q.map f) (E.mapCoeffs f hf) :=
  isRieszColemanProjection_def.mpr <| by
    simpa only [mapCoeffsRingHom_apply, aeval_mapCoeffs,
      Polynomial.reverse_map_of_natDegree_eq f hdeg] using
      IsSpectralProjection.map (isRieszColemanProjection_def.mp hE) (mapCoeffsRingHom f hf)
        (fun hv ↦ by simpa only [mapCoeffsRingHom_apply] using mapCoeffs_mem_closure_adjoin f hf hv)

/-- Bounded coefficient extension commutes with taking the complementary inverse of a Riesz–Coleman
projection, whenever `f` preserves the degree of `Q`. -/
theorem IsRieszColemanProjection.inverse_mapCoeffs {u E : C₀(J, R) →L[R] C₀(J, R)} {Q : R[X]}
    (hE : IsRieszColemanProjection u Q E) (f : R →+* S)
    (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) (hdeg : (Q.map f).natDegree = Q.natDegree) :
    (isRieszColemanProjection_def.mp (hE.mapCoeffs f hf hdeg)).inverse =
      (isRieszColemanProjection_def.mp hE).inverse.mapCoeffs f hf :=
  ((isRieszColemanProjection_def.mp hE).inverse_map (mapCoeffsRingHom f hf)
    (isRieszColemanProjection_def.mp (hE.mapCoeffs f hf hdeg))
    (by simp [mapCoeffsRingHom_apply, Polynomial.reverse_map_of_natDegree_eq f hdeg])
    (mapCoeffsRingHom_apply _ _ _).symm).trans (mapCoeffsRingHom_apply _ _ _)

end BaseChange

end ContinuousLinearMap
