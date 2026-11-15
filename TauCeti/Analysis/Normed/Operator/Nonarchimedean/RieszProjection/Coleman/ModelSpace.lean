/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.BaseChange
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.Coleman
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.PrModule.Coprime
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszProjection.Coleman.Basic
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszProjection.Multiplicity
import TauCeti.Algebra.Polynomial.DivX
import TauCeti.Algebra.Ring.SpectralIdempotent
import TauCeti.Analysis.Polynomial.Coleman.Coprime

/-!
# Construction of Riesz–Coleman projectors on model spaces

Let `R` be a complete ultrametric normed commutative ring with Tate scalars, `I` a discrete index
type, and `u` a row-compact endomorphism of the model space `C₀(I, R)` with Fredholm series
`H_u(T) = det (1 - T u)`. Suppose `H_u = Q · S`, where `Q ∈ R[X]` satisfies `Q(0) = 1`, has
invertible leading coefficient, and is coprime in the ring of entire power series to an entire
series `S`.

Coleman's polynomial `B = 1 - c Q*`, with `c = Ring.inverse Q.leadingCoeff`, vanishes at `0` and
sends `Q` to `(1 - T) ^ deg Q` under Coleman's transform
(`Polynomial.colemanDSeries_one_sub_C_mul_reverse_self`), while coprimality of `Q` and `S` makes
`D(B, S)(1)` a unit (`Polynomial.isUnit_evalAt_one_colemanDSeries_one_sub_C_mul_reverse_iff`). By
spectral mapping (`ContinuousLinearMap.IsRowCompact.charPowerSeries_matrixCoeff_aeval`), the
Fredholm series of `v = B(u)` has a good zero of order `d = deg Q` at `1`. Its single-point Riesz
projector `E = v.rieszProjection 1 d` (`ContinuousLinearMap.rieszColemanProjection`) already has a
finite projective range of constant rank `d` and makes `1 - v = c • Q*(u)` invertible on
`range (1 - E)`. Coprimality of `Q` with `H_{u(1 - E)}` then forces `Q` to divide the reversed
characteristic polynomial `P = det (1 - T u|_{range E})` of degree at most `d`, hence `P = Q` and
`H_{u(1 - E)} = S`. Since `Q.leadingCoeff` is a unit, `det (u|_{range E})` is a unit, so
`u|_{range E}` is invertible and killed by `P* = Q*` by Cayley–Hamilton on finite projective
modules (`LinearMap.aeval_reverse_projectiveCharpolyRev_of_isUnit`), giving `Q*(u) * E = 0` without
meromorphic Laurent-series contour arguments.

## Main definitions

* `ContinuousLinearMap.rieszColemanProjection`: the explicit projector
  `(B(u)).rieszProjection 1 Q.natDegree` on `C₀(I, R)` for `B = 1 - c Q*`.

## Main results

* `ContinuousLinearMap.IsRowCompact.isRieszColemanProjection_rieszColemanProjection`: existence of
  the Riesz–Coleman projection on `C₀(I, R)` for any coprime factorisation `H_u = Q · S`.
* `ContinuousLinearMap.IsRieszColemanProjection.rankAtStalk_range`,
  `ContinuousLinearMap.IsRieszColemanProjection.projectiveCharpolyRev_restrict_range`,
  `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_matrixCoeff_mul_eq`,
  `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_matrixCoeff_mul_one_sub_eq`:
  constant rank `deg Q`, characteristic polynomial `Q` on `range E`, and identification of the two
  Fredholm factors with `Q` and `S`.
* `ContinuousLinearMap.IsRieszColemanProjection.mapCoeffs`,
  `ContinuousLinearMap.IsRowCompact.rieszColemanProjection_mapCoeffs`: compatibility with bounded
  ring homomorphisms of Tate rings.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127** (1997),
  417–479, Appendices A3–A4.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.2.
-/

public section

open Polynomial
open PowerSeries (IsEntire)
open scoped ZeroAtInfty NNReal TauCeti.RingOpNorm

namespace ContinuousLinearMap

section ModelSpace

variable {R I : Type*} [NormedCommRing R] [TauCeti.NormedRing.IsTate R]
  [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]

/-- The **Riesz–Coleman projector** of an endomorphism `u` of `C₀(I, R)` for a polynomial `Q`: the
single-point Riesz projector at `1` of order `Q.natDegree` of `B(u)`, where
`B = 1 - C (Ring.inverse Q.leadingCoeff) * Q.reverse`. When `u` is row compact, `Q(0) = 1`,
`Q.leadingCoeff` is a unit, and `Q` splits off as a coprime factor of the Fredholm series of `u`,
it is the unique Riesz–Coleman projection of `u` for `Q`
(`ContinuousLinearMap.IsRowCompact.isRieszColemanProjection_rieszColemanProjection`). -/
noncomputable def rieszColemanProjection (u : C₀(I, R) →L[R] C₀(I, R)) (Q : R[X]) :
    C₀(I, R) →L[R] C₀(I, R) :=
  (Polynomial.aeval u (1 - C (Ring.inverse Q.leadingCoeff) * Q.reverse)).rieszProjection
    1 Q.natDegree

/-- Unfolding lemma for `ContinuousLinearMap.rieszColemanProjection`. -/
theorem rieszColemanProjection_def (u : C₀(I, R) →L[R] C₀(I, R)) (Q : R[X]) :
    u.rieszColemanProjection Q =
      (Polynomial.aeval u (1 - C (Ring.inverse Q.leadingCoeff) * Q.reverse)).rieszProjection
        1 Q.natDegree :=
  (rfl)

/-- The Riesz–Coleman projector for the polynomial `1` is zero. -/
@[simp]
theorem rieszColemanProjection_one (u : C₀(I, R) →L[R] C₀(I, R)) :
    u.rieszColemanProjection 1 = 0 := by
  rw [rieszColemanProjection_def, natDegree_one, rieszProjection_order_zero]

section RowCompact

variable [IsUltrametricDist R]

/-- Every Riesz–Coleman projection of a row-compact operator for a polynomial with invertible
leading coefficient is row compact: `X_mul_divX_add Q.reverse` expresses `E` as a multiple of
`u * (divX Q*)(u) * E`. -/
theorem IsRieszColemanProjection.isRowCompact {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact) (hQ : IsUnit Q.leadingCoeff) :
    E.IsRowCompact := by
  rw [hE.eq_neg_inverse_smul_mul_aeval_divX hQ, mul_def]
  exact (hu.comp_clm _).smul _

variable [CompleteSpace R]

/-- The range of a Riesz–Coleman projection of a row-compact operator is finitely generated when
`Q.leadingCoeff` is a unit. -/
theorem IsRieszColemanProjection.finite_range {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact) (hQ : IsUnit Q.leadingCoeff) :
    Module.Finite R E.range :=
  (hE.isRowCompact hu hQ).finite_range_of_isIdempotentElem hE.isIdempotentElem

/-- The range of a Riesz–Coleman projection of a row-compact operator is projective when
`Q.leadingCoeff` is a unit. -/
theorem IsRieszColemanProjection.projective_range {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact) (hQ : IsUnit Q.leadingCoeff) :
    Module.Projective R E.range :=
  (hE.isRowCompact hu hQ).projective_range_of_isIdempotentElem hE.isIdempotentElem

/-- The kernel of `Q*(u)` for a row-compact operator admitting a Riesz–Coleman projection is
finitely generated when `Q.leadingCoeff` is a unit. -/
theorem IsRieszColemanProjection.finite_ker_aeval_reverse {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact) (hQ : IsUnit Q.leadingCoeff) :
    Module.Finite R
      (LinearMap.ker ((Polynomial.aeval u Q.reverse : C₀(I, R) →L[R] C₀(I, R)) :
        C₀(I, R) →ₗ[R] C₀(I, R))) := by
  rw [← hE.range_eq_ker]
  exact hE.finite_range hu hQ

/-- The kernel of `Q*(u)` for a row-compact operator admitting a Riesz–Coleman projection is
projective when `Q.leadingCoeff` is a unit. -/
theorem IsRieszColemanProjection.projective_ker_aeval_reverse {u E : C₀(I, R) →L[R] C₀(I, R)}
    {Q : R[X]} (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact)
    (hQ : IsUnit Q.leadingCoeff) :
    Module.Projective R
      (LinearMap.ker ((Polynomial.aeval u Q.reverse : C₀(I, R) →L[R] C₀(I, R)) :
        C₀(I, R) →ₗ[R] C₀(I, R))) := by
  rw [← hE.range_eq_ker]
  exact hE.projective_range hu hQ

omit [TauCeti.NormedRing.IsTate R] [IsUltrametricDist R] [CompleteSpace R] in
/-- Evaluating a polynomial at the compressed operator `u * (1 - E)` adds `P(0) • E` to the block
`P(u) * (1 - E)`. -/
private theorem aeval_mul_one_sub_of_isIdempotentElem {A : Type*} [Ring A] [Algebra R A]
    {u E : A} (hE : IsIdempotentElem E) (huE : Commute u E) (P : R[X]) :
    Polynomial.aeval (u * (1 - E)) P = P.coeff 0 • E + Polynomial.aeval u P * (1 - E) := by
  have huE' : Commute u (1 - E) := (Commute.one_right u).sub_right huE
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, coeff_add, add_smul, map_add, add_mul, hp, hq]
    abel
  | monomial n a =>
    cases n with
    | zero =>
      rw [monomial_zero_left, coeff_C_zero, aeval_C, aeval_C, Algebra.algebraMap_eq_smul_one,
        smul_mul_assoc, one_mul, smul_sub, add_sub_cancel]
    | succ k =>
      rw [coeff_monomial_succ, zero_smul, zero_add, aeval_monomial, aeval_monomial, huE'.mul_pow,
        hE.one_sub.pow_succ_eq, mul_assoc]

/-- If `Q` with `Q(0) = 1` and unit leading coefficient divides a polynomial `P` of degree at most
`deg Q` with `P(0) = 1` in the ring of entire series, then `P = Q`. -/
private theorem eq_of_dvd_in_isEntire_subring {P Q : R[X]} (hP0 : P.coeff 0 = 1)
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hd : P.natDegree ≤ Q.natDegree)
    (hdvd : (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R) ∣
      ⟨P, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe P)⟩) :
    P = Q := by
  have : Nontrivial R := NormOneClass.nontrivial
  set c := Ring.inverse Q.leadingCoeff
  have hc : c * Q.leadingCoeff = 1 := Ring.inverse_mul_cancel _ hQ
  have hQ₁ : (C c * Q).Monic := monic_C_mul_of_mul_leadingCoeff_eq_one hc
  have hd₁ : (C c * Q).natDegree = Q.natDegree :=
    natDegree_C_mul_eq_of_mul_eq_one (by rw [mul_comm]; exact hc)
  obtain ⟨⟨H, hH⟩, hPH⟩ := hdvd
  have hPH' : (P : PowerSeries R) =
      ((C c * Q : R[X]) : PowerSeries R) * (PowerSeries.C Q.leadingCoeff * H) := by
    calc (P : PowerSeries R) = (Q : PowerSeries R) * H := congrArg Subtype.val hPH
      _ = (PowerSeries.C c * PowerSeries.C Q.leadingCoeff) * ((Q : PowerSeries R) * H) := by
          rw [← map_mul, hc, map_one, one_mul]
      _ = ((C c * Q : R[X]) : PowerSeries R) * (PowerSeries.C Q.leadingCoeff * H) := by
          rw [Polynomial.coe_mul, Polynomial.coe_C]; ring
  have hdvdP : C c * Q ∣ P := by
    rw [← modByMonic_eq_zero_iff_dvd hQ₁, ← PowerSeries.modByMonic_coe P hQ₁]
    exact ((PowerSeries.isEntire_coe P).modByMonic_eq_zero_iff hQ₁).mpr
      ⟨_, (PowerSeries.isEntire_C _).mul (IsEntire.mem_subring.mp hH), hPH'⟩
  obtain ⟨R₀, hPR₀⟩ := hdvdP
  have hR₀ : R₀ ≠ 0 := by
    rintro rfl
    simp [hPR₀] at hP0
  have hdeg0 : R₀.natDegree = 0 := by
    have hm := hQ₁.natDegree_mul' hR₀
    rw [← hPR₀, hd₁] at hm
    omega
  rw [eq_C_of_natDegree_eq_zero hdeg0] at hPR₀
  have hc0 : c * R₀.coeff 0 = 1 := by
    have := congrArg (fun p ↦ p.coeff 0) hPR₀
    simpa [hP0, hQ0, mul_assoc] using this.symm
  have hr0 : R₀.coeff 0 = Q.leadingCoeff := by
    calc R₀.coeff 0 = Q.leadingCoeff * (c * R₀.coeff 0) := by
          rw [← mul_assoc, mul_comm Q.leadingCoeff c, hc, one_mul]
      _ = Q.leadingCoeff := by rw [hc0, mul_one]
  rw [hPR₀, hr0, mul_comm _ (C Q.leadingCoeff), ← mul_assoc, ← C_mul, mul_comm Q.leadingCoeff c,
    hc, C_1, one_mul]

/-- Along `B = 1 - c Q*`, the Fredholm series of `B(u)` has a good zero of order `deg Q` at `1`
whenever `H_u = Q · S` is a coprime factorisation with `Q(0) = 1` and `IsUnit Q.leadingCoeff`. -/
private theorem isGoodZero_charPowerSeries_aeval_one_sub {u : C₀(I, R) →L[R] C₀(I, R)}
    (hu : u.IsRowCompact) {Q : R[X]} {S : PowerSeries R} (hQ0 : Q.coeff 0 = 1)
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.matrixCoeff.charPowerSeries = (Q : PowerSeries R) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
        IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (Polynomial.aeval u (1 - C (Ring.inverse Q.leadingCoeff) * Q.reverse)).matrixCoeff
      |>.charPowerSeries.IsGoodZero 1 Q.natDegree := by
  set c := Ring.inverse Q.leadingCoeff
  have hc : c * Q.leadingCoeff = 1 := Ring.inverse_mul_cancel _ hQ
  set B := 1 - C c * Q.reverse
  have hB0 : B.coeff 0 = 0 := coeff_zero_one_sub_C_mul_reverse hc
  have hS0 : PowerSeries.constantCoeff S = 1 := by
    have := congrArg PowerSeries.constantCoeff hfac
    simpa [hQ0] using this.symm
  have hS0' : PowerSeries.coeff 0 S = 1 := by
    rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have hDe : (B.colemanDSeries S).IsEntire :=
    PowerSeries.colemanDEntire_coe (F := S) hB0 hS0' ▸
      PowerSeries.isEntire_colemanDEntire (PowerSeries.isEntire_coe B) hS
        (by rwa [Polynomial.coeff_coe]) hS0'
  have hunit : IsUnit ((B.colemanDSeries S).evalAt (1 : R)) :=
    (isUnit_evalAt_one_colemanDSeries_one_sub_C_mul_reverse_iff hc hS hS0).mpr hcop
  rw [hu.charPowerSeries_matrixCoeff_aeval hB0, hfac, colemanDSeries_mul hB0,
    colemanDSeries_one_sub_C_mul_reverse_self hQ0 hc]
  have hrew : (1 - PowerSeries.X : PowerSeries R) ^ Q.natDegree * B.colemanDSeries S =
      (PowerSeries.X - PowerSeries.C 1) ^ Q.natDegree *
        ((-1 : R) ^ Q.natDegree • B.colemanDSeries S) := by
    have h1 : (1 - PowerSeries.X : PowerSeries R) =
        (-1 : R) • (PowerSeries.X - PowerSeries.C 1) := by
      ext n
      simp [sub_eq_add_neg, add_comm]
    rw [h1, smul_pow, smul_mul_assoc, mul_smul_comm]
  rw [hrew, (hDe.smul _).isGoodZero_X_sub_C_pow_mul_iff, hDe.evalAt_smul, smul_eq_mul]
  exact ((isUnit_one.neg).pow _).mul hunit

/-- On the finite projective range of a row-compact idempotent `E` commuting with `u`, the Fredholm
factor `H_{u E}` is the reversed characteristic polynomial of `u|_{range E}`. -/
private theorem charPowerSeries_matrixCoeff_mul_eq_projectiveCharpolyRev
    {u E : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact) (hEc : E.IsRowCompact)
    (hEi : IsIdempotentElem E) (hm : ∀ x ∈ E.range, u x ∈ E.range) :
    letI : AddCommGroup E.range := inferInstance
    haveI : Module.Finite R E.range := hEc.finite_range_of_isIdempotentElem hEi
    haveI : Module.Projective R E.range := hEc.projective_range_of_isIdempotentElem hEi
    (u * E).matrixCoeff.charPowerSeries =
      ((u.restrict hm).toLinearMap.projectiveCharpolyRev : PowerSeries R) := by
  let : AddCommGroup E.range := inferInstance
  have := hEc.finite_range_of_isIdempotentElem hEi
  have := hEc.projective_range_of_isIdempotentElem hEi
  let v₀ : E.range →L[R] E.range := u.restrict hm
  have hfix (x : E.range) : E x = x :=
    (LinearMap.IsIdempotentElem.mem_range_iff
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap hEi)).mp x.property
  have hri : E.rangeRestrict.comp E.range.subtypeL = .id R E.range :=
    ContinuousLinearMap.ext fun x ↦ Subtype.ext (hfix x)
  have hM : TauCeti.HasPr R E.range :=
    (isPrCompact_iff_isRowCompact.2 hu).hasPr_source.of_retract E.range.subtypeL E.rangeRestrict hri
  have hv₀ := isPrCompact_of_finite (R := R) (M := E.range) (L := E.range) hM hM v₀
  have hext : E.range.subtypeL.comp (v₀.comp E.rangeRestrict) = u * E := by ext x; rfl
  have hchar := charPowerSeries_eq_projectiveCharpolyRev (R := R) (M := E.range) hM v₀
  rw [← hext, ← hv₀.charPowerSeries_eq hri, hchar]

/-- When `H_u = Q · S` is a coprime factorisation and `Q*(u * (1 - E₀))` is invertible for a
row-compact idempotent `E₀` commuting with `u` whose range has constant rank `deg Q`, the reversed
characteristic polynomial of `u|_{range E₀}` is `Q` and `H_{u(1 - E₀)} = S`. -/
private theorem eq_and_eq_of_isUnit_aeval_complement
    {u E₀ : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact) (hE₀c : E₀.IsRowCompact)
    (hE₀i : IsIdempotentElem E₀) (huE₀ : Commute u E₀) (hm : ∀ x ∈ E₀.range, u x ∈ E₀.range)
    {Q : R[X]} {S : PowerSeries R} (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff)
    (hS : S.IsEntire) (hfac : u.matrixCoeff.charPowerSeries = (Q : PowerSeries R) * S)
    (hrank : ∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) E₀.range p = Q.natDegree)
    (hunitComp : IsUnit (Polynomial.aeval (u * (1 - E₀)) Q.reverse)) :
    letI : AddCommGroup E₀.range := inferInstance
    haveI := hE₀c.finite_range_of_isIdempotentElem hE₀i
    haveI := hE₀c.projective_range_of_isIdempotentElem hE₀i
    (u.restrict hm).toLinearMap.projectiveCharpolyRev = Q ∧
      (u * (1 - E₀)).matrixCoeff.charPowerSeries = S := by
  let : AddCommGroup E₀.range := inferInstance
  have := hE₀c.finite_range_of_isIdempotentElem hE₀i
  have := hE₀c.projective_range_of_isIdempotentElem hE₀i
  let f₀ : Module.End R E₀.range := (u.restrict hm).toLinearMap
  set P := f₀.projectiveCharpolyRev
  have hcharP := charPowerSeries_matrixCoeff_mul_eq_projectiveCharpolyRev hu hE₀c hE₀i hm
  have hcopG := ((hu.comp_clm (1 - E₀)).isUnit_aeval_reverse_iff hQ).mp hunitComp
  have hsplit := hu.charPowerSeries_matrixCoeff_eq_mul_of_commute hE₀i huE₀
  rw [hfac, hcharP] at hsplit
  have hdP : P.natDegree ≤ Q.natDegree :=
    LinearMap.natDegree_projectiveCharpolyRev_le (fun p ↦ (hrank p).le) f₀
  have hdvdQP : (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R) ∣
      ⟨P, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe P)⟩ :=
    hcopG.dvd_of_dvd_mul_right ⟨⟨S, IsEntire.mem_subring.mpr hS⟩, Subtype.ext hsplit.symm⟩
  have hPQ : P = Q := eq_of_dvd_in_isEntire_subring
    (LinearMap.coeff_projectiveCharpolyRev_zero f₀) hQ0 hQ hdP hdvdQP
  refine ⟨hPQ, ?_⟩
  have hsplit' : (Q : PowerSeries R) * S =
      (Q : PowerSeries R) * (u * (1 - E₀)).matrixCoeff.charPowerSeries := by
    simpa only [f₀, P, hPQ] using hsplit
  have hQu : IsUnit (Q : PowerSeries R) := PowerSeries.isUnit_iff_constantCoeff.mpr (by simp [hQ0])
  exact hQu.mul_left_cancel hsplit'.symm

/-- On the complementary summand of `E₀ = u.rieszColemanProjection Q`, the compressed operator
`u * (1 - E₀)` makes `Q*(u * (1 - E₀))` a unit in `C₀(I, R) →L[R] C₀(I, R)`. -/
private theorem isUnit_aeval_mul_one_sub_rieszColemanProjection
    {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact) {Q : R[X]} {S : PowerSeries R}
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.matrixCoeff.charPowerSeries = (Q : PowerSeries R) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
        IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    IsUnit (Polynomial.aeval (u * (1 - u.rieszColemanProjection Q)) Q.reverse) := by
  set c := Ring.inverse Q.leadingCoeff
  have hc : c * Q.leadingCoeff = 1 := Ring.inverse_mul_cancel _ hQ
  set v := Polynomial.aeval u (1 - C c * Q.reverse)
  have hv : v.IsRowCompact := hu.aeval (coeff_zero_one_sub_C_mul_reverse hc)
  have hgood := isGoodZero_charPowerSeries_aeval_one_sub hu hQ0 hQ hS hfac hcop
  have hEv : IsRieszProjection v 1 Q.natDegree (u.rieszColemanProjection Q) :=
    hv.isRieszProjection_rieszProjection (fun _ ↦ hgood.evalAt_hasseDeriv_eq_zero)
      hgood.isUnit_evalAt_hasseDeriv
  have huv : Commute u v := by
    rw [Commute, SemiconjBy, mul_def, mul_def]
    apply ContinuousLinearMap.coe_injective
    simpa only [v, toLinearMap_comp, toLinearMap_aeval] using
      (Module.End.aeval_comp_of_comp_eq (f := u.toLinearMap) (g := u.toLinearMap)
        (g₂ := u.toLinearMap) rfl (1 - C c * Q.reverse)).symm
  have huE₀ : Commute u (u.rieszColemanProjection Q) := hEv.commute_of_commute huv
  have h1 := _root_.IsIdempotentElem.isUnit_add_mul_one_sub (A := C₀(I, R) →L[R] C₀(I, R))
    hEv.isIdempotentElem hEv.one_sub_smul_mul_inverse hEv.inverse_mul_one_sub_smul
  have h1v : (1 - (1 : R) • v : C₀(I, R) →L[R] C₀(I, R)) = c • Polynomial.aeval u Q.reverse := by
    simp [v, Algebra.algebraMap_eq_smul_one]
  rw [h1v] at h1
  have h2 : u.rieszColemanProjection Q +
      (c • Polynomial.aeval u Q.reverse) * (1 - u.rieszColemanProjection Q) =
      (c • 1 : C₀(I, R) →L[R] C₀(I, R)) *
        Polynomial.aeval (u * (1 - u.rieszColemanProjection Q)) Q.reverse := by
    rw [aeval_mul_one_sub_of_isIdempotentElem (A := C₀(I, R) →L[R] C₀(I, R))
        hEv.isIdempotentElem huE₀ Q.reverse, coeff_zero_reverse]
    ext x i
    simp [mul_apply_eq_comp, mul_add, ← mul_assoc, hc]
  have hc1 : IsUnit (c • 1 : C₀(I, R) →L[R] C₀(I, R)) :=
    isUnit_iff_exists.mpr ⟨Q.leadingCoeff • 1,
      by rw [smul_mul_smul_comm, one_mul, hc, one_smul],
      by rw [smul_mul_smul_comm, one_mul, mul_comm, hc, one_smul]⟩
  exact hc1.mul_left_iff.mp (h2 ▸ h1)

/-- For the projector `E₀ = u.rieszColemanProjection Q`, the finite projective characteristic
polynomial of `u|_{range E₀}` is `Q`, the complementary Fredholm series is `S`, and `Q*(u)`
annihilates `E₀`. -/
private theorem rieszColemanProjection_factors_and_aeval_reverse_eq_zero
    {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact) {Q : R[X]} {S : PowerSeries R}
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.matrixCoeff.charPowerSeries = (Q : PowerSeries R) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
        IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    let E₀ := u.rieszColemanProjection Q
    letI : AddCommGroup E₀.range := inferInstance
    ∃ (hm : ∀ x ∈ E₀.range, u x ∈ E₀.range) (_ : Module.Finite R E₀.range)
      (_ : Module.Projective R E₀.range),
      (u.restrict hm).toLinearMap.projectiveCharpolyRev = Q ∧
      (u * E₀).matrixCoeff.charPowerSeries = (Q : PowerSeries R) ∧
      (u * (1 - E₀)).matrixCoeff.charPowerSeries = S ∧
      Polynomial.aeval u Q.reverse * E₀ = 0 := by
  set c := Ring.inverse Q.leadingCoeff
  have hc : c * Q.leadingCoeff = 1 := Ring.inverse_mul_cancel _ hQ
  set v := Polynomial.aeval u (1 - C c * Q.reverse)
  have hv : v.IsRowCompact := hu.aeval (coeff_zero_one_sub_C_mul_reverse hc)
  have hgood := isGoodZero_charPowerSeries_aeval_one_sub hu hQ0 hQ hS hfac hcop
  have hEv : IsRieszProjection v 1 Q.natDegree (u.rieszColemanProjection Q) :=
    hv.isRieszProjection_rieszProjection (fun _ ↦ hgood.evalAt_hasseDeriv_eq_zero)
      hgood.isUnit_evalAt_hasseDeriv
  set E₀ := u.rieszColemanProjection Q
  have huv : Commute u v := by
    rw [Commute, SemiconjBy, mul_def, mul_def]
    apply ContinuousLinearMap.coe_injective
    simpa only [v, toLinearMap_comp, toLinearMap_aeval] using
      (Module.End.aeval_comp_of_comp_eq (f := u.toLinearMap) (g := u.toLinearMap)
        (g₂ := u.toLinearMap) rfl (1 - C c * Q.reverse)).symm
  have huE₀ : Commute u E₀ := hEv.commute_of_commute huv
  have hm : ∀ x ∈ E₀.range, u x ∈ E₀.range := by
    rintro _ ⟨x, rfl⟩
    exact ⟨u x, congr($(huE₀.eq.symm) x)⟩
  have hE₀c : E₀.IsRowCompact := hEv.isRowCompact hv
  let : AddCommGroup E₀.range := inferInstance
  have : Module.Finite R E₀.range := hE₀c.finite_range_of_isIdempotentElem hEv.isIdempotentElem
  have : Module.Projective R E₀.range :=
    hE₀c.projective_range_of_isIdempotentElem hEv.isIdempotentElem
  have hrank := hEv.rankAtStalk_range hv hgood
  obtain ⟨hPQ, hGS⟩ := eq_and_eq_of_isUnit_aeval_complement hu hE₀c hEv.isIdempotentElem huE₀ hm
    hQ0 hQ hS hfac hrank (isUnit_aeval_mul_one_sub_rieszColemanProjection hu hQ0 hQ hS hfac hcop)
  have hcharQ : (u * E₀).matrixCoeff.charPowerSeries = (Q : PowerSeries R) := by
    rw [charPowerSeries_matrixCoeff_mul_eq_projectiveCharpolyRev hu hE₀c hEv.isIdempotentElem hm,
      hPQ]
  let f₀ : Module.End R E₀.range := (u.restrict hm).toLinearMap
  have hf₀u : IsUnit f₀ := by
    rw [LinearMap.isUnit_iff_isUnit_projectiveDet]
    have hdet := LinearMap.coeff_projectiveCharpolyRev_of_rankAtStalk_eq hrank f₀
    rw [show f₀.projectiveCharpolyRev = Q from hPQ, coeff_natDegree] at hdet
    exact isUnit_of_mul_isUnit_right (hdet ▸ hQ)
  have hQf₀ : Polynomial.aeval f₀ Q.reverse = 0 := by
    simpa only [f₀, hPQ] using LinearMap.aeval_reverse_projectiveCharpolyRev_of_isUnit hf₀u
  refine ⟨hm, inferInstance, inferInstance, hPQ, hcharQ, hGS, ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  have hinter : u.toLinearMap.comp E₀.range.subtype = E₀.range.subtype.comp f₀ := by ext y; rfl
  let y : E₀.range := ⟨E₀ x, ⟨x, rfl⟩⟩
  have hsub := LinearMap.congr_fun (Module.End.aeval_comp_of_comp_eq hinter Q.reverse) y
  have hy : Polynomial.aeval f₀ Q.reverse y = 0 := by rw [hQf₀]; rfl
  simpa only [LinearMap.comp_apply, Submodule.coe_subtype, hy, map_zero, ← toLinearMap_aeval,
    coe_coe, mul_apply_eq_comp, zero_apply] using hsub

/-- **The Riesz–Coleman projector for a coprime polynomial factor.** Let `u` be a row-compact
endomorphism of `C₀(I, R)`, let `Q : R[X]` have `Q(0) = 1` and invertible leading coefficient, and
let `S` be an entire power series coprime to `Q` in `IsEntire.subring R` with `H_u = Q · S`. Then
`u.rieszColemanProjection Q` is a Riesz–Coleman projection of `u` for `Q`. -/
theorem IsRowCompact.isRieszColemanProjection_rieszColemanProjection
    {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact) {Q : R[X]} {S : PowerSeries R}
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.matrixCoeff.charPowerSeries = (Q : PowerSeries R) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
        IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    IsRieszColemanProjection u Q (u.rieszColemanProjection Q) := by
  set c := Ring.inverse Q.leadingCoeff
  have hc : c * Q.leadingCoeff = 1 := Ring.inverse_mul_cancel _ hQ
  set B := 1 - C c * Q.reverse
  have hB0 : B.coeff 0 = 0 := coeff_zero_one_sub_C_mul_reverse hc
  set v := Polynomial.aeval u B
  have hv : v.IsRowCompact := hu.aeval hB0
  have hgood := isGoodZero_charPowerSeries_aeval_one_sub hu hQ0 hQ hS hfac hcop
  have hEv : IsRieszProjection v 1 Q.natDegree (u.rieszColemanProjection Q) :=
    hv.isRieszProjection_rieszProjection (fun _ ↦ hgood.evalAt_hasseDeriv_eq_zero)
      hgood.isUnit_evalAt_hasseDeriv
  obtain ⟨-, -, -, -, -, -, hzero⟩ :=
    rieszColemanProjection_factors_and_aeval_reverse_eq_zero hu hQ0 hQ hS hfac hcop
  have huv : Commute u v := by
    rw [Commute, SemiconjBy, mul_def, mul_def]
    apply ContinuousLinearMap.coe_injective
    simpa only [v, toLinearMap_comp, toLinearMap_aeval] using
      (Module.End.aeval_comp_of_comp_eq (f := u.toLinearMap) (g := u.toLinearMap)
        (g₂ := u.toLinearMap) rfl B).symm
  have hadj : (Algebra.adjoin R {v} : Set (C₀(I, R) →L[R] C₀(I, R))) ⊆
      Algebra.adjoin R {u} :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr
      (SetLike.mem_coe.mpr (aeval_mem_adjoin_singleton R u)))
  have h1v : (1 - (1 : R) • v : C₀(I, R) →L[R] C₀(I, R)) = c • Polynomial.aeval u Q.reverse := by
    simp [v, B, Algebra.algebraMap_eq_smul_one]
  have : IsTopologicalSemiring (C₀(I, R) →L[R] C₀(I, R)) := inferInstance
  set T := (Algebra.adjoin R {u}).topologicalClosure
  have hT (x : C₀(I, R) →L[R] C₀(I, R)) :
      x ∈ T ↔ x ∈ closure (Algebra.adjoin R {u} : Set (C₀(I, R) →L[R] C₀(I, R))) := by
    rw [← SetLike.mem_coe, Subalgebra.topologicalClosure_coe]
  refine ⟨hEv.isIdempotentElem, hEv.commute_of_commute huv,
    closure_mono hadj hEv.mem_closure_adjoin, hzero,
    ⟨c • hEv.inverse, ?_, ?_, ?_, ?_,
      (hT _).mp (T.smul_mem ((hT _).mpr (closure_mono hadj hEv.inverse_mem_closure_adjoin)) c)⟩⟩
  · rw [mul_smul_comm, ← smul_mul_assoc, ← h1v, hEv.one_sub_smul_mul_inverse]
  · rw [smul_mul_assoc, ← mul_smul_comm, ← h1v, hEv.inverse_mul_one_sub_smul]
  · rw [mul_smul_comm, hEv.mul_inverse_eq_zero, smul_zero]
  · rw [smul_mul_assoc, hEv.inverse_mul_eq_zero, smul_zero]

/-- **Existence of the Riesz–Coleman projection on `C₀(I, R)`.** Every coprime polynomial factor `Q`
with `Q(0) = 1` and invertible leading coefficient of the Fredholm series of a row-compact
operator `u` admits a Riesz–Coleman projection. -/
theorem IsRowCompact.exists_isRieszColemanProjection
    {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact) {Q : R[X]} {S : PowerSeries R}
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.matrixCoeff.charPowerSeries = (Q : PowerSeries R) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
        IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    ∃ E, IsRieszColemanProjection u Q E :=
  ⟨u.rieszColemanProjection Q,
    hu.isRieszColemanProjection_rieszColemanProjection hQ0 hQ hS hfac hcop⟩

/-- Any Riesz–Coleman projection of a row-compact `u` for a coprime polynomial factor `Q` of `H_u`
with `Q(0) = 1` and invertible leading coefficient equals `u.rieszColemanProjection Q`. -/
theorem IsRieszColemanProjection.eq_rieszColemanProjection
    {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]} {S : PowerSeries R}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact)
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.matrixCoeff.charPowerSeries = (Q : PowerSeries R) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
        IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    E = u.rieszColemanProjection Q :=
  hE.unique (hu.isRieszColemanProjection_rieszColemanProjection hQ0 hQ hS hfac hcop)

/-- **Constant rank of the Riesz–Coleman summand.** For a coprime factorisation `H_u = Q · S` with
`Q(0) = 1` and invertible leading coefficient, the range of the Riesz–Coleman projection has
constant rank `deg Q` on `Spec R`. -/
theorem IsRieszColemanProjection.rankAtStalk_range
    {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]} {S : PowerSeries R}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact)
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.matrixCoeff.charPowerSeries = (Q : PowerSeries R) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
        IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) E.range p = Q.natDegree := by
  rw [hE.eq_rieszColemanProjection hu hQ0 hQ hS hfac hcop]
  have hB0 : (1 - C (Ring.inverse Q.leadingCoeff) * Q.reverse).coeff 0 = 0 :=
    coeff_zero_one_sub_C_mul_reverse (Ring.inverse_mul_cancel _ hQ)
  have hgood := isGoodZero_charPowerSeries_aeval_one_sub hu hQ0 hQ hS hfac hcop
  exact ((hu.aeval hB0).isRieszProjection_rieszProjection
    (fun _ ↦ hgood.evalAt_hasseDeriv_eq_zero) hgood.isUnit_evalAt_hasseDeriv).rankAtStalk_range
    (hu.aeval hB0) hgood p

/-- **Constant rank of `ker Q*(u)` on `C₀(I, R)`.** For a coprime factorisation `H_u = Q · S` with
`Q(0) = 1` and invertible leading coefficient, `ker Q*(u)` has rank `deg Q` at every prime ideal. -/
theorem IsRowCompact.rankAtStalk_ker_aeval_reverse
    {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact) {Q : R[X]} {S : PowerSeries R}
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.matrixCoeff.charPowerSeries = (Q : PowerSeries R) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
        IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R)
      (LinearMap.ker ((Polynomial.aeval u Q.reverse : C₀(I, R) →L[R] C₀(I, R)) :
        C₀(I, R) →ₗ[R] C₀(I, R))) p = Q.natDegree := by
  have hE := hu.isRieszColemanProjection_rieszColemanProjection hQ0 hQ hS hfac hcop
  rw [← hE.range_eq_ker]
  exact hE.rankAtStalk_range hu hQ0 hQ hS hfac hcop p

/-- **Characteristic polynomial of the Riesz–Coleman summand.** On the finite projective summand
`range E`, the reversed characteristic polynomial `det (1 - X u|_{range E})` is `Q`. -/
theorem IsRieszColemanProjection.projectiveCharpolyRev_restrict_range
    {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]} {S : PowerSeries R}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact)
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.matrixCoeff.charPowerSeries = (Q : PowerSeries R) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
        IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    letI : AddCommGroup E.range := inferInstance
    haveI := hE.finite_range hu hQ
    haveI := hE.projective_range hu hQ
    (u.restrict (fun _ hx ↦ hE.mapsTo_range hx)).toLinearMap.projectiveCharpolyRev = Q := by
  have hEq := hE.eq_rieszColemanProjection hu hQ0 hQ hS hfac hcop
  subst hEq
  obtain ⟨hm, _, _, hPQ, -, -, -⟩ :=
    rieszColemanProjection_factors_and_aeval_reverse_eq_zero hu hQ0 hQ hS hfac hcop
  exact hPQ

/-- **Finite Fredholm factor of a Riesz–Coleman splitting.** For a coprime factorisation
`H_u = Q · S` with `Q(0) = 1` and invertible leading coefficient, `det (1 - T u E) = Q`. -/
theorem IsRieszColemanProjection.charPowerSeries_matrixCoeff_mul_eq
    {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]} {S : PowerSeries R}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact)
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.matrixCoeff.charPowerSeries = (Q : PowerSeries R) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
        IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (u * E).matrixCoeff.charPowerSeries = (Q : PowerSeries R) := by
  rw [hE.eq_rieszColemanProjection hu hQ0 hQ hS hfac hcop]
  obtain ⟨-, -, -, -, hQ', -, -⟩ :=
    rieszColemanProjection_factors_and_aeval_reverse_eq_zero hu hQ0 hQ hS hfac hcop
  exact hQ'

/-- **Complementary Fredholm factor of a Riesz–Coleman splitting.** For a coprime factorisation
`H_u = Q · S` with `Q(0) = 1` and invertible leading coefficient, `det (1 - T u (1 - E)) = S`. -/
theorem IsRieszColemanProjection.charPowerSeries_matrixCoeff_mul_one_sub_eq
    {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]} {S : PowerSeries R}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact)
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.matrixCoeff.charPowerSeries = (Q : PowerSeries R) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
        IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (u * (1 - E)).matrixCoeff.charPowerSeries = S := by
  rw [hE.eq_rieszColemanProjection hu hQ0 hQ hS hfac hcop]
  obtain ⟨-, -, -, -, -, hS', -⟩ :=
    rieszColemanProjection_factors_and_aeval_reverse_eq_zero hu hQ0 hQ hS hfac hcop
  exact hS'

end RowCompact

section BaseChange

variable {S : Type*} [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S]
  [TauCeti.NormedRing.IsTate S]

/-- **Riesz–Coleman projections under bounded base change.** When `Q.leadingCoeff` is a unit, so
that `(Q.map f).reverse = Q.reverse.map f`, coefficientwise extension along a bounded ring
homomorphism `f : R →+* S` preserves Riesz–Coleman projections. No compactness is needed. -/
theorem IsRieszColemanProjection.mapCoeffs {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]}
    (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff)
    (f : R →+* S) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) :
    IsRieszColemanProjection (u.mapCoeffs f hf) (Q.map f) (E.mapCoeffs f hf) := by
  have : Nontrivial S := NormOneClass.nontrivial
  have hrev : (Q.map f).reverse = Q.reverse.map f := by
    rw [Polynomial.reverse, Polynomial.reverse,
      natDegree_map_of_leadingCoeff_ne_zero f (hQ.map f).ne_zero, reflect_map]
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

/-- **Bounded base change of the explicit Riesz–Coleman projector.** For a coprime factorisation
`H_u = Q · G` of a row-compact `u` with `Q(0) = 1` and invertible leading coefficient, the explicit
Riesz–Coleman projector commutes with bounded coefficient extension. -/
theorem IsRowCompact.rieszColemanProjection_mapCoeffs [IsUltrametricDist R] [CompleteSpace R]
    {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact) {Q : R[X]} {G : PowerSeries R}
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hG : G.IsEntire)
    (hfac : u.matrixCoeff.charPowerSeries = (Q : PowerSeries R) * G)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
        IsEntire.subring R) ⟨G, IsEntire.mem_subring.mpr hG⟩)
    (f : R →+* S) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) :
    (u.mapCoeffs f hf).rieszColemanProjection (Q.map f) =
      (u.rieszColemanProjection Q).mapCoeffs f hf := by
  have : Nontrivial S := NormOneClass.nontrivial
  have hdeg : (Q.map f).natDegree = Q.natDegree :=
    natDegree_map_of_leadingCoeff_ne_zero f (hQ.map f).ne_zero
  have hlead : (Q.map f).leadingCoeff = f Q.leadingCoeff :=
    leadingCoeff_map_of_leadingCoeff_ne_zero f (hQ.map f).ne_zero
  have hrev : (Q.map f).reverse = Q.reverse.map f := by
    rw [Polynomial.reverse, Polynomial.reverse, hdeg, reflect_map]
  let B := 1 - C (Ring.inverse Q.leadingCoeff) * Q.reverse
  have hB0 : B.coeff 0 = 0 := coeff_zero_one_sub_C_mul_reverse (Ring.inverse_mul_cancel _ hQ)
  have hBmap : 1 - C (Ring.inverse (Q.map f).leadingCoeff) * (Q.map f).reverse = B.map f := by
    rw [hlead, ← hQ.map_ringInverse f, hrev, Polynomial.map_sub, Polynomial.map_one,
      Polynomial.map_mul, map_C]
  have hgood := isGoodZero_charPowerSeries_aeval_one_sub hu hQ0 hQ hG hfac hcop
  change (Polynomial.aeval (u.mapCoeffs f hf) _).rieszProjection 1 (Q.map f).natDegree =
    ((Polynomial.aeval u B).rieszProjection 1 Q.natDegree).mapCoeffs f hf
  rw [hdeg, hBmap, ← mapCoeffs_aeval, ← map_one f]
  exact (hu.aeval hB0).rieszProjection_mapCoeffs f hf hgood.isUnit_evalAt_hasseDeriv

end BaseChange

end ModelSpace

section Field

variable {I K : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {u E : C₀(I, K) →L[K] C₀(I, K)} {Q : K[X]} {S : PowerSeries K}

/-- Over a complete ultrametric field, the range of the Riesz–Coleman projection for a coprime
factor `Q` with `Q(0) = 1` of `H_u = Q · S` has dimension `deg Q`. -/
theorem IsRieszColemanProjection.finrank_range
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact)
    (hQ0 : Q.coeff 0 = 1) (hS : S.IsEntire)
    (hfac : u.matrixCoeff.charPowerSeries = (Q : PowerSeries K) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
        IsEntire.subring K) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    Module.finrank K E.range = Q.natDegree := by
  have hQ : IsUnit Q.leadingCoeff :=
    Ne.isUnit (leadingCoeff_ne_zero.mpr fun h0 ↦ by simp [h0] at hQ0)
  have hr := hE.rankAtStalk_range hu hQ0 hQ hS hfac hcop ⟨⊥, Ideal.isPrime_bot⟩
  let : AddCommGroup E.range := inferInstance
  rwa [Module.rankAtStalk_eq_finrank_of_free] at hr

/-- Over a complete ultrametric field, `ker Q*(u)` has dimension `deg Q` whenever `H_u = Q · S` is
a coprime factorisation with `Q(0) = 1`. -/
theorem IsRowCompact.finrank_ker_aeval_reverse (hu : u.IsRowCompact)
    (hQ0 : Q.coeff 0 = 1) (hS : S.IsEntire)
    (hfac : u.matrixCoeff.charPowerSeries = (Q : PowerSeries K) * S)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
        IsEntire.subring K) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    Module.finrank K
      (LinearMap.ker ((Polynomial.aeval u Q.reverse : C₀(I, K) →L[K] C₀(I, K)) :
        Module.End K C₀(I, K))) = Q.natDegree := by
  have hQ : IsUnit Q.leadingCoeff :=
    Ne.isUnit (leadingCoeff_ne_zero.mpr fun h0 ↦ by simp [h0] at hQ0)
  have hE := hu.isRieszColemanProjection_rieszColemanProjection hQ0 hQ hS hfac hcop
  rw [← hE.range_eq_ker]
  exact hE.finrank_range hu hQ0 hS hfac hcop

end Field

end ContinuousLinearMap
