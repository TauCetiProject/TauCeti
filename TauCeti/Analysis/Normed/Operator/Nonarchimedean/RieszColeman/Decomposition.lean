/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszColeman.Basic
public import TauCeti.LinearAlgebra.Charpoly.Projective
public import TauCeti.RingTheory.PowerSeries.Entire.GoodZero
import TauCeti.Analysis.Normed.Operator.Nonarchimedean.Coleman
import TauCeti.Analysis.Normed.Operator.Nonarchimedean.Idempotent
import TauCeti.Analysis.Normed.Operator.Nonarchimedean.PrModule.Basic
import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszProjection.Intertwining
import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszProjection.Multiplicity
import TauCeti.Analysis.Polynomial.Coleman.Coprime
import TauCeti.LinearAlgebra.End.Aeval
import TauCeti.RingTheory.Polynomial.Resultant.Coleman
import TauCeti.RingTheory.PowerSeries.Entire.Division

/-!
# Riesz–Coleman decomposition on model spaces

Let `R` be a complete ultrametric normed commutative Tate ring, `u` a row-compact endomorphism of
the model space `C₀(I, R)`, and `H_u = Q * S` a factorisation of its Fredholm series where `Q` is
a polynomial with invertible leading coefficient, `S` is entire, and `Q` and `S` are coprime in the
ring of entire series `PowerSeries.IsEntire.subring R`. Since `H_u(0) = 1`, we automatically get
`Q(0) * S(0) = 1`, so both `Q(0)` and `S(0)` are units of `R`. Multiplying `Q` by `S(0)` and `S`
by `Q(0)` reduces to the normalised case `Q(0) = S(0) = 1` without changing `deg Q`, `B`, `E`, or
`ker Q*(u)`; the normalisation `Q(0) = 1` is needed only to identify the individual factors
`(u * E).charPowerSeries = Q` and `(u * (1 - E)).charPowerSeries = S`.

Writing `c` for the inverse of `lc(Q)` and `B = 1 - c Q*` (so `B(0) = 0`), Coleman's spectral
mapping theorem (`ContinuousLinearMap.IsRowCompact.charPowerSeries_matrixCoeff_aeval`) transforms
the Fredholm series of `B(u)` into

`H_(B(u)) = D(B, Q) * D(B, S) = (1 - X) ^ (deg Q) * D(B, S)`,

where `D(B, S)(1)` is a unit by coprimality of `Q` and `S`
(`Polynomial.isUnit_evalAt_one_colemanDSeries_one_sub_C_mul_reverse_iff`). Hence `H_(B(u))` has a
good zero of order `deg Q` at `1`
(`ContinuousLinearMap.IsRowCompact.isGoodZero_charPowerSeries_aeval_one_sub_C_mul_reverse`).

Let `E = u.rieszColemanProjection Q` be the Riesz projector of `B(u)` at `1` of order `deg Q`. Then
`E` commutes with `u`, is row compact, and its range is a finitely generated projective `R`-module
of constant rank `deg Q` on `Spec R`. Assuming `Q(0) = 1`, let `P₁` be the reversed characteristic
polynomial of the restriction `u₁` of `u` to `range E`, and let `S₁` be the Fredholm series of
`u * (1 - E)`. By multiplicativity of Fredholm series along commuting idempotents,
`Q * S = H_u = P₁ * S₁`. Since `B(u * (1 - E)) = B(u) * (1 - E)`, the complementary factor `S₁` is
coprime to `Q` in `IsEntire.subring R`, forcing `Q ∣ P₁` as entire series. Entire division by the
monic polynomial `c Q` descends this divisibility to `R[X]`; combining `deg P₁ ≤ deg Q` with
`P₁(0) = Q(0) = 1` gives `P₁ = Q` and hence `S₁ = S`. The sharp Cayley–Hamilton theorem at the
rank bound `deg Q` (`LinearMap.aeval_reflect_projectiveCharpolyRev_eq_zero`) then yields
`Q*(u₁) = 0`, so `Q*(u) * E = 0`, upgrading the Riesz projector `E` of `B(u)` into a Riesz–Coleman
projection of `u` at `Q`.

The argument works over arbitrary complete ultrametric Tate rings — nilpotents, zero divisors, and
non-Noetherian rings are allowed, the projective summand need not be free, and the trivial factor
`Q = 1` (degree `0`) requires no separate case split. Over a complete ultrametric field `K`, the
factorisation `H_u = Q * S` also forces `Q ≠ 0`, so `lc(Q)` is automatically a unit.

## Main results

* `ContinuousLinearMap.IsRowCompact.isGoodZero_charPowerSeries_aeval_one_sub_C_mul_reverse`:
  the Fredholm series of `B(u)` has a good zero of order `deg Q` at `1`.
* `ContinuousLinearMap.IsRowCompact.isRieszColemanProjection_rieszColemanProjection`:
  the explicit candidate `u.rieszColemanProjection Q` is a Riesz–Coleman projection of `u` at `Q`.
* `ContinuousLinearMap.IsRowCompact.exists_rieszColemanProjection`: existence of the Riesz–Coleman
  projection.
* `ContinuousLinearMap.IsRieszColemanProjection.eq_rieszColemanProjection`: every Riesz–Coleman
  projection equals the explicit candidate `u.rieszColemanProjection Q`.
* `ContinuousLinearMap.IsRieszColemanProjection.rankAtStalk_range`: the finite projective summand
  `range E` has constant rank `deg Q` on `Spec R`.
* `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_matrixCoeff_mul_eq`,
  `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_matrixCoeff_mul_one_sub_eq`:
  the Fredholm series of `u * E` is `Q` and that of `u * (1 - E)` is `S` (when `Q(0) = 1`).
* `ContinuousLinearMap.IsRieszColemanProjection.finrank_range`,
  `ContinuousLinearMap.IsRowCompact.finrank_ker_aeval_reverse`: over a complete ultrametric field,
  `ker Q*(u)` has dimension `deg Q`.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127** (1997),
  417–479, Appendix A4.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.2.
-/

public section

open Polynomial
open scoped ZeroAtInfty PowerSeries TauCeti.RingOpNorm

open PowerSeries (IsEntire)

namespace ContinuousLinearMap

section Helpers

/-- For a commuting idempotent `e`, multiplying `p(u * e)` on the right by `e` agrees with
`p(u) * e`. -/
private theorem aeval_mul_eq_mul_of_isIdempotentElem {R A : Type*} [CommRing R] [Ring A]
    [Algebra R A] {u e : A} (he : IsIdempotentElem e) (hcomm : Commute u e) (p : R[X]) :
    Polynomial.aeval (u * e) p * e = Polynomial.aeval u p * e := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, add_mul, hp, hq]
  | monomial n a =>
    simp only [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    congr 1
    cases n with
    | zero => simp
    | succ k =>
      rw [hcomm.mul_pow, he.pow_succ_eq, mul_assoc, he.eq]

/-- For a polynomial `B` with zero constant term and a commuting idempotent `e`,
`B(u * e) = B(u) * e`. -/
private theorem aeval_mul_of_isIdempotentElem {R A : Type*} [CommRing R] [Ring A]
    [Algebra R A] {u e : A} (he : IsIdempotentElem e) (hcomm : Commute u e) {B : R[X]}
    (hB0 : B.coeff 0 = 0) :
    Polynomial.aeval (u * e) B = Polynomial.aeval u B * e := by
  have hB : B = X * B.divX := by
    have h := X_mul_divX_add B
    rw [hB0, map_zero, add_zero] at h
    exact h.symm
  have hcomm_e : Commute e (u * e) := hcomm.symm.mul_right (Commute.refl e)
  have hcomm_div : Commute e (Polynomial.aeval (u * e) B.divX) := by
    induction B.divX using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add]; exact hp.add_right hq
    | monomial n a =>
      rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
      exact (hcomm_e.pow_right n).smul_right a
  rw [hB, map_mul, aeval_X, map_mul, aeval_X, mul_assoc u e, hcomm_div.eq,
    aeval_mul_eq_mul_of_isIdempotentElem he hcomm, mul_assoc]

/-- Over a complete ultrametric norm-one ring, if two polynomials `P, Q` satisfy `P(0) = Q(0) = 1`,
`lc(Q)` is a unit inverted by `c`, `deg P ≤ deg Q`, and `P = Q * G` in `R⟦X⟧` for an entire series
`G`, then `P = Q`. -/
private theorem eq_of_coe_dvd_of_natDegree_le {R : Type*} [NormedCommRing R] [CompleteSpace R]
    [NormOneClass R] [IsUltrametricDist R] {P Q : R[X]} {c : R} {G : R⟦X⟧}
    (hP0 : P.coeff 0 = 1) (hQ0 : Q.coeff 0 = 1) (hc : c * Q.leadingCoeff = 1)
    (hdeg : P.natDegree ≤ Q.natDegree) (hG : G.IsEntire)
    (hPG : (P : R⟦X⟧) = (Q : R⟦X⟧) * G) : P = Q := by
  have : Nontrivial R := NormOneClass.nontrivial
  have hq₀ : (C c * Q).Monic := monic_C_mul_of_mul_leadingCoeff_eq_one hc
  have hG' : (PowerSeries.C Q.leadingCoeff * G).IsEntire := by
    rw [← Polynomial.coe_C]
    exact (PowerSeries.isEntire_coe (C Q.leadingCoeff)).mul hG
  have hmul :
      (P : R⟦X⟧) = ((C c * Q : R[X]) : R⟦X⟧) * (PowerSeries.C Q.leadingCoeff * G) := by
    rw [hPG, Polynomial.coe_mul, Polynomial.coe_C]
    calc (Q : R⟦X⟧) * G
        = PowerSeries.C (c * Q.leadingCoeff) * ((Q : R⟦X⟧) * G) := by rw [hc, map_one, one_mul]
      _ = PowerSeries.C c * (Q : R⟦X⟧) * (PowerSeries.C Q.leadingCoeff * G) := by
          rw [map_mul]; ring
  have hmod : P %ₘ (C c * Q) = 0 := by
    rw [← PowerSeries.modByMonic_coe P hq₀, hmul, hG'.coe_mul_modByMonic hq₀]
  obtain ⟨k, hk⟩ := (Polynomial.modByMonic_eq_zero_iff_dvd hq₀).mp hmod
  let r : R[X] := C c * k
  have hPr : P = Q * r := by dsimp only [r]; rw [hk]; ring
  have hr : r ≠ 0 := fun hr0 ↦ by
    have hP' : P = 0 := by rw [hPr, hr0, mul_zero]
    exact one_ne_zero (hP0.symm.trans (by simp [hP']))
  have hQunit : IsUnit Q.leadingCoeff := IsUnit.of_mul_eq_one_right c hc
  have hlc : Q.leadingCoeff * r.leadingCoeff ≠ 0 :=
    hQunit.mul_right_eq_zero.not.mpr (Polynomial.leadingCoeff_ne_zero.mpr hr)
  have hdeg_eq : P.natDegree = Q.natDegree + r.natDegree := by
    rw [hPr, Polynomial.natDegree_mul' hlc]
  have hrC : r = C (r.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero (by omega)
  have hr_coeff : r.coeff 0 = 1 := by
    have := congrArg (fun p : R[X] ↦ p.coeff 0) hPr
    simpa [Polynomial.mul_coeff_zero, hP0, hQ0] using this.symm
  rw [hPr, hrC, hr_coeff, map_one, mul_one]

/-- From `H_u = Q * S` with `Q(0) = 1` and `H_u(0) = 1`, we automatically get `S(0) = 1`. -/
private theorem constantCoeff_eq_one_of_mul {R : Type*} [CommRing R] {H S : R⟦X⟧} {Q : R[X]}
    (hH0 : PowerSeries.constantCoeff H = 1) (hH : H = (Q : R⟦X⟧) * S)
    (hQ0 : Q.coeff 0 = 1) : PowerSeries.constantCoeff S = 1 := by
  have h := congrArg PowerSeries.constantCoeff hH
  rw [hH0, map_mul, Polynomial.constantCoeff_coe, hQ0, one_mul] at h
  exact h.symm

/-- Normalising a coprime factorisation `H = Q * S` with `H(0) = 1` by the mutually inverse unit
constants `a = Q(0)` and `b = S(0)` yields `Q₀ = C b * Q` and `S₀ = C a * S` satisfying
`Q₀(0) = 1`, `H = Q₀ * S₀`, `S₀` entire, and `IsCoprime Q₀ S₀` in `IsEntire.subring R`. -/
private theorem normalize_factorisation {R : Type*} [NormedCommRing R]
    {H S : R⟦X⟧} {Q : R[X]} (hH0 : PowerSeries.constantCoeff H = 1)
    (hH : H = (Q : R⟦X⟧) * S) (hS : S.IsEntire)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    let a : R := Q.coeff 0
    let b : R := PowerSeries.constantCoeff S
    let Q₀ : R[X] := C b * Q
    let S₀ : R⟦X⟧ := PowerSeries.C a * S
    a * b = 1 ∧ Q₀.coeff 0 = 1 ∧ Q₀.natDegree = Q.natDegree ∧
      Q₀.leadingCoeff = b * Q.leadingCoeff ∧ Q₀.reverse = C b * Q.reverse ∧
      H = (Q₀ : R⟦X⟧) * S₀ ∧ S₀.IsEntire ∧
      ∀ hS₀ : S₀.IsEntire,
        IsCoprime (⟨Q₀, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q₀)⟩ :
          IsEntire.subring R) ⟨S₀, IsEntire.mem_subring.mpr hS₀⟩ := by
  intro a b Q₀ S₀
  have hab : a * b = 1 := by
    have h := congrArg PowerSeries.constantCoeff hH
    rw [hH0, map_mul, Polynomial.constantCoeff_coe] at h
    exact h.symm
  have hba : b * a = 1 := mul_comm a b ▸ hab
  have hdeg : Q₀.natDegree = Q.natDegree := natDegree_C_mul_eq_of_mul_eq_one hab
  have hS₀ : S₀.IsEntire := by
    have hCa : (PowerSeries.C a : R⟦X⟧) = ((C a : R[X]) : R⟦X⟧) := (Polynomial.coe_C a).symm
    dsimp only [S₀]
    rw [hCa]
    exact (PowerSeries.isEntire_coe (C a)).mul hS
  refine ⟨hab, by simp [Q₀, a, hba], hdeg,
    by rw [leadingCoeff, hdeg, coeff_C_mul, ← leadingCoeff],
    by rw [reverse, reverse, hdeg, reflect_C_mul], ?_, hS₀, fun hS₀' ↦ ?_⟩
  · rw [hH]
    simp only [Q₀, S₀, Polynomial.coe_mul, Polynomial.coe_C]
    calc (Q : R⟦X⟧) * S = PowerSeries.C (b * a) * ((Q : R⟦X⟧) * S) := by rw [hba, map_one, one_mul]
      _ = PowerSeries.C b * (Q : R⟦X⟧) * (PowerSeries.C a * S) := by rw [map_mul]; ring
  · obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy⟩ := hcop
    have hCa : (PowerSeries.C a : R⟦X⟧).IsEntire :=
      Polynomial.coe_C a ▸ PowerSeries.isEntire_coe (C a)
    have hCb : (PowerSeries.C b : R⟦X⟧).IsEntire :=
      Polynomial.coe_C b ▸ PowerSeries.isEntire_coe (C b)
    refine ⟨⟨x * PowerSeries.C a,
        IsEntire.mem_subring.mpr ((IsEntire.mem_subring.mp hx).mul hCa)⟩,
      ⟨y * PowerSeries.C b,
        IsEntire.mem_subring.mpr ((IsEntire.mem_subring.mp hy).mul hCb)⟩, Subtype.ext ?_⟩
    have hval := congrArg Subtype.val hxy
    simp only [OneMemClass.coe_one, Q₀, S₀, Polynomial.coe_mul, Polynomial.coe_C] at hval ⊢
    calc x * PowerSeries.C a * (PowerSeries.C b * (Q : R⟦X⟧)) +
          y * PowerSeries.C b * (PowerSeries.C a * S)
        = x * PowerSeries.C (a * b) * (Q : R⟦X⟧) + y * PowerSeries.C (b * a) * S := by
            rw [map_mul, map_mul]; ring
      _ = x * (Q : R⟦X⟧) + y * S := by rw [hab, hba, map_one, mul_one, mul_one]
      _ = 1 := hval

end Helpers

section Ring

variable {I R : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [NormedCommRing R] [TauCeti.NormedRing.IsTate R] [IsUltrametricDist R] [CompleteSpace R]
  {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]} {S : R⟦X⟧}

/-- Normalised case (`Q(0) = 1`) of
`IsRowCompact.isGoodZero_charPowerSeries_aeval_one_sub_C_mul_reverse`. -/
private theorem isGoodZero_charPowerSeries_aeval_of_coeff_zero_eq_one
    (hu : u.IsRowCompact) {c : R}
    (hH : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S) (hQ0 : Q.coeff 0 = 1)
    (hc : c * Q.leadingCoeff = 1) (hS : S.IsEntire)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (Polynomial.aeval u (1 - C c * Q.reverse)).matrixCoeff.charPowerSeries.IsGoodZero 1
      Q.natDegree := by
  set B : R[X] := 1 - C c * Q.reverse
  have hB0 : B.coeff 0 = 0 := coeff_zero_one_sub_C_mul_reverse hc
  have hS0 : PowerSeries.constantCoeff S = 1 :=
    constantCoeff_eq_one_of_mul (Matrix.constantCoeff_charPowerSeries _) hH hQ0
  have hS0' : PowerSeries.coeff 0 S = 1 := by rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have hE := PowerSeries.colemanDEntire_coe (F := S) hB0 hS0'
  have hBS : (B.colemanDSeries S).IsEntire :=
    hE ▸ PowerSeries.isEntire_colemanDEntire (PowerSeries.isEntire_coe B) hS
      (by rwa [Polynomial.coeff_coe]) hS0'
  have hsign : ((C ((-1 : R) ^ Q.natDegree) : R[X]) : R⟦X⟧).IsEntire :=
    PowerSeries.isEntire_coe _
  have hmul : (Polynomial.aeval u B).matrixCoeff.charPowerSeries =
      (PowerSeries.X - PowerSeries.C 1) ^ Q.natDegree *
        (((C ((-1 : R) ^ Q.natDegree) : R[X]) : R⟦X⟧) * B.colemanDSeries S) := by
    rw [hu.charPowerSeries_matrixCoeff_aeval hB0, hH, colemanDSeries_mul hB0,
      colemanDSeries_one_sub_C_mul_reverse_self hQ0 hc, Polynomial.coe_C, map_pow, map_neg,
      map_one]
    have hpow : (1 - PowerSeries.X : R⟦X⟧) ^ Q.natDegree =
        (PowerSeries.X - PowerSeries.C 1) ^ Q.natDegree * (-1 : R⟦X⟧) ^ Q.natDegree := by
      rw [← mul_pow, map_one]
      ring
    rw [hpow, mul_assoc, map_one]
  rw [hmul, (hsign.mul hBS).isGoodZero_X_sub_C_pow_mul_iff, hsign.evalAt_mul hBS,
    PowerSeries.evalAt_coe, Polynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply]
  exact (isUnit_one.neg.pow Q.natDegree).mul
    ((isUnit_evalAt_one_colemanDSeries_one_sub_C_mul_reverse_iff hc hS hS0).mpr hcop)

/-- **Good zero criterion for Coleman's transform.** If `H_u = Q * S` with `c` inverting `lc(Q)`,
`S` entire, and `Q, S` coprime in `IsEntire.subring R`, then the Fredholm series of `B(u)`
(where `B = 1 - c Q*`) has a good zero of order `deg Q` at `1`. -/
theorem IsRowCompact.isGoodZero_charPowerSeries_aeval_one_sub_C_mul_reverse
    (hu : u.IsRowCompact) {c : R}
    (hH : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hc : c * Q.leadingCoeff = 1) (hS : S.IsEntire)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (Polynomial.aeval u (1 - C c * Q.reverse)).matrixCoeff.charPowerSeries.IsGoodZero 1
      Q.natDegree := by
  obtain ⟨hab, hQ₀0, hdeg, hlc, hrev, hH₀, hS₀, hcop₀⟩ :=
    normalize_factorisation (Matrix.constantCoeff_charPowerSeries _) hH hS hcop
  set a : R := Q.coeff 0
  set b : R := PowerSeries.constantCoeff S
  have hc₀ : (c * a) * (C b * Q).leadingCoeff = 1 := by
    rw [hlc]
    calc (c * a) * (b * Q.leadingCoeff) = c * (a * b) * Q.leadingCoeff := by ring
      _ = 1 := by rw [hab, mul_one, hc]
  have hB : C (c * a) * (C b * Q).reverse = C c * Q.reverse := by
    rw [hrev, ← mul_assoc, ← map_mul, mul_assoc, hab, mul_one]
  simpa only [hdeg, hB] using
    isGoodZero_charPowerSeries_aeval_of_coeff_zero_eq_one hu hH₀ hQ₀0 hc₀ hS₀ (hcop₀ hS₀)

/-- For a row-compact idempotent `E` commuting with `u`, `u * E` has Fredholm series equal to the
reversed characteristic polynomial of the restriction of `u` to the finite projective module
`E.range`. -/
private theorem charPowerSeries_mul_eq_projectiveCharpolyRev (hu : u.IsRowCompact)
    (hE : IsIdempotentElem E) (hEc : E.IsRowCompact) (hcomm : Commute u E) :
    letI : AddCommGroup E.range := inferInstance
    ∃ (_ : Module.Finite R E.range) (_ : Module.Projective R E.range)
      (hmaps : Set.MapsTo u E.range E.range),
      (u * E).matrixCoeff.charPowerSeries =
        ((u.restrict hmaps).toLinearMap.projectiveCharpolyRev : PowerSeries R) := by
  let : AddCommGroup E.range := inferInstance
  have hfin : Module.Finite R E.range := hEc.finite_range_of_isIdempotentElem hE
  have hproj : Module.Projective R E.range := hEc.projective_range_of_isIdempotentElem hE
  have hmaps : Set.MapsTo u E.range E.range := by
    rw [LinearMap.coe_range, coe_coe]
    exact Function.Semiconj.mapsTo_range fun x ↦ congr($(hcomm.eq.symm) x)
  let v : E.range →L[R] E.range := u.restrict hmaps
  have hfix (x : E.range) : E x = x :=
    (LinearMap.IsIdempotentElem.mem_range_iff
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap hE)).mp x.property
  have hri : E.rangeRestrict.comp E.range.subtypeL = .id R E.range :=
    ContinuousLinearMap.ext fun x ↦ Subtype.ext (hfix x)
  have hM : TauCeti.HasPr R E.range :=
    (isPrCompact_iff_isRowCompact.2 hu).hasPr_source.of_retract
      E.range.subtypeL E.rangeRestrict hri
  have hv := isPrCompact_of_finite (R := R) (M := E.range) (L := E.range) hM hM v
  have hext : E.range.subtypeL.comp (v.comp E.rangeRestrict) = u * E := by
    ext x; rfl
  refine ⟨hfin, hproj, hmaps, ?_⟩
  have hchar := charPowerSeries_eq_projectiveCharpolyRev (R := R) (M := E.range) hM v
  rw [← hext, ← hv.charPowerSeries_eq hri, hchar]

/-- For a Riesz projection `E` of `B(u)` at `1` (where `B = 1 - c Q*`), the complementary Fredholm
factor `(u * (1 - E)).matrixCoeff.charPowerSeries` is coprime to `Q` in `IsEntire.subring R`. -/
private theorem isCoprime_complement_of_isRieszProjection (hu : u.IsRowCompact) {c : R}
    (hc : c * Q.leadingCoeff = 1) {h : ℕ}
    (hE : IsRieszProjection (Polynomial.aeval u (1 - C c * Q.reverse)) 1 h E)
    (hcomm : Commute u E) :
    IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨(u * (1 - E)).matrixCoeff.charPowerSeries,
        IsEntire.mem_subring.mpr (hu.comp_clm (1 - E)).isEntire_charPowerSeries⟩ := by
  set B : R[X] := 1 - C c * Q.reverse
  have hB0 : B.coeff 0 = 0 := coeff_zero_one_sub_C_mul_reverse hc
  have h1E : IsIdempotentElem (1 - E) := by
    rw [IsIdempotentElem, mul_sub (α := C₀(I, R) →L[R] C₀(I, R)), mul_one,
      sub_mul (α := C₀(I, R) →L[R] C₀(I, R)), one_mul, hE.isIdempotentElem.eq,
      sub_self, sub_zero (G := C₀(I, R) →L[R] C₀(I, R))]
  have hcomm1 : Commute u (1 - E) := by
    rw [Commute, SemiconjBy, mul_sub (α := C₀(I, R) →L[R] C₀(I, R)), mul_one,
      sub_mul (α := C₀(I, R) →L[R] C₀(I, R)), one_mul, hcomm.eq]
  have hBcomp :
      Polynomial.aeval (u * (1 - E)) B = Polynomial.aeval u B * (1 - E) :=
    aeval_mul_of_isIdempotentElem (R := R) (A := C₀(I, R) →L[R] C₀(I, R)) h1E hcomm1 hB0
  have hu1 : (u * (1 - E)).IsRowCompact := by simpa only [mul_def] using hu.comp_clm (1 - E)
  have hunit : IsUnit ((B.colemanDSeries (u * (1 - E)).matrixCoeff.charPowerSeries).evalAt
      (1 : R)) := by
    rw [← hu1.charPowerSeries_matrixCoeff_aeval hB0, hBcomp]
    exact hE.isUnit_evalAt_charPowerSeries_complement (hu.aeval hB0)
  exact (isUnit_evalAt_one_colemanDSeries_one_sub_C_mul_reverse_iff hc
    (hu.comp_clm (1 - E)).isEntire_charPowerSeries
    (Matrix.constantCoeff_charPowerSeries _)).mp hunit

omit [DiscreteTopology I] [DecidableEq I] [TauCeti.NormedRing.IsTate R] [CompleteSpace R] in
/-- If the restriction `f` of `u` to the finite projective range of `E` has reversed characteristic
polynomial `Q` and rank at most `deg Q` at every prime, sharp Cayley–Hamilton gives
`Q*(u) * E = 0`. -/
private theorem aeval_reverse_mul_eq_zero_of_projectiveCharpolyRev
    (hmaps : Set.MapsTo u E.range E.range) :
    letI : AddCommGroup E.range := inferInstance
    ∀ [Module.Finite R E.range] [Module.Projective R E.range],
      (u.restrict hmaps).toLinearMap.projectiveCharpolyRev = Q →
      (∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) E.range p ≤ Q.natDegree) →
      Polynomial.aeval u Q.reverse * E = 0 := by
  let : AddCommGroup E.range := inferInstance
  intro _ _ hP₁ hrank
  set f : Module.End R E.range := (u.restrict hmaps).toLinearMap
  have hfzero : Polynomial.aeval f Q.reverse = 0 := by
    have hch := f.aeval_reflect_projectiveCharpolyRev_eq_zero hrank
    rwa [hP₁, ← Polynomial.reverse] at hch
  have hsub : u.toLinearMap.comp E.range.subtype = E.range.subtype.comp f := by ext x; rfl
  have hae := Module.End.aeval_comp_of_comp_eq hsub Q.reverse
  ext x : 1
  have hx := congr($(hae) ⟨E x, ⟨x, rfl⟩⟩)
  simpa only [mul_apply_eq_comp, zero_apply, LinearMap.comp_apply, Submodule.coe_subtype,
    ← toLinearMap_aeval, coe_coe, hfzero, LinearMap.zero_apply, ZeroMemClass.coe_zero] using hx

/-- Core bundle proving simultaneously that `E = u.rieszColemanProjection Q` is a Riesz–Coleman
projection, has constant rank `deg Q`, has finite-factor Fredholm series `Q`, and has
complementary Fredholm series `S`. -/
private theorem rieszColemanProjection_spec (hu : u.IsRowCompact)
    (hH : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S) (hQ0 : Q.coeff 0 = 1)
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    let E := u.rieszColemanProjection Q
    IsRieszColemanProjection u Q E ∧
      (∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) E.range p = Q.natDegree) ∧
      (u * E).matrixCoeff.charPowerSeries = (Q : R⟦X⟧) ∧
      (u * (1 - E)).matrixCoeff.charPowerSeries = S := by
  set c : R := Ring.inverse Q.leadingCoeff
  have hc : c * Q.leadingCoeff = 1 := Ring.inverse_mul_cancel _ hQ
  set B : R[X] := 1 - C c * Q.reverse
  have hB0 : B.coeff 0 = 0 := coeff_zero_one_sub_C_mul_reverse hc
  set v : C₀(I, R) →L[R] C₀(I, R) := Polynomial.aeval u B
  have hv : v.IsRowCompact := hu.aeval hB0
  have hHv : v.matrixCoeff.charPowerSeries.IsGoodZero 1 Q.natDegree :=
    hu.isGoodZero_charPowerSeries_aeval_one_sub_C_mul_reverse hH hc hS hcop
  set E : C₀(I, R) →L[R] C₀(I, R) := u.rieszColemanProjection Q
  have hEdef : E = v.rieszProjection 1 Q.natDegree := rieszColemanProjection_def u Q
  have hE : IsRieszProjection v 1 Q.natDegree E :=
    hEdef ▸ hv.isRieszProjection_rieszProjection (fun _ ↦ hHv.evalAt_hasseDeriv_eq_zero)
      hHv.isUnit_evalAt_hasseDeriv
  have huv : Commute u v := by simpa only [aeval_X] using (Commute.all X B).map (aeval u)
  have hcomm : Commute u E := hE.commute_of_commute huv
  have hrank (p : PrimeSpectrum R) : Module.rankAtStalk (R := R) E.range p = Q.natDegree :=
    hE.rankAtStalk_range hv hHv p
  -- Restrict `u` to the finite projective module `E.range` and compare its determinant `P₁` to `Q`.
  let : AddCommGroup E.range := inferInstance
  obtain ⟨_, _, hmaps, hchar⟩ :=
    charPowerSeries_mul_eq_projectiveCharpolyRev hu hE.isIdempotentElem (hE.isRowCompact hv) hcomm
  set f : Module.End R E.range := (u.restrict hmaps).toLinearMap
  set P₁ : R[X] := f.projectiveCharpolyRev
  set S₁ : R⟦X⟧ := (u * (1 - E)).matrixCoeff.charPowerSeries
  have hfac : (Q : R⟦X⟧) * S = (P₁ : R⟦X⟧) * S₁ := by
    rw [← hH, hu.charPowerSeries_matrixCoeff_eq_mul_of_commute hE.isIdempotentElem hcomm, hchar]
  -- Coprimality of `Q` and `S₁` in `IsEntire.subring R` gives `Q ∣ P₁`, hence `P₁ = Q`.
  have hcop₁ := isCoprime_complement_of_isRieszProjection hu hc hE hcomm
  obtain ⟨⟨G, hG⟩, hPG⟩ :
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R) ∣
        ⟨P₁, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe P₁)⟩ :=
    hcop₁.dvd_of_dvd_mul_right ⟨⟨S, IsEntire.mem_subring.mpr hS⟩, Subtype.ext hfac.symm⟩
  have hP₁ : P₁ = Q :=
    eq_of_coe_dvd_of_natDegree_le f.coeff_projectiveCharpolyRev_zero hQ0 hc
      (f.natDegree_projectiveCharpolyRev_le (fun p ↦ (hrank p).le))
      (IsEntire.mem_subring.mp hG) (congrArg Subtype.val hPG)
  have hS₁eq : S₁ = S := by
    have hQunit : IsUnit (Q : R⟦X⟧) := PowerSeries.isUnit_iff_constantCoeff.mpr
      (by rw [Polynomial.constantCoeff_coe, hQ0]; exact isUnit_one)
    rw [hP₁] at hfac
    exact hQunit.mul_left_cancel hfac.symm
  have hzero := aeval_reverse_mul_eq_zero_of_projectiveCharpolyRev hmaps hP₁
    (fun p ↦ (hrank p).le)
  exact ⟨IsRieszColemanProjection.of_isRieszProjection hE hzero, hrank, hP₁ ▸ hchar, hS₁eq⟩

/-- Unnormalised version of `rieszColemanProjection_spec`: drops `Q(0) = 1` by scaling `Q` by the
unit `S(0)` (the inverse of `Q(0)`). -/
private theorem rieszColemanProjection_spec_of_mul (hu : u.IsRowCompact)
    (hH : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    let E := u.rieszColemanProjection Q
    IsRieszColemanProjection u Q E ∧
      (∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) E.range p = Q.natDegree) := by
  obtain ⟨hab, hQ₀0, hdeg, hlc, -, hH₀, hS₀, hcop₀⟩ :=
    normalize_factorisation (Matrix.constantCoeff_charPowerSeries _) hH hS hcop
  set b : R := PowerSeries.constantCoeff S
  have hb : IsUnit b := IsUnit.of_mul_eq_one_right (Q.coeff 0) hab
  have hQ₀ : IsUnit (C b * Q).leadingCoeff := by
    rw [hlc]
    exact hb.mul hQ
  obtain ⟨hE₀, hrank₀, -, -⟩ := rieszColemanProjection_spec hu hH₀ hQ₀0 hQ₀ hS₀ (hcop₀ hS₀)
  have hEeq : u.rieszColemanProjection (C b * Q) = u.rieszColemanProjection Q :=
    u.rieszColemanProjection_C_mul hb Q
  rw [hEeq] at hE₀ hrank₀
  exact ⟨(IsRieszColemanProjection.C_mul_iff hb).mp hE₀, fun p ↦ by rw [hrank₀ p, hdeg]⟩

/-- **Existence and explicit formula for the Riesz–Coleman projection.** Let `u` be a row-compact
endomorphism of `C₀(I, R)` whose Fredholm series admits a coprime factorisation `H_u = Q * S`,
where `Q` is a polynomial with invertible leading coefficient and `S` is entire. Then
`u.rieszColemanProjection Q` is a Riesz–Coleman projection of `u` at `Q`. -/
theorem IsRowCompact.isRieszColemanProjection_rieszColemanProjection (hu : u.IsRowCompact)
    (hH : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    IsRieszColemanProjection u Q (u.rieszColemanProjection Q) :=
  (rieszColemanProjection_spec_of_mul hu hH hQ hS hcop).1

/-- **Existence of a Riesz–Coleman projection** on a model space `C₀(I, R)` for any coprime
polynomial factor `Q` of `H_u` with invertible leading coefficient. -/
theorem IsRowCompact.exists_rieszColemanProjection (hu : u.IsRowCompact)
    (hH : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    ∃ E, IsRieszColemanProjection u Q E :=
  ⟨u.rieszColemanProjection Q, hu.isRieszColemanProjection_rieszColemanProjection hH hQ hS hcop⟩

/-- Every Riesz–Coleman projection equals the explicit projector `u.rieszColemanProjection Q`. -/
theorem IsRieszColemanProjection.eq_rieszColemanProjection (hE : IsRieszColemanProjection u Q E)
    (hu : u.IsRowCompact) (hH : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    E = u.rieszColemanProjection Q :=
  hE.unique (hu.isRieszColemanProjection_rieszColemanProjection hH hQ hS hcop)

/-- **Constant rank of the finite summand.** The range of a Riesz–Coleman projection for a coprime
factor `Q` of `H_u` has constant rank `deg Q` at every prime ideal of `R`. -/
theorem IsRieszColemanProjection.rankAtStalk_range (hE : IsRieszColemanProjection u Q E)
    (hu : u.IsRowCompact) (hH : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) E.range p = Q.natDegree := by
  rw [hE.eq_rieszColemanProjection hu hH hQ hS hcop]
  exact (rieszColemanProjection_spec_of_mul hu hH hQ hS hcop).2 p

/-- On a model space `C₀(I, R)`, `ker Q*(u)` has constant rank `deg Q` at every prime ideal of
`R`. -/
theorem IsRowCompact.rankAtStalk_ker_aeval_reverse (hu : u.IsRowCompact)
    (hH : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R)
      (LinearMap.ker ((Polynomial.aeval u Q.reverse : C₀(I, R) →L[R] C₀(I, R)) :
        C₀(I, R) →ₗ[R] C₀(I, R))) p = Q.natDegree := by
  have hE := hu.isRieszColemanProjection_rieszColemanProjection hH hQ hS hcop
  rw [← hE.range_eq_ker]
  exact hE.rankAtStalk_range hu hH hQ hS hcop p

/-- **Determinant on the finite summand.** The Fredholm series of `u * E` is `Q` when `Q` is
normalised by `Q(0) = 1`. -/
theorem IsRieszColemanProjection.charPowerSeries_matrixCoeff_mul_eq
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact)
    (hH : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S) (hQ0 : Q.coeff 0 = 1)
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (u * E).matrixCoeff.charPowerSeries = (Q : R⟦X⟧) := by
  rw [hE.eq_rieszColemanProjection hu hH hQ hS hcop]
  exact (rieszColemanProjection_spec hu hH hQ0 hQ hS hcop).2.2.1

/-- **Determinant on the complementary summand.** The Fredholm series of `u * (1 - E)` is `S` when
`Q` is normalised by `Q(0) = 1`. -/
theorem IsRieszColemanProjection.charPowerSeries_matrixCoeff_mul_one_sub_eq
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact)
    (hH : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S) (hQ0 : Q.coeff 0 = 1)
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring R) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (u * (1 - E)).matrixCoeff.charPowerSeries = S := by
  rw [hE.eq_rieszColemanProjection hu hH hQ hS hcop]
  exact (rieszColemanProjection_spec hu hH hQ0 hQ hS hcop).2.2.2

end Ring

section Field

variable {I K : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {u E : C₀(I, K) →L[K] C₀(I, K)} {Q : K[X]} {S : K⟦X⟧}

/-- Over a complete ultrametric field, the range of a Riesz–Coleman projection has dimension
`deg Q`. -/
theorem IsRieszColemanProjection.finrank_range (hE : IsRieszColemanProjection u Q E)
    (hu : u.IsRowCompact) (hH : u.matrixCoeff.charPowerSeries = (Q : K⟦X⟧) * S)
    (hS : S.IsEntire)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring K) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    Module.finrank K E.range = Q.natDegree := by
  have hQne : Q ≠ 0 := fun h ↦ by
    have hc := congrArg PowerSeries.constantCoeff hH
    simp [h] at hc
  have hQ : IsUnit Q.leadingCoeff :=
    isUnit_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hQne)
  have hr := hE.rankAtStalk_range hu hH hQ hS hcop ⟨⊥, Ideal.isPrime_bot⟩
  let : AddCommGroup E.range := inferInstance
  rw [Module.rankAtStalk_eq_finrank_of_free] at hr
  exact hr

/-- Over a complete ultrametric field, `ker Q*(u)` has dimension `deg Q`. -/
theorem IsRowCompact.finrank_ker_aeval_reverse (hu : u.IsRowCompact)
    (hH : u.matrixCoeff.charPowerSeries = (Q : K⟦X⟧) * S) (hS : S.IsEntire)
    (hcop : IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
      IsEntire.subring K) ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    Module.finrank K (LinearMap.ker ((Polynomial.aeval u Q.reverse : C₀(I, K) →L[K] C₀(I, K)) :
      Module.End K C₀(I, K))) = Q.natDegree := by
  have hQne : Q ≠ 0 := fun h ↦ by
    have hc := congrArg PowerSeries.constantCoeff hH
    simp [h] at hc
  have hQ : IsUnit Q.leadingCoeff :=
    isUnit_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hQne)
  have hE := hu.isRieszColemanProjection_rieszColemanProjection hH hQ hS hcop
  rw [← hE.range_eq_ker]
  exact hE.finrank_range hu hH hS hcop

end Field

end ContinuousLinearMap
