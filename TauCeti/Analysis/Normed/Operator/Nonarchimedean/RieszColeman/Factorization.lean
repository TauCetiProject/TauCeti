/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszColeman.Basic
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszProjection.Multiplicity
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.PrModule.Coprime
import Mathlib.Algebra.Polynomial.Div
import TauCeti.Analysis.Normed.Operator.Nonarchimedean.Coleman
import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszProjection.Intertwining
import TauCeti.Analysis.Polynomial.Coleman.Coprime
import TauCeti.RingTheory.Idempotents.Polynomial
import TauCeti.RingTheory.Polynomial.Resultant.Coleman
import TauCeti.RingTheory.PowerSeries.Entire.Division
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.IdempotentRange
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Intertwining

/-!
# Riesz–Coleman decomposition on model spaces from coprime Fredholm factors

Let `R` be a complete ultrametric normed commutative ring with Tate scalars and `u` a row-compact
endomorphism of `C₀(I, R)` whose Fredholm series `H_u = u.matrixCoeff.charPowerSeries` factors as
`H_u = Q * S`, where `Q : R[X]` satisfies `IsUnit Q.leadingCoeff`, `S` is entire, and `Q`, `S` are
coprime in `IsEntire.subring R`.

For `c = Ring.inverse Q.leadingCoeff`, `B = 1 - c Q*` (`Q* = Q.reverse`), and `d = Q.natDegree`,
`v = B(u)` is row compact with a good Fredholm zero at `1` of order `d` by Coleman's resultant
theorem (`ContinuousLinearMap.IsRowCompact.isGoodZero_charPowerSeries_aeval_one_sub_C_mul_reverse`),
and `E := u.rieszColemanProjection Q := v.rieszProjection 1 d` is the unique Riesz–Coleman
projection of `u` for `Q`. Coprimality of `Q` with the complementary Fredholm factor identifies the
reversed characteristic polynomial of `u|_{range E}` with the normalized factor
`Q₁ = (Q.coeff 0)⁻¹ • Q`, and Cayley–Hamilton with invertibility of `u|_{range E}` yields
`Q*(u) * E = 0`. No normalization `Q.coeff 0 = 1` is needed except for the literal determinant
identities `det (1 - X u|_{range E}) = Q`, `H_{u E} = Q`, and `H_{u (1 - E)} = S`.

## Main definitions

* `ContinuousLinearMap.rieszColemanProjection`: `(B(u)).rieszProjection 1 Q.natDegree` for
  `B = 1 - c Q*`.

## Main results

* `ContinuousLinearMap.IsRowCompact.isGoodZero_charPowerSeries_aeval_one_sub_C_mul_reverse`,
  `ContinuousLinearMap.IsRowCompact.isRieszColemanProjection_rieszColemanProjection`,
  `ContinuousLinearMap.IsRowCompact.exists_rieszColemanProjection`,
  `ContinuousLinearMap.IsRieszColemanProjection.eq_rieszColemanProjection`: good zero of `B(u)`,
  existence, and explicit formula for the Riesz–Coleman projection.
* `ContinuousLinearMap.IsRieszColemanProjection.isCoprime_charPowerSeries_complement`,
  `ContinuousLinearMap.IsRieszColemanProjection.isCoprime_charPowerSeries_matrixCoeff_complement`:
  `Q` is coprime to the complementary Fredholm series on `(Pr)` modules and model spaces.
* `ContinuousLinearMap.IsRieszColemanProjection.rankAtStalk_range`,
  `ContinuousLinearMap.IsRowCompact.rankAtStalk_ker_aeval_reverse`,
  `ContinuousLinearMap.IsRieszColemanProjection.finrank_range`,
  `ContinuousLinearMap.IsRowCompact.finrank_ker_aeval_reverse`: constant stalk rank and
  field dimension `Q.natDegree`.
* `ContinuousLinearMap.IsRieszColemanProjection.projectiveCharpolyRev_restrict_range`,
  `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_matrixCoeff_mul_eq`,
  `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_matrixCoeff_mul_one_sub_eq`:
  summand determinant identities when `Q.coeff 0 = 1`.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127** (1997),
  417–479, Appendix A4, Theorem A4.2.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*, Algebra
  Number Theory **13** (2019), 93–158, §2.2, Theorem 2.2.2.
-/

public section

open Polynomial
open PowerSeries (IsEntire)
open scoped ZeroAtInfty TauCeti.RingOpNorm PowerSeries

namespace ContinuousLinearMap

section ExplicitProjector

variable {I R : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [NormedCommRing R] [TauCeti.NormedRing.IsTate R]

/-- The **Riesz–Coleman projector** of `u` on `C₀(I, R)` for `Q : R[X]`: the Riesz projector at `1`
of order `Q.natDegree` of `(1 - c Q*)(u)` (`c = Ring.inverse Q.leadingCoeff`, `Q* = Q.reverse`),
and a junk value outside coprime Fredholm factorizations with `IsUnit Q.leadingCoeff`. -/
noncomputable def rieszColemanProjection (u : C₀(I, R) →L[R] C₀(I, R)) (Q : R[X]) :
    C₀(I, R) →L[R] C₀(I, R) :=
  (Polynomial.aeval u (1 - C (Ring.inverse Q.leadingCoeff) * Q.reverse)).rieszProjection 1
    Q.natDegree

/-- Unfolding lemma for `ContinuousLinearMap.rieszColemanProjection`. -/
theorem rieszColemanProjection_def (u : C₀(I, R) →L[R] C₀(I, R)) (Q : R[X]) :
    u.rieszColemanProjection Q =
      (Polynomial.aeval u (1 - C (Ring.inverse Q.leadingCoeff) * Q.reverse)).rieszProjection 1
        Q.natDegree := (rfl)

/-- For `Q = 0`, `deg Q = 0`, so the Riesz–Coleman projector is zero. -/
@[simp] theorem rieszColemanProjection_zero (u : C₀(I, R) →L[R] C₀(I, R)) :
    u.rieszColemanProjection 0 = 0 := by
  rw [rieszColemanProjection_def, natDegree_zero, rieszProjection_order_zero]

/-- For `Q = 1`, `deg Q = 0`, so the Riesz–Coleman projector is zero. -/
@[simp] theorem rieszColemanProjection_one (u : C₀(I, R) →L[R] C₀(I, R)) :
    u.rieszColemanProjection 1 = 0 := by
  rw [rieszColemanProjection_def, natDegree_one, rieszProjection_order_zero]

/-- The Riesz–Coleman projector is invariant under scaling `Q` by any unit of `R`. -/
@[simp] theorem rieszColemanProjection_units_smul (u : C₀(I, R) →L[R] C₀(I, R)) (Q : R[X])
    (c : Rˣ) : u.rieszColemanProjection (c • Q) = u.rieszColemanProjection Q := by
  rw [rieszColemanProjection_def, rieszColemanProjection_def,
    natDegree_smul_of_smul_regular Q (IsSMulRegular.all c),
    one_sub_C_inverse_mul_reverse_units_smul]

end ExplicitProjector

section Ring

variable {I R : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [NormedCommRing R] [TauCeti.NormedRing.IsTate R] [IsUltrametricDist R] [CompleteSpace R]

omit [TauCeti.NormedRing.IsTate R] [IsUltrametricDist R] [CompleteSpace R] in
/-- Normalize `F = Q * S` with `F(0) = 1` by `Q(0)⁻¹` so `(u₀ • Q).coeff 0 = 1`. -/
private theorem exists_unit_smul_coeff_zero_eq_one {F S : R⟦X⟧} {Q : R[X]}
    (hF0 : PowerSeries.constantCoeff F = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : F = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    ∃ (u₀ : Rˣ) (S₁ : R⟦X⟧) (hS₁ : S₁.IsEntire),
      (u₀ • Q).coeff 0 = 1 ∧ IsUnit (u₀ • Q).leadingCoeff ∧
      F = ((u₀ • Q : R[X]) : R⟦X⟧) * S₁ ∧
      IsCoprime
        (⟨(u₀ • Q : R[X]), IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe _)⟩ :
          IsEntire.subring R)
        ⟨S₁, IsEntire.mem_subring.mpr hS₁⟩ := by
  have h1 : Q.coeff 0 * PowerSeries.constantCoeff S = 1 := by
    simpa [hF0] using (congrArg (PowerSeries.constantCoeff (R := R)) hfac).symm
  let c₀ : Rˣ := Units.mkOfMulEqOne (Q.coeff 0) (PowerSeries.constantCoeff S) h1
  let u₀ : Rˣ := c₀⁻¹
  set S₁ : R⟦X⟧ := PowerSeries.C (c₀ : R) * S with hS₁_def
  have hS₁ : S₁.IsEntire := (PowerSeries.isEntire_C (c₀ : R)).mul hS
  have hu₀Q0 : (u₀ • Q).coeff 0 = 1 := c₀.inv_mul
  have hu₀Q_lc : IsUnit (u₀ • Q).leadingCoeff := by
    rw [leadingCoeff, natDegree_smul_of_smul_regular Q (IsSMulRegular.all u₀),
      Units.smul_def, smul_eq_C_mul, coeff_C_mul, ← leadingCoeff]
    exact u₀.isUnit.mul hQ
  have hfac₁ : F = ((u₀ • Q : R[X]) : R⟦X⟧) * S₁ := by
    rw [hfac, Units.smul_def, smul_eq_C_mul, Polynomial.coe_mul, Polynomial.coe_C, hS₁_def,
      mul_assoc, ← mul_assoc (PowerSeries.C (u₀ : R)) (Q : R⟦X⟧),
      mul_comm (PowerSeries.C (u₀ : R)), mul_assoc, ← mul_assoc (PowerSeries.C (u₀ : R)),
      ← map_mul, c₀.inv_mul, map_one, one_mul]
  let uC : (IsEntire.subring R)ˣ :=
    ⟨⟨PowerSeries.C (u₀ : R), IsEntire.mem_subring.mpr (PowerSeries.isEntire_C (u₀ : R))⟩,
     ⟨PowerSeries.C (c₀ : R), IsEntire.mem_subring.mpr (PowerSeries.isEntire_C (c₀ : R))⟩,
     Subtype.ext (by simp [u₀, ← map_mul]),
     Subtype.ext (by simp [u₀, ← map_mul])⟩
  refine ⟨u₀, S₁, hS₁, hu₀Q0, hu₀Q_lc, hfac₁, ?_⟩
  convert (isCoprime_mul_unit_left_left uC.isUnit _ _).mpr
    ((isCoprime_mul_unit_left_right uC⁻¹.isUnit _ _).mpr hcop) using 1
  exact Subtype.ext (by simp [uC, Units.smul_def, smul_eq_C_mul])

/-- If `E` commutes with `u` on a `(Pr)` module and `Q*(u)` is invertible modulo `E`, `Q` is
coprime to the complementary Fredholm series `(u * (1 - E)).charPowerSeries`. -/
private theorem isCoprime_complement_of_exists_inverse
    {M : Type*} [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
    {u E : M →L[R] M} {Q : R[X]} (hu : u.IsPrCompact)
    (hQ : IsUnit Q.leadingCoeff) (hIdem : IsIdempotentElem E) (huE : Commute u E)
    (hinv : ∃ w : M →L[R] M,
      Polynomial.aeval u Q.reverse * w = 1 - E ∧ w * Polynomial.aeval u Q.reverse = 1 - E) :
    IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨(u * (1 - E)).charPowerSeries,
        IsEntire.mem_subring.mpr
          (hu.comp_clm (1 - E) hu.hasPr_source).isEntire_charPowerSeries⟩ := by
  obtain ⟨w, hw₁, hw₂⟩ := hinv
  set c := Ring.inverse Q.leadingCoeff
  have hc : c * Q.leadingCoeff = 1 := Ring.inverse_mul_cancel _ hQ
  set B := 1 - C c * Q.reverse
  have h1B : 1 - Polynomial.aeval u B = c • Polynomial.aeval u Q.reverse := by
    simp [B, Algebra.algebraMap_eq_smul_one]
  have hw₁' : (1 - Polynomial.aeval u B) * (Q.leadingCoeff • w) = 1 - E := by
    rw [h1B, smul_mul_smul_comm, hc, one_smul, hw₁]
  have hw₂' : (Q.leadingCoeff • w) * (1 - Polynomial.aeval u B) = 1 - E := by
    rw [h1B, smul_mul_smul_comm, mul_comm Q.leadingCoeff c, hc, one_smul, hw₂]
  have hunit_block : IsUnit (E + (1 - Polynomial.aeval u B) * (1 - E)) := by
    convert _root_.IsIdempotentElem.isUnit_add_mul_one_sub (A := M →L[R] M) hIdem hw₁' hw₂'
  have hblock_eq : E + (1 - Polynomial.aeval u B) * (1 - E) =
      (IsUnit.of_mul_eq_one _ hc).unit • Polynomial.aeval (u * (1 - E)) Q.reverse := by
    have h1B_comp : 1 - Polynomial.aeval (u * (1 - E)) B =
        (IsUnit.of_mul_eq_one _ hc).unit • Polynomial.aeval (u * (1 - E)) Q.reverse := by
      simp [B, Units.smul_def, Algebra.algebraMap_eq_smul_one]
    rw [← h1B_comp,
      hIdem.aeval_mul_one_sub_of_coeff_zero huE (coeff_zero_one_sub_C_mul_reverse hc),
      sub_mul (α := M →L[R] M), one_mul]
    abel
  rw [hblock_eq, isUnit_smul_iff] at hunit_block
  exact ((hu.comp_clm (1 - E) hu.hasPr_source).isUnit_aeval_reverse_iff hQ).mp hunit_block

/-- **Coprimality on the complementary summand.** For any Riesz–Coleman projection `E` of a
row-compact operator `u` on a `(Pr)` module for `Q` with `IsUnit Q.leadingCoeff`, `Q` is coprime to
`(u * (1 - E)).charPowerSeries`. -/
theorem IsRieszColemanProjection.isCoprime_charPowerSeries_complement
    {M : Type*} [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
    {u E : M →L[R] M} {Q : R[X]} (hE : IsRieszColemanProjection u Q E)
    (hQ : IsUnit Q.leadingCoeff) (hu : u.IsPrCompact) :
    IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨(u * (1 - E)).charPowerSeries,
        IsEntire.mem_subring.mpr
          (hu.comp_clm (1 - E) hu.hasPr_source).isEntire_charPowerSeries⟩ :=
  isCoprime_complement_of_exists_inverse hu hQ hE.isIdempotentElem hE.commute
    ⟨hE.inverse, hE.aeval_reverse_mul_inverse, hE.inverse_mul_aeval_reverse⟩

variable {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]} {S : R⟦X⟧}

/-- **Coprimality on the complementary model-space summand.** For any Riesz–Coleman projection `E`
of `u` on `C₀(I, R)` for `Q` with `IsUnit Q.leadingCoeff`, `Q` is coprime to
`(u * (1 - E)).matrixCoeff.charPowerSeries`. -/
theorem IsRieszColemanProjection.isCoprime_charPowerSeries_matrixCoeff_complement
    (hE : IsRieszColemanProjection u Q E) (hQ : IsUnit Q.leadingCoeff) (hu : u.IsRowCompact) :
    IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨(u * (1 - E)).matrixCoeff.charPowerSeries,
        IsEntire.mem_subring.mpr (hu.comp_clm (1 - E)).isEntire_charPowerSeries⟩ := by
  convert hE.isCoprime_charPowerSeries_complement hQ (isPrCompact_iff_isRowCompact.2 hu) using 1
  exact Subtype.ext (hu.comp_clm (1 - E)).charPowerSeries_eq_charPowerSeries_matrixCoeff.symm

/-- **Good zero after Coleman's polynomial transform.** Under a coprime factorization `H_u = Q * S`
with `IsUnit Q.leadingCoeff`, `(1 - c Q*)(u)` has a good Fredholm zero at `1` of order
`Q.natDegree`. -/
theorem IsRowCompact.isGoodZero_charPowerSeries_aeval_one_sub_C_mul_reverse
    (hu : u.IsRowCompact) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (Polynomial.aeval u (1 - C (Ring.inverse Q.leadingCoeff) * Q.reverse))
      |>.matrixCoeff.charPowerSeries.IsGoodZero 1 Q.natDegree := by
  obtain ⟨u₀, S₁, hS₁, hQ₁0, hQ₁, hfac₁, hcop₁⟩ :=
    exists_unit_smul_coeff_zero_eq_one u.matrixCoeff.constantCoeff_charPowerSeries hQ hS hfac hcop
  rw [← natDegree_smul_of_smul_regular Q (IsSMulRegular.all u₀),
    ← one_sub_C_inverse_mul_reverse_units_smul Q u₀]
  set Q₁ := u₀ • Q
  have hc₁ : Ring.inverse Q₁.leadingCoeff * Q₁.leadingCoeff = 1 := Ring.inverse_mul_cancel _ hQ₁
  set B := 1 - C (Ring.inverse Q₁.leadingCoeff) * Q₁.reverse
  have hB0 : B.coeff 0 = 0 := coeff_zero_one_sub_C_mul_reverse hc₁
  have hS₁0 : PowerSeries.constantCoeff S₁ = 1 := by
    simpa [u.matrixCoeff.constantCoeff_charPowerSeries, hQ₁0] using
      (congrArg (PowerSeries.constantCoeff (R := R)) hfac₁).symm
  have hDe : (B.colemanDSeries S₁).IsEntire := by
    rw [← PowerSeries.colemanDEntire_coe hB0
      (by rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply])]
    exact PowerSeries.isEntire_colemanDEntire (PowerSeries.isEntire_coe B) hS₁
      (by rwa [Polynomial.coeff_coe]) (by rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply])
  have hDunit : IsUnit ((B.colemanDSeries S₁).evalAt (1 : R)) :=
    (isUnit_evalAt_one_colemanDSeries_one_sub_C_mul_reverse_iff hc₁ hS₁ hS₁0).mpr hcop₁
  set G : R⟦X⟧ := PowerSeries.C ((-1 : R) ^ Q₁.natDegree) * B.colemanDSeries S₁ with hG_def
  have hGe : G.IsEntire := (PowerSeries.isEntire_C ((-1 : R) ^ Q₁.natDegree)).mul hDe
  have hchar : (Polynomial.aeval u B).matrixCoeff.charPowerSeries =
      (PowerSeries.X - PowerSeries.C 1) ^ Q₁.natDegree * G := by
    rw [hu.charPowerSeries_matrixCoeff_aeval hB0, hfac₁, colemanDSeries_mul hB0,
      colemanDSeries_one_sub_C_mul_reverse_self hQ₁0 hc₁]
    have h1X : (1 - PowerSeries.X : R⟦X⟧) = PowerSeries.C (-1 : R) * (PowerSeries.X - 1) := by
      ext n; cases n <;> simp [sub_eq_add_neg, add_comm]
    rw [h1X, map_one, mul_pow, ← map_pow, hG_def]; ring
  rw [hchar, hGe.isGoodZero_X_sub_C_pow_mul_iff]
  have heval :
      G.evalAt (1 : R) = (-1 : R) ^ Q₁.natDegree * (B.colemanDSeries S₁).evalAt (1 : R) := by
    rw [hG_def, (PowerSeries.isEntire_C ((-1 : R) ^ Q₁.natDegree)).evalAt_mul hDe,
      ← Polynomial.coe_C, PowerSeries.evalAt_coe]
    simp
  rw [heval]
  exact (isUnit_neg_one.pow Q₁.natDegree).mul hDunit

/-- Shared determinant computation on a row-compact commuting idempotent `E` with stalk rank
`≤ deg Q` and complement coprime to `Q`. -/
private theorem projectiveCharpolyRev_and_charPowerSeries_of_rankAtStalk_le
    (hu : u.IsRowCompact) (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S) (hIdem : IsIdempotentElem E)
    (huE : Commute u E) (hrc : E.IsRowCompact) (hm : Set.MapsTo u E.range E.range)
    (hrank : ∀ p, Module.rankAtStalk (R := R) E.range p ≤ Q.natDegree)
    (hcop_comp : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨(u * (1 - E)).matrixCoeff.charPowerSeries,
        IsEntire.mem_subring.mpr (hu.comp_clm (1 - E)).isEntire_charPowerSeries⟩) :
    letI : AddCommGroup E.range := inferInstance
    letI := hrc.finite_range_of_isIdempotentElem hIdem
    letI := hrc.projective_range_of_isIdempotentElem hIdem
    ((u.restrict hm : E.range →L[R] E.range) : Module.End R E.range).projectiveCharpolyRev = Q ∧
      (u * E).matrixCoeff.charPowerSeries = (Q : R⟦X⟧) ∧
      (u * (1 - E)).matrixCoeff.charPowerSeries = S := by
  let : AddCommGroup E.range := inferInstance
  have := hrc.finite_range_of_isIdempotentElem hIdem
  have := hrc.projective_range_of_isIdempotentElem hIdem
  let v_u : E.range →L[R] E.range := u.restrict hm
  let f : Module.End R E.range := v_u.toLinearMap
  have hri : E.rangeRestrict.comp E.range.subtypeL = .id R E.range :=
    IsIdempotentElem.rangeRestrict_comp_subtypeL hIdem
  have hM : TauCeti.HasPr R E.range :=
    (isPrCompact_iff_isRowCompact.2 hu).hasPr_source.range_of_isIdempotentElem hIdem
  have hv_pr := isPrCompact_of_finite (R := R) (M := E.range) (L := E.range) hM hM v_u
  have hext : E.range.subtypeL.comp (v_u.comp E.rangeRestrict) = u * E := by ext x; rfl
  have hchar : (u * E).matrixCoeff.charPowerSeries = (f.projectiveCharpolyRev : R⟦X⟧) := by
    rw [← hext, ← hv_pr.charPowerSeries_eq hri,
      charPowerSeries_eq_projectiveCharpolyRev (R := R) (M := E.range) hM v_u]
  have hsplit := hu.charPowerSeries_matrixCoeff_eq_mul_of_commute hIdem huE
  rw [hfac, hchar] at hsplit
  have hdvd : IsEntire.polynomialHom Q ∣ IsEntire.polynomialHom f.projectiveCharpolyRev := by
    have hpol (P : R[X]) : IsEntire.polynomialHom P =
        ⟨P, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe P)⟩ :=
      Subtype.ext (IsEntire.coe_polynomialHom P)
    rw [hpol, hpol]
    exact hcop_comp.dvd_of_dvd_mul_right ⟨⟨S, IsEntire.mem_subring.mpr hS⟩, Subtype.ext hsplit.symm⟩
  have hf_eq : f.projectiveCharpolyRev = Q :=
    TauCeti.PowerSeries.eq_of_polynomialHom_dvd_of_natDegree_le hQ0 hQ
      f.coeff_projectiveCharpolyRev_zero (f.natDegree_projectiveCharpolyRev_le hrank) hdvd
  refine ⟨hf_eq, hf_eq ▸ hchar, ?_⟩
  rw [hf_eq] at hsplit
  exact (PowerSeries.isUnit_iff_constantCoeff.mpr (by simp [hQ0])).mul_left_cancel hsplit.symm

/-- Cayley–Hamilton annihilation `Q*(u) * E = 0` from `projectiveCharpolyRev = Q` on `E.range`. -/
private theorem aeval_reverse_mul_eq_zero_of_projectiveCharpolyRev_eq {B : R[X]}
    (hB0 : B.coeff 0 = 0) (hEv : IsRieszProjection (Polynomial.aeval u B) 1 Q.natDegree E)
    (hrc : E.IsRowCompact) (hm : Set.MapsTo u E.range E.range)
    (hf_char :
      letI : AddCommGroup E.range := inferInstance
      letI := hrc.finite_range_of_isIdempotentElem hEv.isIdempotentElem
      letI := hrc.projective_range_of_isIdempotentElem hEv.isIdempotentElem
      ((u.restrict hm : E.range →L[R] E.range) : Module.End R E.range).projectiveCharpolyRev = Q) :
    Polynomial.aeval u Q.reverse * E = 0 := by
  let : AddCommGroup E.range := inferInstance
  have := hrc.finite_range_of_isIdempotentElem hEv.isIdempotentElem
  have := hrc.projective_range_of_isIdempotentElem hEv.isIdempotentElem
  let f : Module.End R E.range := (u.restrict hm).toLinearMap
  have hf_sub : Function.Semiconj E.range.subtype (u.restrict hm) u := fun _ ↦ rfl
  have hf_aeval (P : R[X]) (x : E.range) :
      ((Polynomial.aeval f P) x : C₀(I, R)) = Polynomial.aeval u P x := by
    simpa only [f, ← toLinearMap_aeval, coe_coe, Submodule.subtype_apply] using hf_sub.aeval P x
  have hf_unit : IsUnit f := by
    set A : R[X] := 1 - (1 - B) ^ Q.natDegree with hA_def
    have hA0 : A.coeff 0 = 0 := by
      rw [coeff_zero_eq_eval_zero] at hB0 ⊢; simp [hA_def, hB0]
    have hAE (x : E.range) : Polynomial.aeval u A x = x := by
      have hfix : E x = x := IsIdempotentElem.apply_coe_range hEv.isIdempotentElem x
      have hz := congr($(hEv.pow_mul_eq_zero) (x : C₀(I, R)))
      simp only [one_smul, mul_apply_eq_comp, hfix, zero_apply] at hz
      simp [hA_def, hz]
    have hfg : f * Polynomial.aeval f A.divX = 1 := by
      ext x : 1; apply Subtype.ext
      have hXA : f * Polynomial.aeval f A.divX = Polynomial.aeval f A := by
        conv_rhs => rw [← show X * A.divX = A by simpa [hA0] using X_mul_divX_add A]
        rw [map_mul, aeval_X]
      simpa only [hXA, Module.End.one_eq_id, LinearMap.id_apply, hf_aeval] using hAE x
    have hcomm : Commute f (Polynomial.aeval f A.divX) := by
      simpa only [aeval_X] using (Commute.all X A.divX).map (Polynomial.aeval f)
    exact isUnit_iff_exists.mpr ⟨Polynomial.aeval f A.divX, hfg, hcomm.symm.eq.trans hfg⟩
  obtain ⟨n, hn, hCH⟩ := f.exists_aeval_reflect_projectiveCharpolyRev_eq_zero
  rw [hf_char] at hn hCH
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have href : Q.reflect (Q.natDegree + k) = Q.reverse * X ^ k := by
    calc Q.reflect (Q.natDegree + k) = (Q * 1).reflect (Q.natDegree + k) := by rw [mul_one]
      _ = Q.reflect Q.natDegree * (1 : R[X]).reflect k := reflect_mul Q 1 le_rfl (by simp)
      _ = Q.reverse * X ^ k := by rw [← reverse, ← C_1, reflect_C, C_1, one_mul]
  rw [href, map_mul, map_pow, aeval_X] at hCH
  have hfQ : Polynomial.aeval f Q.reverse = 0 := (hf_unit.pow k).mul_left_eq_zero.mp hCH
  ext y; simp [← hf_aeval Q.reverse ⟨E y, ⟨y, rfl⟩⟩, hfQ]

/-- Normalized core: when `Q.coeff 0 = 1`, `u.rieszColemanProjection Q` is a Riesz–Coleman
projection of `u` for `Q`. -/
private theorem isRieszColemanProjection_rieszColemanProjection_of_coeff_zero
    (hu : u.IsRowCompact) (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    IsRieszColemanProjection u Q (u.rieszColemanProjection Q) := by
  set c := Ring.inverse Q.leadingCoeff
  set B := 1 - C c * Q.reverse
  have hB0 : B.coeff 0 = 0 := coeff_zero_one_sub_C_mul_reverse (Ring.inverse_mul_cancel _ hQ)
  set v := Polynomial.aeval u B
  set E := u.rieszColemanProjection Q
  have hv : v.IsRowCompact := hu.aeval hB0
  have hGood := hu.isGoodZero_charPowerSeries_aeval_one_sub_C_mul_reverse hQ hS hfac hcop
  have hEv : IsRieszProjection v 1 Q.natDegree E :=
    hv.isRieszProjection_rieszProjection (fun _ ↦ hGood.evalAt_hasseDeriv_eq_zero)
      hGood.isUnit_evalAt_hasseDeriv
  have huE : Commute u E := hEv.commute_of_commute <| by
    simpa only [aeval_X] using (Commute.all X B).map (Polynomial.aeval u)
  have hrc : E.IsRowCompact := hEv.isRowCompact hv
  have hm : Set.MapsTo u E.range E.range := by
    rw [LinearMap.coe_range, coe_coe]
    exact Function.Semiconj.mapsTo_range fun x ↦ congr($(huE.eq.symm) x)
  have h1v : 1 - (1 : R) • v = c • Polynomial.aeval u Q.reverse := by
    simp [v, B, Algebra.algebraMap_eq_smul_one]
  set w := c • hEv.inverse
  have hw₁ : Polynomial.aeval u Q.reverse * w = 1 - E := by
    rw [mul_smul_comm, ← smul_mul_assoc, ← h1v]; exact hEv.one_sub_smul_mul_inverse
  have hw₂ : w * Polynomial.aeval u Q.reverse = 1 - E := by
    rw [smul_mul_assoc, ← mul_smul_comm, ← h1v]; exact hEv.inverse_mul_one_sub_smul
  obtain ⟨hf_char, -, -⟩ := projectiveCharpolyRev_and_charPowerSeries_of_rankAtStalk_le
    hu hQ0 hQ hS hfac hEv.isIdempotentElem huE hrc hm
    (fun p ↦ (hEv.rankAtStalk_range hv hGood p).le)
    (by
      convert isCoprime_complement_of_exists_inverse (isPrCompact_iff_isRowCompact.2 hu) hQ
        hEv.isIdempotentElem huE ⟨w, hw₁, hw₂⟩ using 1
      exact Subtype.ext (hu.comp_clm (1 - E)).charPowerSeries_eq_charPowerSeries_matrixCoeff.symm)
  have hcl : closure (Algebra.adjoin R {v} : Set (C₀(I, R) →L[R] C₀(I, R))) ⊆
      closure (Algebra.adjoin R {u} : Set (C₀(I, R) →L[R] C₀(I, R))) :=
    closure_mono (Algebra.adjoin_singleton_le (B.aeval_mem_adjoin_singleton R u))
  have : IsTopologicalSemiring (C₀(I, R) →L[R] C₀(I, R)) := inferInstance
  have hw_mem : w ∈ closure (Algebra.adjoin R {u} : Set (C₀(I, R) →L[R] C₀(I, R))) := by
    have h0 := hcl hEv.inverse_mem_closure_adjoin
    rw [← Subalgebra.topologicalClosure_coe, SetLike.mem_coe] at h0 ⊢
    exact Subalgebra.smul_mem _ h0 _
  refine ⟨hEv.isIdempotentElem, huE, hcl hEv.mem_closure_adjoin,
    aeval_reverse_mul_eq_zero_of_projectiveCharpolyRev_eq hB0 hEv hrc hm hf_char,
    ⟨w, hw₁, hw₂, ?_, ?_, hw_mem⟩⟩
  · rw [mul_smul_comm, hEv.mul_inverse_eq_zero, smul_zero]
  · rw [smul_mul_assoc, hEv.inverse_mul_eq_zero, smul_zero]

/-- **The explicit Riesz–Coleman projector on a model space.** Under a coprime factorization
`H_u = Q * S` with `IsUnit Q.leadingCoeff`, `u.rieszColemanProjection Q` is a Riesz–Coleman
projection of `u` for `Q`. -/
theorem IsRowCompact.isRieszColemanProjection_rieszColemanProjection
    (hu : u.IsRowCompact) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    IsRieszColemanProjection u Q (u.rieszColemanProjection Q) := by
  obtain ⟨u₀, S₁, hS₁, hQ₁0, hQ₁, hfac₁, hcop₁⟩ :=
    exists_unit_smul_coeff_zero_eq_one u.matrixCoeff.constantCoeff_charPowerSeries hQ hS hfac hcop
  rw [← isRieszColemanProjection_units_smul_iff u₀, ← u.rieszColemanProjection_units_smul Q u₀]
  exact isRieszColemanProjection_rieszColemanProjection_of_coeff_zero hu hQ₁0 hQ₁ hS₁ hfac₁ hcop₁

/-- Under a coprime Fredholm factorization `H_u = Q * S` with `IsUnit Q.leadingCoeff`, the explicit
Riesz–Coleman projector is row compact. -/
theorem IsRowCompact.isRowCompact_rieszColemanProjection
    (hu : u.IsRowCompact) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (u.rieszColemanProjection Q).IsRowCompact :=
  (hu.isRieszColemanProjection_rieszColemanProjection hQ hS hfac hcop).isRowCompact hQ hu

/-- **Existence of the Riesz–Coleman projection on a model space.** Every coprime factorization
`H_u = Q * S` with `IsUnit Q.leadingCoeff` admits a Riesz–Coleman projection for `Q`. -/
theorem IsRowCompact.exists_rieszColemanProjection
    (hu : u.IsRowCompact) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    ∃ E, IsRieszColemanProjection u Q E :=
  ⟨u.rieszColemanProjection Q, hu.isRieszColemanProjection_rieszColemanProjection hQ hS hfac hcop⟩

/-- Every Riesz–Coleman projection of `u` for a coprime factor `Q` of `H_u` with
`IsUnit Q.leadingCoeff` equals `u.rieszColemanProjection Q`. -/
theorem IsRieszColemanProjection.eq_rieszColemanProjection
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact) (hQ : IsUnit Q.leadingCoeff)
    (hS : S.IsEntire) (hfac : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    E = u.rieszColemanProjection Q :=
  hE.unique (hu.isRieszColemanProjection_rieszColemanProjection hQ hS hfac hcop)

/-- **Constant stalk rank of the Riesz–Coleman summand.** Under a coprime factorization
`H_u = Q * S` with `IsUnit Q.leadingCoeff`, `range E` has rank `Q.natDegree` on `Spec R`. -/
theorem IsRieszColemanProjection.rankAtStalk_range
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact) (hQ : IsUnit Q.leadingCoeff)
    (hS : S.IsEntire) (hfac : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) E.range p = Q.natDegree := by
  obtain rfl := hE.eq_rieszColemanProjection hu hQ hS hfac hcop
  have hv := hu.aeval (coeff_zero_one_sub_C_mul_reverse (Ring.inverse_mul_cancel _ hQ))
  have hGood := hu.isGoodZero_charPowerSeries_aeval_one_sub_C_mul_reverse hQ hS hfac hcop
  exact (hv.isRieszProjection_rieszProjection (fun _ ↦ hGood.evalAt_hasseDeriv_eq_zero)
    hGood.isUnit_evalAt_hasseDeriv).rankAtStalk_range hv hGood p

/-- Under a coprime factorization `H_u = Q * S` with `IsUnit Q.leadingCoeff`, `ker Q*(u)` has rank
`Q.natDegree` at every point of `Spec R`. -/
theorem IsRowCompact.rankAtStalk_ker_aeval_reverse
    (hu : u.IsRowCompact) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R)
      (LinearMap.ker (Polynomial.aeval u Q.reverse : C₀(I, R) →ₗ[R] C₀(I, R))) p =
      Q.natDegree := by
  have hE := hu.isRieszColemanProjection_rieszColemanProjection hQ hS hfac hcop
  rw [← hE.range_eq_ker]; exact hE.rankAtStalk_range hu hQ hS hfac hcop p

/-- **Reversed characteristic polynomial on the Riesz–Coleman summand.** Under a coprime Fredholm
factorization `H_u = Q * S` with `IsUnit Q.leadingCoeff` and `Q.coeff 0 = 1`,
`det (1 - X u|_{range E}) = Q`. -/
theorem IsRieszColemanProjection.projectiveCharpolyRev_restrict_range
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact) (hQ0 : Q.coeff 0 = 1)
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    letI : AddCommGroup E.range := inferInstance
    letI := (hE.isRowCompact hQ hu).finite_range_of_isIdempotentElem hE.isIdempotentElem
    letI := (hE.isRowCompact hQ hu).projective_range_of_isIdempotentElem hE.isIdempotentElem
    ((u.restrict hE.mapsTo_range : E.range →L[R] E.range) :
      Module.End R E.range).projectiveCharpolyRev = Q :=
  (projectiveCharpolyRev_and_charPowerSeries_of_rankAtStalk_le hu hQ0 hQ hS hfac
    hE.isIdempotentElem hE.commute (hE.isRowCompact hQ hu) hE.mapsTo_range
    (fun p ↦ (hE.rankAtStalk_range hu hQ hS hfac hcop p).le)
    (hE.isCoprime_charPowerSeries_matrixCoeff_complement hQ hu)).1

/-- **Fredholm series of the finite Riesz–Coleman summand.** Under a coprime Fredholm factorization
`H_u = Q * S` with `IsUnit Q.leadingCoeff` and `Q.coeff 0 = 1`, the Fredholm series of `u * E` is
`(Q : R⟦X⟧)`. -/
theorem IsRieszColemanProjection.charPowerSeries_matrixCoeff_mul_eq
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact) (hQ0 : Q.coeff 0 = 1)
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (u * E).matrixCoeff.charPowerSeries = (Q : R⟦X⟧) :=
  (projectiveCharpolyRev_and_charPowerSeries_of_rankAtStalk_le hu hQ0 hQ hS hfac
    hE.isIdempotentElem hE.commute (hE.isRowCompact hQ hu) hE.mapsTo_range
    (fun p ↦ (hE.rankAtStalk_range hu hQ hS hfac hcop p).le)
    (hE.isCoprime_charPowerSeries_matrixCoeff_complement hQ hu)).2.1

/-- **Fredholm series of the complementary Riesz–Coleman summand.** Under a coprime Fredholm
factorization `H_u = Q * S` with `IsUnit Q.leadingCoeff` and `Q.coeff 0 = 1`, the Fredholm series of
`u * (1 - E)` is `S`. -/
theorem IsRieszColemanProjection.charPowerSeries_matrixCoeff_mul_one_sub_eq
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact) (hQ0 : Q.coeff 0 = 1)
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (u * (1 - E)).matrixCoeff.charPowerSeries = S :=
  (projectiveCharpolyRev_and_charPowerSeries_of_rankAtStalk_le hu hQ0 hQ hS hfac
    hE.isIdempotentElem hE.commute (hE.isRowCompact hQ hu) hE.mapsTo_range
    (fun p ↦ (hE.rankAtStalk_range hu hQ hS hfac hcop p).le)
    (hE.isCoprime_charPowerSeries_matrixCoeff_complement hQ hu)).2.2

end Ring

section Field

variable {I K : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {u E : C₀(I, K) →L[K] C₀(I, K)} {Q : K[X]} {S : K⟦X⟧}

/-- Over a complete ultrametric field, `range E` associated to a coprime factorization `H_u = Q * S`
has dimension `Q.natDegree`. -/
theorem IsRieszColemanProjection.finrank_range
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact) (hS : S.IsEntire)
    (hfac : u.matrixCoeff.charPowerSeries = (Q : K⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring K)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    Module.finrank K E.range = Q.natDegree := by
  have hQ : IsUnit Q.leadingCoeff := (leadingCoeff_ne_zero.mpr fun h0 ↦ by
    simpa [h0, u.matrixCoeff.constantCoeff_charPowerSeries] using
      congrArg (PowerSeries.constantCoeff (R := K)) hfac).isUnit
  have hr := hE.rankAtStalk_range hu hQ hS hfac hcop ⟨⊥, Ideal.isPrime_bot⟩
  let : AddCommGroup E.range := inferInstance
  rwa [Module.rankAtStalk_eq_finrank_of_free] at hr

/-- Over a complete ultrametric field, `ker Q*(u)` associated to a coprime factorization
`H_u = Q * S` has dimension `Q.natDegree`. -/
theorem IsRowCompact.finrank_ker_aeval_reverse (hu : u.IsRowCompact) (hS : S.IsEntire)
    (hfac : u.matrixCoeff.charPowerSeries = (Q : K⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring K)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    Module.finrank K (LinearMap.ker (Polynomial.aeval u Q.reverse : C₀(I, K) →ₗ[K] C₀(I, K))) =
      Q.natDegree := by
  have hQ : IsUnit Q.leadingCoeff := (leadingCoeff_ne_zero.mpr fun h0 ↦ by
    simpa [h0, u.matrixCoeff.constantCoeff_charPowerSeries] using
      congrArg (PowerSeries.constantCoeff (R := K)) hfac).isUnit
  have hE := hu.isRieszColemanProjection_rieszColemanProjection hQ hS hfac hcop
  rw [← hE.range_eq_ker]; exact hE.finrank_range hu hS hfac hcop

end Field

end ContinuousLinearMap
