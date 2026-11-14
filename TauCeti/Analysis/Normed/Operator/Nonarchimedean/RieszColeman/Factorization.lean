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
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Intertwining

/-!
# Riesz–Coleman decomposition on model spaces from coprime Fredholm factors

Let `R` be a complete ultrametric normed commutative ring with Tate scalars, `I` a discrete index
type, and `u` a row-compact endomorphism of `C₀(I, R)` whose Fredholm series
`H_u = u.matrixCoeff.charPowerSeries` admits a factorization `H_u = Q * S`, where `Q : R[X]` has
invertible leading coefficient, `S` is entire, and `Q` and `S` are coprime in `IsEntire.subring R`.

Put `c = Ring.inverse Q.leadingCoeff`, `B = 1 - c Q*` (`Q* = Q.reverse`), `d = Q.natDegree`, and
`v = B(u)`. Because `B(0) = 0`, `v` is row compact, and polynomial spectral mapping transforms
`H_u` into `H_v = D(B, H_u) = (1 - T) ^ d * D(B, S₁)` (after normalizing `Q` by its automatically
invertible constant coefficient), where `D(B, S₁)(1)` is a unit by Coleman's resultant identity.
Hence `v` has a good Fredholm zero at `1` of order `d`
(`ContinuousLinearMap.IsRowCompact.isGoodZero_charPowerSeries_aeval_one_sub_C_mul_reverse`), and

`u.rieszColemanProjection Q := v.rieszProjection 1 d`

is the unique Riesz–Coleman projection of `u` for `Q`
(`ContinuousLinearMap.IsRowCompact.isRieszColemanProjection_rieszColemanProjection`).

Crucially, `IsRieszColemanProjection` requires `Q*(u) * E = 0` directly (not merely
`Q*(u) ^ d * E = 0`): on the finite projective summand `range E` of constant rank `d`, coprimality
of `Q` with the complementary Fredholm factor forces the reversed characteristic polynomial of
`u|_{range E}` to be the normalized factor `Q₁`, and Cayley–Hamilton on `range E` together with
invertibility of `u|_{range E}` annihilates `Q*(u)` on `range E`.

No normalization `Q.coeff 0 = 1` is needed for the projector, its row compactness, or the stalk-rank
and dimension formulas (`rankAtStalk E.range = Q.natDegree`, `finrank K E.range = Q.natDegree`),
because `1 = H_u(0) = Q(0) S(0)` forces `Q(0)` to be a unit and `rieszColemanProjection` is
invariant under unit scaling (`ContinuousLinearMap.rieszColemanProjection_units_smul`). When
`Q.coeff 0 = 1`, the Fredholm factors on the two summands are literally `Q` and `S`.

## Main definitions

* `ContinuousLinearMap.rieszColemanProjection`: the explicit Riesz–Coleman projector of `u` for `Q`
  on `C₀(I, R)`, defined as `(B(u)).rieszProjection 1 Q.natDegree` for `B = 1 - c Q*`.

## Main results

* `ContinuousLinearMap.IsRowCompact.isGoodZero_charPowerSeries_aeval_one_sub_C_mul_reverse`:
  `B(u)` has a good Fredholm zero at `1` of order `Q.natDegree`.
* `ContinuousLinearMap.IsRowCompact.isRieszColemanProjection_rieszColemanProjection`,
  `ContinuousLinearMap.IsRowCompact.exists_rieszColemanProjection`,
  `ContinuousLinearMap.IsRieszColemanProjection.eq_rieszColemanProjection`: existence and explicit
  identification of the Riesz–Coleman projection from a coprime Fredholm factorization.
* `ContinuousLinearMap.IsRieszColemanProjection.isCoprime_charPowerSeries_matrixCoeff_complement`:
  for any Riesz–Coleman projection, `Q` is coprime to the complementary Fredholm series.
* `ContinuousLinearMap.IsRieszColemanProjection.rankAtStalk_range`,
  `ContinuousLinearMap.IsRieszColemanProjection.rankAtStalk_ker_aeval_reverse`: `range E` and
  `ker Q*(u)` have constant rank `Q.natDegree` on `Spec R`.
* `ContinuousLinearMap.IsRieszColemanProjection.projectiveCharpolyRev_restrict_range`,
  `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_matrixCoeff_mul_eq`,
  `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_matrixCoeff_mul_one_sub_eq`: when
  `Q.coeff 0 = 1`, the two summand Fredholm series are `Q` and `S`.
* `ContinuousLinearMap.IsRieszColemanProjection.finrank_range`,
  `ContinuousLinearMap.IsRieszColemanProjection.finrank_ker_aeval_reverse`: over a complete
  ultrametric field, `dim range E = dim ker Q*(u) = Q.natDegree`.

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

omit [TauCeti.NormedRing.IsTate R] in
private theorem one_sub_C_inverse_mul_reverse_units_smul (Q : R[X]) (c : Rˣ) :
    1 - C (Ring.inverse (c • Q).leadingCoeff) * (c • Q).reverse =
      1 - C (Ring.inverse Q.leadingCoeff) * Q.reverse := by
  have hdeg : (c • Q).natDegree = Q.natDegree :=
    natDegree_smul_of_smul_regular Q (IsSMulRegular.all c)
  have hrev : (c • Q).reverse = C (c : R) * Q.reverse := by
    rw [reverse, hdeg, Units.smul_def, smul_eq_C_mul, reflect_C_mul, ← reverse]
  have hlc : (c • Q).leadingCoeff = (c : R) * Q.leadingCoeff := by
    rw [leadingCoeff, leadingCoeff, hdeg, Units.smul_def, smul_eq_C_mul, coeff_C_mul]
  have hinv : Ring.inverse ((c : R) * Q.leadingCoeff) * (c : R) = Ring.inverse Q.leadingCoeff := by
    rw [Ring.inverse_mul (.inl c.isUnit), Ring.inverse_unit, mul_assoc, c.inv_mul, mul_one]
  rw [hlc, hrev, ← mul_assoc, ← C_mul, hinv]

/-- The **Riesz–Coleman projector** of an endomorphism `u` of `C₀(I, R)` for `Q : R[X]`:
the Riesz projector at `1` of order `Q.natDegree` of `(1 - c Q*)(u)`, where
`c = Ring.inverse Q.leadingCoeff` and `Q* = Q.reverse`. When `u` is row compact and `Q` is a
coprime polynomial factor of `det (1 - T u)` with invertible leading coefficient, it is the unique
Riesz–Coleman projection of `u` for `Q`
(`ContinuousLinearMap.IsRowCompact.isRieszColemanProjection_rieszColemanProjection`); otherwise it
is a junk value. -/
noncomputable def rieszColemanProjection (u : C₀(I, R) →L[R] C₀(I, R)) (Q : R[X]) :
    C₀(I, R) →L[R] C₀(I, R) :=
  (Polynomial.aeval u (1 - C (Ring.inverse Q.leadingCoeff) * Q.reverse)).rieszProjection 1
    Q.natDegree

/-- Unfolding lemma for `ContinuousLinearMap.rieszColemanProjection`. -/
theorem rieszColemanProjection_def (u : C₀(I, R) →L[R] C₀(I, R)) (Q : R[X]) :
    u.rieszColemanProjection Q =
      (Polynomial.aeval u (1 - C (Ring.inverse Q.leadingCoeff) * Q.reverse)).rieszProjection 1
        Q.natDegree :=
  (rfl)

/-- For `Q = 1`, `deg Q = 0`, so the Riesz–Coleman projector is zero. -/
@[simp]
theorem rieszColemanProjection_one (u : C₀(I, R) →L[R] C₀(I, R)) :
    u.rieszColemanProjection 1 = 0 := by
  rw [rieszColemanProjection_def, natDegree_one, rieszProjection_order_zero]

/-- The Riesz–Coleman projector is invariant under scaling `Q` by any unit of `R`. -/
@[simp]
theorem rieszColemanProjection_units_smul (u : C₀(I, R) →L[R] C₀(I, R)) (Q : R[X]) (c : Rˣ) :
    u.rieszColemanProjection (c • Q) = u.rieszColemanProjection Q := by
  rw [rieszColemanProjection_def, rieszColemanProjection_def,
    natDegree_smul_of_smul_regular Q (IsSMulRegular.all c),
    one_sub_C_inverse_mul_reverse_units_smul]

end ExplicitProjector

section Ring

variable {I R : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [NormedCommRing R] [TauCeti.NormedRing.IsTate R] [IsUltrametricDist R] [CompleteSpace R]

omit [TauCeti.NormedRing.IsTate R] [IsUltrametricDist R] [CompleteSpace R] in
/-- Normalize a coprime factorization `F = Q * S` with `F(0) = 1` by the unit `Q(0)⁻¹`, yielding
`Q₁ = u₀ • Q` with `Q₁(0) = 1` and `F = Q₁ * S₁` with `Q₁`, `S₁` still coprime entire series. -/
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
    have hc := congrArg (PowerSeries.constantCoeff (R := R)) hfac
    simpa [hF0] using hc.symm
  let c₀ : Rˣ := Units.mkOfMulEqOne (Q.coeff 0) (PowerSeries.constantCoeff S) h1
  let u₀ : Rˣ := c₀⁻¹
  set S₁ : R⟦X⟧ := PowerSeries.C (c₀ : R) * S with hS₁_def
  have hS₁ : S₁.IsEntire := (PowerSeries.isEntire_C (c₀ : R)).mul hS
  have hu₀Q0 : (u₀ • Q).coeff 0 = 1 := by
    change (↑c₀⁻¹ : R) * Q.coeff 0 = 1
    exact c₀.inv_mul
  have hu₀Q_lc : IsUnit (u₀ • Q).leadingCoeff := by
    rw [leadingCoeff, natDegree_smul_of_smul_regular Q (IsSMulRegular.all u₀),
      Units.smul_def, smul_eq_C_mul, coeff_C_mul, ← leadingCoeff]
    exact u₀.isUnit.mul hQ
  have hfac₁ : F = ((u₀ • Q : R[X]) : R⟦X⟧) * S₁ := by
    rw [hfac, Units.smul_def, smul_eq_C_mul, Polynomial.coe_mul, Polynomial.coe_C, hS₁_def,
      mul_assoc, ← mul_assoc (PowerSeries.C (u₀ : R)) (Q : R⟦X⟧),
      mul_comm (PowerSeries.C (u₀ : R)), mul_assoc, ← mul_assoc (PowerSeries.C (u₀ : R)),
      ← map_mul, c₀.inv_mul, map_one, one_mul]
  have hunit₁ : IsUnit (⟨PowerSeries.C (u₀ : R),
      IsEntire.mem_subring.mpr (PowerSeries.isEntire_C (u₀ : R))⟩ : IsEntire.subring R) :=
    IsUnit.of_mul_eq_one
      ⟨PowerSeries.C (c₀ : R), IsEntire.mem_subring.mpr (PowerSeries.isEntire_C (c₀ : R))⟩
      (Subtype.ext (by
        change PowerSeries.C (↑c₀⁻¹ : R) * PowerSeries.C (c₀ : R) = 1
        rw [← map_mul, c₀.inv_mul, map_one]))
  have hunit₂ : IsUnit (⟨PowerSeries.C (c₀ : R),
      IsEntire.mem_subring.mpr (PowerSeries.isEntire_C (c₀ : R))⟩ : IsEntire.subring R) :=
    IsUnit.of_mul_eq_one
      ⟨PowerSeries.C (u₀ : R), IsEntire.mem_subring.mpr (PowerSeries.isEntire_C (u₀ : R))⟩
      (Subtype.ext (by
        change PowerSeries.C (c₀ : R) * PowerSeries.C (↑c₀⁻¹ : R) = 1
        rw [← map_mul, c₀.mul_inv, map_one]))
  have hcop₁ : IsCoprime
      (⟨(u₀ • Q : R[X]), IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe _)⟩ :
        IsEntire.subring R)
      ⟨S₁, IsEntire.mem_subring.mpr hS₁⟩ := by
    have h' := (isCoprime_mul_unit_left_left hunit₁ _ _).mpr
      ((isCoprime_mul_unit_left_right hunit₂ _ _).mpr hcop)
    convert h' using 1
    exact Subtype.ext (by simp [Units.smul_def, smul_eq_C_mul])
  exact ⟨u₀, S₁, hS₁, hu₀Q0, hu₀Q_lc, hfac₁, hcop₁⟩

/-- If `P` and `Q` are polynomials with constant coefficient `1`, `Q.leadingCoeff` is a unit,
`deg P ≤ deg Q`, and `Q` divides `P` in the ring of entire series, then `P = Q`. -/
private theorem eq_of_coe_dvd_of_natDegree_le {Q P : R[X]} (hQ0 : Q.coeff 0 = 1)
    (hQ : IsUnit Q.leadingCoeff) (hP0 : P.coeff 0 = 1) (hdeg : P.natDegree ≤ Q.natDegree)
    (hdvd : (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R) ∣
      ⟨P, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe P)⟩) :
    P = Q := by
  have := NormOneClass.nontrivial (G := R)
  set c := Ring.inverse Q.leadingCoeff
  have hc : c * Q.leadingCoeff = 1 := Ring.inverse_mul_cancel _ hQ
  set Qm := C c * Q with hQm_def
  have hm : Qm.Monic := monic_C_mul_of_mul_leadingCoeff_eq_one hc
  have hQm_deg : Qm.natDegree = Q.natDegree :=
    natDegree_C_mul_eq_of_mul_eq_one (by rw [mul_comm]; exact hc)
  obtain ⟨⟨H, hH⟩, hPH⟩ := hdvd
  have hPH' : (P : R⟦X⟧) = (Qm : R⟦X⟧) * (PowerSeries.C Q.leadingCoeff * H) := by
    have hP_eq : (P : R⟦X⟧) = (Q : R⟦X⟧) * H := congrArg Subtype.val hPH
    rw [hP_eq, hQm_def, Polynomial.coe_mul, Polynomial.coe_C, mul_comm (PowerSeries.C c),
      mul_assoc, ← mul_assoc (PowerSeries.C c), ← map_mul, hc, map_one, one_mul]
  have hmk : AdjoinRoot.mk Qm P = 0 := by
    rw [← IsEntire.mkAdjoinRoot_coe hm P, IsEntire.mkAdjoinRoot_eq_zero_iff hm]
    exact ⟨PowerSeries.C Q.leadingCoeff * H,
      (PowerSeries.isEntire_C Q.leadingCoeff).mul (IsEntire.mem_subring.mp hH), hPH'⟩
  obtain ⟨Km, hPKm⟩ := AdjoinRoot.mk_eq_zero.mp hmk
  have hKm0 : Km.coeff 0 = Q.leadingCoeff := by
    have h0 := congrArg (Polynomial.eval 0) hPKm
    simp only [eval_mul, hQm_def, eval_C, ← coeff_zero_eq_eval_zero, hP0, hQ0, mul_one] at h0
    calc Km.coeff 0 = 1 * Km.coeff 0 := (one_mul _).symm
      _ = Q.leadingCoeff * (c * Km.coeff 0) := by rw [← mul_assoc, mul_comm Q.leadingCoeff c, hc]
      _ = Q.leadingCoeff := by rw [← h0, mul_one]
  have hKm_ne : Km ≠ 0 := fun h0 ↦ hQ.ne_zero (by simpa [h0] using hKm0.symm)
  have hKm_deg : Km.natDegree = 0 := by
    have hd := hPKm ▸ hm.natDegree_mul' hKm_ne
    omega
  rw [hPKm, eq_C_of_natDegree_eq_zero hKm_deg, hKm0, hQm_def, mul_comm (C c), mul_assoc,
    ← C_mul, hc, C_1, mul_one]

omit [TauCeti.NormedRing.IsTate R] [IsUltrametricDist R] [CompleteSpace R] in
/-- Evaluating a polynomial `B` with zero constant term at `u * (1 - E)` multiplies `B(u)` by the
commuting idempotent `1 - E`. -/
private theorem aeval_mul_one_sub_of_coeff_zero {M : Type*}
    [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
    {u E : M →L[R] M} (hIdem : IsIdempotentElem E) (huE : Commute u E)
    {B : R[X]} (hB0 : B.coeff 0 = 0) :
    Polynomial.aeval (u * (1 - E)) B = Polynomial.aeval u B * (1 - E) := by
  obtain ⟨P, rfl⟩ := X_dvd_iff.mpr hB0
  have hup : Commute u (1 - E) := (Commute.one_right u).sub_right huE
  suffices ∀ Q : R[X],
      u * (1 - E) * Polynomial.aeval (u * (1 - E)) Q =
        u * Polynomial.aeval u Q * (1 - E) by
    simpa only [map_mul, aeval_X, mul_assoc] using this P
  intro Q
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, mul_add, add_mul, hp, hq]
  | monomial n r =>
    simp only [aeval_monomial, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc,
      one_mul]
    congr 1
    rw [← pow_succ' (u * (1 - E)) n, hup.mul_pow, hIdem.one_sub.pow_succ_eq, pow_succ' u n]

/-- If `E` is an idempotent commuting with `u` and `Q*(u)` is invertible modulo `E`, then `Q` is
coprime to `(u * (1 - E)).matrixCoeff.charPowerSeries` in `IsEntire.subring R`. -/
private theorem isCoprime_complement_of_exists_inverse
    {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]} (hu : u.IsRowCompact)
    (hQ : IsUnit Q.leadingCoeff) (hIdem : IsIdempotentElem E) (huE : Commute u E)
    (hinv : ∃ w : C₀(I, R) →L[R] C₀(I, R),
      Polynomial.aeval u Q.reverse * w = 1 - E ∧ w * Polynomial.aeval u Q.reverse = 1 - E) :
    IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨(u * (1 - E)).matrixCoeff.charPowerSeries,
        IsEntire.mem_subring.mpr (hu.comp_clm (1 - E)).isEntire_charPowerSeries⟩ := by
  obtain ⟨w, hw₁, hw₂⟩ := hinv
  set c := Ring.inverse Q.leadingCoeff
  have hc : c * Q.leadingCoeff = 1 := Ring.inverse_mul_cancel _ hQ
  set B := 1 - C c * Q.reverse
  have hB0 : B.coeff 0 = 0 := coeff_zero_one_sub_C_mul_reverse hc
  have h1B : 1 - Polynomial.aeval u B = c • Polynomial.aeval u Q.reverse := by
    simp [B, Algebra.algebraMap_eq_smul_one]
  have hw₁' : (1 - Polynomial.aeval u B) * (Q.leadingCoeff • w) = 1 - E := by
    rw [h1B, smul_mul_smul_comm, hc, one_smul, hw₁]
  have hw₂' : (Q.leadingCoeff • w) * (1 - Polynomial.aeval u B) = 1 - E := by
    rw [h1B, smul_mul_smul_comm, mul_comm Q.leadingCoeff c, hc, one_smul, hw₂]
  have hunit_block : IsUnit (E + (1 - Polynomial.aeval u B) * (1 - E)) := by
    convert _root_.IsIdempotentElem.isUnit_add_mul_one_sub
      (A := C₀(I, R) →L[R] C₀(I, R)) hIdem hw₁' hw₂'
  have hblock_eq : E + (1 - Polynomial.aeval u B) * (1 - E) =
      (IsUnit.of_mul_eq_one _ hc).unit • Polynomial.aeval (u * (1 - E)) Q.reverse := by
    have hB_comp := aeval_mul_one_sub_of_coeff_zero hIdem huE hB0
    have h1B_comp : 1 - Polynomial.aeval (u * (1 - E)) B =
        (IsUnit.of_mul_eq_one _ hc).unit • Polynomial.aeval (u * (1 - E)) Q.reverse := by
      simp [B, Units.smul_def, Algebra.algebraMap_eq_smul_one]
    rw [← h1B_comp, hB_comp, sub_mul (α := C₀(I, R) →L[R] C₀(I, R)), one_mul]
    abel
  rw [hblock_eq, isUnit_smul_iff] at hunit_block
  exact ((hu.comp_clm (1 - E)).isUnit_aeval_reverse_iff hQ).mp hunit_block

/-- **Coprimality on the complementary summand.** For any Riesz–Coleman projection `E` of a
row-compact operator `u` on `C₀(I, R)` and `Q` with invertible leading coefficient, `Q` is coprime
to the complementary Fredholm factor `(u * (1 - E)).matrixCoeff.charPowerSeries` in the ring of
entire series. -/
theorem IsRieszColemanProjection.isCoprime_charPowerSeries_matrixCoeff_complement
    {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]} (hE : IsRieszColemanProjection u Q E)
    (hQ : IsUnit Q.leadingCoeff) (hu : u.IsRowCompact) :
    IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨(u * (1 - E)).matrixCoeff.charPowerSeries,
        IsEntire.mem_subring.mpr (hu.comp_clm (1 - E)).isEntire_charPowerSeries⟩ :=
  isCoprime_complement_of_exists_inverse hu hQ hE.isIdempotentElem hE.commute
    ⟨hE.inverse, hE.aeval_reverse_mul_inverse, hE.inverse_mul_aeval_reverse⟩

/-- **Good zero after Coleman's polynomial transform.** Let `u` be row compact on `C₀(I, R)` and
`H_u = Q * S` a coprime factorization in `IsEntire.subring R` with `IsUnit Q.leadingCoeff`. Then
`(1 - c Q*)(u)` (`c = Ring.inverse Q.leadingCoeff`) has a good Fredholm zero at `1` of order
`Q.natDegree`. -/
theorem IsRowCompact.isGoodZero_charPowerSeries_aeval_one_sub_C_mul_reverse
    {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact) {Q : R[X]} {S : R⟦X⟧}
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
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
  set c₁ := Ring.inverse Q₁.leadingCoeff
  have hc₁ : c₁ * Q₁.leadingCoeff = 1 := Ring.inverse_mul_cancel _ hQ₁
  set B := 1 - C c₁ * Q₁.reverse
  have hB0 : B.coeff 0 = 0 := coeff_zero_one_sub_C_mul_reverse hc₁
  have hS₁0 : PowerSeries.constantCoeff S₁ = 1 := by
    have hc := congrArg (PowerSeries.constantCoeff (R := R)) hfac₁
    simpa [u.matrixCoeff.constantCoeff_charPowerSeries, hQ₁0] using hc.symm
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
    have h1X : (1 - PowerSeries.X : R⟦X⟧) =
        PowerSeries.C (-1 : R) * (PowerSeries.X - PowerSeries.C 1) := by
      ext n; cases n <;> simp [sub_eq_add_neg, add_comm]
    rw [h1X, mul_pow, ← map_pow, hG_def]
    ring
  rw [hchar, hGe.isGoodZero_X_sub_C_pow_mul_iff]
  have heval :
      G.evalAt (1 : R) = (-1 : R) ^ Q₁.natDegree * (B.colemanDSeries S₁).evalAt (1 : R) := by
    rw [hG_def, (PowerSeries.isEntire_C ((-1 : R) ^ Q₁.natDegree)).evalAt_mul hDe,
      ← Polynomial.coe_C, PowerSeries.evalAt_coe]
    simp
  rw [heval]
  exact (isUnit_neg_one.pow Q₁.natDegree).mul hDunit

/-- Shared determinant computation on any row-compact commuting idempotent `E` whose range has
stalk rank `≤ deg Q` and whose complement has Fredholm series coprime to `Q`. -/
private theorem projectiveCharpolyRev_and_charPowerSeries_of_rankAtStalk_le
    {u E : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact)
    {Q : R[X]} {S : R⟦X⟧} (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hIdem : IsIdempotentElem E) (huE : Commute u E) (hrc : E.IsRowCompact)
    (hm : Set.MapsTo u E.range E.range)
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
  have hfix (x : E.range) : E x = x :=
    (LinearMap.IsIdempotentElem.mem_range_iff
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap hIdem)).mp x.property
  have hri : E.rangeRestrict.comp E.range.subtypeL = .id R E.range :=
    ContinuousLinearMap.ext fun x ↦ Subtype.ext (hfix x)
  have hM : TauCeti.HasPr R E.range :=
    (isPrCompact_iff_isRowCompact.2 hu).hasPr_source.of_retract
      E.range.subtypeL E.rangeRestrict hri
  have hv_pr := isPrCompact_of_finite (R := R) (M := E.range) (L := E.range) hM hM v_u
  have hext : E.range.subtypeL.comp (v_u.comp E.rangeRestrict) = u * E := by
    ext x; rfl
  have hchar : (u * E).matrixCoeff.charPowerSeries = (f.projectiveCharpolyRev : R⟦X⟧) := by
    rw [← hext, ← hv_pr.charPowerSeries_eq hri,
      charPowerSeries_eq_projectiveCharpolyRev (R := R) (M := E.range) hM v_u]
  have hsplit := hu.charPowerSeries_matrixCoeff_eq_mul_of_commute hIdem huE
  rw [hfac, hchar] at hsplit
  have hdvd :
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R) ∣
        ⟨f.projectiveCharpolyRev,
          IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe _)⟩ :=
    hcop_comp.dvd_of_dvd_mul_right ⟨⟨S, IsEntire.mem_subring.mpr hS⟩,
      Subtype.ext hsplit.symm⟩
  have hf_eq : f.projectiveCharpolyRev = Q :=
    eq_of_coe_dvd_of_natDegree_le hQ0 hQ f.coeff_projectiveCharpolyRev_zero
      (f.natDegree_projectiveCharpolyRev_le hrank) hdvd
  have hQunit : IsUnit (Q : R⟦X⟧) :=
    PowerSeries.isUnit_iff_constantCoeff.mpr (by simp [hQ0])
  refine ⟨hf_eq, by rwa [hf_eq] at hchar, ?_⟩
  rw [hf_eq] at hsplit
  exact hQunit.mul_left_cancel hsplit.symm

/-- Cayley–Hamilton annihilation on the finite projective summand `E.range`: when `E` is a Riesz
projection of `B(u)` (`B(0) = 0`) at `1` of order `Q.natDegree` and `u|_{E.range}` has reversed
characteristic polynomial `Q`, `Q*(u) * E = 0`. -/
private theorem aeval_reverse_mul_eq_zero_of_projectiveCharpolyRev_eq
    {u E : C₀(I, R) →L[R] C₀(I, R)} {Q B : R[X]}
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
  have hf_sub : (u : Module.End R C₀(I, R)).comp E.range.subtype = E.range.subtype.comp f :=
    LinearMap.ext fun _ ↦ rfl
  have hf_aeval (P : R[X]) (x : E.range) :
      ((Polynomial.aeval f P) x : C₀(I, R)) = Polynomial.aeval u P x := by
    have h := LinearMap.congr_fun (Module.End.aeval_comp_of_comp_eq hf_sub P) x
    simpa only [LinearMap.comp_apply, Submodule.subtype_apply, ← toLinearMap_aeval, coe_coe]
      using h.symm
  have hf_unit : IsUnit f := by
    set A : R[X] := 1 - (1 - B) ^ Q.natDegree with hA_def
    have hA0 : A.coeff 0 = 0 := by
      rw [coeff_zero_eq_eval_zero, hA_def, eval_sub, eval_one, eval_pow, eval_sub, eval_one,
        ← coeff_zero_eq_eval_zero, hB0, sub_zero, one_pow, sub_self]
    have hA : X * A.divX = A := by simpa [hA0] using X_mul_divX_add A
    have hAE (x : E.range) : Polynomial.aeval u A x = x := by
      have hfix : E x = x :=
        (LinearMap.IsIdempotentElem.mem_range_iff
          (ContinuousLinearMap.IsIdempotentElem.toLinearMap hEv.isIdempotentElem)).mp x.property
      have hz := congr($(hEv.pow_mul_eq_zero) (x : C₀(I, R)))
      simp only [one_smul, mul_apply_eq_comp, hfix, zero_apply] at hz
      have hAu : Polynomial.aeval u A = 1 - (1 - Polynomial.aeval u B) ^ Q.natDegree := by
        simp [hA_def]
      simp only [hAu, sub_apply, one_apply_eq_self, hz, sub_zero]
    have hfg : f * Polynomial.aeval f A.divX = 1 := by
      ext x : 1
      apply Subtype.ext
      have hXA : f * Polynomial.aeval f A.divX = Polynomial.aeval f A := by
        conv_rhs => rw [← hA]
        rw [map_mul, aeval_X]
      simpa only [hXA, Module.End.one_eq_id, LinearMap.id_apply, hf_aeval] using hAE x
    have hcomm : Commute f (Polynomial.aeval f A.divX) := by
      simpa only [aeval_X] using (Commute.all X A.divX).map (Polynomial.aeval f)
    exact isUnit_iff_exists.mpr ⟨Polynomial.aeval f A.divX, hfg, hcomm.symm.eq.trans hfg⟩
  obtain ⟨n, hn, hCH⟩ := f.exists_aeval_reflect_projectiveCharpolyRev_eq_zero
  rw [hf_char] at hn hCH
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h1ref : (1 : R[X]).reflect k = X ^ k := by rw [← C_1, reflect_C, C_1, one_mul]
  have href : Q.reflect (Q.natDegree + k) = Q.reverse * X ^ k := by
    calc Q.reflect (Q.natDegree + k) = (Q * 1).reflect (Q.natDegree + k) := by rw [mul_one]
      _ = Q.reflect Q.natDegree * (1 : R[X]).reflect k := reflect_mul Q 1 le_rfl (by simp)
      _ = Q.reverse * X ^ k := by rw [reverse, h1ref]
  rw [href, map_mul, map_pow, aeval_X] at hCH
  have hfQ : Polynomial.aeval f Q.reverse = 0 :=
    (hf_unit.pow k).mul_left_eq_zero.mp hCH
  ext y
  simp only [mul_apply_eq_comp, zero_apply, ← hf_aeval Q.reverse ⟨E y, ⟨y, rfl⟩⟩, hfQ,
    LinearMap.zero_apply, ZeroMemClass.coe_zero]

/-- Normalized core: when `Q.coeff 0 = 1`, `u.rieszColemanProjection Q` is a Riesz–Coleman
projection of `u` for `Q`. -/
private theorem isRieszColemanProjection_rieszColemanProjection_of_coeff_zero
    {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact) {Q : R[X]} {S : R⟦X⟧}
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    IsRieszColemanProjection u Q (u.rieszColemanProjection Q) := by
  set c := Ring.inverse Q.leadingCoeff
  have hc : c * Q.leadingCoeff = 1 := Ring.inverse_mul_cancel _ hQ
  set B := 1 - C c * Q.reverse
  have hB0 : B.coeff 0 = 0 := coeff_zero_one_sub_C_mul_reverse hc
  set v := Polynomial.aeval u B
  set E := u.rieszColemanProjection Q
  have hv : v.IsRowCompact := hu.aeval hB0
  have hGood := hu.isGoodZero_charPowerSeries_aeval_one_sub_C_mul_reverse hQ hS hfac hcop
  have hEv : IsRieszProjection v 1 Q.natDegree E :=
    hv.isRieszProjection_rieszProjection (fun _ ↦ hGood.evalAt_hasseDeriv_eq_zero)
      hGood.isUnit_evalAt_hasseDeriv
  have huv : Commute u v := by
    simpa only [aeval_X] using (Commute.all X B).map (Polynomial.aeval u)
  have huE : Commute u E := hEv.commute_of_commute huv
  have hrc : E.IsRowCompact := hEv.isRowCompact hv
  have hm : Set.MapsTo u E.range E.range := by
    rw [LinearMap.coe_range, coe_coe]
    exact Function.Semiconj.mapsTo_range fun x ↦ congr($(huE.eq.symm) x)
  have h1v : 1 - (1 : R) • v = c • Polynomial.aeval u Q.reverse := by
    simp [v, B, Algebra.algebraMap_eq_smul_one]
  set w := c • hEv.inverse
  have hw₁ : Polynomial.aeval u Q.reverse * w = 1 - E := by
    rw [mul_smul_comm, ← smul_mul_assoc, ← h1v]
    exact hEv.one_sub_smul_mul_inverse
  have hw₂ : w * Polynomial.aeval u Q.reverse = 1 - E := by
    rw [smul_mul_assoc, ← mul_smul_comm, ← h1v]
    exact hEv.inverse_mul_one_sub_smul
  have hcop_comp := isCoprime_complement_of_exists_inverse hu hQ hEv.isIdempotentElem huE
    ⟨w, hw₁, hw₂⟩
  obtain ⟨hf_char, -, -⟩ := projectiveCharpolyRev_and_charPowerSeries_of_rankAtStalk_le
    hu hQ0 hQ hS hfac hEv.isIdempotentElem huE hrc hm
    (fun p ↦ (hEv.rankAtStalk_range hv hGood p).le) hcop_comp
  have hQ_zero := aeval_reverse_mul_eq_zero_of_projectiveCharpolyRev_eq hB0 hEv hrc hm hf_char
  have hcl : closure (Algebra.adjoin R {v} : Set (C₀(I, R) →L[R] C₀(I, R))) ⊆
      closure (Algebra.adjoin R {u} : Set (C₀(I, R) →L[R] C₀(I, R))) :=
    closure_mono (Algebra.adjoin_singleton_le (B.aeval_mem_adjoin_singleton R u))
  have : IsTopologicalSemiring (C₀(I, R) →L[R] C₀(I, R)) := inferInstance
  set T := (Algebra.adjoin R {u}).topologicalClosure
  have hT (x : C₀(I, R) →L[R] C₀(I, R)) :
      x ∈ T ↔ x ∈ closure (Algebra.adjoin R {u} : Set (C₀(I, R) →L[R] C₀(I, R))) := by
    rw [← SetLike.mem_coe, Subalgebra.topologicalClosure_coe]
  refine ⟨hEv.isIdempotentElem, huE, hcl hEv.mem_closure_adjoin, hQ_zero,
    ⟨w, hw₁, hw₂, ?_, ?_, (hT _).1 (T.smul_mem ((hT _).2 (hcl hEv.inverse_mem_closure_adjoin)) _)⟩⟩
  · rw [mul_smul_comm, hEv.mul_inverse_eq_zero, smul_zero]
  · rw [smul_mul_assoc, hEv.inverse_mul_eq_zero, smul_zero]

/-- **The explicit Riesz–Coleman projector on a model space.** Let `u` be a row-compact
endomorphism of `C₀(I, R)` whose Fredholm series factors as `H_u = Q * S`, where `Q : R[X]` has
invertible leading coefficient, `S` is entire, and `Q` and `S` are coprime in `IsEntire.subring R`.
Then `u.rieszColemanProjection Q` is a Riesz–Coleman projection of `u` for `Q`. No normalization
on `Q.coeff 0` is required. -/
theorem IsRowCompact.isRieszColemanProjection_rieszColemanProjection
    {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact) {Q : R[X]} {S : R⟦X⟧}
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    IsRieszColemanProjection u Q (u.rieszColemanProjection Q) := by
  obtain ⟨u₀, S₁, hS₁, hQ₁0, hQ₁, hfac₁, hcop₁⟩ :=
    exists_unit_smul_coeff_zero_eq_one u.matrixCoeff.constantCoeff_charPowerSeries hQ hS hfac hcop
  rw [← isRieszColemanProjection_units_smul_iff u₀, ← u.rieszColemanProjection_units_smul Q u₀]
  exact isRieszColemanProjection_rieszColemanProjection_of_coeff_zero
    hu hQ₁0 hQ₁ hS₁ hfac₁ hcop₁

/-- Under a coprime Fredholm factorization `H_u = Q * S` with `IsUnit Q.leadingCoeff`, the explicit
Riesz–Coleman projector is row compact. -/
theorem IsRowCompact.isRowCompact_rieszColemanProjection
    {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact) {Q : R[X]} {S : R⟦X⟧}
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (u.rieszColemanProjection Q).IsRowCompact :=
  (hu.isRieszColemanProjection_rieszColemanProjection hQ hS hfac hcop).isRowCompact hQ hu

/-- **Existence of the Riesz–Coleman projection on a model space.** Every coprime factorization
`H_u = Q * S` of the Fredholm series of a row-compact operator `u` on `C₀(I, R)` with
`IsUnit Q.leadingCoeff` admits a Riesz–Coleman projection for `Q`. -/
theorem IsRowCompact.exists_rieszColemanProjection
    {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact) {Q : R[X]} {S : R⟦X⟧}
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    ∃ E, IsRieszColemanProjection u Q E :=
  ⟨u.rieszColemanProjection Q,
    hu.isRieszColemanProjection_rieszColemanProjection hQ hS hfac hcop⟩

/-- Every Riesz–Coleman projection of a row-compact `u` on `C₀(I, R)` for a coprime factor `Q` of
`H_u` with `IsUnit Q.leadingCoeff` coincides with the explicit projector
`u.rieszColemanProjection Q`. -/
theorem IsRieszColemanProjection.eq_rieszColemanProjection
    {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]} {S : R⟦X⟧}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact)
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    E = u.rieszColemanProjection Q :=
  hE.unique (hu.isRieszColemanProjection_rieszColemanProjection hQ hS hfac hcop)

/-- **Constant stalk rank of the Riesz–Coleman summand.** Under a coprime factorization
`H_u = Q * S` with `IsUnit Q.leadingCoeff`, the finite projective module `range E` has rank
`Q.natDegree` at every point of `Spec R`. No normalization on `Q.coeff 0` is needed. -/
theorem IsRieszColemanProjection.rankAtStalk_range
    {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]} {S : R⟦X⟧}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact)
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩)
    (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) E.range p = Q.natDegree := by
  have hEq := hE.eq_rieszColemanProjection hu hQ hS hfac hcop
  subst hEq
  have hB0 : (1 - C (Ring.inverse Q.leadingCoeff) * Q.reverse).coeff 0 = 0 :=
    coeff_zero_one_sub_C_mul_reverse (Ring.inverse_mul_cancel _ hQ)
  have hv := hu.aeval hB0
  have hGood := hu.isGoodZero_charPowerSeries_aeval_one_sub_C_mul_reverse hQ hS hfac hcop
  exact (hv.isRieszProjection_rieszProjection (fun _ ↦ hGood.evalAt_hasseDeriv_eq_zero)
    hGood.isUnit_evalAt_hasseDeriv).rankAtStalk_range hv hGood p

/-- Under a coprime factorization `H_u = Q * S` with `IsUnit Q.leadingCoeff`, the polynomial kernel
`ker Q*(u)` has rank `Q.natDegree` at every point of `Spec R`. -/
theorem IsRieszColemanProjection.rankAtStalk_ker_aeval_reverse
    {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]} {S : R⟦X⟧}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact)
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩)
    (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R)
      (LinearMap.ker (Polynomial.aeval u Q.reverse : C₀(I, R) →ₗ[R] C₀(I, R))) p =
      Q.natDegree := by
  rw [← hE.range_eq_ker]
  exact hE.rankAtStalk_range hu hQ hS hfac hcop p

/-- **Reversed characteristic polynomial on the Riesz–Coleman summand.** When `Q.coeff 0 = 1`, the
reversed characteristic polynomial `det (1 - X u|_{range E})` on the finite projective summand
`range E` is literally `Q`. -/
theorem IsRieszColemanProjection.projectiveCharpolyRev_restrict_range
    {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]} {S : R⟦X⟧}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact)
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
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

/-- **Fredholm series of the finite Riesz–Coleman summand.** When `Q.coeff 0 = 1`, the Fredholm
series of `u * E` is `(Q : R⟦X⟧)`. -/
theorem IsRieszColemanProjection.charPowerSeries_matrixCoeff_mul_eq
    {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]} {S : R⟦X⟧}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact)
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (u * E).matrixCoeff.charPowerSeries = (Q : R⟦X⟧) :=
  (projectiveCharpolyRev_and_charPowerSeries_of_rankAtStalk_le hu hQ0 hQ hS hfac
    hE.isIdempotentElem hE.commute (hE.isRowCompact hQ hu) hE.mapsTo_range
    (fun p ↦ (hE.rankAtStalk_range hu hQ hS hfac hcop p).le)
    (hE.isCoprime_charPowerSeries_matrixCoeff_complement hQ hu)).2.1

/-- **Fredholm series of the complementary Riesz–Coleman summand.** When `Q.coeff 0 = 1`, the
Fredholm series of `u * (1 - E)` is `S`. -/
theorem IsRieszColemanProjection.charPowerSeries_matrixCoeff_mul_one_sub_eq
    {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : R[X]} {S : R⟦X⟧}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact)
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
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

/-- Over a complete ultrametric field, the range of a Riesz–Coleman projection associated to a
coprime factorization `H_u = Q * S` has dimension `Q.natDegree` (`Q ≠ 0` is automatic from
`H_u(0) = 1`). -/
theorem IsRieszColemanProjection.finrank_range
    {u E : C₀(I, K) →L[K] C₀(I, K)} {Q : K[X]} {S : K⟦X⟧}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact) (hS : S.IsEntire)
    (hfac : u.matrixCoeff.charPowerSeries = (Q : K⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring K)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    Module.finrank K E.range = Q.natDegree := by
  have hQ : IsUnit Q.leadingCoeff := by
    refine (leadingCoeff_ne_zero.mpr ?_).isUnit
    rintro rfl
    have hc := congrArg (PowerSeries.constantCoeff (R := K)) hfac
    simp [u.matrixCoeff.constantCoeff_charPowerSeries] at hc
  have hr := hE.rankAtStalk_range hu hQ hS hfac hcop ⟨⊥, Ideal.isPrime_bot⟩
  let : AddCommGroup E.range := inferInstance
  rwa [Module.rankAtStalk_eq_finrank_of_free] at hr

/-- Over a complete ultrametric field, the polynomial kernel `ker Q*(u)` associated to a coprime
factorization `H_u = Q * S` has dimension `Q.natDegree`. -/
theorem IsRieszColemanProjection.finrank_ker_aeval_reverse
    {u E : C₀(I, K) →L[K] C₀(I, K)} {Q : K[X]} {S : K⟦X⟧}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact) (hS : S.IsEntire)
    (hfac : u.matrixCoeff.charPowerSeries = (Q : K⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring K)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    Module.finrank K
      (LinearMap.ker (Polynomial.aeval u Q.reverse : C₀(I, K) →ₗ[K] C₀(I, K))) =
      Q.natDegree := by
  rw [← hE.range_eq_ker]
  exact hE.finrank_range hu hS hfac hcop

end Field

end ContinuousLinearMap
