/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszColeman.Basic
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszProjection.Multiplicity
public import TauCeti.Analysis.Polynomial.Coleman.Coprime
import TauCeti.Analysis.Normed.Operator.Nonarchimedean.Coleman
import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszProjection.Intertwining
import TauCeti.RingTheory.Idempotents.Polynomial
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.IdempotentRange
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Intertwining

/-!
# Riesz–Coleman decomposition on model spaces `C₀(I, R)`

Let `R` be a complete ultrametric normed commutative ring with Tate scalars, and let `u` be a
row-compact endomorphism of a model space `C₀(I, R)` whose Fredholm series admits a coprime
factorisation `H_u = Q * S` in the ring of entire series, where `Q` is a polynomial with invertible
leading coefficient and `S` is entire. Because `H_u(0) = 1`, the constant coefficient `Q(0)` is
automatically a unit, so rescaling by `S(0)` reduces to the normalised case `Q(0) = 1` and covers
both normalised and monic polynomial factors.

In the normalised case `Q(0) = 1`, writing `c` for the inverse of `Q.leadingCoeff` and
`B = 1 - c Q*`, we have `B(0) = 0`, so `v = B(u)` is row compact and polynomial spectral mapping
gives `H_v = (1 - T) ^ deg Q * D(B, S)`. Coprimality of `Q` and `S` implies that `D(B, S)(1)` is a
unit, so `1` is a good zero of `H_v` of order `deg Q`. Its Riesz projector `E` has constant stalk
rank `deg Q`, its complementary Fredholm factor `T = H_{u (1 - E)}` is coprime to `Q`, and
comparing `H_{u E} * T = Q * S` via reduction modulo the monic polynomial `c Q` identifies the
finite factor `H_{u E}` with `Q` and the complementary factor `T` with `S`. Cayley–Hamilton on
the finite projective module `range E`, combined with invertibility of `u` on `range E`, refines
nilpotence of `Q*(u)` on `range E` to `Q*(u) * E = 0`. No scalar division by a nonunit,
Noetherian hypothesis, or global basis of `range E` is used.

## Main results

* `ContinuousLinearMap.IsRieszColemanProjection.isRowCompact`,
  `ContinuousLinearMap.IsRieszColemanProjection.finite_range`,
  `ContinuousLinearMap.IsRieszColemanProjection.projective_range`,
  `ContinuousLinearMap.IsRieszColemanProjection.finite_ker_aeval_reverse`,
  `ContinuousLinearMap.IsRieszColemanProjection.projective_ker_aeval_reverse`: every Riesz–Coleman
  projection of a row-compact operator, for `Q` with unit leading coefficient, is row compact, so
  `range E = ker Q*(u)` is finitely generated and projective.
* `ContinuousLinearMap.IsRowCompact.exists_rieszColemanProjection`: existence of the Riesz–Coleman
  projector on `C₀(I, R)` for a coprime factorisation `H_u = Q * S`.
* `ContinuousLinearMap.IsRieszColemanProjection.rankAtStalk_range`,
  `ContinuousLinearMap.IsRowCompact.rankAtStalk_ker_aeval_reverse`: constant rank `deg Q` of
  `range E = ker Q*(u)` on `Spec R`.
* `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_matrixCoeff_mul`,
  `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_matrixCoeff_mul_one_sub`: when
  `Q(0) = 1`, the Fredholm factors of `u * E` and `u * (1 - E)` are `Q` and `S`.
* `ContinuousLinearMap.IsRieszColemanProjection.finrank_range`,
  `ContinuousLinearMap.IsRowCompact.finrank_ker_aeval_reverse`: over a complete ultrametric field,
  `ker Q*(u)` has dimension `deg Q`.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127** (1997),
  417–479, Appendix A4.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.2.
* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §7.
-/

public section

open scoped ZeroAtInfty TauCeti.RingOpNorm PowerSeries
open PowerSeries (IsEntire)

namespace ContinuousLinearMap

section ModelSpace

variable {I R : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [NormedCommRing R] [IsUltrametricDist R] [TauCeti.NormedRing.IsTate R]

/-- Every Riesz–Coleman projection of a row-compact operator, for a polynomial `Q` with invertible
leading coefficient, is row compact. -/
theorem IsRieszColemanProjection.isRowCompact {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : Polynomial R}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact) (hQ : IsUnit Q.leadingCoeff) :
    E.IsRowCompact := by
  rw [← hE.mul_aeval_divX_mul_eq hQ]
  simpa only [mul_def] using (hu.comp_clm _).comp_clm E

variable [CompleteSpace R]

/-- The range of a Riesz–Coleman projection of a row-compact operator is finitely generated. -/
theorem IsRieszColemanProjection.finite_range {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : Polynomial R}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact) (hQ : IsUnit Q.leadingCoeff) :
    Module.Finite R E.range :=
  (hE.isRowCompact hu hQ).finite_range_of_isIdempotentElem hE.isIdempotentElem

/-- The range of a Riesz–Coleman projection of a row-compact operator is projective. -/
theorem IsRieszColemanProjection.projective_range {u E : C₀(I, R) →L[R] C₀(I, R)}
    {Q : Polynomial R} (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact)
    (hQ : IsUnit Q.leadingCoeff) : Module.Projective R E.range :=
  (hE.isRowCompact hu hQ).projective_range_of_isIdempotentElem hE.isIdempotentElem

/-- The kernel of `Q*(u)` for a row-compact operator admitting a Riesz–Coleman projection is
finitely generated. -/
theorem IsRieszColemanProjection.finite_ker_aeval_reverse {u E : C₀(I, R) →L[R] C₀(I, R)}
    {Q : Polynomial R} (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact)
    (hQ : IsUnit Q.leadingCoeff) :
    Module.Finite R
      (LinearMap.ker ((Polynomial.aeval u Q.reverse : C₀(I, R) →L[R] C₀(I, R)) :
        C₀(I, R) →ₗ[R] C₀(I, R))) := by
  rw [← hE.range_eq_ker]
  exact hE.finite_range hu hQ

/-- The kernel of `Q*(u)` for a row-compact operator admitting a Riesz–Coleman projection is
projective over the coefficient ring. -/
theorem IsRieszColemanProjection.projective_ker_aeval_reverse {u E : C₀(I, R) →L[R] C₀(I, R)}
    {Q : Polynomial R} (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact)
    (hQ : IsUnit Q.leadingCoeff) :
    Module.Projective R
      (LinearMap.ker ((Polynomial.aeval u Q.reverse : C₀(I, R) →L[R] C₀(I, R)) :
        C₀(I, R) →ₗ[R] C₀(I, R))) := by
  rw [← hE.range_eq_ker]
  exact hE.projective_range hu hQ

/-- When `H_u = Q * S` is a coprime factorisation with `Q(0) = 1` and `c * lc(Q) = 1`, the
Fredholm series of `B(u)` for `B = 1 - c Q*` has a good zero at `1` of order `deg Q`. -/
private theorem isGoodZero_charPowerSeries_aeval_one_sub_C_mul_reverse
    {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact) {Q : Polynomial R} {S : R⟦X⟧} {c : R}
    (hH : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S) (hQ0 : Q.coeff 0 = 1)
    (hc : c * Q.leadingCoeff = 1) (hS : S.IsEntire)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (Polynomial.aeval u (1 - Polynomial.C c * Q.reverse)).matrixCoeff.charPowerSeries.IsGoodZero
      1 Q.natDegree := by
  set B : Polynomial R := 1 - Polynomial.C c * Q.reverse
  have hB0 : B.coeff 0 = 0 := Polynomial.coeff_zero_one_sub_C_mul_reverse hc
  have hS0 : PowerSeries.constantCoeff S = 1 := by
    have := congrArg PowerSeries.constantCoeff hH
    simpa [hQ0] using this.symm
  have hS0' : PowerSeries.coeff 0 S = 1 := by
    rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have hBS_ent : (B.colemanDSeries S).IsEntire := by
    rw [← PowerSeries.colemanDEntire_coe (F := S) hB0 hS0']
    exact PowerSeries.isEntire_colemanDEntire (PowerSeries.isEntire_coe B) hS
      (by rwa [Polynomial.coeff_coe]) hS0'
  have hBS_unit : IsUnit ((B.colemanDSeries S).evalAt (1 : R)) :=
    (Polynomial.isUnit_evalAt_one_colemanDSeries_one_sub_C_mul_reverse_iff hc hS hS0).2 hcop
  have hHv : (Polynomial.aeval u B).matrixCoeff.charPowerSeries =
      (PowerSeries.X - PowerSeries.C (1 : R)) ^ Q.natDegree *
        (PowerSeries.C ((-1 : R) ^ Q.natDegree) * B.colemanDSeries S) := by
    rw [hu.charPowerSeries_matrixCoeff_aeval hB0, hH, Polynomial.colemanDSeries_mul hB0,
      Polynomial.colemanDSeries_one_sub_C_mul_reverse_self hQ0 hc]
    have hpow : (1 - PowerSeries.X : R⟦X⟧) ^ Q.natDegree =
        (PowerSeries.X - PowerSeries.C (1 : R)) ^ Q.natDegree *
          PowerSeries.C ((-1 : R) ^ Q.natDegree) := by
      rw [map_pow, ← mul_pow, map_neg, map_one, mul_neg_one, neg_sub]
    rw [hpow, mul_assoc]
  rw [hHv]
  have hG_ent : (PowerSeries.C ((-1 : R) ^ Q.natDegree) * B.colemanDSeries S).IsEntire :=
    (PowerSeries.isEntire_C _).mul hBS_ent
  refine (hG_ent.isGoodZero_X_sub_C_pow_mul_iff (a := 1) (h := Q.natDegree)).2 ?_
  rw [(PowerSeries.isEntire_C _).evalAt_mul hBS_ent, PowerSeries.evalAt_C]
  exact (isUnit_neg_one.pow Q.natDegree).mul hBS_unit

/-- In the coprime factorisation `P * T = Q * S` of entire series, if `P` has constant term `1`,
degree at most `deg Q`, and `Q` is coprime to `T`, then `P = Q` and `T = S`. -/
private theorem eq_of_mul_eq_mul_of_isCoprime {P Q : Polynomial R} {S T : R⟦X⟧} {c : R}
    (hPT : (P : R⟦X⟧) * T = (Q : R⟦X⟧) * S) (hP0 : P.coeff 0 = 1) (hQ0 : Q.coeff 0 = 1)
    (hc : c * Q.leadingCoeff = 1) (hPdeg : P.natDegree ≤ Q.natDegree)
    (hS : S.IsEntire) (hT : T.IsEntire)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨T, IsEntire.mem_subring.mpr hT⟩) :
    P = Q ∧ T = S := by
  have hPQ : P = Q := by
    nontriviality R
    let Pe : IsEntire.subring R := ⟨P, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe P)⟩
    let Se : IsEntire.subring R := ⟨S, IsEntire.mem_subring.mpr hS⟩
    obtain ⟨G, hG⟩ := hcop.dvd_of_dvd_mul_right (y := Pe) ⟨Se, Subtype.ext hPT⟩
    set Q₁ : Polynomial R := Polynomial.C c * Q
    have hQ₁_monic : Q₁.Monic := Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one hc
    have hQ₁_deg : Q₁.natDegree = Q.natDegree :=
      Polynomial.natDegree_C_mul_eq_of_mul_eq_one (by rw [mul_comm]; exact hc)
    have hQ₁_dvd_Q : Q₁ ∣ Q := ⟨Polynomial.C Q.leadingCoeff, by
      rw [mul_comm, ← mul_assoc, ← Polynomial.C_mul, mul_comm Q.leadingCoeff c, hc,
        Polynomial.C_1, one_mul]⟩
    have hmkP : AdjoinRoot.mk Q₁ P = 0 := by
      have hmk := congrArg (IsEntire.mkAdjoinRoot hQ₁_monic) hG
      rw [map_mul, IsEntire.mkAdjoinRoot_coe, IsEntire.mkAdjoinRoot_coe,
        AdjoinRoot.mk_eq_zero.2 hQ₁_dvd_Q, zero_mul] at hmk
      exact hmk
    obtain ⟨D, hD⟩ := AdjoinRoot.mk_eq_zero.1 hmkP
    have hDne : D ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hD
      simp [hD] at hP0
    have hdegP : P.natDegree = Q.natDegree + D.natDegree := by
      rw [hD, hQ₁_monic.natDegree_mul' hDne, hQ₁_deg]
    have hDdeg : D.natDegree = 0 := by omega
    have hDC : D = Polynomial.C (D.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hDdeg
    have hPeq : P = Polynomial.C (c * D.coeff 0) * Q := by
      calc P = Polynomial.C c * Q * Polynomial.C (D.coeff 0) := by rw [hD, ← hDC]
        _ = Polynomial.C (c * D.coeff 0) * Q := by rw [Polynomial.C_mul]; ring
    have hcD : c * D.coeff 0 = 1 := by
      have := congrArg (fun f : Polynomial R ↦ f.coeff 0) hPeq
      simpa [hP0, hQ0] using this.symm
    rw [hPeq, hcD, Polynomial.C_1, one_mul]
  refine ⟨hPQ, ?_⟩
  have hQunit : IsUnit (Q : R⟦X⟧) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    simp [hQ0]
  exact hQunit.mul_left_cancel (hPQ ▸ hPT)

/-- Restricting a row-compact `u` to the range of a commuting row-compact idempotent `E` produces
a finite projective endomorphism whose reversed characteristic polynomial is the Fredholm factor
`H_{u E}`. -/
private theorem exists_projectiveCharpolyRev_eq_charPowerSeries_mul
    {u E : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact) (hE : E.IsRowCompact)
    (hE_idem : IsIdempotentElem E) (huE : Commute u E) :
    letI : AddCommGroup E.range := inferInstance
    ∃ (_ : Module.Finite R E.range) (_ : Module.Projective R E.range) (f : Module.End R E.range),
      (∀ x : E.range, (f x : C₀(I, R)) = u x) ∧
      (u * E).matrixCoeff.charPowerSeries = (f.projectiveCharpolyRev : R⟦X⟧) := by
  -- Fix the additive group before forming endomorphisms of the range, matching
  -- `IsRieszProjection.exists_charPowerSeries_eq_projectiveCharpolyRev`.
  let : AddCommGroup E.range := inferInstance
  have := hE.finite_range_of_isIdempotentElem hE_idem
  have := hE.projective_range_of_isIdempotentElem hE_idem
  have hmaps : Set.MapsTo u E.range E.range := by
    rw [LinearMap.coe_range, coe_coe]
    exact Function.Semiconj.mapsTo_range fun x ↦ congr($(huE.eq.symm) x)
  let uE : E.range →L[R] E.range := u.restrict hmaps
  have hfix (x : E.range) : E x = x :=
    ContinuousLinearMap.IsIdempotentElem.apply_coe_range hE_idem x
  have hri : E.rangeRestrict.comp E.range.subtypeL = .id R E.range :=
    ext fun x ↦ Subtype.ext (hfix x)
  have hM : TauCeti.HasPr R E.range :=
    (isPrCompact_iff_isRowCompact.2 hu).hasPr_source.of_retract
      E.range.subtypeL E.rangeRestrict hri
  have huE_pr := isPrCompact_of_finite (R := R) (M := E.range) (L := E.range) hM hM uE
  refine ⟨inferInstance, inferInstance, uE.toLinearMap, fun _ ↦ rfl, ?_⟩
  have hext : E.range.subtypeL.comp (uE.comp E.rangeRestrict) = u * E := by
    ext x
    rfl
  have hchar := charPowerSeries_eq_projectiveCharpolyRev (R := R) (M := E.range) hM uE
  rw [← hext, ← huE_pr.charPowerSeries_eq hri, hchar]

omit [DiscreteTopology I] [DecidableEq I] [CompleteSpace R] in
/-- Refining nilpotence on `range E` to `Q*(u) * E = 0`: if `E` is the Riesz projection at `1` of
order `deg Q` for `B(u)` (where `B = 1 - c Q*` has zero constant term) and the restriction `f` of
`u` to the finite projective summand `range E` has reversed characteristic polynomial `Q`, then `f`
is invertible and Cayley–Hamilton gives `Q*(u) * E = 0`. -/
private theorem aeval_reverse_mul_eq_zero_of_projectiveCharpolyRev
    {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : Polynomial R} {c : R}
    (hB0 : (1 - Polynomial.C c * Q.reverse).coeff 0 = 0)
    (hEv : IsRieszProjection (Polynomial.aeval u (1 - Polynomial.C c * Q.reverse))
      1 Q.natDegree E) :
    letI : AddCommGroup E.range := inferInstance
    ∀ [Module.Finite R E.range] [Module.Projective R E.range]
      (f : Module.End R E.range), (∀ x : E.range, (f x : C₀(I, R)) = u x) →
      f.projectiveCharpolyRev = Q →
      Polynomial.aeval u Q.reverse * E = 0 := by
  let : AddCommGroup E.range := inferInstance
  intro _ _ f hf_eq hPQ
  set B : Polynomial R := 1 - Polynomial.C c * Q.reverse
  set v : C₀(I, R) →L[R] C₀(I, R) := Polynomial.aeval u B
  have hfix (x : E.range) : E x = x :=
    ContinuousLinearMap.IsIdempotentElem.apply_coe_range hEv.isIdempotentElem x
  have hsub_f : E.range.subtype ∘ₗ f = u.toLinearMap ∘ₗ E.range.subtype :=
    LinearMap.ext hf_eq
  have hsub_aeval (p : Polynomial R) (x : E.range) :
      ((Polynomial.aeval f p x : E.range) : C₀(I, R)) = Polynomial.aeval u p x := by
    have h := congr($(Module.End.aeval_comp_of_comp_eq hsub_f.symm p) x)
    simpa only [LinearMap.comp_apply, Submodule.coe_subtype, ← toLinearMap_aeval, coe_coe] using
      h.symm
  have hnil : IsNilpotent (1 - Polynomial.aeval f B) := by
    refine ⟨Q.natDegree, LinearMap.ext fun x ↦ Subtype.ext ?_⟩
    have h1 : E.range.subtype ∘ₗ (1 - Polynomial.aeval f B) =
        (1 - (1 : R) • v : C₀(I, R) →L[R] C₀(I, R)).toLinearMap ∘ₗ E.range.subtype :=
      LinearMap.ext fun y ↦ by
        simp only [LinearMap.comp_apply, Submodule.coe_subtype, LinearMap.sub_apply,
          one_apply_eq_self, AddSubgroupClass.coe_sub, hsub_aeval, toLinearMap_sub,
          toLinearMap_one, one_smul, coe_coe, v]
    have hpow := Module.End.aeval_comp_of_comp_eq h1.symm (Polynomial.X ^ Q.natDegree)
    simp only [map_pow, Polynomial.aeval_X, ← toLinearMap_pow] at hpow
    have hx : (((1 - Polynomial.aeval f B) ^ Q.natDegree) x : C₀(I, R)) =
        ((1 - (1 : R) • v) ^ Q.natDegree) x := by
      simpa only [LinearMap.comp_apply, Submodule.coe_subtype, coe_coe] using congr($hpow x).symm
    have hz : ((1 - (1 : R) • v) ^ Q.natDegree) (x : C₀(I, R)) = 0 := by
      simpa only [mul_apply_eq_comp, hfix, zero_apply] using
        congr($(hEv.pow_mul_eq_zero) (x : C₀(I, R)))
    exact hx.trans hz
  have hf_unit : IsUnit f := by
    have hBf_unit : IsUnit (Polynomial.aeval f B) := by
      simpa only [sub_sub_cancel] using hnil.isUnit_one_sub
    have hXB : Polynomial.X * B.divX = B := by
      simpa only [hB0, map_zero, add_zero] using Polynomial.X_mul_divX_add B
    have hcomm : Commute f (Polynomial.aeval f B.divX) := by
      simpa only [Polynomial.aeval_X] using
        (Commute.all Polynomial.X B.divX).map (Polynomial.aeval f)
    have hmul : f * Polynomial.aeval f B.divX = Polynomial.aeval f B := by
      simpa only [map_mul, Polynomial.aeval_X] using congrArg (Polynomial.aeval f) hXB
    exact (hcomm.isUnit_mul_iff.1 (hmul.symm ▸ hBf_unit)).1
  have hQf : Polynomial.aeval f Q.reverse = 0 := by
    obtain ⟨n, hn, hCH⟩ := f.exists_aeval_reflect_projectiveCharpolyRev_eq_zero
    rw [hPQ] at hn hCH
    have href : Q.reflect n = Polynomial.X ^ (n - Q.natDegree) * Q.reverse := by
      conv_lhs => rw [← one_mul Q, ← Nat.sub_add_cancel hn]
      rw [Polynomial.reflect_mul 1 Q (by simp) le_rfl, Polynomial.reflect_one, Polynomial.reverse]
    rw [href, map_mul, map_pow, Polynomial.aeval_X] at hCH
    exact ((hf_unit.pow (n - Q.natDegree)).mul_right_eq_zero).1 hCH
  ext x : 1
  have := congrArg Subtype.val (congr($hQf ⟨E x, ⟨x, rfl⟩⟩))
  simpa only [mul_apply_eq_comp, zero_apply, hsub_aeval, LinearMap.zero_apply,
    ZeroMemClass.coe_zero] using this

/-- Construction of the Riesz–Coleman projector on a model space `C₀(I, R)` for normalised
`Q(0) = 1`, together with its constant stalk rank and the identification of both Fredholm
factors. -/
private theorem exists_rieszColemanProjection_model {u : C₀(I, R) →L[R] C₀(I, R)}
    (hu : u.IsRowCompact) {Q : Polynomial R} {S : R⟦X⟧}
    (hH : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S) (hQ0 : Q.coeff 0 = 1)
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    ∃ E : C₀(I, R) →L[R] C₀(I, R), IsRieszColemanProjection u Q E ∧
      (∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) E.range p = Q.natDegree) ∧
      (u * E).matrixCoeff.charPowerSeries = (Q : R⟦X⟧) ∧
      (u * (1 - E)).matrixCoeff.charPowerSeries = S := by
  set c := Ring.inverse Q.leadingCoeff
  have hc : c * Q.leadingCoeff = 1 := Ring.inverse_mul_cancel _ hQ
  set B : Polynomial R := 1 - Polynomial.C c * Q.reverse
  have hB0 : B.coeff 0 = 0 := Polynomial.coeff_zero_one_sub_C_mul_reverse hc
  set v : C₀(I, R) →L[R] C₀(I, R) := Polynomial.aeval u B
  have hv : v.IsRowCompact := hu.aeval hB0
  have hHv_good : v.matrixCoeff.charPowerSeries.IsGoodZero 1 Q.natDegree :=
    isGoodZero_charPowerSeries_aeval_one_sub_C_mul_reverse hu hH hQ0 hc hS hcop
  set E : C₀(I, R) →L[R] C₀(I, R) := v.rieszProjection 1 Q.natDegree
  have hEv : IsRieszProjection v 1 Q.natDegree E :=
    hv.isRieszProjection_rieszProjection
      (fun _ ↦ hHv_good.evalAt_hasseDeriv_eq_zero) hHv_good.isUnit_evalAt_hasseDeriv
  have huv : Commute u v := by
    simpa only [Polynomial.aeval_X] using (Commute.all Polynomial.X B).map (Polynomial.aeval u)
  have huE : Commute u E := hEv.commute_of_commute huv
  have hsub_cl : closure (Algebra.adjoin R {v} : Set (C₀(I, R) →L[R] C₀(I, R))) ⊆
      closure (Algebra.adjoin R {u} : Set (C₀(I, R) →L[R] C₀(I, R))) := by
    refine closure_mono (SetLike.coe_subset_coe.mpr (Algebra.adjoin_le ?_))
    rw [Set.singleton_subset_iff, SetLike.mem_coe, Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨B, rfl⟩
  have hrank (p : PrimeSpectrum R) : Module.rankAtStalk (R := R) E.range p = Q.natDegree :=
    hEv.rankAtStalk_range hv hHv_good p
  let : AddCommGroup E.range := inferInstance
  obtain ⟨_, _, f, hf_eq, hP_char⟩ := exists_projectiveCharpolyRev_eq_charPowerSeries_mul
    hu (hEv.isRowCompact hv) hEv.isIdempotentElem huE
  set T : R⟦X⟧ := (u * (1 - E)).matrixCoeff.charPowerSeries
  have hcomp : (u * (1 - E)).IsRowCompact := hu.comp_clm (1 - E)
  have hcop_QT : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨T, IsEntire.mem_subring.mpr hcomp.isEntire_charPowerSeries⟩ := by
    have hue : Commute u (1 - E) :=
      (Commute.one_right u).sub_right (R := C₀(I, R) →L[R] C₀(I, R)) huE
    have h1E : IsIdempotentElem (1 - E) :=
      IsIdempotentElem.one_sub (R := C₀(I, R) →L[R] C₀(I, R)) hEv.isIdempotentElem
    have hBv : Polynomial.aeval (u * (1 - E)) B = v * (1 - E) :=
      IsIdempotentElem.aeval_mul_of_commute h1E hue hB0
    rw [← Polynomial.isUnit_evalAt_one_colemanDSeries_one_sub_C_mul_reverse_iff hc
      hcomp.isEntire_charPowerSeries (Matrix.constantCoeff_charPowerSeries _),
      ← hcomp.charPowerSeries_matrixCoeff_aeval hB0, hBv]
    exact hEv.isUnit_evalAt_charPowerSeries_complement hv
  have hPT : (f.projectiveCharpolyRev : R⟦X⟧) * T = (Q : R⟦X⟧) * S := by
    rw [← hP_char, ← hu.charPowerSeries_matrixCoeff_eq_mul_of_commute hEv.isIdempotentElem huE, hH]
  have ⟨hPQ, hTS⟩ := eq_of_mul_eq_mul_of_isCoprime hPT
    (LinearMap.coeff_projectiveCharpolyRev_zero f) hQ0 hc
    (f.natDegree_projectiveCharpolyRev_le fun p ↦ (hrank p).le) hS
    hcomp.isEntire_charPowerSeries hcop_QT
  have hQE : Polynomial.aeval u Q.reverse * E = 0 :=
    aeval_reverse_mul_eq_zero_of_projectiveCharpolyRev hB0 hEv f hf_eq hPQ
  -- Scale the complementary inverse of `1 - v = c • Q*(u)` by `c` to invert `Q*(u)` on `ker E`.
  have h1v : (1 - (1 : R) • v : C₀(I, R) →L[R] C₀(I, R)) = c • Polynomial.aeval u Q.reverse := by
    simp only [v, B, one_smul, map_sub, map_one, map_mul, Polynomial.aeval_C, sub_sub_cancel,
      ← Algebra.smul_def]
  have : IsTopologicalSemiring (C₀(I, R) →L[R] C₀(I, R)) := inferInstance
  set Cl := (Algebra.adjoin R {u}).topologicalClosure
  have hw_mem : c • hEv.inverse ∈
      closure (Algebra.adjoin R {u} : Set (C₀(I, R) →L[R] C₀(I, R))) := by
    have hmem : hEv.inverse ∈ Cl := by
      rw [← SetLike.mem_coe, Subalgebra.topologicalClosure_coe]
      exact hsub_cl hEv.inverse_mem_closure_adjoin
    have hsmul : c • hEv.inverse ∈ Cl := Cl.smul_mem hmem c
    rwa [← SetLike.mem_coe, Subalgebra.topologicalClosure_coe] at hsmul
  refine ⟨E, ⟨hEv.isIdempotentElem, huE, hsub_cl hEv.mem_closure_adjoin, hQE,
    c • hEv.inverse, ?_, ?_, ?_, ?_, hw_mem⟩, hrank, hP_char.trans (by rw [hPQ]), hTS⟩
  · rw [mul_smul_comm, ← smul_mul_assoc, ← h1v, hEv.one_sub_smul_mul_inverse]
  · rw [smul_mul_assoc, ← mul_smul_comm, ← h1v, hEv.inverse_mul_one_sub_smul]
  · rw [mul_smul_comm, hEv.mul_inverse_eq_zero, smul_zero]
  · rw [smul_mul_assoc, hEv.inverse_mul_eq_zero, smul_zero]

/-- Rescaling a general coprime factorisation `H_u = Q * S` to the normalised case `Q₁(0) = 1`:
since `H_u(0) = 1`, the constant coefficient `Q(0)` is automatically a unit with inverse `S(0)`. -/
private theorem exists_rieszColemanProjection_and_rank {u : C₀(I, R) →L[R] C₀(I, R)}
    (hu : u.IsRowCompact) {Q : Polynomial R} {S : R⟦X⟧}
    (hH : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S) (hQ : IsUnit Q.leadingCoeff)
    (hS : S.IsEntire)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    ∃ E : C₀(I, R) →L[R] C₀(I, R), IsRieszColemanProjection u Q E ∧
      (∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) E.range p = Q.natDegree) := by
  set a : R := Q.coeff 0
  set b : R := PowerSeries.constantCoeff S
  have hba : b * a = 1 := by
    have h0 := congrArg PowerSeries.constantCoeff hH
    simpa [a, b, mul_comm] using h0.symm
  have hbu : IsUnit b := IsUnit.of_mul_eq_one a hba
  set Q₁ : Polynomial R := Polynomial.C b * Q
  set S₁ : R⟦X⟧ := PowerSeries.C a * S
  have hQ₁0 : Q₁.coeff 0 = 1 := by simp [Q₁, hba, a]
  have hQ₁deg : Q₁.natDegree = Q.natDegree :=
    Polynomial.natDegree_C_mul_eq_of_mul_eq_one (by rw [mul_comm]; exact hba)
  have hQ₁lc : IsUnit Q₁.leadingCoeff := by
    have hlc : Q₁.leadingCoeff = b * Q.leadingCoeff := by
      rw [Polynomial.leadingCoeff, Polynomial.leadingCoeff, hQ₁deg, Polynomial.coeff_C_mul]
    rw [hlc]
    exact hbu.mul hQ
  have hS₁ : S₁.IsEntire := (PowerSeries.isEntire_C a).mul hS
  have hH₁ : u.matrixCoeff.charPowerSeries = (Q₁ : R⟦X⟧) * S₁ := by
    rw [hH]
    simp only [Q₁, S₁, Polynomial.coe_mul, Polynomial.coe_C]
    calc (Q : R⟦X⟧) * S = PowerSeries.C (b * a) * ((Q : R⟦X⟧) * S) := by rw [hba, map_one, one_mul]
      _ = PowerSeries.C b * (Q : R⟦X⟧) * (PowerSeries.C a * S) := by rw [map_mul]; ring
  have hcop₁ : IsCoprime
      (⟨Q₁, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q₁)⟩ : IsEntire.subring R)
      ⟨S₁, IsEntire.mem_subring.mpr hS₁⟩ := by
    obtain ⟨x, y, hxy⟩ := hcop
    refine ⟨⟨PowerSeries.C a, IsEntire.mem_subring.mpr (PowerSeries.isEntire_C a)⟩ * x,
      ⟨PowerSeries.C b, IsEntire.mem_subring.mpr (PowerSeries.isEntire_C b)⟩ * y, ?_⟩
    apply Subtype.ext
    have hxy' := congrArg Subtype.val hxy
    simp only [Subring.coe_add, Subring.coe_mul, OneMemClass.coe_one, Polynomial.coe_mul,
      Polynomial.coe_C, Q₁, S₁] at hxy' ⊢
    calc PowerSeries.C a * x.1 * (PowerSeries.C b * (Q : R⟦X⟧)) +
          PowerSeries.C b * y.1 * (PowerSeries.C a * S)
        = PowerSeries.C (b * a) * (x.1 * (Q : R⟦X⟧) + y.1 * S) := by rw [map_mul]; ring
      _ = 1 := by rw [hba, map_one, one_mul, hxy']
  obtain ⟨E, hE₁, hrank, -⟩ := exists_rieszColemanProjection_model hu hH₁ hQ₁0 hQ₁lc hS₁ hcop₁
  exact ⟨E, (IsRieszColemanProjection.iff_C_mul hbu).1 hE₁, fun p ↦ (hrank p).trans hQ₁deg⟩

/-- **Riesz–Coleman decomposition on a model space.** Let `u` be a row-compact endomorphism of
`C₀(I, R)` whose Fredholm series admits a coprime factorisation `H_u = Q * S` in the ring of
entire series, where `Q` is a polynomial with invertible leading coefficient and `S` is entire.
Then `u` has a Riesz–Coleman projection for `Q`. The factorisation forces `Q(0)` to be a unit, so
both normalised (`Q(0) = 1`) and monic polynomial factors are covered directly. -/
theorem IsRowCompact.exists_rieszColemanProjection {u : C₀(I, R) →L[R] C₀(I, R)}
    (hu : u.IsRowCompact) {Q : Polynomial R} {S : R⟦X⟧}
    (hH : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S) (hQ : IsUnit Q.leadingCoeff)
    (hS : S.IsEntire)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    ∃ E, IsRieszColemanProjection u Q E := by
  obtain ⟨E, hE, -⟩ := exists_rieszColemanProjection_and_rank hu hH hQ hS hcop
  exact ⟨E, hE⟩

/-- **Constant rank of the Riesz–Coleman summand.** For a coprime factorisation `H_u = Q * S` with
invertible leading coefficient of `Q`, the range of the Riesz–Coleman projection has rank `deg Q`
at every point of `Spec R`. -/
theorem IsRieszColemanProjection.rankAtStalk_range {u E : C₀(I, R) →L[R] C₀(I, R)}
    {Q : Polynomial R} {S : R⟦X⟧} (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact)
    (hH : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S) (hQ : IsUnit Q.leadingCoeff)
    (hS : S.IsEntire)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) E.range p = Q.natDegree := by
  obtain ⟨E', hE', hrank⟩ := exists_rieszColemanProjection_and_rank hu hH hQ hS hcop
  rw [hE.unique hE']
  exact hrank p

/-- For a coprime factorisation `H_u = Q * S` on `C₀(I, R)` with invertible leading coefficient of
`Q`, the kernel `ker Q*(u)` has constant rank `deg Q` on `Spec R`. -/
theorem IsRowCompact.rankAtStalk_ker_aeval_reverse {u : C₀(I, R) →L[R] C₀(I, R)}
    (hu : u.IsRowCompact) {Q : Polynomial R} {S : R⟦X⟧}
    (hH : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S) (hQ : IsUnit Q.leadingCoeff)
    (hS : S.IsEntire)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R)
      (LinearMap.ker ((Polynomial.aeval u Q.reverse : C₀(I, R) →L[R] C₀(I, R)) :
        C₀(I, R) →ₗ[R] C₀(I, R))) p = Q.natDegree := by
  obtain ⟨E, hE⟩ := hu.exists_rieszColemanProjection hH hQ hS hcop
  rw [← hE.range_eq_ker]
  exact hE.rankAtStalk_range hu hH hQ hS hcop p

/-- **Determinant on the finite Riesz–Coleman summand.** For a normalised coprime factorisation
`H_u = Q * S` with `Q(0) = 1`, the Fredholm series of `u * E` is the polynomial factor `Q`. -/
theorem IsRieszColemanProjection.charPowerSeries_matrixCoeff_mul {u E : C₀(I, R) →L[R] C₀(I, R)}
    {Q : Polynomial R} {S : R⟦X⟧} (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact)
    (hH : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S) (hQ0 : Q.coeff 0 = 1)
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (u * E).matrixCoeff.charPowerSeries = (Q : R⟦X⟧) := by
  obtain ⟨E', hE', -, hQ', -⟩ := exists_rieszColemanProjection_model hu hH hQ0 hQ hS hcop
  rw [hE.unique hE']
  exact hQ'

/-- **Determinant on the complementary Riesz–Coleman summand.** For a normalised coprime
factorisation `H_u = Q * S` with `Q(0) = 1`, the Fredholm series of `u * (1 - E)` is the entire
cofactor `S`. -/
theorem IsRieszColemanProjection.charPowerSeries_matrixCoeff_mul_one_sub
    {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : Polynomial R} {S : R⟦X⟧}
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact)
    (hH : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S) (hQ0 : Q.coeff 0 = 1)
    (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    (u * (1 - E)).matrixCoeff.charPowerSeries = S := by
  obtain ⟨E', hE', -, -, hS'⟩ := exists_rieszColemanProjection_model hu hH hQ0 hQ hS hcop
  rw [hE.unique hE']
  exact hS'

end ModelSpace

section Field

variable {I K : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {u E : C₀(I, K) →L[K] C₀(I, K)} {Q : Polynomial K} {S : K⟦X⟧}

/-- Over a complete ultrametric field, the range of a Riesz–Coleman projection has dimension
`deg Q`. -/
theorem IsRieszColemanProjection.finrank_range (hE : IsRieszColemanProjection u Q E)
    (hu : u.IsRowCompact) (hH : u.matrixCoeff.charPowerSeries = (Q : K⟦X⟧) * S)
    (hS : S.IsEntire)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring K)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    Module.finrank K E.range = Q.natDegree := by
  have hQne : Q ≠ 0 := by
    rintro rfl
    have h0 := congrArg PowerSeries.constantCoeff hH
    simp at h0
  have hQ : IsUnit Q.leadingCoeff := (Polynomial.leadingCoeff_ne_zero.2 hQne).isUnit
  have hr := hE.rankAtStalk_range hu hH hQ hS hcop ⟨⊥, Ideal.isPrime_bot⟩
  let : AddCommGroup E.range := inferInstance
  rw [Module.rankAtStalk_eq_finrank_of_free] at hr
  exact hr

/-- Over a complete ultrametric field, for a coprime factorisation `H_u = Q * S`, the kernel
`ker Q*(u)` has dimension `deg Q`. -/
theorem IsRowCompact.finrank_ker_aeval_reverse (hu : u.IsRowCompact)
    (hH : u.matrixCoeff.charPowerSeries = (Q : K⟦X⟧) * S) (hS : S.IsEntire)
    (hcop : IsCoprime
      (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring K)
      ⟨S, IsEntire.mem_subring.mpr hS⟩) :
    Module.finrank K
      (LinearMap.ker ((Polynomial.aeval u Q.reverse : C₀(I, K) →L[K] C₀(I, K)) :
        Module.End K C₀(I, K))) = Q.natDegree := by
  have hQne : Q ≠ 0 := by
    rintro rfl
    have h0 := congrArg PowerSeries.constantCoeff hH
    simp at h0
  have hQ : IsUnit Q.leadingCoeff := (Polynomial.leadingCoeff_ne_zero.2 hQne).isUnit
  obtain ⟨E, hE⟩ := hu.exists_rieszColemanProjection hH hQ hS hcop
  rw [← hE.range_eq_ker]
  exact hE.finrank_range hu hH hS hcop

end Field

end ContinuousLinearMap
