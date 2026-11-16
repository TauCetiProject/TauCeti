/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.CharPowerSeries
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszColeman.Basic
public import TauCeti.RingTheory.PowerSeries.Entire.Basic
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.RingTheory.Nilpotent.Basic
import TauCeti.Analysis.Normed.Operator.Nonarchimedean.BaseChange
import TauCeti.Analysis.Normed.Operator.Nonarchimedean.Coleman
import TauCeti.Analysis.Normed.Operator.Nonarchimedean.Idempotent
import TauCeti.Analysis.Normed.Operator.Nonarchimedean.PrModule.Basic
import TauCeti.Analysis.Normed.Operator.Nonarchimedean.PrModule.Coprime
import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszProjection.Basic
import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszProjection.Intertwining
import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszProjection.Multiplicity
import TauCeti.Analysis.Polynomial.Coleman.Coprime
import TauCeti.LinearAlgebra.Charpoly.Projective
import TauCeti.RingTheory.PowerSeries.Entire.Division
import TauCeti.RingTheory.PowerSeries.Entire.GoodZero

/-!
# Riesz–Coleman decomposition on model spaces

Let `R` be a complete ultrametric normed commutative ring with Tate scalars, `I` a discrete index
type, and `u : C₀(I, R) →L[R] C₀(I, R)` a row-compact endomorphism with Fredholm series
`H_u(T) = det (1 - T u)`. Suppose `H_u = Q * S`, where `Q ∈ R[T]` satisfies `Q(0) = 1` and has
invertible leading coefficient, `S ∈ R⟦T⟧` is entire, and `Q` and `S` are coprime in the ring of
entire series `PowerSeries.IsEntire.subring R`.

Then `u` admits a unique Riesz–Coleman projection `E` at `Q`
(`ContinuousLinearMap.IsRowCompact.exists_isRieszColemanProjection`), whose range `ker Q*(u)` is
finitely generated and projective of constant rank `Q.natDegree` over `Spec R`
(`ContinuousLinearMap.IsRieszColemanProjection.rankAtStalk_range`,
`ContinuousLinearMap.IsRowCompact.rankAtStalk_ker_aeval_reverse`), and whose two Fredholm factors
are `H_(u E) = Q` and `H_(u (1 - E)) = S`
(`ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_matrixCoeff_mul_eq`,
`ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_matrixCoeff_mul_one_sub_eq`). Over a
complete ultrametric field, the dimension of `ker Q*(u)` is `Q.natDegree`
(`ContinuousLinearMap.IsRowCompact.finrank_ker_aeval_reverse`).

The construction passes to `v = B(u)` for `B = 1 - lc(Q)⁻¹ Q*`. By Coleman's spectral mapping
theorem, `H_v = (1 - T) ^ deg Q * D(B, S)` has a good zero of order `deg Q` at `1`. Its Riesz
projection `E` has constant rank `deg Q`, commutes with `u`, and makes `Q*(u)` invertible on
`ker E` and nilpotent on `range E`. Invertibility of `u` on `range E` follows from that
nilpotence; coprimality of `Q` with `H_(u (1 - E))` forces `det (1 - T u|_{range E}) = Q` and
`H_(u (1 - E)) = S` via entire division; Cayley–Hamilton on the finite projective module `range E`
refines nilpotence to `Q*(u) * E = 0`. No Noetherianity, reducedness, or freeness is assumed, and
the case `Q = 1` (giving `E = 0` and rank zero) is included.

Under bounded coefficient extension on model spaces, the coprime factorisation persists, so the
rank (and over a field, the dimension) of `ker Q*(u)` is preserved
(`ContinuousLinearMap.IsRowCompact.rankAtStalk_ker_aeval_reverse_mapCoeffs`,
`ContinuousLinearMap.IsRowCompact.finrank_ker_aeval_reverse_mapCoeffs`).

## Main results

* `ContinuousLinearMap.IsRowCompact.exists_isRieszColemanProjection`: existence of the
  Riesz–Coleman projection on `C₀(I, R)` attached to a coprime polynomial factor of `H_u`.
* `ContinuousLinearMap.IsRieszColemanProjection.rankAtStalk_range`,
  `ContinuousLinearMap.IsRowCompact.rankAtStalk_ker_aeval_reverse`: constant rank `Q.natDegree`
  over `Spec R`.
* `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_matrixCoeff_mul_eq`,
  `ContinuousLinearMap.IsRieszColemanProjection.charPowerSeries_matrixCoeff_mul_one_sub_eq`:
  identification of the Fredholm series on the two summands.
* `ContinuousLinearMap.IsRieszColemanProjection.finrank_range`,
  `ContinuousLinearMap.IsRowCompact.finrank_ker_aeval_reverse`: over a field, `ker Q*(u)` has
  dimension `Q.natDegree`.
* `ContinuousLinearMap.IsRowCompact.rankAtStalk_ker_aeval_reverse_mapCoeffs`,
  `ContinuousLinearMap.IsRowCompact.finrank_ker_aeval_reverse_mapCoeffs`: invariance of rank and
  dimension under bounded base change.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127** (1997),
  417–479, Appendix A4.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  Algebra Number Theory **13** (2019), §2.2.
-/

public section

open Filter Topology
open scoped ZeroAtInfty NNReal PowerSeries TauCeti.RingOpNorm

namespace ContinuousLinearMap

section Helpers

/-- If `P` and `Q` are polynomials with constant term `1`, `Q` has unit leading coefficient,
`P.natDegree ≤ Q.natDegree`, `(P : R⟦X⟧) * F₂ = (Q : R⟦X⟧) * S` for entire `S` and `F₂`, and `Q`
is coprime to `F₂` in the ring of entire series, then `P = Q` and `F₂ = S`. -/
private theorem eq_of_coe_mul_eq_coe_mul_of_isCoprime
    {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R]
    {P Q : Polynomial R} {S F₂ : R⟦X⟧}
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff)
    (hP0 : P.coeff 0 = 1) (hPdeg : P.natDegree ≤ Q.natDegree)
    (hS : S.IsEntire) (hF₂ : F₂.IsEntire)
    (heq : (P : R⟦X⟧) * F₂ = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, PowerSeries.IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
        PowerSeries.IsEntire.subring R)
      ⟨F₂, PowerSeries.IsEntire.mem_subring.mpr hF₂⟩) :
    P = Q ∧ F₂ = S := by
  have : Nontrivial R := NormOneClass.nontrivial
  obtain ⟨c, hc⟩ := hQ.exists_left_inv
  set Qm : Polynomial R := Polynomial.C c * Q
  have hQm : Qm.Monic := Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one hc
  have hQm_deg : Qm.natDegree = Q.natDegree :=
    Polynomial.natDegree_C_mul_eq_of_mul_eq_one (by rw [mul_comm]; exact hc)
  obtain ⟨A, B, hAB⟩ := hcop
  have hAB' : (A : R⟦X⟧) * (Q : R⟦X⟧) + (B : R⟦X⟧) * F₂ = 1 := by
    simpa only [Subring.coe_add, Subring.coe_mul, Subring.coe_one] using congrArg Subtype.val hAB
  -- Multiply the Bézout relation by `P` and substitute `P * F₂ = Q * S` to show `Qm ∣ P` in entire
  -- series, hence in `R[X]` by uniqueness of entire division.
  let G : R⟦X⟧ :=
    (Polynomial.C Q.leadingCoeff : R⟦X⟧) * ((A : R⟦X⟧) * (P : R⟦X⟧) + (B : R⟦X⟧) * S)
  have hG : G.IsEntire :=
    (PowerSeries.isEntire_coe _).mul
      (((PowerSeries.IsEntire.mem_subring.mp A.2).mul (PowerSeries.isEntire_coe P)).add
        ((PowerSeries.IsEntire.mem_subring.mp B.2).mul hS))
  have hP_div : (P : R⟦X⟧) = (Qm : R⟦X⟧) * G := by
    have h1 : (P : R⟦X⟧) = (Q : R⟦X⟧) * ((A : R⟦X⟧) * (P : R⟦X⟧) + (B : R⟦X⟧) * S) := by
      calc (P : R⟦X⟧) = ((A : R⟦X⟧) * (Q : R⟦X⟧) + (B : R⟦X⟧) * F₂) * (P : R⟦X⟧) := by
            rw [hAB', one_mul]
        _ = (A : R⟦X⟧) * (Q : R⟦X⟧) * (P : R⟦X⟧) + (B : R⟦X⟧) * ((P : R⟦X⟧) * F₂) := by ring
        _ = (A : R⟦X⟧) * (Q : R⟦X⟧) * (P : R⟦X⟧) + (B : R⟦X⟧) * ((Q : R⟦X⟧) * S) := by rw [heq]
        _ = (Q : R⟦X⟧) * ((A : R⟦X⟧) * (P : R⟦X⟧) + (B : R⟦X⟧) * S) := by ring
    have hQeq : (Q : R⟦X⟧) = (Qm : R⟦X⟧) * (Polynomial.C Q.leadingCoeff : R⟦X⟧) := by
      simp only [Qm, Polynomial.coe_mul, Polynomial.coe_C]
      rw [mul_right_comm, ← map_mul, hc, map_one, one_mul]
    rw [h1, hQeq, mul_assoc]
  have hmod : P %ₘ Qm = 0 := by
    rw [← PowerSeries.modByMonic_coe P hQm, hP_div, hG.coe_mul_modByMonic hQm]
  have hP_eq : P = Qm * (P /ₘ Qm) := by
    have h := Polynomial.modByMonic_add_div P Qm
    rw [hmod, zero_add] at h
    exact h.symm
  set K : Polynomial R := P /ₘ Qm
  have hK0 : K ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hP_eq
    rw [hP_eq, Polynomial.coeff_zero] at hP0
    exact zero_ne_one hP0
  have hKdeg : K.natDegree = 0 := by
    have hdeg := hQm.natDegree_mul' hK0
    rw [← hP_eq, hQm_deg] at hdeg
    omega
  have hP_C : P = Polynomial.C (c * K.coeff 0) * Q := by
    have hK_C : K = Polynomial.C (K.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hKdeg
    calc P = Qm * K := hP_eq
      _ = Polynomial.C c * Q * Polynomial.C (K.coeff 0) := by conv_lhs => rw [hK_C]
      _ = Polynomial.C (c * K.coeff 0) * Q := by rw [map_mul]; ring
  have hcK : c * K.coeff 0 = 1 := by
    have h := congrArg (fun p : Polynomial R ↦ p.coeff 0) hP_C
    simpa only [hP0, Polynomial.coeff_C_mul, hQ0, mul_one] using h.symm
  have hPQ : P = Q := by rw [hP_C, hcK, map_one, one_mul]
  refine ⟨hPQ, ?_⟩
  rw [hPQ] at heq
  have hQu : IsUnit (Q : R⟦X⟧) := PowerSeries.isUnit_iff_constantCoeff.mpr (by simp [hQ0])
  exact hQu.mul_left_cancel heq

/-- Reflecting `Q` in degree `n ≥ Q.natDegree` multiplies `Q.reverse` by `X ^ (n - Q.natDegree)`. -/
private theorem reflect_eq_X_pow_mul_reverse {R : Type*} [CommSemiring R] {Q : Polynomial R}
    {n : ℕ} (hn : Q.natDegree ≤ n) :
    Q.reflect n = Polynomial.X ^ (n - Q.natDegree) * Q.reverse := by
  have h := Polynomial.reflect_mul (1 : Polynomial R) Q
    (F := n - Q.natDegree) (G := Q.natDegree) (by simp) le_rfl
  rw [one_mul, Nat.sub_add_cancel hn, Polynomial.reflect_one] at h
  exact h

/-- If `c` inverts `Q.leadingCoeff` and `c • Q*(f)` is nilpotent in an `R`-algebra, then `f` is a
unit. -/
private theorem isUnit_of_isNilpotent_smul_aeval_reverse {R A : Type*} [CommRing R] [Ring A]
    [Algebra R A] {Q : Polynomial R} {c : R} {f : A}
    (hc : c * Q.leadingCoeff = 1) (hnil : IsNilpotent (c • Polynomial.aeval f Q.reverse)) :
    IsUnit f := by
  have h1 : IsUnit (1 - c • Polynomial.aeval f Q.reverse) := hnil.isUnit_one_sub
  have hdiv : f * Polynomial.aeval f Q.reverse.divX + algebraMap R A Q.leadingCoeff =
      Polynomial.aeval f Q.reverse := by
    have h := congrArg (Polynomial.aeval f) (Polynomial.X_mul_divX_add Q.reverse)
    simpa only [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C,
      Polynomial.coeff_zero_reverse] using h
  have hfac : 1 - c • Polynomial.aeval f Q.reverse =
      f * (-(c • Polynomial.aeval f Q.reverse.divX)) := by
    have hc_alg : c • algebraMap R A Q.leadingCoeff = 1 := by
      rw [Algebra.smul_def, ← map_mul, hc, map_one]
    have hsmul := congrArg (c • ·) hdiv
    rw [smul_add, hc_alg, ← mul_smul_comm] at hsmul
    rw [← hsmul, mul_neg]
    abel
  have hcomm : Commute f (-(c • Polynomial.aeval f Q.reverse.divX)) := by
    have h : Commute f (Polynomial.aeval f Q.reverse.divX) := by
      simpa only [Polynomial.aeval_X] using
        (Commute.all Polynomial.X Q.reverse.divX).map (Polynomial.aeval f)
    exact (h.smul_right c).neg_right
  exact (hcomm.isUnit_mul_iff.mp (hfac ▸ h1)).1

/-- Polynomial evaluation on the restriction of `u` to an invariant submodule agrees with evaluation
on `u`. -/
private theorem coe_aeval_restrict_apply {R M : Type*} [NormedCommRing R]
    [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
    {u : M →L[R] M} {W : Submodule R M} (hW : Set.MapsTo u W W) (p : Polynomial R) (x : W) :
    ((Polynomial.aeval (u.restrict hW) p : W →L[R] W) x : M) = Polynomial.aeval u p (x : M) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a =>
    have hpow : ∀ k (y : W), (((u.restrict hW) ^ k : W →L[R] W) y : M) = (u ^ k) (y : M) := by
      intro k
      induction k with
      | zero => intro y; rfl
      | succ k ih =>
        intro y
        rw [pow_succ', pow_succ', mul_apply_eq_comp, mul_apply_eq_comp]
        exact congrArg u (ih y)
    simp [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, hpow]

/-- On a model space, a coprime polynomial factor `Q` of `H_u` gives `B(u)`, for `B = 1 - c Q*`,
a good zero of order `Q.natDegree` at `1`. -/
private theorem isGoodZero_charPowerSeries_one_sub_C_mul_reverse
    {I R : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
    [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R] [TauCeti.NormedRing.IsTate R]
    {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact)
    {Q : Polynomial R} {c : R} {S : R⟦X⟧}
    (hQ0 : Q.coeff 0 = 1) (hc : c * Q.leadingCoeff = 1) (hS : S.IsEntire)
    (hfac : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, PowerSeries.IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
        PowerSeries.IsEntire.subring R)
      ⟨S, PowerSeries.IsEntire.mem_subring.mpr hS⟩) :
    (Polynomial.aeval u (1 - Polynomial.C c * Q.reverse)).matrixCoeff.charPowerSeries.IsGoodZero
      1 Q.natDegree := by
  set B : Polynomial R := 1 - Polynomial.C c * Q.reverse
  have hB0 : B.coeff 0 = 0 := Polynomial.coeff_zero_one_sub_C_mul_reverse hc
  have hS0 : PowerSeries.constantCoeff S = 1 := by
    have h := congrArg PowerSeries.constantCoeff hfac
    rw [Matrix.constantCoeff_charPowerSeries, map_mul,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, hQ0, one_mul] at h
    exact h.symm
  have hS0' : PowerSeries.coeff 0 S = 1 := by
    rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have hGe : (B.colemanDSeries S).IsEntire := by
    rw [← PowerSeries.colemanDEntire_coe hB0 hS0']
    exact PowerSeries.isEntire_colemanDEntire (PowerSeries.isEntire_coe B) hS
      (by rwa [Polynomial.coeff_coe]) hS0'
  have hGu : IsUnit ((B.colemanDSeries S).evalAt (1 : R)) :=
    (Polynomial.isUnit_evalAt_one_colemanDSeries_one_sub_C_mul_reverse_iff hc hS hS0).mpr hcop
  have hH : (Polynomial.aeval u B).matrixCoeff.charPowerSeries =
      (PowerSeries.X - PowerSeries.C (1 : R)) ^ Q.natDegree *
        (PowerSeries.C ((-1 : R) ^ Q.natDegree) * B.colemanDSeries S) := by
    rw [hu.charPowerSeries_matrixCoeff_aeval hB0, hfac, Polynomial.colemanDSeries_mul hB0,
      Polynomial.colemanDSeries_one_sub_C_mul_reverse_self hQ0 hc]
    have hsign : (1 - PowerSeries.X : R⟦X⟧) =
        PowerSeries.C (-1 : R) * (PowerSeries.X - PowerSeries.C 1) := by
      simp only [map_neg, map_one]
      ring
    rw [hsign, mul_pow, ← map_pow]
    ring
  rw [hH, ((PowerSeries.isEntire_C _).mul hGe).isGoodZero_X_sub_C_pow_mul_iff,
    (PowerSeries.isEntire_C _).evalAt_mul hGe, PowerSeries.evalAt_C]
  exact (isUnit_neg_one.pow _).mul hGu

/-- If a bounded idempotent `E` commutes with a row-compact operator `u` on a model space and
`Q*(u)` has a complementary two-sided inverse `w` on `ker E` (`Q*(u) * w = w * Q*(u) = 1 - E`,
`E * w = 0`), then `Q` is coprime to the complementary Fredholm series `H_(u (1 - E))`. -/
private theorem isCoprime_charPowerSeries_mul_one_sub
    {I R : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
    [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R] [TauCeti.NormedRing.IsTate R]
    {u E w : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact)
    (hE_idem : IsIdempotentElem E) (hcomm : Commute u E)
    {Q : Polynomial R} (hQ : IsUnit Q.leadingCoeff)
    (hw₁ : Polynomial.aeval u Q.reverse * w = 1 - E)
    (hw₂ : w * Polynomial.aeval u Q.reverse = 1 - E) (hw₃ : E * w = 0) :
    IsCoprime
      (⟨Q, PowerSeries.IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
        PowerSeries.IsEntire.subring R)
      ⟨(u * (1 - E)).matrixCoeff.charPowerSeries,
        PowerSeries.IsEntire.mem_subring.mpr (hu.comp_clm (1 - E)).isEntire_charPowerSeries⟩ := by
  have hu_pr : u.IsPrCompact := isPrCompact_iff_isRowCompact.2 hu
  have hmaps_ker : Set.MapsTo u E.ker E.ker := fun x hx ↦ by
    have hx' : E x = 0 := LinearMap.mem_ker.mp hx
    exact LinearMap.mem_ker.mpr <| by
      simpa only [coe_coe, mul_apply_eq_comp, hx', map_zero] using congr($(hcomm.eq.symm) x)
  let r₂ : C₀(I, R) →L[R] E.ker := (1 - E).codRestrict E.ker fun x ↦
    LinearMap.mem_ker.mpr <| by
      have hEE : E (E x) = E x := congr($hE_idem.eq x)
      simp [hEE]
  have hri₂ : r₂.comp E.ker.subtypeL = .id R E.ker := ext fun x ↦ Subtype.ext <| by
    have hx : E x = 0 := LinearMap.mem_ker.mp x.property
    simp [r₂, hx]
  have hM₂ : TauCeti.HasPr R E.ker := hu_pr.hasPr_source.of_retract E.ker.subtypeL r₂ hri₂
  have hu₂_eq : u.restrict hmaps_ker = r₂.comp (u.comp E.ker.subtypeL) :=
    ext fun x ↦ Subtype.ext <| by
      have hux : E (u x) = 0 := LinearMap.mem_ker.mp (hmaps_ker x.property)
      change u x = (1 - E) (u x)
      simp [hux]
  have hu₂_pr := (hu_pr.comp_clm E.ker.subtypeL hM₂).clm_comp r₂ hM₂
  have hchar₂ := (hu_pr.comp_clm E.ker.subtypeL hM₂).charPowerSeries_comp_comm r₂
  have hext : (u.comp E.ker.subtypeL).comp r₂ = u * (1 - E) := ext fun _ ↦ rfl
  rw [hext, mul_def, (hu.comp_clm (1 - E)).charPowerSeries_eq_charPowerSeries_matrixCoeff,
    ← mul_def] at hchar₂
  have hmaps_w : Set.MapsTo w E.ker E.ker := fun x _ ↦
    LinearMap.mem_ker.mpr <| by
      simpa only [coe_coe, mul_apply_eq_comp, zero_apply] using congr($hw₃ x)
  have hcop₂ := (hu₂_pr.isUnit_aeval_reverse_iff hQ).mp <| by
    rw [← hu₂_eq]
    refine ⟨⟨_, w.restrict hmaps_w, ?_, ?_⟩, rfl⟩
    · ext x : 1
      apply Subtype.ext
      have hx : E x = 0 := LinearMap.mem_ker.mp x.property
      have h1 := coe_aeval_restrict_apply hmaps_ker Q.reverse ((w.restrict hmaps_w) x)
      rw [mul_apply_eq_comp, h1, one_apply_eq_self]
      change Polynomial.aeval u Q.reverse (w x) = (x : C₀(I, R))
      simpa only [mul_apply_eq_comp, one_apply_eq_self, sub_apply, hx,
        sub_zero] using congr($hw₁ (x : C₀(I, R)))
    · ext x : 1
      apply Subtype.ext
      have hx : E x = 0 := LinearMap.mem_ker.mp x.property
      have h1 := coe_aeval_restrict_apply hmaps_ker Q.reverse x
      have hw_coe (y : E.ker) : ((w.restrict hmaps_w) y : C₀(I, R)) = w y := rfl
      rw [mul_apply_eq_comp, hw_coe, h1, one_apply_eq_self]
      simpa only [mul_apply_eq_comp, one_apply_eq_self, sub_apply, hx,
        sub_zero] using congr($hw₂ (x : C₀(I, R)))
  convert hcop₂ using 2

/-- **Core model-space Riesz–Coleman construction.** Produces the Riesz–Coleman projection `E`
attached to a coprime factorisation `H_u = Q * S`, together with its constant rank `Q.natDegree`,
its reversed characteristic polynomial `Q`, and its two Fredholm factors `Q` and `S`. -/
private theorem exists_isRieszColemanProjection_aux
    {I R : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
    [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R] [TauCeti.NormedRing.IsTate R]
    {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact)
    {Q : Polynomial R} {S : R⟦X⟧}
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, PowerSeries.IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
        PowerSeries.IsEntire.subring R)
      ⟨S, PowerSeries.IsEntire.mem_subring.mpr hS⟩) :
    ∃ E : C₀(I, R) →L[R] C₀(I, R),
      IsRieszColemanProjection u Q E ∧
      (∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) E.range p = Q.natDegree) ∧
      (u * E).matrixCoeff.charPowerSeries = (Q : R⟦X⟧) ∧
      (u * (1 - E)).matrixCoeff.charPowerSeries = S := by
  obtain ⟨c, hc⟩ := hQ.exists_left_inv
  set B : Polynomial R := 1 - Polynomial.C c * Q.reverse
  have hB0 : B.coeff 0 = 0 := Polynomial.coeff_zero_one_sub_C_mul_reverse hc
  set v : C₀(I, R) →L[R] C₀(I, R) := Polynomial.aeval u B
  have hv : v.IsRowCompact := hu.aeval hB0
  have hgood := isGoodZero_charPowerSeries_one_sub_C_mul_reverse hu hQ0 hc hS hfac hcop
  set E : C₀(I, R) →L[R] C₀(I, R) := v.rieszProjection 1 Q.natDegree
  have hEv : IsRieszProjection v 1 Q.natDegree E :=
    hv.isRieszProjection_rieszProjection (fun _ ↦ hgood.evalAt_hasseDeriv_eq_zero)
      hgood.isUnit_evalAt_hasseDeriv
  have h1v : (1 : C₀(I, R) →L[R] C₀(I, R)) - (1 : R) • v = c • Polynomial.aeval u Q.reverse := by
    simp only [one_smul, v, B, map_sub, map_one, map_mul, Polynomial.aeval_C,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, sub_sub_cancel]
  have hcomm_uv : Commute u v := by
    simpa only [Polynomial.aeval_X] using (Commute.all Polynomial.X B).map (Polynomial.aeval u)
  have hcomm : Commute u E := hEv.commute_of_commute hcomm_uv
  have hclosure : closure (Algebra.adjoin R {v} : Set (C₀(I, R) →L[R] C₀(I, R))) ⊆
      closure (Algebra.adjoin R {u} : Set (C₀(I, R) →L[R] C₀(I, R))) := by
    refine closure_mono (Algebra.adjoin_le ?_)
    rw [Set.singleton_subset_iff, SetLike.mem_coe, Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨B, rfl⟩
  let w : C₀(I, R) →L[R] C₀(I, R) := c • hEv.inverse
  have hw₁ : Polynomial.aeval u Q.reverse * w = 1 - E := by
    rw [mul_smul_comm, ← smul_mul_assoc, ← h1v, hEv.one_sub_smul_mul_inverse]
  have hw₂ : w * Polynomial.aeval u Q.reverse = 1 - E := by
    rw [smul_mul_assoc, ← mul_smul_comm, ← h1v, hEv.inverse_mul_one_sub_smul]
  have hw₃ : E * w = 0 := ext fun x ↦ by
    have h : E (hEv.inverse x) = 0 := by
      simpa only [mul_apply_eq_comp, zero_apply] using congr($hEv.mul_inverse_eq_zero x)
    simp [w, h]
  have hw₄ : w * E = 0 := ext fun x ↦ by
    have h : hEv.inverse (E x) = 0 := by
      simpa only [mul_apply_eq_comp, zero_apply] using congr($hEv.inverse_mul_eq_zero x)
    simp [w, h]
  have hw_mem : w ∈ closure (Algebra.adjoin R {u} : Set (C₀(I, R) →L[R] C₀(I, R))) := by
    refine hclosure ?_
    have hsub : (c • ·) '' (Algebra.adjoin R {v} : Set (C₀(I, R) →L[R] C₀(I, R))) ⊆
        (Algebra.adjoin R {v} : Set (C₀(I, R) →L[R] C₀(I, R))) := by
      rintro _ ⟨y, hy, rfl⟩
      exact Subalgebra.smul_mem _ hy c
    exact closure_mono hsub
      (image_closure_subset_closure_image (continuous_const_smul c)
        ⟨hEv.inverse, hEv.inverse_mem_closure_adjoin, rfl⟩)
  have hrank : ∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) E.range p = Q.natDegree :=
    fun p ↦ hEv.rankAtStalk_range hv hgood p
  have hmaps_range : Set.MapsTo u E.range E.range := by
    rw [LinearMap.coe_range, coe_coe]
    exact Function.Semiconj.mapsTo_range fun x ↦ congr($(hcomm.eq.symm) x)
  -- Fix the additive group of `E.range` so its endomorphism ring matches the submodule structure.
  let : AddCommGroup E.range := inferInstance
  have hE_rc : E.IsRowCompact := hEv.isRowCompact hv
  have := hE_rc.finite_range_of_isIdempotentElem hEv.isIdempotentElem
  have := hE_rc.projective_range_of_isIdempotentElem hEv.isIdempotentElem
  have hfix (x : E.range) : E x = x :=
    (LinearMap.IsIdempotentElem.mem_range_iff
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap hEv.isIdempotentElem)).mp x.property
  let u₁ : E.range →L[R] E.range := u.restrict hmaps_range
  let f : Module.End R E.range := u₁.toLinearMap
  have hfaeval (p : Polynomial R) (x : E.range) :
      (Polynomial.aeval f p x : C₀(I, R)) = Polynomial.aeval u p (x : C₀(I, R)) := by
    simpa only [f, ← toLinearMap_aeval, coe_coe] using coe_aeval_restrict_apply hmaps_range p x
  -- Step 1: `(c • Q*(f)) ^ deg Q = 0`, so `f` is invertible on `E.range`.
  have hf_unit : IsUnit f := by
    refine isUnit_of_isNilpotent_smul_aeval_reverse hc ⟨Q.natDegree, ?_⟩
    ext x : 1
    apply Subtype.ext
    have hpow : (((c • Polynomial.aeval f Q.reverse) ^ Q.natDegree) x : C₀(I, R)) =
        (((1 - (1 : R) • v) ^ Q.natDegree) * E) (x : C₀(I, R)) := by
      rw [h1v, smul_pow, smul_pow, mul_apply_eq_comp, hfix]
      change c ^ Q.natDegree • (((Polynomial.aeval f Q.reverse) ^ Q.natDegree) x : C₀(I, R)) =
        c ^ Q.natDegree • (((Polynomial.aeval u Q.reverse) ^ Q.natDegree) (x : C₀(I, R)))
      congr 1
      have h := hfaeval (Q.reverse ^ Q.natDegree) x
      simpa only [map_pow] using h
    rw [hpow, hEv.pow_mul_eq_zero]
    rfl
  -- Step 2: identify the two Fredholm factors `H_(u E) = Q` and `H_(u (1 - E)) = S`.
  have hri₁ : E.rangeRestrict.comp E.range.subtypeL = .id R E.range :=
    ext fun x ↦ Subtype.ext (hfix x)
  have hM₁ : TauCeti.HasPr R E.range :=
    (isPrCompact_iff_isRowCompact.2 hu).hasPr_source.of_retract
      E.range.subtypeL E.rangeRestrict hri₁
  have hu₁_pr := isPrCompact_of_finite (R := R) (M := E.range) (L := E.range) hM₁ hM₁ u₁
  have hchar₁ : (u * E).matrixCoeff.charPowerSeries = (f.projectiveCharpolyRev : R⟦X⟧) := by
    have hext : E.range.subtypeL.comp (u₁.comp E.rangeRestrict) = u * E := ext fun _ ↦ rfl
    rw [← hext, ← hu₁_pr.charPowerSeries_eq hri₁,
      charPowerSeries_eq_projectiveCharpolyRev (R := R) (M := E.range) hM₁ u₁]
  have hcop₂ := isCoprime_charPowerSeries_mul_one_sub hu hEv.isIdempotentElem hcomm hQ hw₁ hw₂ hw₃
  have hmul_eq :
      (f.projectiveCharpolyRev : R⟦X⟧) * (u * (1 - E)).matrixCoeff.charPowerSeries =
        (Q : R⟦X⟧) * S := by
    rw [← hchar₁, ← hu.charPowerSeries_matrixCoeff_eq_mul_of_commute hEv.isIdempotentElem hcomm,
      hfac]
  obtain ⟨hPQ, hF₂S⟩ := eq_of_coe_mul_eq_coe_mul_of_isCoprime hQ0 hQ
    (LinearMap.coeff_projectiveCharpolyRev_zero f)
    (LinearMap.natDegree_projectiveCharpolyRev_le (fun p ↦ (hrank p).le) f)
    hS (hu.comp_clm (1 - E)).isEntire_charPowerSeries hmul_eq hcop₂
  -- Step 3: Cayley–Hamilton on `E.range` plus invertibility of `f` gives `Q*(u) * E = 0`.
  have hQE : Polynomial.aeval u Q.reverse * E = 0 := by
    obtain ⟨n, hn, hCH⟩ := f.exists_aeval_reflect_projectiveCharpolyRev_eq_zero
    rw [hPQ] at hn hCH
    rw [reflect_eq_X_pow_mul_reverse hn, map_mul, map_pow, Polynomial.aeval_X] at hCH
    have hQf0 : Polynomial.aeval f Q.reverse = 0 := (hf_unit.pow _).mul_right_eq_zero.mp hCH
    ext x : 1
    have h := hfaeval Q.reverse ⟨E x, x, rfl⟩
    rw [hQf0, LinearMap.zero_apply, ZeroMemClass.coe_zero] at h
    simpa only [mul_apply_eq_comp, comp_apply, zero_apply] using h.symm
  refine ⟨E, ⟨hEv.isIdempotentElem, hcomm, hclosure hEv.mem_closure_adjoin, hQE,
    ⟨w, hw₁, hw₂, hw₃, hw₄, hw_mem⟩⟩, hrank, ?_, hF₂S⟩
  rw [hchar₁, hPQ]

end Helpers

section ModelSpace

variable {I R : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R] [TauCeti.NormedRing.IsTate R]
  {u E : C₀(I, R) →L[R] C₀(I, R)} {Q : Polynomial R} {S : R⟦X⟧}

/-- **Riesz–Coleman decomposition on model spaces.** Let `u` be a row-compact endomorphism of
`C₀(I, R)` whose Fredholm series factors as `Q * S` with `Q(0) = 1`, `Q.leadingCoeff` a unit, `S`
entire, and `Q` coprime to `S` in the ring of entire series. Then `u` admits a Riesz–Coleman
projection at `Q`. The case `Q = 1` is included (giving the zero projection). -/
theorem IsRowCompact.exists_isRieszColemanProjection (hu : u.IsRowCompact)
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, PowerSeries.IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
        PowerSeries.IsEntire.subring R)
      ⟨S, PowerSeries.IsEntire.mem_subring.mpr hS⟩) :
    ∃ E, IsRieszColemanProjection u Q E := by
  obtain ⟨E, hE, -, -, -⟩ := exists_isRieszColemanProjection_aux hu hQ0 hQ hS hfac hcop
  exact ⟨E, hE⟩

/-- **Constant rank of the Riesz–Coleman summand on a model space.** Under a coprime factorisation
`H_u = Q * S`, the range of the Riesz–Coleman projection at `Q` has constant rank `Q.natDegree`
at every prime ideal of `R`. -/
theorem IsRieszColemanProjection.rankAtStalk_range (hE : IsRieszColemanProjection u Q E)
    (hu : u.IsRowCompact) (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, PowerSeries.IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
        PowerSeries.IsEntire.subring R)
      ⟨S, PowerSeries.IsEntire.mem_subring.mpr hS⟩)
    (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) E.range p = Q.natDegree := by
  obtain ⟨E', hE', hrank, -, -⟩ := exists_isRieszColemanProjection_aux hu hQ0 hQ hS hfac hcop
  rw [hE.unique hE']
  exact hrank p

/-- Under a coprime factorisation `H_u = Q * S` on a model space, the kernel `ker Q*(u)` has
constant rank `Q.natDegree` at every prime ideal of `R`. -/
theorem IsRowCompact.rankAtStalk_ker_aeval_reverse (hu : u.IsRowCompact)
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, PowerSeries.IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
        PowerSeries.IsEntire.subring R)
      ⟨S, PowerSeries.IsEntire.mem_subring.mpr hS⟩)
    (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R)
      (LinearMap.ker ((Polynomial.aeval u Q.reverse : C₀(I, R) →L[R] C₀(I, R)) :
        C₀(I, R) →ₗ[R] C₀(I, R))) p = Q.natDegree := by
  obtain ⟨E, hE⟩ := hu.exists_isRieszColemanProjection hQ0 hQ hS hfac hcop
  rw [← hE.range_eq_ker]
  exact hE.rankAtStalk_range hu hQ0 hQ hS hfac hcop p

/-- **Finite-summand Fredholm determinant on a model space.** Under a coprime factorisation
`H_u = Q * S`, the Fredholm series of `u * E` is `Q`. -/
theorem IsRieszColemanProjection.charPowerSeries_matrixCoeff_mul_eq
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact)
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, PowerSeries.IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
        PowerSeries.IsEntire.subring R)
      ⟨S, PowerSeries.IsEntire.mem_subring.mpr hS⟩) :
    (u * E).matrixCoeff.charPowerSeries = (Q : R⟦X⟧) := by
  obtain ⟨E', hE', -, hchar₁, -⟩ := exists_isRieszColemanProjection_aux hu hQ0 hQ hS hfac hcop
  rw [hE.unique hE']
  exact hchar₁

/-- **Complementary-summand Fredholm determinant on a model space.** Under a coprime factorisation
`H_u = Q * S`, the Fredholm series of `u * (1 - E)` is `S`. -/
theorem IsRieszColemanProjection.charPowerSeries_matrixCoeff_mul_one_sub_eq
    (hE : IsRieszColemanProjection u Q E) (hu : u.IsRowCompact)
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, PowerSeries.IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
        PowerSeries.IsEntire.subring R)
      ⟨S, PowerSeries.IsEntire.mem_subring.mpr hS⟩) :
    (u * (1 - E)).matrixCoeff.charPowerSeries = S := by
  obtain ⟨E', hE', -, -, hchar₂⟩ := exists_isRieszColemanProjection_aux hu hQ0 hQ hS hfac hcop
  rw [hE.unique hE']
  exact hchar₂

end ModelSpace

section ModelSpaceField

variable {I K : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {u E : C₀(I, K) →L[K] C₀(I, K)} {Q : Polynomial K} {S : K⟦X⟧}

/-- Over a complete ultrametric field, the range of the Riesz–Coleman projection attached to a
coprime polynomial factor `Q` of `H_u` has dimension `Q.natDegree`. -/
theorem IsRieszColemanProjection.finrank_range (hE : IsRieszColemanProjection u Q E)
    (hu : u.IsRowCompact) (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.matrixCoeff.charPowerSeries = (Q : K⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, PowerSeries.IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
        PowerSeries.IsEntire.subring K)
      ⟨S, PowerSeries.IsEntire.mem_subring.mpr hS⟩) :
    Module.finrank K E.range = Q.natDegree := by
  have hr := hE.rankAtStalk_range hu hQ0 hQ hS hfac hcop ⟨⊥, Ideal.isPrime_bot⟩
  let : AddCommGroup E.range := inferInstance
  rw [Module.rankAtStalk_eq_finrank_of_free] at hr
  exact hr

/-- Over a complete ultrametric field, `ker Q*(u)` has dimension `Q.natDegree` for a coprime
polynomial factor `Q` of `H_u` on a model space. -/
theorem IsRowCompact.finrank_ker_aeval_reverse (hu : u.IsRowCompact)
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hS : S.IsEntire)
    (hfac : u.matrixCoeff.charPowerSeries = (Q : K⟦X⟧) * S)
    (hcop : IsCoprime
      (⟨Q, PowerSeries.IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
        PowerSeries.IsEntire.subring K)
      ⟨S, PowerSeries.IsEntire.mem_subring.mpr hS⟩) :
    Module.finrank K (LinearMap.ker ((Polynomial.aeval u Q.reverse : C₀(I, K) →L[K] C₀(I, K)) :
      C₀(I, K) →ₗ[K] C₀(I, K))) = Q.natDegree := by
  obtain ⟨E, hE⟩ := hu.exists_isRieszColemanProjection hQ0 hQ hS hfac hcop
  rw [← hE.range_eq_ker]
  exact hE.finrank_range hu hQ0 hQ hS hfac hcop

end ModelSpaceField

section BaseChange

variable {I R S : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R] [TauCeti.NormedRing.IsTate R]
  [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S] [TauCeti.NormedRing.IsTate S]
  {u : C₀(I, R) →L[R] C₀(I, R)} {Q : Polynomial R} {G : R⟦X⟧}

/-- **Rank invariance under bounded base change.** If `H_u = Q * G` is a coprime factorisation
with `Q(0) = 1` and unit leading coefficient, then after any bounded unital ring homomorphism
`f : R →+* S` between complete ultrametric Tate rings, `ker (Q.map f)*(u_S)` still has constant
rank `Q.natDegree` over `Spec S`. -/
theorem IsRowCompact.rankAtStalk_ker_aeval_reverse_mapCoeffs (hu : u.IsRowCompact)
    (f : R →+* S) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖)
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hG : G.IsEntire)
    (hfac : u.matrixCoeff.charPowerSeries = (Q : R⟦X⟧) * G)
    (hcop : IsCoprime
      (⟨Q, PowerSeries.IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
        PowerSeries.IsEntire.subring R)
      ⟨G, PowerSeries.IsEntire.mem_subring.mpr hG⟩)
    (p : PrimeSpectrum S) :
    Module.rankAtStalk (R := S)
      (LinearMap.ker ((Polynomial.aeval (u.mapCoeffs f hf) (Q.map f).reverse :
        C₀(I, S) →L[S] C₀(I, S)) : C₀(I, S) →ₗ[S] C₀(I, S))) p = Q.natDegree := by
  have : Nontrivial S := NormOneClass.nontrivial
  have ⟨C, hC⟩ := hf
  have hQ0' : (Q.map f).coeff 0 = 1 := by simp [hQ0]
  have hQ' : IsUnit (Q.map f).leadingCoeff := by
    rw [Polynomial.leadingCoeff_map_eq_of_isUnit_leadingCoeff f hQ]
    exact hQ.map f
  have hG' : (PowerSeries.map f G).IsEntire := hG.map f hC
  have hfac' : (u.mapCoeffs f hf).matrixCoeff.charPowerSeries =
      ((Q.map f : Polynomial S) : S⟦X⟧) * PowerSeries.map f G := by
    rw [hu.charPowerSeries_map f hf, hfac, map_mul, Polynomial.polynomial_map_coe]
  have hcop' : IsCoprime
      (⟨Q.map f, PowerSeries.IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe (Q.map f))⟩ :
        PowerSeries.IsEntire.subring S)
      ⟨PowerSeries.map f G, PowerSeries.IsEntire.mem_subring.mpr hG'⟩ := by
    obtain ⟨A, B, hAB⟩ := hcop
    refine ⟨⟨PowerSeries.map f (A : R⟦X⟧),
        PowerSeries.IsEntire.mem_subring.mpr ((PowerSeries.IsEntire.mem_subring.mp A.2).map f hC)⟩,
      ⟨PowerSeries.map f (B : R⟦X⟧),
        PowerSeries.IsEntire.mem_subring.mpr ((PowerSeries.IsEntire.mem_subring.mp B.2).map f hC)⟩,
      Subtype.ext ?_⟩
    have hAB' : (A : R⟦X⟧) * (Q : R⟦X⟧) + (B : R⟦X⟧) * G = 1 := by
      simpa only [Subring.coe_add, Subring.coe_mul, Subring.coe_one] using congrArg Subtype.val hAB
    simpa only [Subring.coe_add, Subring.coe_mul, Subring.coe_one, map_add, map_mul, map_one,
      Polynomial.polynomial_map_coe] using congrArg (PowerSeries.map f) hAB'
  rw [(hu.mapCoeffs f hf).rankAtStalk_ker_aeval_reverse hQ0' hQ' hG' hfac' hcop' p,
    Polynomial.natDegree_map_eq_of_isUnit_leadingCoeff f hQ]

/-- **Dimension invariance under bounded field extension.** For a coprime polynomial factor `Q` of
`H_u` on a model space over a complete ultrametric field `K`, bounded coefficient extension to a
complete ultrametric field `L` preserves the dimension of `ker Q*(u)`. -/
theorem IsRowCompact.finrank_ker_aeval_reverse_mapCoeffs {K L : Type*}
    [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
    {u : C₀(I, K) →L[K] C₀(I, K)} (hu : u.IsRowCompact)
    (f : K →+* L) (hf : ∃ C : ℝ≥0, ∀ x, ‖f x‖ ≤ C * ‖x‖)
    {Q : Polynomial K} {G : K⟦X⟧}
    (hQ0 : Q.coeff 0 = 1) (hQ : IsUnit Q.leadingCoeff) (hG : G.IsEntire)
    (hfac : u.matrixCoeff.charPowerSeries = (Q : K⟦X⟧) * G)
    (hcop : IsCoprime
      (⟨Q, PowerSeries.IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ :
        PowerSeries.IsEntire.subring K)
      ⟨G, PowerSeries.IsEntire.mem_subring.mpr hG⟩) :
    Module.finrank L (LinearMap.ker ((Polynomial.aeval (u.mapCoeffs f hf) (Q.map f).reverse :
        C₀(I, L) →L[L] C₀(I, L)) : C₀(I, L) →ₗ[L] C₀(I, L))) =
      Module.finrank K (LinearMap.ker ((Polynomial.aeval u Q.reverse :
        C₀(I, K) →L[K] C₀(I, K)) : C₀(I, K) →ₗ[K] C₀(I, K))) := by
  have hr := hu.rankAtStalk_ker_aeval_reverse_mapCoeffs f hf hQ0 hQ hG hfac hcop
    ⟨⊥, Ideal.isPrime_bot⟩
  let : AddCommGroup (LinearMap.ker ((Polynomial.aeval (u.mapCoeffs f hf) (Q.map f).reverse :
      C₀(I, L) →L[L] C₀(I, L)) : C₀(I, L) →ₗ[L] C₀(I, L))) := inferInstance
  rw [Module.rankAtStalk_eq_finrank_of_free] at hr
  change Module.finrank L _ = Q.natDegree at hr
  rw [hr, hu.finrank_ker_aeval_reverse hQ0 hQ hG hfac hcop]

end BaseChange

end ContinuousLinearMap
