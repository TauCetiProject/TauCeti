/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.EvalAt
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Normalization
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Quotient
import Mathlib.Analysis.Normed.Algebra.Ultra

/-!
# Constant-one preparation on a closed disc

For a restricted series `f` with constant coefficient one over a complete ultrametric
field, Weierstrass preparation can be normalised as `f = P * U`, where both factors
have constant coefficient one. The polynomial has degree equal to the last active
coefficient index, and `U` is a unit of the algebra of series restricted to the disc.
These conditions determine both factors uniquely. In particular, the unit condition
is a condition in the restricted algebra, not merely in the formal power-series ring.

The normalised unit satisfies `‖U - 1‖ < 1` in the Gauss norm. Consequently the
polynomial approximation satisfies the scale-correct bound `‖f - P‖ < ‖f‖`.
No assumption of entire convergence is made.

The polynomial carries the zeros of `f` in the closed disc, in any complete normed field
extension, and the same order of vanishing at `0`. If `r ≤ s` and `f = Q * V` is the preparation
at `s`, then `V` is also a unit at `r`, so `Q` is `P` times a unit of the ring of series restricted
at `r`; since division of polynomials by `P` agrees with Weierstrass division at `r`, `P` divides
`Q` as a polynomial.

## Main results

* `TauCeti.PowerSeries.IsDistinguished.exists_isDiscPreparation` and
  `TauCeti.PowerSeries.IsDistinguished.existsUnique_isDiscPreparation`: existence and uniqueness of
  the constant-one disc preparation.
* `TauCeti.PowerSeries.exists_isDiscPreparation_iff`: a series has a constant-one disc preparation
  at `r` in degree `d` exactly when it is restricted and distinguished of degree `d` at `r` and has
  constant coefficient `1`.
* `TauCeti.PowerSeries.IsDiscPreparation.gaussNorm_sub_polynomial_lt`: `‖f - P‖_r < ‖f‖_r`.
* `TauCeti.PowerSeries.IsDiscPreparation.order_eq` and
  `TauCeti.PowerSeries.IsDiscPreparation.evalAt_eq_zero_iff`: `f` and `P` have the same order of
  vanishing at `0` and the same zeros in the closed disc of radius `r`, in every complete normed
  field extension.
* `TauCeti.PowerSeries.IsDiscPreparation.dvd_of_le`: the polynomial factor at a radius `r` divides
  the polynomial factor at every radius `s ≥ r`.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.2.2, Theorem 1.
* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué
  complet*, Publications Mathématiques de l'IHÉS 14 (1962), §3, for the polynomials attached to
  closed discs and their divisibility as the radius grows.
-/

public section

namespace TauCeti.PowerSeries

open _root_.PowerSeries

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {r : ℝ} {d : ℕ}
  {f : K⟦X⟧} {P P' : Polynomial K}
  {U U' : IsRestricted.subring (R := K) r}

/-- A constant-one disc preparation at the last active index `d` is a polynomial of
degree `d` with constant coefficient one times a restricted unit with constant
coefficient one. Recording the active-index condition excludes extraneous polynomial
factors which are themselves units on the disc. -/
structure IsDiscPreparation (r : ℝ) (d : ℕ) (f : K⟦X⟧) (P : Polynomial K)
    (U : IsRestricted.subring (R := K) r) : Prop where
  /-- The degree is the last active coefficient index of the original series. -/
  isDistinguished : IsDistinguished r d f
  /-- The polynomial has constant coefficient one. -/
  coeff_zero_eq_one : P.coeff 0 = 1
  /-- The polynomial has the specified degree. -/
  natDegree_eq : P.natDegree = d
  /-- The restricted cofactor has constant coefficient one. -/
  constantCoeff_unit_eq_one : constantCoeff (U : K⟦X⟧) = 1
  /-- The cofactor is a unit on the whole closed disc. -/
  isUnit : IsUnit U
  /-- The factorisation of the original series. -/
  eq_mul : f = (P : K⟦X⟧) * (U : K⟦X⟧)

/-- A disc preparation has a nonzero polynomial factor. -/
theorem IsDiscPreparation.polynomial_ne_zero (h : IsDiscPreparation r d f P U) : P ≠ 0 := by
  intro hP
  simpa [hP] using h.coeff_zero_eq_one

/-- The leading coefficient of a disc preparation's polynomial factor is a unit. -/
theorem IsDiscPreparation.isUnit_leadingCoeff (h : IsDiscPreparation r d f P U) :
    IsUnit P.leadingCoeff :=
  (Polynomial.leadingCoeff_ne_zero.mpr h.polynomial_ne_zero).isUnit

/-- A disc preparation is multiplicatively distinguished at its polynomial degree. -/
theorem IsDiscPreparation.isMulDistinguished (h : IsDiscPreparation r d f P U) :
    IsMulDistinguished r d f :=
  isMulDistinguished_iff_isUnit.mpr
    ⟨h.isDistinguished, h.isDistinguished.coeff_ne_zero.isUnit⟩

/-- Both normalised factors, and hence their product, have constant coefficient one. -/
theorem IsDiscPreparation.constantCoeff_eq_one (h : IsDiscPreparation r d f P U) :
    constantCoeff f = 1 := by
  rw [h.eq_mul, map_mul, ← coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
    h.coeff_zero_eq_one, h.constantCoeff_unit_eq_one, one_mul]

/-- The normalised restricted unit has Gauss norm one. -/
theorem IsDiscPreparation.gaussNorm_unit_eq_one (h : IsDiscPreparation r d f P U)
    (hr : 0 < r) : (U : K⟦X⟧).gaussNorm norm r = 1 := by
  have hU := isDistinguished_zero_of_isUnit hr h.isUnit
  rw [← hU.norm_coeff_mul_pow_eq, pow_zero, mul_one,
    coeff_zero_eq_constantCoeff_apply, h.constantCoeff_unit_eq_one, norm_one]

/-- The unit of a constant-one disc preparation is strictly within one of the identity
in the Gauss norm. -/
theorem IsDiscPreparation.gaussNorm_sub_one_lt (h : IsDiscPreparation r d f P U)
    (hr : 0 < r) : ((U : K⟦X⟧) - 1).gaussNorm norm r < 1 := by
  have hU := isDistinguished_zero_of_isUnit hr h.isUnit
  simpa [trunc_one_left, coeff_zero_eq_constantCoeff_apply, h.constantCoeff_unit_eq_one,
    h.gaussNorm_unit_eq_one hr] using hU.gaussNorm_sub_trunc_lt hr U.2

/-- The error in replacing a series by its constant-one disc polynomial is strictly
smaller than the Gauss norm of the series, not necessarily smaller than one. -/
theorem IsDiscPreparation.gaussNorm_sub_polynomial_lt (h : IsDiscPreparation r d f P U)
    (hr : 0 < r) : (f - (P : K⟦X⟧)).gaussNorm norm r < f.gaussNorm norm r := by
  have hP := isRestricted_polynomial P (c := r)
  have hpos : 0 < (P : K⟦X⟧).gaussNorm norm r :=
    gaussNorm_pos hr (hasGaussNorm_of_isRestricted hP)
      (Polynomial.coe_eq_zero_iff.not.mpr h.polynomial_ne_zero)
  have herr : f - (P : K⟦X⟧) = (P : K⟦X⟧) * ((U : K⟦X⟧) - 1) := by
    rw [h.eq_mul, mul_sub, mul_one]
  rw [herr, gaussNorm_mul_of_isRestricted hr hP (U.2.sub (isRestricted_one r)),
    h.eq_mul, gaussNorm_mul_of_isRestricted hr hP U.2, h.gaussNorm_unit_eq_one hr, mul_one]
  exact (mul_lt_mul_of_pos_left (h.gaussNorm_sub_one_lt hr) hpos).trans_eq (mul_one _)

/-- The constant-one preparation rescales every unit-times-monic preparation at the
last active coefficient. In particular, its monic normalisation is the usual
Weierstrass polynomial. -/
theorem IsDiscPreparation.eq_smul_and_smul_eq (h : IsDiscPreparation r d f P U)
    (hr : 0 < r)
    {e : IsRestricted.subring (R := K) r} {ω : Polynomial K}
    (he : IsUnit e) (hω : ω.IsMonicOfDegree d)
    (heω : (e : K⟦X⟧) * (ω : K⟦X⟧) = f) :
    P = P.leadingCoeff • ω ∧ P.leadingCoeff • (U : K⟦X⟧) = (e : K⟦X⟧) := by
  exact h.isMulDistinguished.eq_smul_and_smul_eq hr h.isUnit_leadingCoeff h.natDegree_eq
    h.isUnit h.eq_mul he hω heω

/-- Constant-one disc preparations at the last active coefficient are unique. The
restricted-unit hypotheses are essential; degree and constant coefficient alone do
not specify the disc polynomial. -/
theorem IsDiscPreparation.unique (h : IsDiscPreparation r d f P U)
    (h' : IsDiscPreparation r d f P' U') (hr : 0 < r) :
    P = P' ∧ U = U' := by
  exact h.isMulDistinguished.eq_and_eq_of_normalized_mul_eq hr
    h.isUnit_leadingCoeff h'.isUnit_leadingCoeff
    h.natDegree_eq h'.natDegree_eq h.coeff_zero_eq_one h'.coeff_zero_eq_one
    h.isUnit h'.isUnit h.eq_mul h'.eq_mul

/-- The polynomial factor of a disc preparation is distinguished of degree `d` at `r`, like the
original series. -/
theorem IsDiscPreparation.isDistinguished_coe (h : IsDiscPreparation r d f P U) (hr : 0 < r) :
    IsDistinguished r d (P : K⟦X⟧) := by
  obtain ⟨k, hk⟩ := exists_isDistinguished hr (isRestricted_polynomial (c := r) P)
    (by exact_mod_cast h.polynomial_ne_zero)
  have hPU := hk.mul (isDistinguished_zero_of_isUnit hr h.isUnit) hr (norm_mul _ _)
  rw [add_zero, ← h.eq_mul] at hPU
  rwa [hPU.unique h.isDistinguished] at hk

/-- **The order of vanishing at `0`.** The series and the polynomial factor of its disc
preparation have the same order of vanishing at `0`. -/
theorem IsDiscPreparation.order_eq (h : IsDiscPreparation r d f P U) :
    f.order = (P : K⟦X⟧).order := by
  have hU : (U : K⟦X⟧).order = 0 := by
    by_contra hne
    simpa [h.constantCoeff_unit_eq_one] using order_ne_zero_iff_constCoeff_eq_zero.mp hne
  rw [h.eq_mul, order_mul, hU, add_zero]

/-- **The zeros in the closed disc.** In a complete normed field extension `L` of `K`, a point `x`
with `‖x‖ ≤ r` is a zero of `f` exactly when it is a root of the polynomial factor of the disc
preparation of `f` at `r`. -/
theorem IsDiscPreparation.evalAt_eq_zero_iff {L : Type*} [NormedField L] [NormedAlgebra K L]
    [CompleteSpace L] (h : IsDiscPreparation r d f P U) (hr : 0 < r) {x : L} (hx : ‖x‖ ≤ r) :
    f.evalAt x = 0 ↔ Polynomial.aeval x P = 0 := by
  have : IsUltrametricDist L := .of_normedAlgebra K
  have hU1 := U.2.sub (isRestricted_one r)
  -- `U(x) = (U - 1)(x) + 1` with `‖(U - 1)(x)‖ ≤ ‖U - 1‖_r < 1`, so `U(x) ≠ 0`.
  have hu : (U : K⟦X⟧).evalAt x ≠ 0 := by
    intro hx0
    have hlt := (_root_.PowerSeries.norm_evalAt_le_gaussNorm
      (hasGaussNorm_of_isRestricted hU1) hx).trans_lt (h.gaussNorm_sub_one_lt hr)
    rw [← sub_add_cancel (U : K⟦X⟧) 1, _root_.PowerSeries.IsRestricted.evalAt_add hU1
      (isRestricted_one r) hx, _root_.PowerSeries.evalAt_one, add_eq_zero_iff_eq_neg] at hx0
    simp [hx0] at hlt
  rw [h.eq_mul, _root_.PowerSeries.IsRestricted.evalAt_mul (isRestricted_polynomial P) U.2 hx,
    _root_.PowerSeries.evalAt_coe, mul_eq_zero, or_iff_left hu]

/-- **Nested disc polynomials.** If `f = P * U` and `f = Q * V` are the disc preparations of `f`
at radii `0 < r ≤ s`, then `P` divides `Q`. -/
theorem IsDiscPreparation.dvd_of_le [CompleteSpace K] {s : ℝ} {e : ℕ} {Q : Polynomial K}
    {V : IsRestricted.subring (R := K) s} (h : IsDiscPreparation r d f P U)
    (h' : IsDiscPreparation s e f Q V) (hr : 0 < r) (hrs : r ≤ s) : P ∣ Q := by
  have hrs' : |r| ≤ |s| := by rwa [abs_of_pos hr, abs_of_pos (hr.trans_le hrs)]
  -- `V` is close to `1` at `r` as well, so it is a unit at `r`.
  have hVr : (V : K⟦X⟧).IsRestricted r := isRestricted_of_abs_le V.2 hrs'
  have hVs : ((V : K⟦X⟧) - 1).HasGaussNorm norm s :=
    hasGaussNorm_of_isRestricted (V.2.sub (isRestricted_one s))
  have hVr1 : ((V : K⟦X⟧) - 1).gaussNorm norm r < 1 :=
    (gaussNorm_le_gaussNorm_of_le (fun _ ↦ norm_nonneg _) hr.le hrs hVs).trans_lt
      (h'.gaussNorm_sub_one_lt (hr.trans_le hrs))
  let Vr : IsRestricted.subring (R := K) r := ⟨(V : K⟦X⟧), hVr⟩
  obtain ⟨W, hW⟩ := ((isUnit_iff_gaussNorm_sub_one_lt_one hr Vr
    h'.constantCoeff_unit_eq_one).mpr hVr1).exists_right_inv
  have hVW : (V : K⟦X⟧) * (W : K⟦X⟧) = 1 := congrArg Subtype.val hW
  -- Normalise `P` to the monic polynomial `ω = a⁻¹ • P`, distinguished of degree `d` at `r`.
  set a := P.leadingCoeff with ha_def
  have ha : a ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr h.polynomial_ne_zero
  set ω : Polynomial K := Polynomial.C a⁻¹ * P with hω_def
  have hω : ω.IsMonicOfDegree d :=
    ⟨by rw [hω_def, Polynomial.natDegree_C_mul (inv_ne_zero ha), h.natDegree_eq],
      Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ ha)⟩
  have hPω : (P : K⟦X⟧) = C a * ω := by
    rw [hω_def, Polynomial.coe_mul, Polynomial.coe_C, ← mul_assoc, ← map_mul,
      mul_inv_cancel₀ ha, map_one, one_mul]
  have hωd : IsDistinguished r d (ω : K⟦X⟧) := by
    have hd := h.isDistinguished_coe hr
    rw [hPω] at hd
    exact hd.of_isUnit_mul hr ((isUnit_iff_ne_zero.mpr ha).map
      (algebraMap K (IsRestricted.subring (R := K) r)))
  -- At `r`, `Q = f * W = ω * (a • U * W)`, so `ω` divides `Q` among restricted series.
  have hdvd : polynomialToRestricted r ω ∣ polynomialToRestricted r Q := by
    refine ⟨algebraMap K _ a * U * W, Subtype.ext ?_⟩
    have hQ : (Q : K⟦X⟧) = f * W := by
      rw [h'.eq_mul, mul_assoc, hVW, mul_one]
    simp only [coe_polynomialToRestricted, Subring.coe_mul, coe_algebraMap_isRestrictedSubring,
      Algebra.algebraMap_self_apply]
    rw [hQ, h.eq_mul, hPω]
    ring
  exact (dvd_mul_left P _).trans ((hωd.polynomialToRestricted_dvd_iff hr hω Q).mp hdvd)

/-- A restricted series with constant coefficient one has a constant-one disc
preparation at its last active coefficient. -/
theorem IsDistinguished.exists_isDiscPreparation [CompleteSpace K]
    (hf : IsDistinguished r d f) (hr : 0 < r) (hfr : f.IsRestricted r)
    (hf0 : constantCoeff f = 1) :
    ∃ (P : Polynomial K) (U : IsRestricted.subring (R := K) r),
      IsDiscPreparation r d f P U := by
  obtain ⟨e, ω, he, hω, heω⟩ :=
    hf.exists_isUnit_isMonicOfDegree_mul_eq hf.coeff_ne_zero.isUnit hr hfr
  -- The constant-one rescaling `exists_normalized_factors_of_mul_eq` is shared with
  -- `IsMulDistinguished.exists_isEntirePreparation`, without requiring entire convergence.
  obtain ⟨a, U, hP0, hd, -, hU0, hU, hPU, -⟩ :=
    exists_normalized_factors_of_mul_eq he hω heω hf0
  exact ⟨a • ω, U, ⟨hf, hP0, hd, hU0, hU, hPU⟩⟩

/-- Unique constant-one preparation on a closed disc, with the polynomial degree
given by the greatest active coefficient index. -/
theorem IsDistinguished.existsUnique_isDiscPreparation [CompleteSpace K]
    (hf : IsDistinguished r d f) (hr : 0 < r) (hfr : f.IsRestricted r)
    (hf0 : constantCoeff f = 1) :
    ∃! PU : Polynomial K × IsRestricted.subring (R := K) r,
      IsDiscPreparation r d f PU.1 PU.2 := by
  obtain ⟨P, U, h⟩ := hf.exists_isDiscPreparation hr hfr hf0
  refine ⟨(P, U), h, fun PU h' => ?_⟩
  obtain ⟨hP, hU⟩ := h'.unique h hr
  exact Prod.ext hP hU

/-- **Characterisation of the constant-one disc preparation.** Over a complete nonarchimedean
field and at a radius `r > 0`, a series has a constant-one preparation on the closed disc of
radius `r` in degree `d` exactly when it is restricted and distinguished of degree `d` at `r` and
has constant coefficient `1`. -/
theorem exists_isDiscPreparation_iff [CompleteSpace K] (hr : 0 < r) :
    (∃ (P : Polynomial K) (U : IsRestricted.subring (R := K) r), IsDiscPreparation r d f P U) ↔
      IsDistinguished r d f ∧ f.IsRestricted r ∧ constantCoeff f = 1 := by
  refine ⟨fun ⟨P, U, h⟩ ↦ ⟨h.isDistinguished, ?_, h.constantCoeff_eq_one⟩,
    fun ⟨hf, hfr, hf0⟩ ↦ hf.exists_isDiscPreparation hr hfr hf0⟩
  rw [h.eq_mul]
  exact (isRestricted_polynomial P).mul U.2

end TauCeti.PowerSeries
