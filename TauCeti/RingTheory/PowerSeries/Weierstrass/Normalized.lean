/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Weierstrass.Preparation

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

The rescaling of the monic preparation follows the construction used in
`TauCeti.PowerSeries.IsMulDistinguished.exists_isEntirePreparation`; here only
restrictedness, rather than entire convergence, is required.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.2.2, Theorem 1.
* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué
  complet*, Publications Mathématiques de l'IHÉS 14 (1962), §3.
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
  constantCoeff_eq_one : constantCoeff (U : K⟦X⟧) = 1
  /-- The cofactor is a unit on the whole closed disc. -/
  isUnit : IsUnit U
  /-- The factorisation of the original series. -/
  eq_mul : f = (P : K⟦X⟧) * (U : K⟦X⟧)

/-- A disc preparation has a nonzero polynomial factor. -/
theorem IsDiscPreparation.polynomial_ne_zero (h : IsDiscPreparation r d f P U) : P ≠ 0 := by
  intro hP
  simpa [hP] using h.coeff_zero_eq_one

/-- Both normalised factors, and hence their product, have constant coefficient one. -/
theorem IsDiscPreparation.constantCoeff (h : IsDiscPreparation r d f P U) :
    constantCoeff f = 1 := by
  rw [h.eq_mul, map_mul, ← coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
    h.coeff_zero_eq_one, h.constantCoeff_eq_one, one_mul]

/-- The normalised restricted unit has Gauss norm one. -/
theorem IsDiscPreparation.gaussNorm_unit (h : IsDiscPreparation r d f P U)
    (hr : 0 < r) : (U : K⟦X⟧).gaussNorm norm r = 1 := by
  have hU := isDistinguished_zero_of_isUnit hr h.isUnit
  rw [← hU.norm_coeff_mul_pow_eq, pow_zero, mul_one,
    coeff_zero_eq_constantCoeff_apply, h.constantCoeff_eq_one, norm_one]

/-- The unit of a constant-one disc preparation is strictly within one of the identity
in the Gauss norm. Restrictedness upgrades the strict coefficient inequalities to a
strict bound on the supremum. -/
theorem IsDiscPreparation.gaussNorm_sub_one_lt (h : IsDiscPreparation r d f P U)
    (hr : 0 < r) : ((U : K⟦X⟧) - 1).gaussNorm norm r < 1 := by
  have hU := isDistinguished_zero_of_isUnit hr h.isUnit
  simpa [trunc_one_left, coeff_zero_eq_constantCoeff_apply, h.constantCoeff_eq_one,
    h.gaussNorm_unit hr] using hU.gaussNorm_sub_trunc_lt hr U.2

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
    h.eq_mul, gaussNorm_mul_of_isRestricted hr hP U.2, h.gaussNorm_unit hr, mul_one]
  exact (mul_lt_mul_of_pos_left (h.gaussNorm_sub_one_lt hr) hpos).trans_eq (mul_one _)

/-- A constant-one preparation can be made monic by dividing its polynomial by its
leading coefficient and multiplying its unit by that coefficient. -/
private theorem IsDiscPreparation.exists_monic (h : IsDiscPreparation r d f P U) :
    ∃ e : IsRestricted.subring (R := K) r, IsUnit e ∧
      (P.leadingCoeff⁻¹ • P).IsMonicOfDegree d ∧
      (e : K⟦X⟧) = P.leadingCoeff • (U : K⟦X⟧) ∧
      (e : K⟦X⟧) * ((P.leadingCoeff⁻¹ • P : Polynomial K) : K⟦X⟧) = f := by
  have ha := Polynomial.leadingCoeff_ne_zero.mpr h.polynomial_ne_zero
  have hm : (P.leadingCoeff⁻¹ • P).Monic := by
    simpa only [Units.smul_def, Units.val_inv_eq_inv_val, IsUnit.unit_spec] using
      Polynomial.monic_of_isUnit_leadingCoeff_inv_smul ha.isUnit
  refine ⟨algebraMap K _ P.leadingCoeff * U,
    (ha.isUnit.map (algebraMap K _)).mul h.isUnit,
    ⟨by rw [Polynomial.natDegree_smul P (inv_ne_zero ha), h.natDegree_eq], hm⟩, ?_, ?_⟩
  · rw [Subring.coe_mul, coe_algebraMap_isRestrictedSubring, Algebra.algebraMap_self_apply,
      smul_eq_C_mul]
  · rw [Subring.coe_mul, coe_algebraMap_isRestrictedSubring, Algebra.algebraMap_self_apply,
      ← smul_eq_C_mul, Polynomial.coe_smul, smul_mul_smul_comm,
      mul_inv_cancel₀ ha, one_smul, mul_comm]
    exact h.eq_mul.symm

/-- The constant-one preparation rescales every unit-times-monic preparation at the
last active coefficient. In particular, its monic normalisation is the usual
Weierstrass polynomial. -/
theorem IsDiscPreparation.eq_smul_and_smul_eq (h : IsDiscPreparation r d f P U)
    (hr : 0 < r)
    {e : IsRestricted.subring (R := K) r} {ω : Polynomial K}
    (he : IsUnit e) (hω : ω.IsMonicOfDegree d)
    (heω : (e : K⟦X⟧) * (ω : K⟦X⟧) = f) :
    P = P.leadingCoeff • ω ∧ P.leadingCoeff • (U : K⟦X⟧) = (e : K⟦X⟧) := by
  obtain ⟨e', he', hω', he'U, he'P⟩ := h.exists_monic
  obtain ⟨rfl, rfl⟩ := h.isDistinguished.eq_and_eq_of_mul_eq_mul hr he' he hω' hω he'P heω
  refine ⟨?_, he'U.symm⟩
  rw [smul_smul, mul_inv_cancel₀ (Polynomial.leadingCoeff_ne_zero.mpr h.polynomial_ne_zero),
    one_smul]

/-- Constant-one disc preparations at the last active coefficient are unique. The
restricted-unit hypotheses are essential; degree and constant coefficient alone do
not specify the disc polynomial. -/
theorem IsDiscPreparation.unique (h : IsDiscPreparation r d f P U)
    (h' : IsDiscPreparation r d f P' U') (hr : 0 < r) :
    P = P' ∧ U = U' := by
  obtain ⟨e, he, hω, heU, heP⟩ := h.exists_monic
  obtain ⟨e', he', hω', heU', heP'⟩ := h'.exists_monic
  obtain ⟨hee, hPP⟩ := h.isDistinguished.eq_and_eq_of_mul_eq_mul hr he he' hω hω' heP heP'
  have ha : P.leadingCoeff = P'.leadingCoeff := by
    have he0 := congrArg (fun x : IsRestricted.subring (R := K) r =>
      _root_.PowerSeries.constantCoeff (x : K⟦X⟧)) hee
    rw [heU, heU', smul_eq_C_mul, smul_eq_C_mul, map_mul, map_mul,
      constantCoeff_C, constantCoeff_C, h.constantCoeff_eq_one,
      h'.constantCoeff_eq_one, mul_one, mul_one] at he0
    exact he0
  have hmul : P.leadingCoeff • (U : K⟦X⟧) = P.leadingCoeff • (U' : K⟦X⟧) := by
    rw [ha, ← heU', ← hee, heU, ha]
  have hne := Polynomial.leadingCoeff_ne_zero.mpr h.polynomial_ne_zero
  refine ⟨?_, Subtype.ext ((smul_right_injective K⟦X⟧ hne) hmul)⟩
  have hu := congrArg (fun q : Polynomial K => P.leadingCoeff • q) hPP
  simpa only [smul_smul, ← ha, mul_inv_cancel₀ hne, one_smul] using hu

/-- A restricted series with constant coefficient one has a constant-one disc
preparation at its last active coefficient. Completeness is used only to obtain the
underlying Weierstrass preparation. -/
theorem IsDistinguished.exists_isDiscPreparation [CompleteSpace K]
    (hf : IsDistinguished r d f) (hr : 0 < r) (hfr : f.IsRestricted r)
    (hf0 : constantCoeff f = 1) :
    ∃ (P : Polynomial K) (U : IsRestricted.subring (R := K) r),
      IsDiscPreparation r d f P U := by
  obtain ⟨e, ω, he, hω, heω⟩ :=
    hf.exists_isUnit_isMonicOfDegree_mul_eq hf.coeff_ne_zero.isUnit hr hfr
  have h0 : constantCoeff (e : K⟦X⟧) * ω.coeff 0 = 1 := by
    rw [← hf0, ← heω, map_mul, ← Polynomial.coeff_coe, coeff_zero_eq_constantCoeff_apply]
  let a : Kˣ := ⟨constantCoeff (e : K⟦X⟧), ω.coeff 0, h0, by rw [mul_comm]; exact h0⟩
  let U : IsRestricted.subring (R := K) r := algebraMap K _ (a⁻¹ : Kˣ) * e
  have hU : (U : K⟦X⟧) = ((a⁻¹ : Kˣ) : K) • (e : K⟦X⟧) := by
    rw [Subring.coe_mul, coe_algebraMap_isRestrictedSubring, Algebra.algebraMap_self_apply,
      smul_eq_C_mul]
  refine ⟨a • ω, U, ?_⟩
  exact
    { isDistinguished := hf
      coeff_zero_eq_one := by
        rw [Units.smul_def, Polynomial.coeff_smul, smul_eq_mul]; exact h0
      natDegree_eq := by
        rw [Polynomial.natDegree_smul_of_smul_regular ω (IsSMulRegular.all _), hω.natDegree_eq]
      constantCoeff_eq_one := by
        rw [hU, smul_eq_C_mul, map_mul, constantCoeff_C, mul_comm]
        exact a.mul_inv
      isUnit := ((a⁻¹).isUnit.map (algebraMap K _)).mul he
      eq_mul := by
        rw [hU, Units.smul_def, Polynomial.coe_smul, smul_mul_smul_comm, a.mul_inv,
          one_smul, mul_comm, heω] }

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

end TauCeti.PowerSeries
