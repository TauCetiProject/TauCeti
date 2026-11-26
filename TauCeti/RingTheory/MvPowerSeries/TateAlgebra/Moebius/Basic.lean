/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Mul
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.AutomorphyFactor
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Units
import TauCeti.Analysis.Normed.Group.Ultra

/-!
# Möbius transformations of the closed unit polydisc

Let `R` be a complete ultrametric normed commutative ring with `‖1‖ = 1`. A matrix
`g = !![a, b; c, d]` over `R` with `‖a‖, ‖b‖ ≤ 1`, `‖c‖ < 1` and `d` a multiplicative unit of
norm one (`TauCeti.IsNormMulUnit`) acts on the closed unit disc by the Möbius transformation
`z ↦ (a z + b) / (c z + d)`: since `‖c‖ < 1 = ‖d‖`, the denominator `c z + d` is a unit of the
Tate algebra `R⟨z⟩`, given by a Neumann series, and the quotient is a restricted series of Gauss
norm at most one. Such matrices form a monoid (`TauCeti.MvPowerSeries.moebiusSubmonoid`). Over
`ℚ_p`, or over a Banach algebra over a finite extension of `ℚ_p` through a norm-preserving
embedding (`TauCeti.MvPowerSeries.map_mem_moebiusSubmonoid`), it contains, for `t ≥ 1`, the monoids
`Σ₀(pᵗ)` of integral matrices with `c ≡ 0 mod pᵗ` and unit `d` that act on the coefficient
modules of overconvergent automorphic forms.

For a `k`-tuple of such matrices, one for each variable, the series
`TauCeti.MvPowerSeries.moebius i g = (a Xᵢ + b) (c Xᵢ + d)⁻¹` are formed in the unit Tate algebra
`R⟨X₁, …, X_k⟩`, with numerators `a Xᵢ + b` (`TauCeti.MvPowerSeries.moebiusNum i g`) and
denominators `c Xᵢ + d` (`TauCeti.MvPowerSeries.moebiusDenom i g`). The
main identity is the composition law `w_g(w_δ) = w_{g δ}`
(`TauCeti.MvPowerSeries.restrictedAnalyticSubst_moebius`), proved by analytic substitution in the
Tate algebra, together with the cocycle law of the denominators
`(c w_δ + d) (c' X + d') = c'' X + d''` for `g δ = !![a'', b''; c'', d'']`
(`TauCeti.MvPowerSeries.restrictedAnalyticSubst_moebiusDenom_mul_moebiusDenom`) and its numerator
analogue (`TauCeti.MvPowerSeries.restrictedAnalyticSubst_moebiusNum_mul_moebiusDenom`). Neither uses
evaluation at points, so both hold over nonreduced and integral coefficient rings.

Together they make `γ ↦ (w_γ, ∏ᵢ (cᵢ Xᵢ + dᵢ) ^ nᵢ)` a restricted automorphy factor
(`TauCeti.MvPowerSeries.moebiusAutomorphyFactor`), whose slash action
`f ↦ ∏ᵢ (cᵢ Xᵢ + dᵢ) ^ nᵢ · f((a X + b) / (c X + d))` is the weight-`n` action of the monoid by
norm-nonincreasing operators on `R⟨X⟩`.

## Main definitions

* `TauCeti.MvPowerSeries.moebiusSubmonoid`: the monoid of matrices `!![a, b; c, d]` with
  `‖a‖, ‖b‖ ≤ 1`, `‖c‖ < 1` and `d` a multiplicative unit of norm one.
* `TauCeti.MvPowerSeries.moebiusNum`: the numerator `a Xᵢ + b`.
* `TauCeti.MvPowerSeries.moebiusDenom`: the denominator `c Xᵢ + d`.
* `TauCeti.MvPowerSeries.moebius`: the Möbius series `(a Xᵢ + b) (c Xᵢ + d)⁻¹`.
* `TauCeti.MvPowerSeries.moebiusAutomorphyFactor`: the automorphy factor of weight `n`.

## Main results

* `TauCeti.MvPowerSeries.isNormMulUnit_moebiusDenom`, `TauCeti.MvPowerSeries.norm_moebiusDenom`:
  the denominator is a multiplicative unit of norm one.
* `TauCeti.MvPowerSeries.moebius_mul_moebiusDenom`, `TauCeti.MvPowerSeries.norm_moebius_le`: the
  Möbius series is the quotient `(a Xᵢ + b) / (c Xᵢ + d)` and lies in the closed unit ball.
* `TauCeti.MvPowerSeries.restrictedAnalyticSubst_moebiusDenom_mul_moebiusDenom`,
  `TauCeti.MvPowerSeries.restrictedAnalyticSubst_moebiusNum_mul_moebiusDenom`: the cocycle laws of
  the denominators and numerators.
* `TauCeti.MvPowerSeries.restrictedAnalyticSubst_moebius`: the composition law of Möbius series.
* `TauCeti.MvPowerSeries.norm_moebiusAutomorphyFactor_factor`: the weight-`n` factor has norm one,
  so its slash operators do not increase norms.

## References

* K. Buzzard, *Eigenvarieties*, in *L-functions and Galois representations*, LMS Lecture Note
  Ser. 320 (2007), 59–120, §§9–10.
* D. Jacobs, *Slopes of compact Hecke operators*, PhD thesis, Imperial College London (2003),
  §1.5.
-/

public section

open MvPowerSeries

namespace TauCeti.MvPowerSeries

section Submonoid

variable (R : Type*) [NormedRing R] [NormOneClass R] [IsUltrametricDist R]
  [HasSummableGeomSeries R]

/-- The monoid of `2 × 2` matrices `!![a, b; c, d]` over `R` with `‖a‖ ≤ 1`, `‖b‖ ≤ 1`,
`‖c‖ < 1` and `d` a multiplicative unit of norm one. For these matrices the Möbius
transformation `z ↦ (a z + b) / (c z + d)` is an analytic self-map of the closed unit disc with
unit denominator `c z + d`. -/
def moebiusSubmonoid : Submonoid (Matrix (Fin 2) (Fin 2) R) where
  carrier := {g | ‖g 0 0‖ ≤ 1 ∧ ‖g 0 1‖ ≤ 1 ∧ ‖g 1 0‖ < 1 ∧ IsNormMulUnit (g 1 1) ∧ ‖g 1 1‖ = 1}
  one_mem' := by simp [isNormMulUnit_one]
  mul_mem' {g h} hg hh := by
    obtain ⟨ha, hb, hc, hd, hd1⟩ := hg
    obtain ⟨ha', hb', hc', hd', hd1'⟩ := hh
    have hle {x y : R} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x * y‖ ≤ 1 :=
      (norm_mul_le x y).trans ((mul_le_of_le_one_left (norm_nonneg y) hx).trans hy)
    have hlt {x y : R} (hx : ‖x‖ < 1) (hy : ‖y‖ ≤ 1) : ‖x * y‖ < 1 :=
      (norm_mul_le x y).trans_lt ((mul_le_of_le_one_right (norm_nonneg x) hy).trans_lt hx)
    have hu : ‖g 1 1 * h 1 1‖ = 1 := by rw [hd.norm_mul, hd1, hd1', one_mul]
    have hsub : ‖g 1 0 * h 0 1 + g 1 1 * h 1 1 - g 1 1 * h 1 1‖ < ‖g 1 1 * h 1 1‖ := by
      rw [add_sub_cancel_right, hu]
      exact hlt hc hb'
    simp only [Set.mem_ofPred_eq, Matrix.mul_apply, Fin.sum_univ_two]
    refine ⟨(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hle ha ha') (hle hb hc'.le)),
      (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hle ha hb') (hle hb hd1'.le)),
      (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (hlt hc ha') ?_),
      (hd.mul hd').of_norm_sub_lt hsub, ?_⟩
    · rw [hd.norm_mul, hd1, one_mul]
      exact hc'
    · rw [← IsUltrametricDist.norm_eq_of_norm_sub_lt_left (by rwa [norm_sub_rev]), hu]

variable {R}

/-- Membership in `moebiusSubmonoid R`: `‖a‖ ≤ 1`, `‖b‖ ≤ 1`, `‖c‖ < 1`, and `d` a multiplicative
unit of norm one. -/
theorem mem_moebiusSubmonoid_iff {g : Matrix (Fin 2) (Fin 2) R} :
    g ∈ moebiusSubmonoid R ↔
      ‖g 0 0‖ ≤ 1 ∧ ‖g 0 1‖ ≤ 1 ∧ ‖g 1 0‖ < 1 ∧ IsNormMulUnit (g 1 1) ∧ ‖g 1 1‖ = 1 :=
  Iff.rfl

/-- The upper left entry of a matrix in `moebiusSubmonoid R` has norm at most one. -/
theorem norm_upperLeft_le_one_of_mem_moebiusSubmonoid {g : Matrix (Fin 2) (Fin 2) R}
    (hg : g ∈ moebiusSubmonoid R) : ‖g 0 0‖ ≤ 1 :=
  (mem_moebiusSubmonoid_iff.mp hg).1

/-- The upper right entry of a matrix in `moebiusSubmonoid R` has norm at most one. -/
theorem norm_upperRight_le_one_of_mem_moebiusSubmonoid {g : Matrix (Fin 2) (Fin 2) R}
    (hg : g ∈ moebiusSubmonoid R) : ‖g 0 1‖ ≤ 1 :=
  (mem_moebiusSubmonoid_iff.mp hg).2.1

/-- The lower left entry of a matrix in `moebiusSubmonoid R` has norm less than one. -/
theorem norm_lowerLeft_lt_one_of_mem_moebiusSubmonoid {g : Matrix (Fin 2) (Fin 2) R}
    (hg : g ∈ moebiusSubmonoid R) : ‖g 1 0‖ < 1 :=
  (mem_moebiusSubmonoid_iff.mp hg).2.2.1

/-- The lower right entry of a matrix in `moebiusSubmonoid R` is a multiplicative unit. -/
theorem isNormMulUnit_lowerRight_of_mem_moebiusSubmonoid {g : Matrix (Fin 2) (Fin 2) R}
    (hg : g ∈ moebiusSubmonoid R) : IsNormMulUnit (g 1 1) :=
  (mem_moebiusSubmonoid_iff.mp hg).2.2.2.1

/-- The lower right entry of a matrix in `moebiusSubmonoid R` has norm one. -/
theorem norm_lowerRight_eq_one_of_mem_moebiusSubmonoid {g : Matrix (Fin 2) (Fin 2) R}
    (hg : g ∈ moebiusSubmonoid R) : ‖g 1 1‖ = 1 :=
  (mem_moebiusSubmonoid_iff.mp hg).2.2.2.2

/-- A matrix with lower right entry one lies in `moebiusSubmonoid R` exactly when its other
entries satisfy `‖a‖ ≤ 1`, `‖b‖ ≤ 1` and `‖c‖ < 1`. This covers the diagonal matrices
`diag(a, 1)` and the translations `!![1, b; 0, 1]`. -/
theorem mem_moebiusSubmonoid_iff_of_eq_one {g : Matrix (Fin 2) (Fin 2) R} (hg : g 1 1 = 1) :
    g ∈ moebiusSubmonoid R ↔ ‖g 0 0‖ ≤ 1 ∧ ‖g 0 1‖ ≤ 1 ∧ ‖g 1 0‖ < 1 := by
  simp [mem_moebiusSubmonoid_iff, hg, isNormMulUnit_one]

/-- A norm-preserving ring homomorphism maps `moebiusSubmonoid S` into `moebiusSubmonoid R`. For
instance, the algebra map of a normed algebra with `‖1‖ = 1` over a normed field carries the
integral matrices with small lower left and unit lower right entry into `moebiusSubmonoid R`. -/
theorem map_mem_moebiusSubmonoid {S : Type*} [NormedRing S] [NormOneClass S] [IsUltrametricDist S]
    [HasSummableGeomSeries S] {g : Matrix (Fin 2) (Fin 2) S} (hg : g ∈ moebiusSubmonoid S)
    (φ : S →+* R) (hφ : ∀ x, ‖φ x‖ = ‖x‖) : g.map φ ∈ moebiusSubmonoid R := by
  obtain ⟨ha, hb, hc, hd, hd1⟩ := mem_moebiusSubmonoid_iff.mp hg
  simp only [mem_moebiusSubmonoid_iff, Matrix.map_apply, hφ]
  exact ⟨ha, hb, hc, hd.map φ.toMonoidHom hφ, hd1⟩

end Submonoid

section Moebius

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] {k : ℕ}

/-- The **denominator** `c Xᵢ + d` of the Möbius transformation of `g = !![a, b; c, d]` in the
variable `Xᵢ` of the unit Tate algebra. It is a unit when `g ∈ moebiusSubmonoid R`
(`TauCeti.MvPowerSeries.isNormMulUnit_moebiusDenom`). -/
noncomputable def moebiusDenom (i : Fin k) (g : Matrix (Fin 2) (Fin 2) R) :
    IsRestricted.subring (R := R) fun _ : Fin k ↦ (1 : ℝ) :=
  g 1 0 • ⟨X i, isRestricted_monomial _ (Finsupp.single i 1) 1⟩ + algebraMap R _ (g 1 1)

/-- The **numerator** `a Xᵢ + b` of the Möbius transformation of `g = !![a, b; c, d]` in the
variable `Xᵢ` of the unit Tate algebra. -/
noncomputable def moebiusNum (i : Fin k) (g : Matrix (Fin 2) (Fin 2) R) :
    IsRestricted.subring (R := R) fun _ : Fin k ↦ (1 : ℝ) :=
  g 0 0 • ⟨X i, isRestricted_monomial _ (Finsupp.single i 1) 1⟩ + algebraMap R _ (g 0 1)

/-- The **Möbius series** `(a Xᵢ + b) (c Xᵢ + d)⁻¹` of `g = !![a, b; c, d]` in the variable `Xᵢ`
of the unit Tate algebra. For `g ∈ moebiusSubmonoid R` it is the quotient
`(a Xᵢ + b) / (c Xᵢ + d)` (`TauCeti.MvPowerSeries.moebius_mul_moebiusDenom`) and has Gauss norm at
most one (`TauCeti.MvPowerSeries.norm_moebius_le`). Outside that monoid the inverse is
`Ring.inverse`, which is `0` on nonunits. -/
noncomputable def moebius (i : Fin k) (g : Matrix (Fin 2) (Fin 2) R) :
    IsRestricted.subring (R := R) fun _ : Fin k ↦ (1 : ℝ) :=
  moebiusNum i g * Ring.inverse (moebiusDenom i g)

theorem moebiusNum_def (i : Fin k) (g : Matrix (Fin 2) (Fin 2) R) :
    moebiusNum i g =
      g 0 0 • ⟨X i, isRestricted_monomial _ (Finsupp.single i 1) 1⟩ + algebraMap R _ (g 0 1) :=
  (rfl)

theorem moebiusDenom_def (i : Fin k) (g : Matrix (Fin 2) (Fin 2) R) :
    moebiusDenom i g =
      g 1 0 • ⟨X i, isRestricted_monomial _ (Finsupp.single i 1) 1⟩ + algebraMap R _ (g 1 1) :=
  (rfl)

theorem moebius_def (i : Fin k) (g : Matrix (Fin 2) (Fin 2) R) :
    moebius i g = moebiusNum i g * Ring.inverse (moebiusDenom i g) :=
  (rfl)

/-- The affine series `x Xᵢ + y` as a sum of two monomials. -/
private theorem coe_smul_X_add_algebraMap (i : Fin k) (x y : R) :
    ((x • ⟨X i, isRestricted_monomial _ (Finsupp.single i 1) 1⟩ + algebraMap R _ y :
        IsRestricted.subring (R := R) fun _ : Fin k ↦ (1 : ℝ)) : _root_.MvPowerSeries (Fin k) R) =
      monomial (Finsupp.single i 1) x + monomial 0 y := by
  rw [Subring.coe_add, coe_smul_isRestrictedSubring, coe_algebraMap_isRestrictedSubring,
    ← monomial_zero_eq_C_apply]
  congr 1
  dsimp only
  rw [X_def, ← map_smul, smul_eq_mul, mul_one]

/-- The numerator `a Xᵢ + b` as a sum of two monomials. -/
theorem coe_moebiusNum (i : Fin k) (g : Matrix (Fin 2) (Fin 2) R) :
    (moebiusNum i g : _root_.MvPowerSeries (Fin k) R) =
      monomial (Finsupp.single i 1) (g 0 0) + monomial 0 (g 0 1) := by
  rw [moebiusNum_def, coe_smul_X_add_algebraMap]

/-- The denominator `c Xᵢ + d` as a sum of two monomials. -/
theorem coe_moebiusDenom (i : Fin k) (g : Matrix (Fin 2) (Fin 2) R) :
    (moebiusDenom i g : _root_.MvPowerSeries (Fin k) R) =
      monomial (Finsupp.single i 1) (g 1 0) + monomial 0 (g 1 1) := by
  rw [moebiusDenom_def, coe_smul_X_add_algebraMap]

/-- The constant term of the denominator `c Xᵢ + d` is `d`. -/
@[simp]
theorem constantCoeff_moebiusDenom (i : Fin k) (g : Matrix (Fin 2) (Fin 2) R) :
    constantCoeff (moebiusDenom i g : _root_.MvPowerSeries (Fin k) R) = g 1 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coe_moebiusDenom, map_add]
  simp [coeff_monomial, (Finsupp.single_ne_zero.mpr one_ne_zero).symm]

@[simp]
theorem moebiusNum_one (i : Fin k) :
    moebiusNum i (1 : Matrix (Fin 2) (Fin 2) R) =
      ⟨X i, isRestricted_monomial _ (Finsupp.single i 1) 1⟩ := by
  simp [moebiusNum_def]

@[simp]
theorem moebiusDenom_one (i : Fin k) : moebiusDenom i (1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
  simp [moebiusDenom_def]

@[simp]
theorem moebius_one (i : Fin k) :
    moebius i (1 : Matrix (Fin 2) (Fin 2) R) =
      ⟨X i, isRestricted_monomial _ (Finsupp.single i 1) 1⟩ := by
  simp [moebius_def]

/-- **The affine case.** When `c = 0` and `d = 1`, the Möbius series is its numerator
`a Xᵢ + b`. -/
theorem moebius_eq_moebiusNum_of_eq_zero_of_eq_one (i : Fin k) {g : Matrix (Fin 2) (Fin 2) R}
    (hc : g 1 0 = 0) (hd : g 1 1 = 1) : moebius i g = moebiusNum i g := by
  rw [moebius_def, moebiusDenom_def, hc, hd, zero_smul, zero_add, map_one, Ring.inverse_one,
    mul_one]

variable [CompleteSpace R] [NormOneClass R] {i : Fin k} {g : Matrix (Fin 2) (Fin 2) R}

/-- The denominator differs from its constant term `d` by `c Xᵢ`, of norm less than one. -/
private theorem norm_moebiusDenom_sub_C_lt (hg : g ∈ moebiusSubmonoid R) :
    ‖moebiusDenom i g - ⟨C (g 1 1), isRestricted_C _ (g 1 1)⟩‖ < ‖g 1 1‖ := by
  rw [← algebraMap_isRestrictedSubring_eq_mk_C, moebiusDenom_def, add_sub_cancel_right,
    norm_smul_X, mul_one, norm_lowerRight_eq_one_of_mem_moebiusSubmonoid hg]
  exact norm_lowerLeft_lt_one_of_mem_moebiusSubmonoid hg

/-- For `g ∈ moebiusSubmonoid R` the denominator `c Xᵢ + d` is a multiplicative unit of the
Tate algebra: its inverse is the Neumann series of `d⁻¹ c Xᵢ`. -/
theorem isNormMulUnit_moebiusDenom (hg : g ∈ moebiusSubmonoid R) :
    IsNormMulUnit (moebiusDenom i g) :=
  isNormMulUnit_of_norm_sub_C_lt (isNormMulUnit_lowerRight_of_mem_moebiusSubmonoid hg)
    (norm_moebiusDenom_sub_C_lt hg)

theorem isUnit_moebiusDenom (hg : g ∈ moebiusSubmonoid R) : IsUnit (moebiusDenom i g) :=
  (isNormMulUnit_moebiusDenom hg).isUnit

/-- For `g ∈ moebiusSubmonoid R` the denominator `c Xᵢ + d` has Gauss norm one. -/
theorem norm_moebiusDenom (hg : g ∈ moebiusSubmonoid R) : ‖moebiusDenom i g‖ = 1 := by
  rw [← IsUltrametricDist.norm_eq_of_norm_sub_lt_left
    (by rw [norm_sub_rev, norm_C]; exact norm_moebiusDenom_sub_C_lt hg),
    norm_C, norm_lowerRight_eq_one_of_mem_moebiusSubmonoid hg]

/-- For `g ∈ moebiusSubmonoid R` the inverse of the denominator has Gauss norm one. -/
theorem norm_ringInverse_moebiusDenom (hg : g ∈ moebiusSubmonoid R) :
    ‖Ring.inverse (moebiusDenom i g)‖ = 1 := by
  rw [norm_inverse_of_norm_sub_C_lt (isNormMulUnit_lowerRight_of_mem_moebiusSubmonoid hg)
    (norm_moebiusDenom_sub_C_lt hg), norm_lowerRight_eq_one_of_mem_moebiusSubmonoid hg, inv_one]

/-- For `g ∈ moebiusSubmonoid R` the Möbius series is the quotient `(a Xᵢ + b) / (c Xᵢ + d)`. -/
theorem moebius_mul_moebiusDenom (hg : g ∈ moebiusSubmonoid R) :
    moebius i g * moebiusDenom i g = moebiusNum i g := by
  rw [moebius_def, Ring.inverse_mul_cancel_right _ _ (isUnit_moebiusDenom hg)]

/-- For `g ∈ moebiusSubmonoid R` the Möbius series lies in the closed unit ball, so it can be
substituted into series restricted at radius one. -/
theorem norm_moebius_le (hg : g ∈ moebiusSubmonoid R) : ‖moebius i g‖ ≤ 1 := by
  rw [moebius_def]
  refine (norm_mul_le _ _).trans ?_
  rw [norm_ringInverse_moebiusDenom hg, mul_one, moebiusNum_def]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_smul_X, mul_one]
    exact norm_upperLeft_le_one_of_mem_moebiusSubmonoid hg
  · rw [norm_algebraMap_isRestrictedSubring]
    exact norm_upperRight_le_one_of_mem_moebiusSubmonoid hg

variable {h : Fin k → IsRestricted.subring (R := R) fun _ : Fin k ↦ (1 : ℝ)} {hh : ∀ j, ‖h j‖ ≤ 1}

omit [NormOneClass R] in
/-- Substituting `h` into the numerator `a Xᵢ + b` gives `a hᵢ + b`. -/
@[simp]
theorem restrictedAnalyticSubst_moebiusNum :
    restrictedAnalyticSubst h hh (moebiusNum i g) = g 0 0 • h i + algebraMap R _ (g 0 1) := by
  rw [moebiusNum_def, map_add, map_smul, AlgHom.commutes, restrictedAnalyticSubst_X]

omit [NormOneClass R] in
/-- Substituting `h` into the denominator `c Xᵢ + d` gives `c hᵢ + d`. -/
@[simp]
theorem restrictedAnalyticSubst_moebiusDenom :
    restrictedAnalyticSubst h hh (moebiusDenom i g) = g 1 0 • h i + algebraMap R _ (g 1 1) := by
  rw [moebiusDenom_def, map_add, map_smul, AlgHom.commutes, restrictedAnalyticSubst_X]

variable {δ : Fin k → Matrix (Fin 2) (Fin 2) R}

/-- **The cocycle law of a row.** Writing `w_δ` for the Möbius series of the matrices
`δⱼ ∈ moebiusSubmonoid R`, substituting `w_δ` into the affine series `x Xᵢ + y` built from row `r`
of `g` and multiplying by the denominator of `δᵢ` gives the affine series built from row `r` of
`g δᵢ`. Row `0` is the numerator law and row `1` the denominator law. -/
theorem restrictedAnalyticSubst_row_mul_moebiusDenom (hδ : ∀ j, δ j ∈ moebiusSubmonoid R)
    (r : Fin 2) :
    restrictedAnalyticSubst (fun j ↦ moebius j (δ j)) (fun j ↦ norm_moebius_le (hδ j))
        (g r 0 • ⟨X i, isRestricted_monomial _ (Finsupp.single i 1) 1⟩ +
          algebraMap R _ (g r 1)) * moebiusDenom i (δ i) =
      (g * δ i) r 0 • ⟨X i, isRestricted_monomial _ (Finsupp.single i 1) 1⟩ +
        algebraMap R _ ((g * δ i) r 1) := by
  rw [map_add, map_smul, AlgHom.commutes, restrictedAnalyticSubst_X, add_mul, smul_mul_assoc,
    moebius_mul_moebiusDenom (hδ i)]
  simp only [moebiusNum_def, moebiusDenom_def, Matrix.mul_apply, Fin.sum_univ_two, mul_add,
    Algebra.smul_def, map_add, map_mul]
  ring

/-- **The cocycle law of the numerators.** Substituting the Möbius series `w_δ` of the matrices
`δⱼ ∈ moebiusSubmonoid R` into the numerator of `g` and multiplying by the denominator of `δᵢ`
gives the numerator of `g δᵢ`: `(a w_δ + b) (c' Xᵢ + d') = a'' Xᵢ + b''`. -/
theorem restrictedAnalyticSubst_moebiusNum_mul_moebiusDenom
    (hδ : ∀ j, δ j ∈ moebiusSubmonoid R) :
    restrictedAnalyticSubst (fun j ↦ moebius j (δ j)) (fun j ↦ norm_moebius_le (hδ j))
        (moebiusNum i g) * moebiusDenom i (δ i) = moebiusNum i (g * δ i) :=
  restrictedAnalyticSubst_row_mul_moebiusDenom hδ 0

/-- **The cocycle law of the denominators.** Writing `w_δ` for the Möbius series of the matrices
`δⱼ ∈ moebiusSubmonoid R`, substituting `w_δ` into the denominator of `g` and multiplying by the
denominator of `δᵢ` gives the denominator of `g δᵢ`: `(c w_δ + d) (c' Xᵢ + d') = c'' Xᵢ + d''`. -/
theorem restrictedAnalyticSubst_moebiusDenom_mul_moebiusDenom
    (hδ : ∀ j, δ j ∈ moebiusSubmonoid R) :
    restrictedAnalyticSubst (fun j ↦ moebius j (δ j)) (fun j ↦ norm_moebius_le (hδ j))
        (moebiusDenom i g) * moebiusDenom i (δ i) = moebiusDenom i (g * δ i) :=
  restrictedAnalyticSubst_row_mul_moebiusDenom hδ 1

/-- **The composition law of Möbius series.** For `g` and `δⱼ` in `moebiusSubmonoid R`,
substituting the Möbius series `w_δ` of the `δⱼ` into the Möbius series of `g` in `Xᵢ` gives the
Möbius series of `g δᵢ`: `w_g(w_δ) = w_{g δ}`. -/
theorem restrictedAnalyticSubst_moebius (hg : g ∈ moebiusSubmonoid R)
    (hδ : ∀ j, δ j ∈ moebiusSubmonoid R) :
    restrictedAnalyticSubst (fun j ↦ moebius j (δ j)) (fun j ↦ norm_moebius_le (hδ j))
      (moebius i g) = moebius i (g * δ i) := by
  rw [moebius_def (g := g * δ i), Ring.eq_mul_inverse_iff_mul_eq _ _ _
    (isUnit_moebiusDenom (mul_mem hg (hδ i))),
    ← restrictedAnalyticSubst_moebiusDenom_mul_moebiusDenom hδ, ← mul_assoc, ← map_mul,
    moebius_mul_moebiusDenom hg, restrictedAnalyticSubst_moebiusNum_mul_moebiusDenom hδ]

end Moebius

section AutomorphyFactor

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R] [NormOneClass R]
  {k : ℕ}

variable (R) in
/-- The **automorphy factor of weight `n`** for `k`-tuples of matrices in `moebiusSubmonoid R`,
one for each variable: the substitution is the Möbius series `w_γ = ((aᵢ Xᵢ + bᵢ)/(cᵢ Xᵢ + dᵢ))ᵢ`
and the factor is `∏ᵢ (cᵢ Xᵢ + dᵢ) ^ nᵢ`. Its slash action is
`f ↦ ∏ᵢ (cᵢ Xᵢ + dᵢ) ^ nᵢ · f(w_γ)`. -/
noncomputable def moebiusAutomorphyFactor (n : Fin k → ℕ) :
    RestrictedAutomorphyFactor (Fin k → moebiusSubmonoid R) R k where
  subst γ i := moebius i (γ i : Matrix (Fin 2) (Fin 2) R)
  norm_subst_le γ i := norm_moebius_le (γ i).property
  factor γ := ∏ i, moebiusDenom i (γ i : Matrix (Fin 2) (Fin 2) R) ^ n i
  subst_one i := moebius_one i
  subst_mul γ δ i := (restrictedAnalyticSubst_moebius (γ i).property fun j ↦ (δ j).property).symm
  factor_one := by simp
  factor_mul γ δ := by
    simp only [Pi.mul_apply, Submonoid.coe_mul, map_prod, map_pow, ← Finset.prod_mul_distrib,
      ← mul_pow, restrictedAnalyticSubst_moebiusDenom_mul_moebiusDenom fun j ↦ (δ j).property]

variable (n : Fin k → ℕ)

@[simp]
theorem moebiusAutomorphyFactor_subst (γ : Fin k → moebiusSubmonoid R) (i : Fin k) :
    (moebiusAutomorphyFactor R n).subst γ i = moebius i (γ i : Matrix (Fin 2) (Fin 2) R) :=
  (rfl)

@[simp]
theorem moebiusAutomorphyFactor_factor (γ : Fin k → moebiusSubmonoid R) :
    (moebiusAutomorphyFactor R n).factor γ =
      ∏ i, moebiusDenom i (γ i : Matrix (Fin 2) (Fin 2) R) ^ n i :=
  (rfl)

/-- The weight-`n` factor has Gauss norm one, so the weight-`n` slash operators do not increase
the Gauss norm (`TauCeti.MvPowerSeries.RestrictedAutomorphyFactor.norm_slash_apply_le`). -/
theorem norm_moebiusAutomorphyFactor_factor (γ : Fin k → moebiusSubmonoid R) :
    ‖(moebiusAutomorphyFactor R n).factor γ‖ = 1 := by
  rw [moebiusAutomorphyFactor_factor,
    IsNormMulUnit.norm_prod fun i _ ↦ (isNormMulUnit_moebiusDenom (γ i).property).pow _]
  exact Finset.prod_eq_one fun i _ ↦ by
    rw [(isNormMulUnit_moebiusDenom (γ i).property).norm_pow, norm_moebiusDenom (γ i).property,
      one_pow]

end AutomorphyFactor

end TauCeti.MvPowerSeries
