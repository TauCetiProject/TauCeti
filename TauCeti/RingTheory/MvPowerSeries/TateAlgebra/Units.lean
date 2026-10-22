/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Ring.MulUnit
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Basic

/-!
# Units of restricted power series

Let `R` be a complete ultrametric normed ring with `‖1‖ = 1`, and let `c` be positive polyradii.
A restricted series `f ∈ R{X/c}` close to a constant `a` that is a multiplicative unit of `R`
(`TauCeti.IsNormMulUnit`), in the sense that `‖f - a‖ < ‖a‖` for the Gauss norm, factors as

```text
f = a * (1 - x),    x = a⁻¹ * (a - f),    ‖x‖ = ‖f - a‖ / ‖a‖ < 1,
```

so it is invertible with inverse given by the Neumann series `∑ₙ xⁿ a⁻¹`, and it is again a
multiplicative unit, of norm `‖a‖`. This is the Neumann series criterion
`TauCeti.IsNormMulUnit.of_norm_sub_lt` applied to the constant series `a`. No commutativity of
`R` and no multiplicativity of its norm is needed; in particular `R` may have nilpotents. Over
the dual numbers `K[ε]` the series `1 + εX` is a unit although its coefficient `ε` may have norm
one, so the converse below does not extend to such rings.

When the norm of `R` is multiplicative and `R` is nontrivial, the converse holds: a restricted
series is a unit exactly when its constant coefficient is a unit and strictly dominates the
weighted norm `‖aₜ‖ cᵗ` of every other coefficient. Restrictedness turns these pointwise strict
inequalities into a uniform one, which is what the Neumann series needs. Over a field, or any
division ring, the constant coefficient need only be nonzero. These criteria hold at arbitrary
positive polyradii.

## Main results

* `MvPowerSeries.isNormMulUnit_C`: constants preserve multiplicative units.
* `MvPowerSeries.isNormMulUnit_of_norm_sub_C_lt`: a series within less than `‖a‖` of a constant
  multiplicative unit `a` is a multiplicative unit;
  `MvPowerSeries.hasSum_inverse_of_norm_sub_C_lt` gives its inverse as a Neumann series and
  `MvPowerSeries.norm_inverse_of_norm_sub_C_lt` computes its norm as `‖a‖⁻¹`.
* `MvPowerSeries.isNormMulUnit_of_norm_coeff_mul_prod_lt`: a series whose constant coefficient is
  a multiplicative unit strictly dominating every other weighted coefficient is a multiplicative
  unit.
* `MvPowerSeries.norm_coeff_mul_prod_lt_of_isUnit`: for a multiplicative coefficient norm, the
  constant coefficient of a unit strictly dominates every other weighted coefficient.
* `MvPowerSeries.isUnit_iff_isUnit_constantCoeff_and_norm_coeff_mul_prod_lt` and, over a division
  ring, `MvPowerSeries.isUnit_iff_constantCoeff_ne_zero_and_norm_coeff_mul_prod_lt`: the units of
  `R{X/c}`.
* `MvPowerSeries.forall_norm_coeff_sub_C_lt_iff`: the constant coefficient strictly dominates
  every coefficient of `f - C (constantCoeff f)` iff it is nonzero and strictly dominates every
  other coefficient of `f`.

## References

* F. Martin, *Overconvergent subanalytic subsets in the framework of Berkovich spaces*,
  J. Eur. Math. Soc. 18 (2016), Lemma 1.21 and Remark 1.22.
* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.1.3, Proposition 1.
-/

public section

namespace MvPowerSeries

open TauCeti

section NormedRing

variable {σ R : Type*} [NormedRing R] [IsUltrametricDist R] {c : σ → ℝ}

/-- The constant-series embedding into the restricted series sends `a` to the constant `C a`. -/
private theorem codRestrict_C_eq (a : R) :
    C.codRestrict (IsRestricted.subring (R := R) c) (isRestricted_C c) a =
      ⟨C a, isRestricted_C c a⟩ :=
  Subtype.ext (RingHom.codRestrict_apply _ _ _ a)

variable [∀ i, Fact (0 < c i)]

section NormOne

variable [NormOneClass R]

/-- Constant series preserve multiplicative units, since taking constant series is a
norm-preserving ring homomorphism. -/
theorem isNormMulUnit_C {u : R} (hu : IsNormMulUnit u) :
    IsNormMulUnit (⟨C u, isRestricted_C c u⟩ : IsRestricted.subring (R := R) c) := by
  rw [← codRestrict_C_eq]
  exact hu.map _ fun a ↦ norm_C a

variable [CompleteSpace R]

/-- **Neumann series criterion.** Over a complete ultrametric norm-one ring, a restricted series
whose distance from a constant multiplicative unit `a` is less than `‖a‖` is a multiplicative
unit. -/
theorem isNormMulUnit_of_norm_sub_C_lt {a : R} (ha : IsNormMulUnit a)
    {f : IsRestricted.subring (R := R) c} (hf : ‖f - ⟨C a, isRestricted_C c a⟩‖ < ‖a‖) :
    IsNormMulUnit f :=
  (isNormMulUnit_C ha).of_norm_sub_lt (by rwa [norm_C])

/-- **The Neumann series of the inverse.** If `‖f - a‖ < ‖a‖` for a constant multiplicative unit
`a`, then `x = a⁻¹ * (a - f)` has norm less than one and `f⁻¹ = ∑ₙ xⁿ * a⁻¹`. -/
theorem hasSum_inverse_of_norm_sub_C_lt {a : Rˣ} (ha : IsNormMulUnit (a : R))
    {f : IsRestricted.subring (R := R) c}
    (hf : ‖f - ⟨C (a : R), isRestricted_C c _⟩‖ < ‖(a : R)‖) :
    HasSum (fun n : ℕ ↦
      ((⟨C ((a⁻¹ : Rˣ) : R), isRestricted_C c _⟩ : IsRestricted.subring (R := R) c) *
        (⟨C (a : R), isRestricted_C c _⟩ - f)) ^ n * ⟨C ((a⁻¹ : Rˣ) : R), isRestricted_C c _⟩)
      (Ring.inverse f) := by
  set A := Units.map (C.codRestrict (IsRestricted.subring (R := R) c) (isRestricted_C c) :
    R →* IsRestricted.subring (R := R) c) a
  have hA : (A : IsRestricted.subring (R := R) c) = ⟨C (a : R), isRestricted_C c _⟩ := by
    rw [Units.coe_map, MonoidHom.coe_ofClass, codRestrict_C_eq]
  have hA' : ((A⁻¹ : (IsRestricted.subring (R := R) c)ˣ) : IsRestricted.subring (R := R) c) =
      ⟨C ((a⁻¹ : Rˣ) : R), isRestricted_C c _⟩ := by
    rw [← map_inv, Units.coe_map, MonoidHom.coe_ofClass, codRestrict_C_eq]
  have h := IsNormMulUnit.hasSum_inverse_of_norm_sub_lt (u := A) (hA ▸ isNormMulUnit_C ha)
    (by rwa [hA, norm_C])
  rwa [hA, hA'] at h

/-- If `‖f - a‖ < ‖a‖` for a constant multiplicative unit `a`, then the inverse of `f` has norm
`‖a‖⁻¹`. -/
theorem norm_inverse_of_norm_sub_C_lt {a : R} (ha : IsNormMulUnit a)
    {f : IsRestricted.subring (R := R) c} (hf : ‖f - ⟨C a, isRestricted_C c a⟩‖ < ‖a‖) :
    ‖Ring.inverse f‖ = ‖a‖⁻¹ := by
  rw [(isNormMulUnit_C ha).norm_inverse_of_norm_sub_lt (by rwa [norm_C]), norm_C]

/-- **Dominant constant coefficient.** Over a complete ultrametric norm-one ring, a restricted
series whose constant coefficient is a multiplicative unit strictly dominating the weighted norm
of every other coefficient is a multiplicative unit. -/
theorem isNormMulUnit_of_norm_coeff_mul_prod_lt {f : IsRestricted.subring (R := R) c}
    (h0 : IsNormMulUnit (constantCoeff (f : MvPowerSeries σ R)))
    (h : ∀ t ≠ 0, ‖coeff t (f : MvPowerSeries σ R)‖ * t.prod (c · ^ ·) <
      ‖constantCoeff (f : MvPowerSeries σ R)‖) :
    IsNormMulUnit f := by
  classical
  set a := constantCoeff (f : MvPowerSeries σ R)
  have : Nontrivial R := NormOneClass.nontrivial
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact h0.isUnit.ne_zero (by simp [a])
  -- The Gauss norm of `f` is attained at the constant coefficient.
  have hfa : ‖f‖ = ‖a‖ := by
    obtain ⟨t, ht⟩ := exists_achievesGaussNorm f
    rw [AchievesGaussNorm, ← norm_eq_gaussNorm] at ht
    rcases eq_or_ne t 0 with rfl | ht0
    · simpa [a, coeff_zero_eq_constantCoeff_apply] using ht.symm
    · refine absurd (h t ht0) (not_lt.mpr ?_)
      rw [ht]
      simpa [a, coeff_zero_eq_constantCoeff_apply] using norm_coeff_mul_prod_le f 0
  -- Restrictedness bounds the nonconstant weighted coefficients uniformly below `‖a‖`.
  obtain ⟨ε, hε0, hεf, hε⟩ := exists_norm_coeff_mul_prod_gap f hf0
  refine isNormMulUnit_of_norm_sub_C_lt h0 (lt_of_le_of_lt ((norm_le_iff hε0).mpr fun t ↦ ?_)
    (hfa ▸ hεf))
  rw [AddSubgroupClass.coe_sub, map_sub, coeff_C]
  split_ifs with ht
  · simp [ht, a, coeff_zero_eq_constantCoeff_apply, hε0]
  · rw [sub_zero]
    exact hε t (hfa ▸ h t ht)

end NormOne

section NormMulClass

variable [NormMulClass R] [Nontrivial R]

/-- **The constant coefficient of a unit dominates.** For a multiplicative coefficient norm, the
constant coefficient of a unit of the ring of restricted series strictly dominates the weighted
norm of every other coefficient. -/
theorem norm_coeff_mul_prod_lt_of_isUnit {f : IsRestricted.subring (R := R) c} (hf : IsUnit f)
    {t : σ →₀ ℕ} (ht : t ≠ 0) :
    ‖coeff t (f : MvPowerSeries σ R)‖ * t.prod (c · ^ ·) <
      ‖constantCoeff (f : MvPowerSeries σ R)‖ := by
  classical
  obtain ⟨g, hfg⟩ := hf.exists_right_inv
  have hfg' : (f : MvPowerSeries σ R) * g = 1 := congrArg Subtype.val hfg
  have hf0 : (f : MvPowerSeries σ R) ≠ 0 := fun h ↦ zero_ne_one (by rw [← hfg', h, zero_mul])
  have hg0 : (g : MvPowerSeries σ R) ≠ 0 := fun h ↦ zero_ne_one (by rw [← hfg', h, mul_zero])
  obtain ⟨i, j, hi, hj, himax, -, hdom'⟩ := f.2.exists_norm_coeff_mul_norm_coeff_lt g.2 hf0 hg0
  -- The dominant summand of the coefficient of `f * g = 1` at `i + j` is nonzero, so `i = 0`.
  have hdom := antidiagonal_dominant norm (f : MvPowerSeries σ R) g i j
    IsUltrametricDist.isNonarchimedean_norm norm_mul (fun a ↦ (norm_neg a).symm)
    fun p hp hne ↦ by simpa only [norm_mul] using hdom' p hp hne
  have hij : i + j = 0 := by
    by_contra hne
    rw [hfg', coeff_one, ite_eq_right hne, norm_zero, norm_mul] at hdom
    exact mul_ne_zero (norm_ne_zero_iff.mpr (f.2.coeff_ne_zero_of_achievesGaussNorm hf0 hi))
      (norm_ne_zero_iff.mpr (g.2.coeff_ne_zero_of_achievesGaussNorm hg0 hj)) hdom.symm
  obtain rfl : i = 0 := (add_eq_zero.mp hij).1
  have hlt := himax t ht
  rwa [zero_add, ← hi, Finsupp.prod_zero_index, mul_one, coeff_zero_eq_constantCoeff_apply] at hlt

/-- **The units of the ring of restricted series.** Over a complete ultrametric normed ring with
multiplicative norm, a restricted series is a unit exactly when its constant coefficient is a unit
and strictly dominates the weighted norm of every other coefficient. -/
theorem isUnit_iff_isUnit_constantCoeff_and_norm_coeff_mul_prod_lt [CompleteSpace R]
    (f : IsRestricted.subring (R := R) c) :
    IsUnit f ↔ IsUnit (constantCoeff (f : MvPowerSeries σ R)) ∧
      ∀ t ≠ 0, ‖coeff t (f : MvPowerSeries σ R)‖ * t.prod (c · ^ ·) <
        ‖constantCoeff (f : MvPowerSeries σ R)‖ := by
  have := NormMulClass.toNormOneClass (α := R)
  refine ⟨fun hf ↦ ⟨(hf.map (IsRestricted.subring (R := R) c).subtype).map _,
    fun t ht ↦ norm_coeff_mul_prod_lt_of_isUnit hf ht⟩, fun ⟨h0, h⟩ ↦ ?_⟩
  exact (isNormMulUnit_of_norm_coeff_mul_prod_lt ((isNormMulUnit_iff_isUnit _).mpr h0) h).isUnit

end NormMulClass

end NormedRing

section NormedDivisionRing

variable {σ K : Type*} [NormedDivisionRing K] [IsUltrametricDist K] [CompleteSpace K] {c : σ → ℝ}
  [∀ i, Fact (0 < c i)]

/-- **The units of a Tate algebra over a division ring.** Over a complete ultrametric normed
division ring, for instance a field, a restricted series is a unit exactly when its constant
coefficient is nonzero and strictly dominates the weighted norm of every other coefficient, that
is, when the constant coefficient is the only one attaining the Gauss norm. -/
theorem isUnit_iff_constantCoeff_ne_zero_and_norm_coeff_mul_prod_lt
    (f : IsRestricted.subring (R := K) c) :
    IsUnit f ↔ constantCoeff (f : MvPowerSeries σ K) ≠ 0 ∧
      ∀ t ≠ 0, ‖coeff t (f : MvPowerSeries σ K)‖ * t.prod (c · ^ ·) <
        ‖constantCoeff (f : MvPowerSeries σ K)‖ := by
  rw [isUnit_iff_isUnit_constantCoeff_and_norm_coeff_mul_prod_lt, isUnit_iff_ne_zero]

end NormedDivisionRing

section Coefficients

variable {σ R : Type*} [NormedRing R]

/-- The constant coefficient `a` of a series dominates the coefficients of `f - a` strictly iff it
is nonzero and dominates all other coefficients of `f` strictly. -/
theorem forall_norm_coeff_sub_C_lt_iff (f : MvPowerSeries σ R) :
    (∀ t, ‖coeff t (f - C (constantCoeff f))‖ < ‖constantCoeff f‖) ↔
      constantCoeff f ≠ 0 ∧ ∀ t ≠ 0, ‖coeff t f‖ < ‖constantCoeff f‖ := by
  classical
  refine ⟨fun h ↦ ⟨norm_pos_iff.1 ((norm_nonneg _).trans_lt (h 0)), fun t ht ↦ ?_⟩,
    fun ⟨h0, h⟩ t ↦ ?_⟩
  · simpa [coeff_C, ht] using h t
  · rcases eq_or_ne t 0 with rfl | ht
    · simpa using norm_pos_iff.2 h0
    · simpa [coeff_C, ht] using h t ht

end Coefficients

end MvPowerSeries
