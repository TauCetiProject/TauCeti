/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Ring.MulUnit
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Basic
import TauCeti.Analysis.Normed.Group.Ultra

/-!
# Units of restricted power series

Let `R` be a complete ultrametric normed ring with `‖1‖ = 1`, and let `c` be positive polyradii.
A restricted series `f ∈ R{X/c}` close to a constant `a` that is a multiplicative unit of `R`
(`TauCeti.IsNormMulUnit`), in the sense that `‖f - a‖ < ‖a‖` for the Gauss norm, factors as

```text
f = a * (1 - x),    x = a⁻¹ * (a - f),    ‖x‖ = ‖f - a‖ / ‖a‖ < 1,
```

so it is invertible with inverse given by the Neumann series `∑ₙ xⁿ a⁻¹`, and it is again a
multiplicative unit, of norm `‖a‖`. No commutativity of `R` and no multiplicativity of its norm
is needed; in particular `R` may have nilpotents. Over the dual numbers `K[ε]` the series
`1 + εX` is a unit although its coefficient `ε` may have norm one, so the converse below does not
extend to such rings.

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

/-- The factorization `f = a * (1 - a⁻¹ * (a - f))` behind the Neumann series criterion. -/
private theorem eq_C_mul_one_sub (a : Rˣ) (f : IsRestricted.subring (R := R) c) :
    f = ⟨C (a : R), isRestricted_C c _⟩ *
      (1 - ⟨C ((a⁻¹ : Rˣ) : R), isRestricted_C c _⟩ * (⟨C (a : R), isRestricted_C c _⟩ - f)) := by
  have h : (⟨C (a : R), isRestricted_C c _⟩ : IsRestricted.subring (R := R) c) *
      ⟨C ((a⁻¹ : Rˣ) : R), isRestricted_C c _⟩ = 1 :=
    (Units.map
      (C.codRestrict (IsRestricted.subring (R := R) c) (isRestricted_C c)).toMonoidHom a).mul_inv
  rw [mul_sub, mul_one, ← mul_assoc, h, one_mul, sub_sub_cancel]

variable [∀ i, Fact (0 < c i)]

section NormOne

variable [NormOneClass R]

/-- Constant series preserve multiplicative units, since taking constant series is a
norm-preserving ring homomorphism. -/
theorem isNormMulUnit_C {u : R} (hu : IsNormMulUnit u) :
    IsNormMulUnit (⟨C u, isRestricted_C c u⟩ : IsRestricted.subring (R := R) c) :=
  hu.map (C.codRestrict (IsRestricted.subring (R := R) c) (isRestricted_C c)) (norm_C (c := c))

/-- If `‖f - a‖ < ‖a‖` for a multiplicative unit `a`, then `a⁻¹ * (a - f)` has norm less than
one. -/
private theorem norm_C_inv_mul_sub_lt_one {a : Rˣ} (ha : IsNormMulUnit (a : R))
    {f : IsRestricted.subring (R := R) c}
    (hf : ‖f - ⟨C (a : R), isRestricted_C c _⟩‖ < ‖(a : R)‖) :
    ‖(⟨C ((a⁻¹ : Rˣ) : R), isRestricted_C c _⟩ : IsRestricted.subring (R := R) c) *
      (⟨C (a : R), isRestricted_C c _⟩ - f)‖ < 1 := by
  rw [(isNormMulUnit_C ha.units_inv).norm_mul, norm_C, (Units.isNormMulUnit_iff_norm_inv a).mp ha,
    norm_sub_rev, inv_mul_lt_one₀ ((norm_nonneg _).trans_lt hf)]
  exact hf

variable [CompleteSpace R]

/-- **Neumann series criterion.** Over a complete ultrametric norm-one ring, a restricted series
whose distance from a constant multiplicative unit `a` is less than `‖a‖` is a multiplicative
unit. -/
theorem isNormMulUnit_of_norm_sub_C_lt {a : R} (ha : IsNormMulUnit a)
    {f : IsRestricted.subring (R := R) c} (hf : ‖f - ⟨C a, isRestricted_C c a⟩‖ < ‖a‖) :
    IsNormMulUnit f := by
  obtain ⟨u, rfl⟩ := ha.isUnit
  rw [eq_C_mul_one_sub u f, sub_eq_add_neg]
  exact (isNormMulUnit_C ha).mul
    (isNormMulUnit_one_add (by rw [norm_neg]; exact norm_C_inv_mul_sub_lt_one ha hf))

/-- **The Neumann series of the inverse.** If `‖f - a‖ < ‖a‖` for a constant multiplicative unit
`a`, then `x = a⁻¹ * (a - f)` has norm less than one and `f⁻¹ = ∑ₙ xⁿ * a⁻¹`. -/
theorem hasSum_inverse_of_norm_sub_C_lt {a : Rˣ} (ha : IsNormMulUnit (a : R))
    {f : IsRestricted.subring (R := R) c}
    (hf : ‖f - ⟨C (a : R), isRestricted_C c _⟩‖ < ‖(a : R)‖) :
    HasSum (fun n : ℕ ↦
      ((⟨C ((a⁻¹ : Rˣ) : R), isRestricted_C c _⟩ : IsRestricted.subring (R := R) c) *
        (⟨C (a : R), isRestricted_C c _⟩ - f)) ^ n * ⟨C ((a⁻¹ : Rˣ) : R), isRestricted_C c _⟩)
      (Ring.inverse f) := by
  have hA := (isNormMulUnit_C (c := c) ha).isUnit
  have hB : Ring.inverse (⟨C (a : R), isRestricted_C c _⟩ : IsRestricted.subring (R := R) c) =
      ⟨C ((a⁻¹ : Rˣ) : R), isRestricted_C c _⟩ :=
    Ring.inverse_unit
      (Units.map (C.codRestrict (IsRestricted.subring (R := R) c) (isRestricted_C c)).toMonoidHom a)
  have hf' : Ring.inverse f = Ring.inverse (1 - ⟨C ((a⁻¹ : Rˣ) : R), isRestricted_C c _⟩ *
      (⟨C (a : R), isRestricted_C c _⟩ - f)) * ⟨C ((a⁻¹ : Rˣ) : R), isRestricted_C c _⟩ := by
    conv_lhs => rw [eq_C_mul_one_sub a f]
    rw [Ring.inverse_mul (.inl hA), hB]
  rw [hf']
  exact (hasSum_geom_series_inverse _ (norm_C_inv_mul_sub_lt_one ha hf)).mul_right _

/-- If `‖f - a‖ < ‖a‖` for a constant multiplicative unit `a`, then the inverse of `f` has norm
`‖a‖⁻¹`. -/
theorem norm_inverse_of_norm_sub_C_lt {a : R} (ha : IsNormMulUnit a)
    {f : IsRestricted.subring (R := R) c} (hf : ‖f - ⟨C a, isRestricted_C c a⟩‖ < ‖a‖) :
    ‖Ring.inverse f‖ = ‖a‖⁻¹ := by
  obtain ⟨u, hu⟩ := (isNormMulUnit_of_norm_sub_C_lt ha hf).isUnit
  have h := (Units.isNormMulUnit_iff_norm_inv u).mp (hu ▸ isNormMulUnit_of_norm_sub_C_lt ha hf)
  rw [← hu, Ring.inverse_unit, h, hu, ← IsUltrametricDist.norm_eq_of_norm_sub_lt_left
    (x := (⟨C a, isRestricted_C c a⟩ : IsRestricted.subring (R := R) c))
    (by rwa [norm_sub_rev, norm_C]), norm_C]

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

end MvPowerSeries
