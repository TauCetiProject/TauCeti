/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Measure.CharacterIntegral
public import TauCeti.NumberTheory.Padics.Measure.Moments
public import TauCeti.NumberTheory.Padics.Measure.Units.Basic

/-!
# Positive moments and regular elements of the measure algebra of `ℤ_pˣ`

Let `M = D(ℤ_pˣ, ℤ_p)` be the convolution algebra of `ℤ_p`-valued measures on the unit group.
The power characters `t_k : u ↦ u ^ k` (`PadicInt.unitsPowCharacter p k`) are continuous
characters, so `μ ↦ μ (t_k)` is a ring homomorphism `M → ℤ_p`. This file proves that the positive
moments `μ (t_k)`, `k > 0`, determine a measure on the units: pushed forward to `ℤ_p`, a measure
with vanishing positive moments has constant Amice transform, hence is a multiple of the Dirac
measure at `0`, and a measure supported on the units can only be such a multiple if it vanishes.

Since `ℤ_p` is a domain, it follows that a measure all of whose positive moments are nonzero is a
non-zero-divisor of `M`. In particular `δ_a - 1` is a non-zero-divisor exactly when the unit `a`
has infinite order, for instance when `a = 1 + p`. These are the clearing factors used to evaluate
pseudo-measures on `ℤ_pˣ`: they become units in the total quotient ring of `M`. As a first
consequence, the total mass `μ ↦ μ 1` does not extend to a ring homomorphism from the total
quotient ring of `M` to `ℤ_p`, since it kills the regular element `δ_{1+p} - 1`.

## Main results

* `AbstractMeasure.units_eq_zero_of_positive_moments`: a measure on `ℤ_pˣ` with vanishing positive
  moments is zero.
* `AbstractMeasure.units_mem_nonZeroDivisors_of_positive_moments`: a measure on `ℤ_pˣ` with
  nonvanishing positive moments is a non-zero-divisor.
* `AbstractMeasure.dirac_sub_one_mem_nonZeroDivisors_iff`: `δ_a - 1` is a non-zero-divisor if and
  only if `a` has infinite order.
* `AbstractMeasure.dirac_sub_one_mem_nonZeroDivisors_of_val_eq_natCast`: `δ_a - 1` is a
  non-zero-divisor when the value of `a` is a natural number `n ≥ 2`, such as `1 + p`.
* `AbstractMeasure.no_totalMass_fraction_extension`: no ring homomorphism from the total quotient
  ring of `M` to `ℤ_p` restricts to the total mass on `M`.

## References

* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, §3.6,
  Definition 3.34, Remark 3.35 and Lemma 3.36.
-/

public noncomputable section

open scoped AbstractMeasure nonZeroDivisors

variable {p : ℕ} [Fact p.Prime]

namespace AbstractMeasure

open ContinuousMonoidHom PadicInt

/-- A `ℤ_p`-valued measure on `ℤ_pˣ` whose positive moments `μ (u ↦ u ^ k)`, `k > 0`, all vanish
is zero. -/
theorem units_eq_zero_of_positive_moments (μ : D(ℤ_[p]ˣ, ℤ_[p]))
    (hμ : ∀ k, 0 < k → μ (unitsPowCharacter p k) = 0) : μ = 0 := by
  set ν : D(ℤ_[p], ℤ_[p]) := map ⟨Units.val, Units.continuous_val⟩ μ with hν_def
  -- The pushforward `ν` to `ℤ_p` has the same positive moments, so its Amice transform is the
  -- constant `ν 1`, which is the Amice transform of `ν 1 • δ₀`.
  have hν : ∀ k, 0 < k → ν ((ContinuousMap.id ℤ_[p] • 1 : C(ℤ_[p], ℤ_[p])) ^ k) = 0 := by
    intro k hk
    rw [← hμ k hk, map_apply]
    congr 1
    ext u
    simp
  have hδ : ν = ν 1 • dirac ℤ_[p] 0 := by
    refine injective_amiceTransform ?_
    rw [(amiceTransform_eq_C_iff ν).2 hν, map_smul]
    ext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [PowerSeries.coeff_C, hn]
  -- Restricting back to the units recovers `μ`, while `δ₀` restricts to zero.
  rw [← restrictUnits_map_unitsVal μ, ← hν_def, hδ, map_smul,
    restrictUnits_dirac_of_not_isUnit not_isUnit_zero, smul_zero]

/-- A `ℤ_p`-valued measure on `ℤ_pˣ` none of whose positive moments `μ (u ↦ u ^ k)`, `k > 0`,
vanishes is a non-zero-divisor of the convolution algebra. -/
theorem units_mem_nonZeroDivisors_of_positive_moments (μ : D(ℤ_[p]ˣ, ℤ_[p]))
    (hμ : ∀ k, 0 < k → μ (unitsPowCharacter p k) ≠ 0) : μ ∈ D(ℤ_[p]ˣ, ℤ_[p])⁰ := by
  refine mem_nonZeroDivisors_iff_right.2 fun ν hν => units_eq_zero_of_positive_moments ν
    fun k hk => ?_
  have h := congrArg (characterIntegralAlgHom (unitsPowCharacter p k)) hν
  rw [map_mul, map_zero, characterIntegralAlgHom_apply, characterIntegralAlgHom_apply] at h
  exact (mul_eq_zero.1 h).resolve_right (hμ k hk)

/-- For a unit `a` of `ℤ_p`, the measure `δ_a - 1` is a non-zero-divisor of the convolution algebra
of `ℤ_pˣ` if and only if `a` has infinite order. -/
theorem dirac_sub_one_mem_nonZeroDivisors_iff (a : ℤ_[p]ˣ) :
    dirac ℤ_[p] a - 1 ∈ D(ℤ_[p]ˣ, ℤ_[p])⁰ ↔ ¬IsOfFinOrder a := by
  refine ⟨fun h hfin => ?_, fun ha => units_mem_nonZeroDivisors_of_positive_moments _
    fun k hk hzero => ha ?_⟩
  · -- If `a ^ n = 1`, then `∑_{i < n} δ_a ^ i`, of total mass `n`, is killed by `δ_a - 1`.
    obtain ⟨n, hn, han⟩ := isOfFinOrder_iff_pow_eq_one.1 hfin
    have hgeom := geom_sum_mul (diracHom a : D(ℤ_[p]ˣ, ℤ_[p])) n
    rw [← map_pow, han, map_one, sub_self, diracHom_apply,
      mul_right_mem_nonZeroDivisors_eq_zero_iff h] at hgeom
    have hmass := congrArg (characterIntegralAlgHom (1 : ℤ_[p]ˣ →ₜ* ℤ_[p])) hgeom
    simp only [map_sum, map_pow, characterIntegralAlgHom_dirac, map_zero] at hmass
    exact hn.ne' (by simpa using hmass)
  · rw [← characterIntegralAlgHom_apply, map_sub, characterIntegralAlgHom_dirac, map_one] at hzero
    exact isOfFinOrder_iff_pow_eq_one.2 ⟨k, hk, Units.ext (by simpa [sub_eq_zero] using hzero)⟩

/-- If the value of a unit `a` of `ℤ_p` is a natural number `n ≥ 2`, for instance `1 + p`, then
`δ_a - 1` is a non-zero-divisor of the convolution algebra of `ℤ_pˣ`. -/
theorem dirac_sub_one_mem_nonZeroDivisors_of_val_eq_natCast {a : ℤ_[p]ˣ} {n : ℕ} (hn : 2 ≤ n)
    (ha : (a : ℤ_[p]) = n) : dirac ℤ_[p] a - 1 ∈ D(ℤ_[p]ˣ, ℤ_[p])⁰ := by
  refine (dirac_sub_one_mem_nonZeroDivisors_iff a).2 fun hfin => ?_
  obtain ⟨k, hk, hak⟩ := isOfFinOrder_iff_pow_eq_one.1 hfin
  have h := congrArg Units.val hak
  rw [Units.val_pow_eq_pow_val, ha, Units.val_one, ← Nat.cast_pow, Nat.cast_eq_one] at h
  exact (Nat.one_lt_pow hk.ne' (by omega)).ne' h

/-- The total mass `μ ↦ μ 1` on `D(ℤ_pˣ, ℤ_p)` does not extend to a ring homomorphism from the total
quotient ring to `ℤ_p`: it kills `δ_{1+p} - 1`, which becomes a unit there. -/
theorem no_totalMass_fraction_extension :
    ¬∃ φ : FractionRing D(ℤ_[p]ˣ, ℤ_[p]) →+* ℤ_[p],
      ∀ μ, φ (algebraMap D(ℤ_[p]ˣ, ℤ_[p]) (FractionRing D(ℤ_[p]ˣ, ℤ_[p])) μ) = μ 1 := by
  rintro ⟨φ, hφ⟩
  obtain ⟨a, ha⟩ := isUnit_one_add_of_dvd (dvd_refl (p : ℤ_[p]))
  have hreg := dirac_sub_one_mem_nonZeroDivisors_of_val_eq_natCast (n := 1 + p)
    (by have := (Fact.out : p.Prime).two_le; omega) (by rw [ha]; push_cast; rfl)
  have hu := (IsLocalization.map_units (FractionRing D(ℤ_[p]ˣ, ℤ_[p])) ⟨_, hreg⟩).map φ
  rw [hφ, ← characterIntegralAlgHom_one_character, map_sub, map_one, characterIntegralAlgHom_dirac,
    ContinuousMonoidHom.coe_one, Pi.one_apply, sub_self] at hu
  exact not_isUnit_zero hu

-- The unit `-1` has order two, so `δ₋₁ - 1` is a zero divisor: `(δ₋₁ + 1) (δ₋₁ - 1) = 0`.
example : dirac ℤ_[p] (-1 : ℤ_[p]ˣ) - 1 ∉ D(ℤ_[p]ˣ, ℤ_[p])⁰ := by
  rw [dirac_sub_one_mem_nonZeroDivisors_iff, not_not]
  exact isOfFinOrder_iff_pow_eq_one.2 ⟨2, two_pos, by simp⟩

-- At `p = 3`, the unit `4 = 1 + 3` gives the regular element `δ₄ - 1`.
example (a : ℤ_[3]ˣ) (ha : (a : ℤ_[3]) = 4) : dirac ℤ_[3] a - 1 ∈ D(ℤ_[3]ˣ, ℤ_[3])⁰ :=
  dirac_sub_one_mem_nonZeroDivisors_of_val_eq_natCast (n := 4) (by norm_num) (by rw [ha]; rfl)

end AbstractMeasure
