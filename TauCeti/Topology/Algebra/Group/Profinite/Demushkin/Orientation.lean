/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.GeneratedClosedSubgroups
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.D0
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicUnits
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# The standard orientation of `D₀`

The standard dyadic one-relator pro-`2` group `D₀ = ⟨A, S, Y ∣ A²S⁴(S,Y)⟩` carries a marked
continuous character `D₀ → ℤ_2ˣ`, its **standard orientation**, with values `-1`, `1` and `(-3)⁻¹`
on `A`, `S` and `Y`. It exists because these values kill the relator: `(-1)² · 1⁴ · 1 = 1`, the
commutator dying because `ℤ_2ˣ` is abelian. In the normal form `x₁² x₂^{2^f} (x₂, x₃)` of a
Demushkin group of odd rank with `q = 2`, these are the tabulated character values at `f = 2`,
namely `χ(x₁) = -1` and `χ(x₃) = (1 - 2²)⁻¹`, so the orientation is surjective: `-1` and `-3`
topologically generate `ℤ_2ˣ = {±1} × (1 + 4ℤ_2)`. The marked generators topologically generate
`D₀`, so the standard orientation is the only continuous character with these values.

## Main declarations

* `TauCeti.negThreeUnit`: the `2`-adic unit `-3`.
* `TauCeti.standardD0Orientation`: the standard orientation `D₀ →ₜ* ℤ_2ˣ`, with its values
  `TauCeti.standardD0Orientation_d0A`, `TauCeti.standardD0Orientation_d0S` and
  `TauCeti.standardD0Orientation_d0Y`.

## Main results

* `TauCeti.standardD0Orientation_relator`: any character of the free pro-`2` group with values
  `-1` on `A` and `1` on `S` kills the relator `A²S⁴(S,Y)`, regardless of its value on `Y`.
* `TauCeti.standardD0Orientation_surjective`: the standard orientation is surjective.
* `TauCeti.standardD0Orientation_unique`: it is the only continuous character of `D₀` with these
  values on the marked generators.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132,
  Theorem 4 and its corollary.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Chapter III, §9.
* D. Roe, D. Turturean, *A Presentation of the Absolute Galois Group of ℚ₂*, preprint (2026).
-/

public section

namespace TauCeti

/-- `-3` is a `2`-adic unit: `-3 = 1 + (-4)` with `2 ∣ -4`. -/
theorem isUnit_neg_three : IsUnit (-3 : ℤ_[2]) := by
  have := PadicInt.isUnit_one_add_of_dvd (p := 2) (x := -4) ⟨-2, by norm_num⟩
  -- Normalize `1 + (-4)` to `-3` in the conclusion of the unit criterion.
  rwa [show (1 : ℤ_[2]) + -4 = -3 by norm_num] at this

/-- The `2`-adic unit with value `-3`, whose inverse is the value of the standard orientation
of `D₀` on `Y`. -/
noncomputable abbrev negThreeUnit : ℤ_[2]ˣ := isUnit_neg_three.unit

/-- The value of `negThreeUnit` is `-3`. -/
@[simp]
theorem negThreeUnit_coe : (negThreeUnit : ℤ_[2]) = -3 :=
  isUnit_neg_three.unit_spec

/-- The inverse of `negThreeUnit` is the value `(1 - 2 ^ 2)⁻¹` of the orientation character table:
`(-3)⁻¹ · (1 - 2²) = 1`. -/
theorem negThreeUnit_inv_mul_one_sub_two_pow_two :
    ((negThreeUnit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * (1 - (2 : ℤ_[2]) ^ 2) = 1 := by
  -- Identify the second factor with the coerced unit so that `Units.inv_mul` applies.
  rw [show (1 : ℤ_[2]) - 2 ^ 2 = negThreeUnit by rw [negThreeUnit_coe]; norm_num, Units.inv_mul]

/-- Any character of the free pro-`2` group on `A, S, Y` with values `-1` on `A` and `1` on `S`
kills the relator `A²S⁴(S,Y)`, regardless of its value on `Y`: `(-1)² · 1⁴ · 1 = 1`. -/
theorem standardD0Orientation_relator (φ : freeProP 2 (Fin 3) →* ℤ_[2]ˣ)
    (hA : φ (freeProP.of 0) = -1) (hS : φ (freeProP.of 1) = 1) : φ d0Relator = 1 := by
  rw [d0Relator_def]
  simp [hA, hS]

/-- **The standard orientation of `D₀`**: the continuous character `D₀ →ₜ* ℤ_2ˣ` with values
`-1`, `1`, `(-3)⁻¹` on the marked generators `A`, `S`, `Y`. -/
noncomputable def standardD0Orientation : demushkinD0 →ₜ* ℤ_[2]ˣ :=
  d0Lift isProP_units_padicInt_two (-1) 1 negThreeUnit⁻¹ (by simp)

/-- The standard orientation sends `A` to `-1`. -/
@[simp]
theorem standardD0Orientation_d0A : standardD0Orientation d0A = -1 :=
  d0Lift_d0A _ _ _ _ _

/-- The standard orientation sends `S` to `1`. -/
@[simp]
theorem standardD0Orientation_d0S : standardD0Orientation d0S = 1 :=
  d0Lift_d0S _ _ _ _ _

/-- The standard orientation sends `Y` to `(-3)⁻¹`. -/
@[simp]
theorem standardD0Orientation_d0Y : standardD0Orientation d0Y = negThreeUnit⁻¹ :=
  d0Lift_d0Y _ _ _ _ _

/-- The standard orientation of `D₀` is **surjective**: its range is closed, being the continuous
image of a compact group, and contains `-1` and `(-3)⁻¹`, which topologically generate
`ℤ_2ˣ = {±1} × (1 + 4ℤ_2)`. -/
theorem standardD0Orientation_surjective : Function.Surjective standardD0Orientation := by
  set R : Subgroup ℤ_[2]ˣ := standardD0Orientation.toMonoidHom.range
  have hR : IsClosed (R : Set ℤ_[2]ˣ) := by
    rw [MonoidHom.coe_range, ContinuousMonoidHom.coe_toMonoidHom]
    exact (isCompact_range standardD0Orientation.continuous).isClosed
  have hle : unitsPlusMinus 2 ≤ R := by
    rw [← topologicalClosure_zpowers_neg_one_sup_zpowers_eq_unitsPlusMinus le_rfl
      negThreeUnit_inv_mul_one_sub_two_pow_two]
    refine Subgroup.topologicalClosure_minimal _ (sup_le (Subgroup.zpowers_le.mpr ⟨d0A, ?_⟩)
      (Subgroup.zpowers_le.mpr ⟨d0Y, ?_⟩)) hR
    · exact standardD0Orientation_d0A
    · exact standardD0Orientation_d0Y
  rw [unitsPlusMinus_two] at hle
  exact MonoidHom.range_eq_top.mp (top_le_iff.mp hle)

/-- The standard orientation is the **only** continuous character of `D₀` with values `-1`, `1`,
`(-3)⁻¹` on `A`, `S`, `Y`, because the marked generators topologically generate `D₀`. -/
theorem standardD0Orientation_unique (ψ : demushkinD0 →ₜ* ℤ_[2]ˣ) (hA : ψ d0A = -1)
    (hS : ψ d0S = 1) (hY : ψ d0Y = negThreeUnit⁻¹) : ψ = standardD0Orientation :=
  d0_hom_ext (by rw [hA, standardD0Orientation_d0A]) (by rw [hS, standardD0Orientation_d0S])
    (by rw [hY, standardD0Orientation_d0Y])

end TauCeti
