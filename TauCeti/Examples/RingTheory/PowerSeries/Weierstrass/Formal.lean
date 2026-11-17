/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Formal
import Mathlib.RingTheory.PowerSeries.Inverse
import TauCeti.NumberTheory.Padics.Basic
import TauCeti.RingTheory.PowerSeries.Restricted

/-!
# Formal and normed Weierstrass degrees over `ℤ_[p]`

These examples compare the invariants of formal Weierstrass preparation over the complete discrete
valuation ring `ℤ_[p]` with the normed Weierstrass degrees of the same series in `ℚ_[p]⟦X⟧`, read
along the inclusion `PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]`.

* The series `p + X + X ^ 2` has μ-invariant `0` and λ-invariant `1`: its first unit coefficient
  is the linear one, so its formal distinguished polynomial has degree one. At every radius
  `r < 1` close enough to one it is distinguished of degree `1` in the normed sense, in agreement
  with the formal degree. At the radius one, however, it is distinguished of degree `2`, the last
  index of a unit coefficient: the normed unit-disc Weierstrass degree is two, and it differs from
  the formal degree because `p + X + X ^ 2` has two unit coefficients.
* The geometric series `∑ Xⁿ` is a unit of `ℤ_[p]⟦X⟧`, with μ- and λ-invariants `0`, although it
  is not restricted at the radius one. So formal preparation applies to series to which normed
  preparation at the radius one does not.

## References

* L. Washington, *Introduction to Cyclotomic Fields*, second edition, GTM 83, §7.1.
* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, Grundlehren 261, Springer,
  1984, §5.2.
-/

public section

open PowerSeries IsDiscreteValuationRing IsLocalRing Filter Topology

namespace TauCeti.Examples

variable {p : ℕ} [Fact p.Prime]

/-- The coefficients of `p + X + X ^ 2`. -/
private theorem coeff_C_add_X_add_X_sq (m : ℕ) :
    coeff m (C (p : ℤ_[p]) + X + X ^ 2) =
      (if m = 0 then (p : ℤ_[p]) else 0) + (if m = 1 then 1 else 0) + if m = 2 then 1 else 0 := by
  simp only [map_add, coeff_C, coeff_X, coeff_X_pow]

/-- The series `p + X + X ^ 2` over `ℤ_[p]` has μ-invariant `0`. -/
theorem muInvariant_C_add_X_add_X_sq : (C (p : ℤ_[p]) + X + X ^ 2).muInvariant = 0 :=
  nonpos_iff_eq_zero.mp <| (muInvariant_le_addVal_coeff _ 1).trans_eq <| by
    rw [coeff_C_add_X_add_X_sq]
    simp

/-- The series `p + X + X ^ 2` over `ℤ_[p]` has λ-invariant `1`: its constant coefficient `p` is
not a unit, and its linear coefficient is. -/
theorem lambdaInvariant_C_add_X_add_X_sq : (C (p : ℤ_[p]) + X + X ^ 2).lambdaInvariant = 1 := by
  rw [lambdaInvariant_eq_iff, muInvariant_C_add_X_add_X_sq]
  refine ⟨by rw [coeff_C_add_X_add_X_sq]; simp, fun i hi => ?_⟩
  obtain rfl : i = 0 := by omega
  rw [coeff_C_add_X_add_X_sq]
  simp [addVal_uniformizer PadicInt.irreducible_p]

/-- At every radius `r < 1` close enough to one, `p + X + X ^ 2` is distinguished of degree `1`
in `ℚ_[p]⟦X⟧`, its formal Weierstrass degree. -/
theorem eventually_isDistinguished_map_C_add_X_add_X_sq :
    ∀ᶠ r in 𝓝[<] (1 : ℝ), PowerSeries.IsDistinguished r 1
      ((C (p : ℤ_[p]) + X + X ^ 2).map PadicInt.Coe.ringHom) := by
  filter_upwards [PowerSeries.eventually_isDistinguished_and_isLowestDominant_map_lambdaInvariant
    PadicInt.norm_coe_ringHom_le_one (fun _ => PadicInt.norm_coe_ringHom_lt_one_iff.mpr)
    (muInvariant_C_add_X_add_X_sq (p := p))] with r hr
  rw [← lambdaInvariant_C_add_X_add_X_sq (p := p)]
  exact hr.1

/-- At the radius one, `p + X + X ^ 2` is distinguished of degree `2` in `ℚ_[p]⟦X⟧`: the normed
unit-disc Weierstrass degree is the last index of a unit coefficient, not the formal degree `1`. -/
theorem isDistinguished_one_map_C_add_X_add_X_sq :
    PowerSeries.IsDistinguished 1 2 ((C (p : ℤ_[p]) + X + X ^ 2).map PadicInt.Coe.ringHom) := by
  refine (PowerSeries.isDistinguished_one_map_iff PadicInt.norm_coe_ringHom_le_one
    (fun _ => PadicInt.norm_coe_ringHom_lt_one_iff.mpr)
    (muInvariant_eq_zero_iff.mp muInvariant_C_add_X_add_X_sq)).mpr
    ⟨by rw [coeff_C_add_X_add_X_sq]; simp, fun m hm => ?_⟩
  rw [coeff_C_add_X_add_X_sq]
  simp [show m ≠ 0 by omega, show m ≠ 1 by omega, show m ≠ 2 by omega]

/-- The geometric series `∑ Xⁿ` is a unit of `ℤ_[p]⟦X⟧`, so its μ- and λ-invariants vanish, but it
is not restricted at the radius one. -/
example : IsUnit (mk 1 : ℤ_[p]⟦X⟧) ∧ (mk 1 : ℤ_[p]⟦X⟧).muInvariant = 0 ∧
    (mk 1 : ℤ_[p]⟦X⟧).lambdaInvariant = 0 ∧ ¬(mk 1 : ℤ_[p]⟦X⟧).IsRestricted 1 := by
  have hu : IsUnit (mk 1 : ℤ_[p]⟦X⟧) := isUnit_iff_constantCoeff.mpr (by simp)
  exact ⟨hu, muInvariant_eq_zero_of_isUnit hu, lambdaInvariant_eq_zero_of_isUnit hu,
    PowerSeries.not_isRestricted_mk_one⟩

end TauCeti.Examples
