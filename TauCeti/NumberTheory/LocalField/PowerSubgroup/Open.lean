/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Quotient
public import TauCeti.Algebra.Group.PowMonoidHom
public import TauCeti.NumberTheory.LocalField.PowerSubgroup.Basic
import Mathlib.GroupTheory.IndexNSmul

/-!
# Openness of power subgroups of a local field

When the image of a natural number `n` in a nonarchimedean local field `K` is nonzero, the
`n`-th powers in `Kˣ` contain an open deep-unit subgroup. This applies to every nonzero `n` in
mixed characteristic and to exponents prime to the characteristic in equal characteristic.
The resulting openness and closedness, and the criterion for a subgroup of finite exponent,
are used when passing from finite quotients of `Kˣ` to continuous characters.

The deep-unit power identity used here is `unitFiltration_le_range_powMonoidHom`; its proof
uses the binomial expansion and completeness of `K`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter V, §3.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §5.
-/

public section

open IsNonarchimedeanLocalField

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The subgroup of `n`-th powers of a nonarchimedean local field is open whenever
`(n : K) ≠ 0`. -/
theorem isOpen_range_powMonoidHom {n : ℕ} (hn : (n : K) ≠ 0) :
    IsOpen ((powMonoidHom n : Kˣ →* Kˣ).range : Set Kˣ) := by
  have hle : unitFiltration K (natCastValuation K n hn + 1 + natCastValuation K n hn) ≤
      (powMonoidHom n : Kˣ →* Kˣ).range := unitFiltration_le_range_powMonoidHom hn
    (i := natCastValuation K n hn + 1) fun p hp hpK hpn =>
      natCastValuation_lt_sub_one_mul_of_lt_of_dvd hn
        (Nat.lt_succ_self _) hp hpK hpn
  exact Subgroup.isOpen_mono hle (isOpen_unitFiltration _)

/-- The subgroup of `n`-th powers is closed whenever `(n : K) ≠ 0`. -/
theorem isClosed_range_powMonoidHom {n : ℕ} (hn : (n : K) ≠ 0) :
    IsClosed ((powMonoidHom n : Kˣ →* Kˣ).range : Set Kˣ) :=
  Subgroup.isClosed_of_isOpen _ (isOpen_range_powMonoidHom hn)

variable (K) in
/-- When two is nonzero, the local square-class quotient is discrete, since the squares are open.
This theorem applies to the literal quotient, with its quotient topology. -/
theorem discreteTopology_localSquareClasses (h2 : (2 : K) ≠ 0) :
    DiscreteTopology (Kˣ ⧸ Subgroup.square Kˣ) := by
  apply QuotientGroup.discreteTopology
  rw [square_eq_range_powMonoidHom]
  exact isOpen_range_powMonoidHom h2

/-- A subgroup of `Kˣ` is open if the exponent of its quotient is nonzero in `K`. -/
theorem isOpen_of_natCast_exponent_ne_zero {H : Subgroup Kˣ}
    (hH : (Monoid.exponent (Kˣ ⧸ H) : K) ≠ 0) : IsOpen (H : Set Kˣ) := by
  refine Subgroup.isOpen_mono ?_ (isOpen_range_powMonoidHom hH)
  rintro _ ⟨y, rfl⟩
  simpa [← QuotientGroup.eq_one_iff] using Monoid.pow_exponent_eq_one (y : Kˣ ⧸ H)

/-- A subgroup of `Kˣ` is open if its index is nonzero in `K`. -/
theorem isOpen_of_natCast_index_ne_zero {H : Subgroup Kˣ} (hH : (H.index : K) ≠ 0) :
    IsOpen (H : Set Kˣ) := by
  have hExp : (Monoid.exponent (Kˣ ⧸ H) : K) ≠ 0 := by
    exact ne_zero_of_dvd_ne_zero (by simpa only [H.index_eq_card] using hH)
      (Nat.cast_dvd_cast Group.exponent_dvd_nat_card)
  exact isOpen_of_natCast_exponent_ne_zero hExp

end TauCeti
