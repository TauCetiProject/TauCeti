/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Topology
public import TauCeti.Algebra.AlgebraicGroup.PrimeUnit
import Mathlib.NumberTheory.Padics.ProperSpace
import TauCeti.NumberTheory.NumberField.SUnits.Rat.Structure

/-!
# Prime-units of the multiplicative group

For a prime `l`, the `l`-units of the multiplicative group `𝔾ₘ` over `ℚ` are exactly the rational
numbers `± lⁿ` with `n ∈ ℤ`. A rational point `γ` with unit `u = pointsMulEquiv γ` has relatively
compact powers in `𝔾ₘ(ℚ_v) = ℚ_vˣ` exactly when `‖u‖_v = 1`
(`TauCeti.MultiplicativeGroup.isCompact_closure_zpowers_iff_norm_eq_one`), and a rational number
is a `v`-adic unit at every prime `v ≠ l` exactly when it is `± lⁿ`
(`Padic.forall_norm_rat_eq_one_iff_exists_zpow`).

The inverse powers matter: for a prime `q ≠ l`, the positive powers of `q` are bounded in `ℚ_q`,
but `q` is not an `l`-unit, since `q⁻ⁿ` is unbounded.

## Main declarations

* `TauCeti.MultiplicativeGroup.isPrimeUnit_iff_exists_zpow`: the `l`-units of `𝔾ₘ(ℚ)` are the
  numbers `± lⁿ`.

## References

* M. Kisin, K. Madapusi Pera, S. W. Shin, *Honda–Tate theory for Shimura varieties*, Duke Math.
  J. 171 (2022), §2.2.3.
-/

public section

open WithConv
open scoped LaurentPolynomial

namespace TauCeti.MultiplicativeGroup

/-- For a prime `l`, a rational point `γ` of the multiplicative group is an `l`-unit exactly when
its unit `pointsMulEquiv γ` is `± lⁿ` for an integer `n`. -/
theorem isPrimeUnit_iff_exists_zpow {l : ℕ} [Fact l.Prime] {γ : WithConv (ℚ[T;T⁻¹] →ₐ[ℚ] ℚ)} :
    HopfAlgebra.IsPrimeUnit l γ ↔
      ∃ n : ℤ, (pointsMulEquiv γ : ℚ) = (l : ℚ) ^ n ∨ (pointsMulEquiv γ : ℚ) = -(l : ℚ) ^ n := by
  -- At each prime `v`, compactness of the closure of the powers is `‖γ‖_v = 1`.
  have hv (v : ℕ) [Fact v.Prime] :
      IsCompact (closure (Subgroup.zpowers (AlgHom.mapValue (Algebra.ofId ℚ ℚ_[v]) γ) :
        Set (WithConv (ℚ[T;T⁻¹] →ₐ[ℚ] ℚ_[v])))) ↔
        ‖((pointsMulEquiv γ : ℚ) : ℚ_[v])‖ = 1 := by
    rw [isCompact_closure_zpowers_iff_norm_eq_one, pointsMulEquiv_mapValue, Units.coe_map]
    simp
  rw [← Padic.forall_norm_rat_eq_one_iff_exists_zpow, HopfAlgebra.isPrimeUnit_iff]
  exact ⟨fun h p hp ↦ (hv p).mp (h p hp), fun h v _ hv' ↦ (hv v).mpr (h ⟨v, Fact.out⟩ hv')⟩

end TauCeti.MultiplicativeGroup
