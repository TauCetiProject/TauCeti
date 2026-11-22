/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.NumberTheory.MulChar.Duality

/-!
# The finite type of multiplicative characters of a monoid with finitely many units

Let `M` be a commutative monoid with finitely many units and `R` a domain. Mathlib's
`MulChar.finite` says that there are only finitely many characters `MulChar M R`. This file adds
the `Fintype` instance that sums over all characters need.

The characters trivial on a subgroup `H` of `Mˣ` are the characters of the quotient `Mˣ ⧸ H`.

## Main results

* `MulChar.instFintypeMulChar`: `MulChar M R` is a `Fintype` for `Mˣ` finite and `R` a domain.
* `MulChar.subtypeTrivialOnEquivQuotient`: the characters trivial on `H` correspond to the
  homomorphisms `Mˣ ⧸ H →* Rˣ`.
-/

public section

namespace MulChar

/-- The characters of a monoid with finitely many units, with values in a domain, form a finite
type (Mathlib's `MulChar.finite`). This instance lets one write sums over all characters. -/
noncomputable instance instFintypeMulChar {M R : Type*} [CommMonoid M] [Finite Mˣ] [CommRing R]
    [IsDomain R] : Fintype (MulChar M R) :=
  .ofFinite _

section TrivialOn

variable {M R : Type*} [CommMonoid M] [CommMonoidWithZero R]

/-- The characters trivial on a subgroup `H` of `Mˣ` correspond to the homomorphisms
`Mˣ ⧸ H →* Rˣ`: Mathlib's `MulChar.equivToUnitHom` followed by
`MonoidHom.domRestrictHomKerEquiv`. -/
noncomputable def subtypeTrivialOnEquivQuotient (H : Subgroup Mˣ) :
    {χ : MulChar M R // ∀ h ∈ H, χ h = 1} ≃ (Mˣ ⧸ H →* Rˣ) :=
  (equivToUnitHom.subtypeEquiv fun χ ↦ by
    simp [MonoidHom.mem_ker, MonoidHom.domRestrict_eq_one_iff, Units.ext_iff]).trans
    (MonoidHom.domRestrictHomKerEquiv Rˣ H).toEquiv

/-- The quotient character attached to `χ` takes the value `χ u` at the class of `u`. -/
@[simp]
theorem subtypeTrivialOnEquivQuotient_apply (H : Subgroup Mˣ)
    (χ : {χ : MulChar M R // ∀ h ∈ H, χ h = 1}) (u : Mˣ) :
    (subtypeTrivialOnEquivQuotient H χ (u : Mˣ ⧸ H) : R) = (χ : MulChar M R) u := by
  simp [subtypeTrivialOnEquivQuotient]

/-- The character attached to a quotient character `ψ` takes the value `ψ u` at a unit `u`. -/
@[simp]
theorem subtypeTrivialOnEquivQuotient_symm_apply (H : Subgroup Mˣ) (ψ : Mˣ ⧸ H →* Rˣ) (u : Mˣ) :
    ((subtypeTrivialOnEquivQuotient H).symm ψ : MulChar M R) u = ((ψ (u : Mˣ ⧸ H) : Rˣ) : R) := by
  rw [← subtypeTrivialOnEquivQuotient_apply, Equiv.apply_symm_apply]

end TrivialOn

end MulChar
