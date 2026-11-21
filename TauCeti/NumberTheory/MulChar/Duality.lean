/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.MulChar.Duality

/-!
# Duality for multiplicative characters of a monoid with finitely many units

Let `M` be a commutative monoid with finitely many units and `R` a domain. Mathlib's
`MulChar.finite` says that there are only finitely many characters `MulChar M R`. This file adds
the `Fintype` instance that sums over all characters need.

With enough roots of unity in `R`, the characters separate the subgroups of `Mˣ`: a unit `u` lies
in a subgroup `H` if and only if every character that is trivial on `H` is trivial at `u`. This is
Mathlib's `CommGroup.forall_monoidHom_apply_eq_one_iff` for the characters `Mˣ →* Rˣ`, transported
along `MulChar.equivToUnitHom`.

## Main results

* `MulChar.instFintypeMulChar`: `MulChar M R` is a `Fintype` for `Mˣ` finite and `R` a domain.
* `Subgroup.mem_iff_forall_mulChar_apply_eq_one`: `u ∈ H` if and only if every character trivial
  on `H` is trivial at `u`.
-/

public section

namespace MulChar

/-- The characters of a monoid with finitely many units, with values in a domain, form a finite
type (Mathlib's `MulChar.finite`). This instance lets one write sums over all characters. -/
noncomputable instance instFintypeMulChar {M R : Type*} [CommMonoid M] [Finite Mˣ] [CommRing R]
    [IsDomain R] : Fintype (MulChar M R) :=
  .ofFinite _

end MulChar

namespace Subgroup

variable {M R : Type*} [CommMonoid M] [Finite Mˣ] [CommRing R]
  [HasEnoughRootsOfUnity R (Monoid.exponent Mˣ)]

/-- A unit lies in a subgroup `H` of `Mˣ` if and only if every character trivial on `H` is
trivial at it. -/
theorem mem_iff_forall_mulChar_apply_eq_one (H : Subgroup Mˣ) {u : Mˣ} :
    u ∈ H ↔ ∀ χ : MulChar M R, (∀ h ∈ H, χ h = 1) → χ u = 1 := by
  rw [← CommGroup.forall_monoidHom_apply_eq_one_iff R H u]
  refine ⟨fun h χ hχ ↦ ?_, fun h φ hφ ↦ ?_⟩
  · have := h (MulChar.equivToUnitHom χ) fun y hy ↦ Units.ext (by simpa using hχ y hy)
    simpa using congrArg Units.val this
  · refine Units.ext ?_
    simpa using h (MulChar.equivToUnitHom.symm φ) fun y hy ↦ by
      simpa using congrArg Units.val (hφ y hy)

end Subgroup
