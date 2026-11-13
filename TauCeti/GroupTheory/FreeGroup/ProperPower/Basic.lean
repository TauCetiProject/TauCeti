/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.Basic
public import TauCeti.GroupTheory.SpecificGroups.Heisenberg
public import TauCeti.GroupTheory.ProperPower

/-!
# Proper powers in free groups

Free generators and commutators of distinct generators are not proper powers; in particular, a
free generator is not a square. For the commutator this is detected by the integer Heisenberg
group, in which the commutator has central coordinate one. The same holds for the commutator
`a⁻¹ b⁻¹ a b` in the convention of surface groups, a conjugate of `⁅a, b⁆ = a b a⁻¹ b⁻¹`.
-/

public section

namespace FreeGroup

variable {α : Type*}
open scoped commutatorElement

/-- The square of any free generator is a proper power. -/
theorem isProperPower_of_sq (a : α) : Group.IsProperPower (of a ^ 2) :=
  Group.isProperPower_pow (of a) (by omega)

/-- A coordinate homomorphism sending a chosen free generator to the generator of
`Multiplicative ℤ`. -/
theorem exists_monoidHom_apply_eq_ofAdd_one (a : α) :
    ∃ f : FreeGroup α →* Multiplicative ℤ, f (of a) = Multiplicative.ofAdd 1 := by
  classical
  let f : FreeGroup α →* Multiplicative ℤ :=
    FreeGroup.lift (fun b => if b = a then Multiplicative.ofAdd 1 else 1)
  exact ⟨f, by simp [f]⟩

/-- A free generator is not a proper power. -/
@[simp] theorem not_isProperPower_of (a : α) : ¬ Group.IsProperPower (of a) := by
  obtain ⟨f, hf⟩ := exists_monoidHom_apply_eq_ofAdd_one a
  intro h
  exact Group.not_isProperPower_ofAdd_one (by simpa [hf] using Group.IsProperPower.map f h)

/-- A free generator is not a square. -/
@[simp] theorem not_isSquare_of (a : α) : ¬IsSquare (of a) := fun ⟨r, hr⟩ =>
  not_isProperPower_of a (hr ▸ sq r ▸ Group.isProperPower_pow r le_rfl)

/-- If a generator of a free group is the `m`-th power of some element, then `m = ±1`. -/
theorem natAbs_eq_one_of_of_eq_zpow {a : α} {r : FreeGroup α} {m : ℤ} (h : of a = r ^ m) :
    m.natAbs = 1 :=
  Group.natAbs_eq_one_of_not_isProperPower_zpow (h ▸ FreeGroup.not_isProperPower_of a)

/-- The commutator of two distinct free generators is not a proper power. -/
theorem not_isProperPower_commutator {a b : α} (hab : a ≠ b) :
    ¬ Group.IsProperPower ⁅of a, of b⁆ := by
  classical
  let f : FreeGroup α →* TauCeti.HeisenbergGroup ℤ :=
    FreeGroup.lift (fun c =>
      if c = a then ⟨1, 0, 0⟩ else if c = b then ⟨0, 1, 0⟩ else 1)
  have ha : f (of a) = ⟨1, 0, 0⟩ := by simp [f]
  have hb : f (of b) = ⟨0, 1, 0⟩ := by simp [f, hab.symm]
  intro h
  apply TauCeti.HeisenbergGroup.not_isProperPower_mk_zero_zero_one
  simpa [ha, hb, TauCeti.HeisenbergGroup.commutatorElement_eq] using
    Group.IsProperPower.map f h

/-- The commutator `a⁻¹ b⁻¹ a b` of two distinct free generators, in the convention
`[x, y] = x⁻¹ y⁻¹ x y` of surface groups, is not a proper power. -/
theorem not_isProperPower_inv_mul_inv_mul_mul {a b : α} (hab : a ≠ b) :
    ¬ Group.IsProperPower ((of a)⁻¹ * (of b)⁻¹ * of a * of b) := by
  -- It is the conjugate of `⁅a, b⁆` by `(b a)⁻¹`.
  have h : (of a)⁻¹ * (of b)⁻¹ * of a * of b =
      (of b * of a)⁻¹ * ⁅of a, of b⁆ * (of b * of a)⁻¹⁻¹ := by
    simp [commutatorElement_def, mul_assoc]
  rw [h, Group.isProperPower_conj_iff]
  exact not_isProperPower_commutator hab

end FreeGroup
