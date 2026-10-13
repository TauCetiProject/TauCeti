/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.Conductor
public import TauCeti.NumberTheory.ClassFieldTheory.LocalExistence.Correspondence
public import TauCeti.NumberTheory.LocalField.UnitsDecomposition

import TauCeti.NumberTheory.LocalField.UnitFiltration.Graded

/-!
# Conductors of local class fields

Let `K` be a nonarchimedean local field of characteristic zero. Local existence attaches to every
open subgroup `N` of finite index in `Kˣ` its class field, the finite abelian extension whose norm
group is `N`. Since the conductor exponent of an extension is the least `n` for which the step
`U(K,n)` of the unit filtration consists of norms, the conductor exponent of the class field of
`N` is the least `n` with `U(K,n) ⊆ N` (`conductorExponent_localClassField_le_iff`).

For a uniformizer `ϖ` the subgroup `U(K,n) · ϖ ^ ℤ` is open of finite index
(`unitFiltrationSupZpowers`), and the steps of the unit filtration it contains are exactly those
contained in `U(K,n)`. Its class field therefore has conductor exponent `n`
(`conductorExponent_localClassField_unitFiltrationSupZpowers`), with one exception: when the
residue field has two elements, `U(K,1) = U(K,0)`, so `U(K,1) · ϖ ^ ℤ = Kˣ` and its class field
is `K` itself, of conductor exponent `0`
(`conductorExponent_localClassField_unitFiltrationSupZpowers_one_eq_zero`). Every conductor exponent
other than `1` is thus attained by an abelian extension of `K`, and `1` is attained unless the
residue field has two elements.

## Main definitions

* `TauCeti.ClassFieldTheory.unitFiltrationSupZpowers`: the subgroup `U(K,n) · ϖ ^ ℤ` of `Kˣ`, as
  an open subgroup of finite index.

## Main results

* `TauCeti.ClassFieldTheory.conductorExponent_localClassField_le_iff`: the conductor exponent of
  the class field of `N` is at most `n` exactly when `U(K,n) ⊆ N`; in arbitrary characteristic,
  `conductorExponent_localClassFieldPrimeToResidueCharacteristic_le_iff` is the same statement
  for `N` of index prime to the residue characteristic.
* `TauCeti.ClassFieldTheory.conductorExponent_localClassField_unitFiltrationSupZpowers`: the
  class field of `U(K,n) · ϖ ^ ℤ` has conductor exponent `n`, unless `n = 1` and the residue field
  has two elements.

## References

* J.-P. Serre, *Local Fields*, Graduate Texts in Mathematics 67, Springer (1979), Chapter XV, §2.
* J. Neukirch, *Algebraic Number Theory*, Chapter V, §1.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

open _root_.ValuativeRel

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- **The conductor of a local class field.** The conductor exponent of the class field of an
open subgroup `N` of finite index in `Kˣ` is at most `n` exactly when `U(K,n) ⊆ N`: it is the
least `n` with `U(K,n) ⊆ N`. -/
theorem conductorExponent_localClassField_le_iff [CharZero K] (N : LocalNormSubgroups K)
    {n : ℕ} :
    conductorExponent K (classField K (localClassField N).1) ≤ n ↔
      unitFiltration K n ≤ N.1.toSubgroup := by
  rw [conductorExponent_le_iff, ← localNormSubgroup_def, localClassField_normSubgroup]

/-- The conductor exponent of the class field of an open subgroup `N` of `Kˣ` whose index is
prime to the residue characteristic `p` is at most `n` exactly when `U(K,n) ⊆ N`. This holds in
every characteristic. -/
theorem conductorExponent_localClassFieldPrimeToResidueCharacteristic_le_iff
    (p : ℕ) [Fact p.Prime] [CharP 𝓀[K] p] (N : LocalNormSubgroupsPrimeTo K p) {n : ℕ} :
    conductorExponent K (classField K (localClassFieldPrimeToResidueCharacteristic p N).1.1) ≤
        n ↔
      unitFiltration K n ≤ N.1.1.toSubgroup := by
  rw [conductorExponent_le_iff, ← localNormSubgroup_def,
    localClassFieldPrimeToResidueCharacteristic_normSubgroup]

/-- The subgroup `U(K,n) · ϖ ^ ℤ` of `Kˣ` attached to a uniformizer `ϖ`, as an open subgroup of
finite index: it contains the open subgroup `U(K,n)`, and its index is `[U(K,0) : U(K,n)]`
(`index_unitFiltration_sup_zpowers`). -/
def unitFiltrationSupZpowers {ϖ : Kˣ} (hϖ : normalizedValuation K ϖ = .ofAdd 1) (n : ℕ) :
    LocalNormSubgroups K :=
  ⟨⟨unitFiltration K n ⊔ Subgroup.zpowers ϖ,
      Subgroup.isOpen_mono le_sup_left (isOpen_unitFiltration n)⟩,
    Subgroup.finiteIndex_iff.mpr <| by
      rw [index_unitFiltration_sup_zpowers hϖ]
      exact Subgroup.relIndex_ne_zero⟩

/-- The subgroup underlying `unitFiltrationSupZpowers hϖ n` is `U(K,n) · ϖ ^ ℤ`. -/
@[simp]
theorem unitFiltrationSupZpowers_toSubgroup {ϖ : Kˣ} (hϖ : normalizedValuation K ϖ = .ofAdd 1)
    (n : ℕ) :
    (unitFiltrationSupZpowers hϖ n).1.toSubgroup = unitFiltration K n ⊔ Subgroup.zpowers ϖ :=
  (rfl)

/-- The conductor exponent of the class field of `U(K,n) · ϖ ^ ℤ` is at most `m` exactly when
`U(K,m) ⊆ U(K,n)`. -/
theorem conductorExponent_localClassField_unitFiltrationSupZpowers_le_iff [CharZero K]
    {ϖ : Kˣ} (hϖ : normalizedValuation K ϖ = .ofAdd 1) {m n : ℕ} :
    conductorExponent K (classField K (localClassField (unitFiltrationSupZpowers hϖ n)).1) ≤ m ↔
      unitFiltration K m ≤ unitFiltration K n := by
  rw [conductorExponent_localClassField_le_iff, unitFiltrationSupZpowers_toSubgroup,
    unitFiltration_le_unitFiltration_sup_zpowers_iff hϖ]

/-- **The class field of `U(K,n) · ϖ ^ ℤ` has conductor exponent `n`.** The exception `n = 1`
with a residue field of two elements is genuine: there `U(K,1) · ϖ ^ ℤ = Kˣ`
(`conductorExponent_localClassField_unitFiltrationSupZpowers_one_eq_zero`). -/
theorem conductorExponent_localClassField_unitFiltrationSupZpowers [CharZero K] {ϖ : Kˣ}
    (hϖ : normalizedValuation K ϖ = .ofAdd 1) {n : ℕ} (h : n ≠ 1 ∨ Nat.card 𝓀[K] ≠ 2) :
    conductorExponent K (classField K (localClassField (unitFiltrationSupZpowers hϖ n)).1) =
      n :=
  eq_of_forall_ge_iff fun _ ↦ by
    rw [conductorExponent_localClassField_unitFiltrationSupZpowers_le_iff,
      unitFiltration_le_unitFiltration_iff h]

/-- When the residue field has two elements, `U(K,1) = U(K,0)`, so `U(K,1) · ϖ ^ ℤ` is all of
`Kˣ`, and its class field has conductor exponent `0`. -/
theorem conductorExponent_localClassField_unitFiltrationSupZpowers_one_eq_zero [CharZero K] {ϖ : Kˣ}
    (hϖ : normalizedValuation K ϖ = .ofAdd 1) (h : Nat.card 𝓀[K] = 2) :
    conductorExponent K (classField K (localClassField (unitFiltrationSupZpowers hϖ 1)).1) =
      0 := by
  rw [← Nat.le_zero, conductorExponent_localClassField_unitFiltrationSupZpowers_le_iff,
    unitFiltration_one_eq_unitFiltration_zero_iff.mpr h]

end TauCeti.ClassFieldTheory
