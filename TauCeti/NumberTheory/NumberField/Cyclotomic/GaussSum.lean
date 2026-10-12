/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
public import TauCeti.NumberTheory.DirichletCharacter.GaussSum
import TauCeti.NumberTheory.NumberField.Cyclotomic.Galois

/-!
# Dirichlet Gauss sums inside a rational cyclotomic field

Let `K` be the `n`-th cyclotomic field over `ℚ` and let `m ∣ n`. Mathlib identifies `Gal(K/ℚ)`
with `(ZMod n)ˣ` through `IsCyclotomicExtension.Rat.galEquivZMod`. The cyclotomic character
`IsPrimitiveRoot.autToPow` of a primitive `m`-th root of unity `ζ` in `K` is the reduction of
`galEquivZMod` modulo `m` (`IsPrimitiveRoot.autToPow_eq_unitsMap_galEquivZMod`).

Consequently the Galois stabilizer of the Gauss sum of a primitive integer-valued Dirichlet
character `χ` of level `m`, formed with `ζ`, is read off from the level-`n` character
`changeLevel χ` evaluated on `galEquivZMod`. This is the form in which Gauss sums of characters of
several different levels can be compared inside one cyclotomic field, and matched with Mathlib's
character correspondence `IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar`.

## Main results

* `DirichletCharacter.mem_stabilizer_gaussSumOfPrimitiveRoot_iff_changeLevel`: an automorphism
  fixes the Gauss sum of a primitive level-`m` character exactly when the character, lifted to
  level `n`, is trivial on its image under `galEquivZMod`.
-/

public section

open IsCyclotomicExtension.Rat

variable {n : ℕ} [NeZero n] {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {n} ℚ K]

namespace DirichletCharacter

/-- **The Galois stabilizer of a Dirichlet Gauss sum in a cyclotomic field.** Let `χ` be a
primitive integer-valued Dirichlet character of level `m ∣ n` and `ζ` a primitive `m`-th root of
unity in the `n`-th cyclotomic field. An automorphism fixes the Gauss sum of `χ` formed with `ζ`
exactly when `χ`, lifted to level `n`, takes the value `1` at its image under `galEquivZMod`. -/
theorem mem_stabilizer_gaussSumOfPrimitiveRoot_iff_changeLevel {m : ℕ} [NeZero m]
    (χ : DirichletCharacter ℤ m) (hχ : IsPrimitive χ) (hmn : m ∣ n) {ζ : K}
    (hζ : IsPrimitiveRoot ζ m) (σ : Gal(K/ℚ)) :
    σ ∈ MulAction.stabilizer Gal(K/ℚ) (gaussSumOfPrimitiveRoot χ hζ) ↔
      changeLevel hmn χ (galEquivZMod n K σ) = 1 := by
  rw [stabilizer_gaussSumOfPrimitiveRoot χ hχ hζ, MonoidHom.mem_ker, MonoidHom.comp_apply,
    hζ.autToPow_eq_unitsMap_galEquivZMod hmn, ← MonoidHom.comp_apply, ← changeLevel_toUnitHom,
    Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one]

end DirichletCharacter
