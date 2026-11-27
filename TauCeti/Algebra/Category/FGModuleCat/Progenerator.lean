/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FGModuleCat.Basic
public import TauCeti.Algebra.Category.ModuleCat.Progenerator

import Mathlib.Algebra.Module.Shrink

/-!
# Progenerators in `FGModuleCat`

A finitely generated projective `R`-module `P` that is a module-theoretic generator
(`TauCeti.Module.IsGenerator R P`) is a categorical progenerator (`TauCeti.IsProgenerator P`) of
`FGModuleCat.{v} R` (`FGModuleCat.isProgenerator_of_projective_of_isGenerator`). When `R` is
`v`-small (automatic for `FGModuleCat.{u} R`), the converse also holds: an object `P` of
`FGModuleCat.{v} R` is a categorical progenerator if and only if it is projective
(`Module.Projective R P`) and a module-theoretic generator (`FGModuleCat.isProgenerator_iff`).
This specializes `TauCeti.Algebra.Category.ModuleCat.Progenerator` to `ModuleCat.isFG R` and
bridges the categorical progenerator API of `TauCeti.CategoryTheory.Preadditive.Progenerator` and
`TauCeti.CategoryTheory.Abelian.Progenerator.Basic` with the module-theoretic progenerator and
Morita API of `TauCeti.Algebra.Module.Generator` and `TauCeti.RingTheory.Morita.Progenerator`.

In particular, over any ring `R`, the regular module `R`, any positive finite free module
`Fin n → R`, and `R × R` are progenerators of `FGModuleCat R`.

## Main results

* `FGModuleCat.isProgenerator_of_projective_of_isGenerator`: every finitely generated projective
  generator is a progenerator of `FGModuleCat R`.
* `FGModuleCat.isProgenerator_iff`: the equivalence between `TauCeti.IsProgenerator P` in
  `FGModuleCat R` and `Module.Projective R P ∧ TauCeti.Module.IsGenerator R P` (when `R` is
  `v`-small, which is automatic for `FGModuleCat.{u} R`).
* `FGModuleCat.isProgenerator_self`, `FGModuleCat.isProgenerator_pi`, and
  `FGModuleCat.isProgenerator_prod_self`: the regular module `R`, `Fin n → R` (`[NeZero n]`), and
  `R × R` are progenerators of `FGModuleCat R`.

## References

* T. Y. Lam, *Lectures on Modules and Rings*, Graduate Texts in Mathematics 189, Springer (1999),
  §18.
-/

public section

namespace FGModuleCat

open CategoryTheory CategoryTheory.Limits TauCeti

universe u v

variable {R : Type u} [Ring R]

/-- A finitely generated projective `R`-module that is a generator is a progenerator of
`FGModuleCat R`. -/
theorem isProgenerator_of_projective_of_isGenerator (P : FGModuleCat.{v} R)
    [Module.Projective R P] [TauCeti.Module.IsGenerator R P] : IsProgenerator P :=
  have := (ModuleCat.isFG.{v} R).projective_of_moduleProjective P
  (ModuleCat.isFG.{v} R).isProgenerator_of_projective_of_isGenerator le_rfl P

/-- **Characterization of progenerators in `FGModuleCat R`.** When `R` is `v`-small (automatic for
`FGModuleCat.{u} R`), an object `P` of `FGModuleCat.{v} R` is a categorical progenerator if and
only if it is projective and a generator as an `R`-module. -/
theorem isProgenerator_iff [Small.{v} R] (P : FGModuleCat.{v} R) :
    IsProgenerator P ↔ Module.Projective R P ∧ TauCeti.Module.IsGenerator R P :=
  let eR : Shrink.{v} R ≃ₗ[R] R := Shrink.linearEquiv.{v} R R
  have : Module.Finite R (Shrink.{v} R) := Module.Finite.equiv eR.symm
  (ModuleCat.isFG.{v} R).isProgenerator_iff_moduleProjective_and_isGenerator le_rfl
    (R₀ := FGModuleCat.of R (Shrink.{v} R)) eR P

variable (R)

/-- The regular module `R` is a progenerator of `FGModuleCat R`. -/
theorem isProgenerator_self : IsProgenerator (FGModuleCat.of R R) :=
  isProgenerator_of_projective_of_isGenerator (FGModuleCat.of R R)

/-- Any positive finite free module `Fin n → R` (`n ≠ 0`) is a progenerator of `FGModuleCat R`. -/
theorem isProgenerator_pi (n : ℕ) [NeZero n] :
    IsProgenerator (FGModuleCat.of R (Fin n → R)) :=
  ((isProgenerator_self R).biproduct n).of_iso <|
    (ModuleCat.isFG.{u} R).fullyFaithfulι.preimageIso <|
      (ModuleCat.isFG.{u} R).biproductObjIsoPi fun _ : Fin n ↦ FGModuleCat.of R R

/-- The rank-two free module `R × R` is a progenerator of `FGModuleCat R`. -/
theorem isProgenerator_prod_self : IsProgenerator (FGModuleCat.of R (R × R)) :=
  have := (isProgenerator_self R).projective
  (isProgenerator_self R).biprod_left.of_iso
    (FGModuleCat.biprodIsoProd (FGModuleCat.of R R) (FGModuleCat.of R R))

end FGModuleCat
