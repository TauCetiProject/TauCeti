/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.HopfModuleCat.Basic
public import TauCeti.Algebra.Category.ModuleCat.Frobenius
public import TauCeti.Algebra.Category.FGModuleCat.Frobenius
public import TauCeti.Algebra.HopfAlgebra.Frobenius
import Mathlib.RingTheory.Finiteness.Small

/-!
# Modules over a finite-dimensional Hopf algebra form a Frobenius category

By the Larson–Sweedler theorem (`TauCeti.exists_isFrobeniusFunctional`), every finite-dimensional
Hopf algebra `H` over a field `k` admits a Frobenius functional. Combining this with
`ModuleCat.abelian_isFrobenius` and `FGModuleCat.abelian_isFrobenius` equips the module categories
of `H` with Frobenius exact structures:

* on `TauCeti.HopfModuleCat k H` (all left `H`-modules in the universe of `k`), `Small.{u} H` holds
  automatically by `Module.Finite.small`, so no universe-smallness hypothesis is needed;
* on `ModuleCat.{w} H` and `FGModuleCat.{w} H` in an arbitrary universe `w` with `[Small.{w} H]`,
  projective and injective objects coincide and the canonical abelian exact structures are
  Frobenius.

## Main declarations

* `TauCeti.HopfModuleCat.projective_iff_injective`: projective and injective objects of
  `HopfModuleCat k H` coincide over a finite-dimensional Hopf algebra.
* `TauCeti.HopfModuleCat.abelian_isFrobenius`: the canonical abelian exact structure on
  `HopfModuleCat k H` is Frobenius.
* `ModuleCat.projective_iff_injective_of_hopfAlgebra` and
  `ModuleCat.abelian_isFrobenius_of_hopfAlgebra`: the universe-polymorphic counterparts on
  `ModuleCat.{w} H`.
* `FGModuleCat.enoughInjectives_of_hopfAlgebra`,
  `FGModuleCat.projective_iff_injective_of_hopfAlgebra`, and
  `FGModuleCat.abelian_isFrobenius_of_hopfAlgebra`: the finitely generated counterparts on
  `FGModuleCat.{w} H`.

## References

* R. G. Larson and M. E. Sweedler, *An associative orthogonal bilinear form for Hopf algebras*,
  Amer. J. Math. 91 (1969), 75–94.
* M. Khovanov, *Hopfological algebra and categorification at a root of unity: the first steps*,
  J. Knot Theory Ramifications 25 (2016), Proposition 1.
-/

public section

open CategoryTheory

namespace TauCeti

universe u v w

namespace HopfModuleCat

section Enough

variable (k : Type u) (H : Type v) [Ring H]

instance [Small.{u} H] : EnoughProjectives (HopfModuleCat k H) :=
  inferInstanceAs (EnoughProjectives (ModuleCat.{u} H))

instance [Small.{u} H] : EnoughInjectives (HopfModuleCat k H) :=
  inferInstanceAs (EnoughInjectives (ModuleCat.{u} H))

instance [Field k] [Algebra k H] [FiniteDimensional k H] :
    EnoughProjectives (HopfModuleCat k H) := by
  have : Small.{u} H := Module.Finite.small k H
  infer_instance

instance [Field k] [Algebra k H] [FiniteDimensional k H] :
    EnoughInjectives (HopfModuleCat k H) := by
  have : Small.{u} H := Module.Finite.small k H
  infer_instance

end Enough

section HopfAlgebra

variable {k : Type u} [Field k] {H : Type v} [Ring H] [_root_.HopfAlgebra k H]
  [FiniteDimensional k H]

/-- Over a finite-dimensional Hopf algebra over a field, an object of `HopfModuleCat k H` is
projective if and only if it is injective. -/
theorem projective_iff_injective (X : HopfModuleCat k H) :
    Projective X ↔ Injective X := by
  have : Small.{u} H := Module.Finite.small k H
  obtain ⟨φ, hφ⟩ := exists_isFrobeniusFunctional k H
  exact ModuleCat.projective_iff_injective_of_isFrobeniusFunctional hφ (X : ModuleCat.{u} H)

variable (k H) in
/-- **All modules over a finite-dimensional Hopf algebra form a Frobenius category**: the canonical
abelian exact structure on `HopfModuleCat k H` is Frobenius, with no smallness assumption on `H`. -/
theorem abelian_isFrobenius :
    (ExactStructure.abelian (HopfModuleCat k H)).IsFrobenius where
  enoughProjectives := ExactStructure.abelian_enoughProjectives
  enoughInjectives := ExactStructure.abelian_enoughInjectives
  projective_iff_injective X := by
    rw [ExactStructure.abelian_isProjective_iff, ExactStructure.abelian_isInjective_iff]
    exact projective_iff_injective X

end HopfAlgebra

end HopfModuleCat

section ModuleCat

variable (k : Type u) [Field k] {H : Type v} [Ring H] [_root_.HopfAlgebra k H]
  [FiniteDimensional k H] [Small.{w} H]

include k

/-- Over a finite-dimensional Hopf algebra over a field, projective and injective objects of
`ModuleCat.{w} H` coincide. -/
theorem _root_.ModuleCat.projective_iff_injective_of_hopfAlgebra (X : ModuleCat.{w} H) :
    Projective X ↔ Injective X := by
  obtain ⟨φ, hφ⟩ := exists_isFrobeniusFunctional k H
  exact ModuleCat.projective_iff_injective_of_isFrobeniusFunctional hφ X

variable (H) in
/-- Over a finite-dimensional Hopf algebra over a field, the canonical abelian exact structure on
`ModuleCat.{w} H` is Frobenius. -/
theorem _root_.ModuleCat.abelian_isFrobenius_of_hopfAlgebra :
    (ExactStructure.abelian (ModuleCat.{w} H)).IsFrobenius := by
  obtain ⟨φ, hφ⟩ := exists_isFrobeniusFunctional k H
  exact ModuleCat.abelian_isFrobenius hφ

/-- Over a finite-dimensional Hopf algebra over a field, `FGModuleCat.{w} H` has enough injectives.
-/
theorem _root_.FGModuleCat.enoughInjectives_of_hopfAlgebra :
    EnoughInjectives (FGModuleCat.{w} H) :=
  FGModuleCat.enoughInjectives_of_moduleInjective_self k
    (HopfAlgebra.moduleInjective_self k H) (HopfAlgebra.moduleInjective_op_self k H)

/-- Over a finite-dimensional Hopf algebra over a field, projective and injective objects of
`FGModuleCat.{w} H` coincide. -/
theorem _root_.FGModuleCat.projective_iff_injective_of_hopfAlgebra (X : FGModuleCat.{w} H) :
    Projective X ↔ Injective X :=
  FGModuleCat.projective_iff_injective_of_moduleInjective_self k
    (HopfAlgebra.moduleInjective_self k H) (HopfAlgebra.moduleInjective_op_self k H) X

variable (H) in
/-- Over a finite-dimensional Hopf algebra over a field, the canonical abelian exact structure on
`FGModuleCat.{w} H` is Frobenius. The `[IsNoetherianRing H]` instance equips `FGModuleCat.{w} H`
with its abelian category structure and is supplied at call sites by `isNoetherian_of_tower`. -/
theorem _root_.FGModuleCat.abelian_isFrobenius_of_hopfAlgebra [IsNoetherianRing H] :
    (ExactStructure.abelian (FGModuleCat.{w} H)).IsFrobenius :=
  FGModuleCat.abelian_isFrobenius k
    (HopfAlgebra.moduleInjective_self k H) (HopfAlgebra.moduleInjective_op_self k H)

end ModuleCat

end TauCeti
