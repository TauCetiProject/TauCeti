/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Finiteness.Small
public import TauCeti.Algebra.Category.HopfModuleCat.Basic
public import TauCeti.Algebra.Category.ModuleCat.Frobenius
public import TauCeti.Algebra.HopfAlgebra.Frobenius

/-!
# All modules over a finite-dimensional Hopf algebra form a Frobenius category

Let `H` be a finite-dimensional Hopf algebra over a field `k`. By the Larson–Sweedler theorem
(`TauCeti.HopfAlgebra.exists_isFrobeniusFunctional`), `H` admits a Frobenius functional, so
arbitrary projective and injective left `H`-modules coincide (`ModuleCat.abelian_isFrobenius`).

This file records the resulting Frobenius exact structure both on `ModuleCat.{w} H` in any universe
`w` in which `H` is small and on `TauCeti.HopfModuleCat k H`, the category of all left `H`-modules
in the universe of the base field `k` that underlies the coproduct monoidal structure of
`TauCeti.Algebra.Category.HopfModuleCat.Monoidal`. Because a module finite over `k : Type u` is
automatically `u`-small (`Module.Finite.small`), the results on `HopfModuleCat k H` require no
auxiliary `Small` hypothesis. Its `ProjectiveStableCategory` is therefore the stable category of
all left `H`-modules, triangulated by `TauCeti.ExactStructure.IsFrobenius.stableIsTriangulated`.

## Main results

* `ModuleCat.projective_iff_injective_of_hopfAlgebra`,
  `ModuleCat.abelian_isFrobenius_of_hopfAlgebra`: projective and injective objects of
  `ModuleCat.{w} H` coincide and the canonical exact structure on `ModuleCat.{w} H` is Frobenius.
* `TauCeti.HopfModuleCat.moduleProjective_iff_projective`,
  `TauCeti.HopfModuleCat.moduleInjective_iff_injective`: comparison of native module
  projectivity/injectivity with categorical projectivity/injectivity in `HopfModuleCat k H`.
* `TauCeti.HopfModuleCat.projective_iff_injective`: over a finite-dimensional Hopf algebra `H`, an
  object of `HopfModuleCat k H` is projective if and only if it is injective.
* `TauCeti.HopfModuleCat.abelian_isFrobenius`: the canonical exact structure on
  `HopfModuleCat k H` is Frobenius (Khovanov, Proposition 1).

## References

* M. Khovanov, *Hopfological algebra and categorification at a root of unity: the first steps*,
  J. Knot Theory Ramifications 25 (2016), Proposition 1.
* R. G. Larson and M. E. Sweedler, *An associative orthogonal bilinear form for
  Hopf algebras*, Amer. J. Math. 91 (1969), 75–94.
-/

public section

open CategoryTheory

universe u v w

namespace ModuleCat

open TauCeti

/-- **Projective and injective modules over a finite-dimensional Hopf algebra coincide.** Over a
finite-dimensional Hopf algebra `H` over a field `k`, an object of `ModuleCat.{w} H`, not
necessarily finitely generated, is projective if and only if it is injective. -/
theorem projective_iff_injective_of_hopfAlgebra (k : Type u) {H : Type v} [Field k] [Ring H]
    [HopfAlgebra k H] [FiniteDimensional k H] [Small.{w} H] (X : ModuleCat.{w} H) :
    Projective X ↔ Injective X := by
  obtain ⟨φ, hφ⟩ := TauCeti.HopfAlgebra.exists_isFrobeniusFunctional k H
  exact projective_iff_injective_of_isFrobeniusFunctional hφ X

/-- **All modules over a finite-dimensional Hopf algebra form a Frobenius category**
(Khovanov, Proposition 1). -/
theorem abelian_isFrobenius_of_hopfAlgebra (k : Type u) (H : Type v) [Field k] [Ring H]
    [HopfAlgebra k H] [FiniteDimensional k H] [Small.{w} H] :
    (ExactStructure.abelian (ModuleCat.{w} H)).IsFrobenius := by
  obtain ⟨φ, hφ⟩ := TauCeti.HopfAlgebra.exists_isFrobeniusFunctional k H
  exact abelian_isFrobenius hφ

end ModuleCat

namespace TauCeti.HopfModuleCat

section Ring

/-- An object of `HopfModuleCat k H` is categorically projective precisely when its underlying
`H`-module is projective. -/
theorem moduleProjective_iff_projective {k : Type u} {H : Type v} [Ring H] [Small.{u} H]
    (M : HopfModuleCat k H) : Module.Projective H M ↔ Projective M :=
  IsProjective.iff_projective (R := H) (M : ModuleCat.{u} H)

/-- An object of `HopfModuleCat k H` is categorically injective precisely when its underlying
`H`-module is injective. -/
theorem moduleInjective_iff_injective {k : Type u} {H : Type v} [Ring H]
    (M : HopfModuleCat k H) : Module.Injective H M ↔ Injective M :=
  Module.injective_iff_injective_object H (M : ModuleCat.{u} H)

instance instEnoughProjectivesOfSmall (k : Type u) (H : Type v) [Ring H] [Small.{u} H] :
    EnoughProjectives (HopfModuleCat k H) :=
  inferInstanceAs (EnoughProjectives (ModuleCat.{u} H))

instance instEnoughInjectivesOfSmall (k : Type u) (H : Type v) [Ring H] [Small.{u} H] :
    EnoughInjectives (HopfModuleCat k H) :=
  inferInstanceAs (EnoughInjectives (ModuleCat.{u} H))

end Ring

section FiniteModule

variable (R : Type u) [Semiring R] (A : Type v) [Ring A] [Module R A] [Module.Finite R A]

instance instEnoughProjectives : EnoughProjectives (HopfModuleCat R A) := by
  have : Small.{u} A := Module.Finite.small R A
  infer_instance

instance instEnoughInjectives : EnoughInjectives (HopfModuleCat R A) := by
  have : Small.{u} A := Module.Finite.small R A
  infer_instance

variable {R A}

/-- When `A` is finite as an `R`-module, an object of `HopfModuleCat R A` is categorically
projective precisely when its underlying `A`-module is projective. -/
theorem moduleProjective_iff_projective_of_finite (M : HopfModuleCat R A) :
    Module.Projective A M ↔ Projective M := by
  have : Small.{u} A := Module.Finite.small R A
  exact moduleProjective_iff_projective M

end FiniteModule

section FiniteDimensionalAlgebra

variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A] [FiniteDimensional k A]

/-- Over a finite-dimensional `k`-algebra with a Frobenius functional, projective and injective
objects of `HopfModuleCat k A` coincide. -/
theorem projective_iff_injective_of_isFrobeniusFunctional {φ : A →ₗ[k] k}
    (hφ : φ.IsFrobeniusFunctional) (M : HopfModuleCat k A) : Projective M ↔ Injective M := by
  have : Small.{u} A := Module.Finite.small k A
  exact ModuleCat.projective_iff_injective_of_isFrobeniusFunctional hφ (M : ModuleCat.{u} A)

/-- Over a finite-dimensional `k`-algebra with a Frobenius functional, the canonical exact
structure on `HopfModuleCat k A` is Frobenius. -/
theorem abelian_isFrobenius_of_isFrobeniusFunctional {φ : A →ₗ[k] k}
    (hφ : φ.IsFrobeniusFunctional) :
    (ExactStructure.abelian (HopfModuleCat k A)).IsFrobenius where
  enoughProjectives := ExactStructure.abelian_enoughProjectives
  enoughInjectives := ExactStructure.abelian_enoughInjectives
  projective_iff_injective M := by
    rw [ExactStructure.abelian_isProjective_iff, ExactStructure.abelian_isInjective_iff]
    exact projective_iff_injective_of_isFrobeniusFunctional hφ M

end FiniteDimensionalAlgebra

section HopfAlgebra

/-- **Projective and injective modules over a finite-dimensional Hopf algebra coincide**
(Khovanov, Proposition 1): an object of `HopfModuleCat k H`, not necessarily finite-dimensional,
is projective if and only if it is injective. -/
theorem projective_iff_injective {k : Type u} {H : Type v} [Field k] [Ring H]
    [_root_.HopfAlgebra k H] [FiniteDimensional k H] (M : HopfModuleCat k H) :
    Projective M ↔ Injective M := by
  obtain ⟨φ, hφ⟩ := TauCeti.HopfAlgebra.exists_isFrobeniusFunctional k H
  exact projective_iff_injective_of_isFrobeniusFunctional hφ M

/-- **All modules over a finite-dimensional Hopf algebra form a Frobenius category**
(Khovanov, Proposition 1): the canonical exact structure on `HopfModuleCat k H` has enough
projectives and enough injectives, and its projective and injective objects coincide. -/
theorem abelian_isFrobenius (k : Type u) (H : Type v) [Field k] [Ring H]
    [_root_.HopfAlgebra k H] [FiniteDimensional k H] :
    (ExactStructure.abelian (HopfModuleCat k H)).IsFrobenius := by
  obtain ⟨φ, hφ⟩ := TauCeti.HopfAlgebra.exists_isFrobeniusFunctional k H
  exact abelian_isFrobenius_of_isFrobeniusFunctional hφ

end HopfAlgebra

end TauCeti.HopfModuleCat
