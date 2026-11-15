/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.HopfModuleCat.Basic
public import TauCeti.Algebra.Category.ModuleCat.Frobenius
public import TauCeti.Algebra.HopfAlgebra.Frobenius
import Mathlib.RingTheory.Finiteness.Small

/-!
# All modules over a finite-dimensional Hopf algebra form a Frobenius category

Let `H` be a finite-dimensional Hopf algebra over a field `k`. By the Larson–Sweedler theorem
(`TauCeti.exists_isFrobeniusFunctional_of_hopfAlgebra`), `H` carries a Frobenius functional.
Specializing `ModuleCat.abelian_isFrobenius` therefore equips the category of **all** left
`H`-modules — both `ModuleCat.{w} H` (for any universe `w` in which `H` is small) and
`TauCeti.HopfModuleCat k H` (with carriers in the universe of `k`, where smallness of `H` holds
automatically by finite-dimensionality over `k`) — with a Frobenius exact structure:

* `HopfModuleCat k H` has enough projectives and enough injectives;
* an object of `HopfModuleCat k H` (not necessarily finite-dimensional) is projective if and only if
  it is injective (`TauCeti.HopfModuleCat.projective_iff_injective`);
* the canonical abelian exact structure on `HopfModuleCat k H` is Frobenius
  (`TauCeti.HopfModuleCat.abelian_isFrobenius`).

Together with `TauCeti.ExactStructure.IsFrobenius.stableIsTriangulated`, its
`ProjectiveStableCategory` is Khovanov's stable module category of all `H`-modules as a triangulated
category.

## Main declarations

* `ModuleCat.projective_iff_injective_of_hopfAlgebra` and
  `ModuleCat.abelian_isFrobenius_of_hopfAlgebra`: over a finite-dimensional Hopf algebra, projective
  and injective `H`-modules coincide and `ModuleCat.{w} H` is Frobenius.
* `TauCeti.HopfModuleCat.instEnoughProjectivesOfFinite` and
  `TauCeti.HopfModuleCat.instEnoughInjectivesOfFinite`: `HopfModuleCat k H` has enough projectives
  and enough injectives for any module-finite `k`-algebra `H`.
* `TauCeti.HopfModuleCat.projective_iff_injective` and `TauCeti.HopfModuleCat.abelian_isFrobenius`:
  projective and injective objects of `HopfModuleCat k H` coincide and its canonical abelian exact
  structure is Frobenius.

## References

* M. Khovanov, *Hopfological algebra and categorification at a root of unity: the first steps*,
  J. Knot Theory Ramifications 25 (2016), Proposition 1.
* R. G. Larson and M. E. Sweedler, *An associative orthogonal bilinear form for Hopf algebras*,
  Amer. J. Math. 91 (1969), 75–94.
* D. Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional Algebras*,
  Chapter I, Section 2.
-/

public section

open CategoryTheory

namespace ModuleCat

open TauCeti

universe w

variable (k : Type*) [Field k] {H : Type*} [Ring H] [HopfAlgebra k H] [FiniteDimensional k H]
  [Small.{w} H]

include k in
/-- Over a finite-dimensional Hopf algebra, an object of `ModuleCat.{w} H` (not necessarily
finitely generated) is projective if and only if it is injective. -/
theorem projective_iff_injective_of_hopfAlgebra (X : ModuleCat.{w} H) :
    Projective X ↔ Injective X := by
  obtain ⟨_, hφ⟩ := exists_isFrobeniusFunctional_of_hopfAlgebra k H
  exact projective_iff_injective_of_isFrobeniusFunctional hφ X

include k in
/-- Over a finite-dimensional Hopf algebra, the canonical exact structure on `ModuleCat.{w} H` is
Frobenius. -/
theorem abelian_isFrobenius_of_hopfAlgebra :
    (ExactStructure.abelian (ModuleCat.{w} H)).IsFrobenius := by
  obtain ⟨_, hφ⟩ := exists_isFrobeniusFunctional_of_hopfAlgebra k H
  exact abelian_isFrobenius hφ

end ModuleCat

namespace TauCeti.HopfModuleCat

universe u v

section Small

variable (k : Type u) (H : Type v) [Ring H] [Small.{u} H]

instance instEnoughProjectives : EnoughProjectives (HopfModuleCat k H) :=
  inferInstanceAs (EnoughProjectives (ModuleCat.{u} H))

instance instEnoughInjectives : EnoughInjectives (HopfModuleCat k H) :=
  inferInstanceAs (EnoughInjectives (ModuleCat.{u} H))

end Small

section Finite

variable (k : Type u) [CommSemiring k] (H : Type v) [Ring H] [Algebra k H] [Module.Finite k H]

/-- Over a module-finite `k`-algebra `H`, `HopfModuleCat k H` has enough projectives without an
explicit `Small` hypothesis. -/
instance instEnoughProjectivesOfFinite : EnoughProjectives (HopfModuleCat k H) := by
  have := Module.Finite.small k H
  exact inferInstance

/-- Over a module-finite `k`-algebra `H`, `HopfModuleCat k H` has enough injectives without an
explicit `Small` hypothesis. -/
instance instEnoughInjectivesOfFinite : EnoughInjectives (HopfModuleCat k H) := by
  have := Module.Finite.small k H
  exact inferInstance

end Finite

section HopfAlgebra

variable {k : Type u} [Field k] {H : Type v} [Ring H] [HopfAlgebra k H] [FiniteDimensional k H]

/-- Over a finite-dimensional Hopf algebra `H` over `k`, an object of `HopfModuleCat k H` (not
necessarily finite-dimensional) is projective if and only if it is injective. -/
theorem projective_iff_injective (X : HopfModuleCat k H) :
    Projective X ↔ Injective X := by
  have := Module.Finite.small k H
  exact ModuleCat.projective_iff_injective_of_hopfAlgebra k (X : ModuleCat.{u} H)

variable (k H) in
/-- **All modules over a finite-dimensional Hopf algebra form a Frobenius category**: the canonical
abelian exact structure on `HopfModuleCat k H` is Frobenius, with no universe-smallness hypothesis
needed beyond finite-dimensionality of `H` over `k`. -/
theorem abelian_isFrobenius :
    (ExactStructure.abelian (HopfModuleCat k H)).IsFrobenius where
  enoughProjectives := ExactStructure.abelian_enoughProjectives
  enoughInjectives := ExactStructure.abelian_enoughInjectives
  projective_iff_injective X := by
    rw [ExactStructure.abelian_isProjective_iff, ExactStructure.abelian_isInjective_iff]
    exact projective_iff_injective X

end HopfAlgebra

end TauCeti.HopfModuleCat
