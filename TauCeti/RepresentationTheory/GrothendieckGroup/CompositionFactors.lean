/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GrothendieckGroup.Artinian

/-!
# Composition factors detect Grothendieck classes

Over an Artinian ring, the Jordan–Hölder coordinates at all simple modules determine a
class in the exact Grothendieck group of finitely generated modules. Callers need not choose
an exhaustive family of simple representatives. For actual modules this says that their
Grothendieck classes agree exactly when their composition multiplicities agree; it does not
assert that the modules themselves are isomorphic.

In particular, the criterion applies to finite group algebras over arbitrary fields, including
characteristic dividing the group order. It uses the finite simple-class basis constructed in
`TauCeti.RepresentationTheory.GrothendieckGroup.Artinian` and its Jordan–Hölder coordinate formula.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, II, §6.
-/

public section

namespace TauCeti

universe u

variable {R : Type u} [Ring R] [IsArtinianRing R]

/-- Jordan–Hölder coordinates at simple modules determine an exact Grothendieck class over
an Artinian ring, without a chosen family of simple representatives. -/
@[ext]
theorem ExactK0.ext_jordanHolderCoordinate
    {x y : ExactK0 (finiteModulesExactStructure R)}
    (h : ∀ S : FGModuleCat.{u} R, IsSimpleModule R S →
      jordanHolderCoordinate R S x = jordanHolderCoordinate R S y) : x = y := by
  obtain ⟨n, S, hS, hnoniso, hexhaustive⟩ := exists_isExhaustiveSimpleFamily R
  let : ∀ i, IsSimpleModule R (S i) := hS
  apply (simpleClassBasis S hnoniso hexhaustive).repr.injective
  ext i
  simpa only [simpleClassBasis_repr_apply] using h (S i) (hS i)

/-- Finitely generated modules over an Artinian ring have the same exact Grothendieck class
exactly when they have the same multiplicity of every simple composition factor. -/
theorem ExactK0.of_eq_of_iff_jordanHolderMultiplicity_eq (M N : FGModuleCat.{u} R) :
    (ExactK0.of M : ExactK0 (finiteModulesExactStructure R)) = ExactK0.of N ↔
      ∀ S : FGModuleCat.{u} R, IsSimpleModule R S →
        jordanHolderMultiplicity R M S = jordanHolderMultiplicity R N S := by
  simp only [ExactK0.ext_jordanHolderCoordinate_iff, jordanHolderCoordinate_of,
    Nat.cast_inj]

end TauCeti
