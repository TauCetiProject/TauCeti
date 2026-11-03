/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import TauCeti.AlgebraicTopology.SerreClass.Torsion
public import TauCeti.CategoryTheory.ObjectProperty.Homology
public import TauCeti.LinearAlgebra.TensorProduct.Torsion

/-!
# Tensor and Tor closure of torsion classes

The torsion abelian groups and the groups annihilated by some power of a fixed natural number
are closed under tensor products and Tor with arbitrary abelian groups. More generally, these
properties hold for the underlying abelian groups of modules over any commutative ring. For
bounded power torsion, the tensor product retains the same annihilating power.
For tensor closure, the scalars may be a commutative semiring and the other factor need only
be a commutative additive monoid.

Tor is Mathlib's left derived tensor functor in `ModuleCat R`. In particular, for `R = ℤ` it
is integral Tor, not the derived functor of the cartesian monoidal structure on
`AddCommGrpCat`. Closure under subobjects and quotients passes the tensor closure property
through a projective resolution in every degree.

These are the tensor and Tor axioms for the classes used in Hurewicz theorems modulo a Serre
class. No finiteness assumptions are imposed. This file does not establish the separate axioms
concerning the homology of Eilenberg--MacLane spaces.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953).
* C. A. Weibel, *An Introduction to Homological Algebra*, Section 3.1.
-/

public noncomputable section

open CategoryTheory MonoidalCategory
open scoped TensorProduct

universe u

namespace TauCeti

/-- Tensoring a group annihilated by some power of `d` on the left with a commutative additive
monoid gives another group annihilated by some power of `d`. -/
theorem isKilledBySomePower_tensorProduct_left {R M N : Type*} [CommSemiring R]
    [AddCommGroup M] [AddCommMonoid N] [Module R M] [Module R N] (d : ℕ)
    (h : AddCommGrpCat.isKilledBySomePower d (AddCommGrpCat.of M)) :
    AddCommGrpCat.isKilledBySomePower d (AddCommGrpCat.of (M ⊗[R] N)) := by
  rw [AddCommGrpCat.prop_isKilledBySomePower_iff] at h ⊢
  obtain ⟨n, hn⟩ := h
  have ht : Module.IsTorsionBy ℤ (M ⊗[R] N) ((d : ℤ) ^ n) :=
    isTorsionBy_tensorProduct_left (fun {x} ↦ hn x)
  exact ⟨n, fun x ↦ ht (x := x)⟩

variable {R : Type u} [CommRing R] {M N : ModuleCat.{u} R}

/-- Every Tor group of a module whose underlying abelian group is torsion on the left and an
arbitrary module on the right is torsion as an abelian group. -/
theorem isAddTorsion_Tor_left (h : IsAddTorsion M) (n : ℕ) :
    IsAddTorsion (((Tor (ModuleCat.{u} R) n).obj M).obj N) := by
  let P := AddCommGrpCat.isTorsion.inverseImage (forget₂ (ModuleCat.{u} R) AddCommGrpCat)
  apply (AddCommGrpCat.prop_isTorsion_iff
    (AddCommGrpCat.of (((Tor (ModuleCat.{u} R) n).obj M).obj N))).1
  exact P.prop_leftDerived_obj ((tensoringLeft (ModuleCat.{u} R)).obj M)
    (fun Y _ ↦ (AddCommGrpCat.prop_isTorsion_iff _).2
      (isAddTorsion_tensorProduct_left (R := R) h)) N n

/-- Every Tor group of a module annihilated by some power of `d` on the left and an arbitrary
module on the right is annihilated by some power of `d` as an abelian group. -/
theorem isKilledBySomePower_Tor_left (d : ℕ)
    (h : AddCommGrpCat.isKilledBySomePower d (AddCommGrpCat.of M)) (n : ℕ) :
    AddCommGrpCat.isKilledBySomePower d
      (AddCommGrpCat.of (((Tor (ModuleCat.{u} R) n).obj M).obj N)) := by
  let P := (AddCommGrpCat.isKilledBySomePower d).inverseImage
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat)
  apply P.prop_leftDerived_obj ((tensoringLeft (ModuleCat.{u} R)).obj M) ?_ N n
  intro Y _
  exact isKilledBySomePower_tensorProduct_left (R := R) d h

end TauCeti
