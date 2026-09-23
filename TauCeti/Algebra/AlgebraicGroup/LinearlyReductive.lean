/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.CommHopfAlgCat
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.BaseChange
public import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive
import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive.BaseChange

/-!
# Linearly reductive commutative Hopf algebras

An affine group over a field is linearly reductive when its finite-dimensional rational
representations are completely reducible. This file packages the existing comodule formulation
as an isomorphism-invariant object property on commutative Hopf algebras. The property tests
comodule carriers in the base field's universe; transport to a finite standard basis then shows
that this covers carriers in every universe.

The property is deliberately separate from smoothness, connectedness, and finite type. In
positive characteristic a torus is linearly reductive, while a general reductive group need not
be. The comparison with reductivity defined by a trivial geometric unipotent radical belongs
later in the theory: for smooth connected affine groups, reductive and linearly reductive are
equivalent in characteristic zero.

## Main declarations

* `TauCeti.linearlyReductiveCommHopfAlgProperty`: linear reductivity as an object property.
* `TauCeti.linearlyReductiveCommHopfAlgProperty_monoidAlgebra`: every commutative group algebra
  has the property.
* `TauCeti.linearlyReductiveCommHopfAlgProperty.of_baseChange`: the property descends along
  field extensions.
* `TauCeti.LinearlyReductiveCommHopfAlgCat`: the corresponding full subcategory.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Section 3.2.
* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.12.

This is the complete-reducibility side of Layer 6, "Reductive and semisimple groups", in the
ReductiveGroups roadmap.

The organization follows `TauCeti/Algebra/AlgebraicGroup/Unipotent/Basic.lean`.
-/

public section

namespace TauCeti

open CategoryTheory
open scoped MonoidAlgebra

universe u v w

/-- The object property selecting commutative Hopf algebras for which every finite-dimensional
comodule is completely reducible. It tests carriers in the base field's universe, which suffices
for carriers in every universe by finite-dimensional transport. -/
def linearlyReductiveCommHopfAlgProperty (k : Type u) [Field k] :
    ObjectProperty (CommHopfAlgCat.{v} k) :=
  fun H ↦ Coalgebra.IsLinearlyReductive.{u, v, u} k H

/-- Membership in the linearly reductive commutative-Hopf-algebra property means that every
finite-dimensional comodule with carrier in the base field's universe is completely reducible. -/
@[simp]
theorem linearlyReductiveCommHopfAlgProperty_iff (k : Type u) [Field k]
    (H : CommHopfAlgCat.{v} k) :
    linearlyReductiveCommHopfAlgProperty.{u, v} k H ↔
      Coalgebra.IsLinearlyReductive.{u, v, u} k H :=
  Iff.rfl

/-- Linear reductivity is invariant under isomorphism of commutative Hopf algebras. -/
instance (k : Type u) [Field k] :
    (linearlyReductiveCommHopfAlgProperty.{u, v} k).IsClosedUnderIsomorphisms where
  of_iso e hH :=
    (Coalgebra.isLinearlyReductive_iff_of_coalgEquiv
      k (CommHopfAlgCat.ofIso e).toCoalgEquiv).mp hH

/-- The monoid algebra of a commutative group is a linearly reductive commutative Hopf
algebra. -/
theorem linearlyReductiveCommHopfAlgProperty_monoidAlgebra
    (k : Type u) [Field k] (G : Type v) [CommGroup G] :
    linearlyReductiveCommHopfAlgProperty k
      (CommHopfAlgCat.of k (MonoidAlgebra k G)) :=
  (linearlyReductiveCommHopfAlgProperty_iff k _).2
    (Coalgebra.isLinearlyReductive_monoidAlgebra k G)

/-- **Linear reductivity descends along field extensions.** A commutative Hopf algebra over `k`
is linearly reductive as soon as its scalar extension to some extension field `K` is. -/
theorem linearlyReductiveCommHopfAlgProperty.of_baseChange {k : Type u} [Field k]
    (K : Type w) [Field K] [Algebra k K] {H : CommHopfAlgCat.{v} k}
    (hH : linearlyReductiveCommHopfAlgProperty K (CommHopfAlgCat.baseChange (K := K) H)) :
    linearlyReductiveCommHopfAlgProperty k H :=
  (linearlyReductiveCommHopfAlgProperty_iff k H).2
    (Coalgebra.IsLinearlyReductive.of_baseChange K
      ((linearlyReductiveCommHopfAlgProperty_iff K _).1 hH))

/-- The category of linearly reductive commutative Hopf algebras over a field. -/
abbrev LinearlyReductiveCommHopfAlgCat (k : Type u) [Field k] :=
  (linearlyReductiveCommHopfAlgProperty.{u, v} k).FullSubcategory

end TauCeti
