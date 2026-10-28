/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Belyi.Basic

/-!
# Bundled algebraic Belyi pairs and their isomorphism classes

The predicate `TauCeti.IsAlgebraicBelyiPair k F` is unbundled: it is a property of a field `F`
carrying a finite `k(t)`-algebra structure. To speak of *the set* of Belyi pairs over `k`, and of
the action of automorphisms of `k` on it, this file bundles the function field `F` with its
structure maps into a single object `TauCeti.AlgebraicBelyiPair k`.

Two algebraic Belyi pairs are isomorphic when there is an isomorphism of their function fields
over `k(t)`, that is, an isomorphism of curves commuting with the Belyi maps. The isomorphism
classes form the type `TauCeti.AlgebraicBelyiPair.IsoClass k`, on which the degree
`[F : k(t)]` is well defined. Isomorphism classes, rather than pairs, are what the Galois action
of `TauCeti.FieldTheory.FunctionField.Belyi.GaloisAction` permutes, and what orbit sizes and
fields of moduli are attached to.

## Main definitions

* `TauCeti.AlgebraicBelyiPair k`: an algebraic Belyi pair over `k`, bundled.
* `TauCeti.AlgebraicBelyiPair.IsoClass k`: the isomorphism classes of algebraic Belyi pairs over
  `k`, with `TauCeti.AlgebraicBelyiPair.IsoClass.mk` sending a pair to its class.
* `TauCeti.AlgebraicBelyiPair.IsoClass.degree`: the degree of a class.

## Main results

* `TauCeti.AlgebraicBelyiPair.IsoClass.mk_eq_mk_iff`: two pairs have the same class exactly when
  their function fields are isomorphic over `k(t)`.

## References

* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, LMS Student Texts 79, Cambridge University Press, 2012, Chapter 3.
-/

public section

universe u

namespace TauCeti

/-- An **algebraic Belyi pair** over a field `k` of characteristic zero, bundled: a field `F`, the
function field of the curve, with a finite `k(t)`-algebra structure, the embedding `k(t) ↪ F`
given by the Belyi map, compatible with its `k`-algebra structure, such that `F / k(t)` is an
algebraic Belyi pair in the sense of `TauCeti.IsAlgebraicBelyiPair`. -/
structure AlgebraicBelyiPair (k : Type u) [Field k] [CharZero k] where
  /-- The function field of the pair. -/
  carrier : Type u
  [field : Field carrier]
  [algebra : Algebra k carrier]
  [algebraRatFunc : Algebra (RatFunc k) carrier]
  [isScalarTower : IsScalarTower k (RatFunc k) carrier]
  [finiteDimensional : FiniteDimensional (RatFunc k) carrier]
  /-- The function field, over the rational function field, is an algebraic Belyi pair. -/
  isAlgebraicBelyiPair : IsAlgebraicBelyiPair k carrier

attribute [instance] AlgebraicBelyiPair.field AlgebraicBelyiPair.algebra
  AlgebraicBelyiPair.algebraRatFunc AlgebraicBelyiPair.isScalarTower
  AlgebraicBelyiPair.finiteDimensional

namespace AlgebraicBelyiPair

variable {k : Type u} [Field k] [CharZero k]

instance : CoeSort (AlgebraicBelyiPair k) (Type u) :=
  ⟨AlgebraicBelyiPair.carrier⟩

attribute [coe] AlgebraicBelyiPair.carrier

variable (k) in
/-- Isomorphism of algebraic Belyi pairs: two pairs are related when their function fields are
isomorphic over `k(t)`. -/
@[expose]
def isoSetoid : Setoid (AlgebraicBelyiPair k) where
  r X Y := Nonempty (X ≃ₐ[RatFunc k] Y)
  iseqv := ⟨fun _ ↦ ⟨AlgEquiv.refl⟩, fun ⟨e⟩ ↦ ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ ↦ ⟨e.trans f⟩⟩

variable (k) in
/-- The **isomorphism classes** of algebraic Belyi pairs over `k`: pairs up to isomorphism of
function fields over `k(t)`. -/
@[expose]
def IsoClass : Type (u + 1) :=
  Quotient (isoSetoid k)

namespace IsoClass

/-- The isomorphism class of an algebraic Belyi pair. -/
@[expose]
def mk (X : AlgebraicBelyiPair k) : IsoClass k :=
  Quotient.mk _ X

/-- Two algebraic Belyi pairs have the same isomorphism class exactly when their function fields
are isomorphic over `k(t)`. -/
theorem mk_eq_mk_iff {X Y : AlgebraicBelyiPair k} :
    mk X = mk Y ↔ Nonempty (X ≃ₐ[RatFunc k] Y) :=
  Quotient.eq

/-- Isomorphic algebraic Belyi pairs have the same isomorphism class. -/
theorem mk_eq_mk {X Y : AlgebraicBelyiPair k} (e : X ≃ₐ[RatFunc k] Y) : mk X = mk Y :=
  mk_eq_mk_iff.mpr ⟨e⟩

theorem mk_surjective : Function.Surjective (mk : AlgebraicBelyiPair k → IsoClass k) :=
  Quotient.mk_surjective

/-- Induction on isomorphism classes: a property of classes holds once it holds for the class of
every pair. -/
@[elab_as_elim]
theorem ind {motive : IsoClass k → Prop} (h : ∀ X, motive (mk X)) (c : IsoClass k) : motive c :=
  Quotient.ind h c

/-- The **degree** of an isomorphism class of algebraic Belyi pairs: the degree `[F : k(t)]` of
the function field of any representative over the rational function field. -/
noncomputable def degree : IsoClass k → ℕ :=
  Quotient.lift (fun X : AlgebraicBelyiPair k ↦ Module.finrank (RatFunc k) X)
    fun _ _ ⟨e⟩ ↦ e.toLinearEquiv.finrank_eq

@[simp]
theorem degree_mk (X : AlgebraicBelyiPair k) : (mk X).degree = Module.finrank (RatFunc k) X :=
  (rfl)

end IsoClass

end AlgebraicBelyiPair

end TauCeti
