/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.AnodyneExtensions.WeakHomotopyEquivalence
public import TauCeti.AlgebraicTopology.SimplicialSet.Pointed.Fibration
public import TauCeti.CategoryTheory.Adhesive.PullbackHom
import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
# Trivial fibrations of based mapping simplicial sets

The based pullback-hom corner
`Map_*(X,E) ⟶ Map_*(A,E) ×[Map_*(A,B)] Map_*(X,B)` lifts against every
simplicial monomorphism in either of the following cases:

* `A ⟶ X` is anodyne and `E ⟶ B` is a Kan fibration;
* `A ⟶ X` is a monomorphism and `E ⟶ B` lifts against all monomorphisms.

These are the two trivial-fibration lifting statements of the simplicial
mapping-space axiom. The conditions refer to the underlying simplicial sets;
no model-category instance or identification of arbitrary weak equivalences
with anodyne extensions is assumed. The corners are native
`Functor.PullbackObjObj` objects for the based internal hom.

In particular, restriction along an anodyne based map into a Kan complex is a
trivial fibration, and based mapping objects preserve trivial fibrations in
the target. All assertions hold for arbitrary simplicial parameter objects,
not just vertices or horns.

The proof uses the unpointed corner results and
`PointedSSet.hasLiftingProperty_pullbackObjObjπ`: the prescribed restriction
to the based source forces an unpointed lift to preserve the basepoint.
The unpointed results reuse Mathlib's parametrized adjunction and Jack McKoen's
adhesive pushout-product theorem, together with the anodyne pushout-product
theorem of Joël Riou and Jack McKoen.

## References

* P. G. Goerss and J. F. Jardine, *Simplicial homotopy theory*, Chapter I.
-/

public section

open CategoryTheory MonoidalClosed Limits MorphismProperty HomotopicalAlgebra
open scoped Simplicial

universe u

namespace TauCeti.PointedSSet

open SSet.modelCategoryQuillen

variable {A X E B : PointedSSet.{u}}

/-- The based corner of an anodyne extension and a Kan fibration lifts against every
monomorphism of simplicial sets. -/
lemma rlp_monomorphisms_pullbackObjObjπ (i : A ⟶ X) (p : E ⟶ B)
    (hi : SSet.anodyneExtensions i.right) [Fibration p.right]
    (P : internalHom.PullbackObjObj i p) :
    (monomorphisms SSet.{u}).rlp P.π.right := by
  let Q := Functor.PullbackObjObj.ofHasPullback internalHom i.right p.right
  have hQ := SSet.rlp_monomorphisms_pullbackObjObjπ hi Q
  intro K L j hj
  have := hQ j hj
  exact hasLiftingProperty_pullbackObjObjπ i p Q P j

/-- The based corner of a monomorphism and a map lifting against all monomorphisms
also lifts against all monomorphisms of simplicial sets. -/
lemma rlp_monomorphisms_pullbackObjObjπ_of_rlp (i : A ⟶ X) (p : E ⟶ B)
    [Mono i.right] (hp : (monomorphisms SSet.{u}).rlp p.right)
    (P : internalHom.PullbackObjObj i p) :
    (monomorphisms SSet.{u}).rlp P.π.right := by
  let Q := Functor.PullbackObjObj.ofHasPullback internalHom i.right p.right
  have hQ := Q.rlp_monomorphisms hp
  intro K L j hj
  have := hQ j hj
  exact hasLiftingProperty_pullbackObjObjπ i p Q P j

/-- Restricting based maps into a Kan complex along an anodyne based map is a
trivial fibration on underlying simplicial sets. -/
lemma rlp_monomorphisms_pre_app (i : A ⟶ X) (hi : SSet.anodyneExtensions i.right)
    (E : PointedSSet.{u}) [SSet.KanComplex E.right] :
    (monomorphisms SSet.{u}).rlp ((MonoidalClosed.pre i).app E).right := by
  have hT := terminalIsTerminal.isTerminalObj (Under.forget (Δ[0] : SSet.{u}))
    (⊤_ PointedSSet.{u})
  have : Fibration (terminal.from E).right :=
    (isFibrant_iff_of_isTerminal _ hT).1 inferInstance
  exact rlp_monomorphisms_pullbackObjObjπ i (terminal.from E) hi
    (Functor.PullbackObjObj.ofIsTerminal internalHom i (terminal.from E) terminalIsTerminal)

/-- Based mapping objects preserve maps lifting against all monomorphisms, with
no fibrancy assumption on either target and no condition on the based source. -/
lemma rlp_monomorphisms_ihom_map (X : PointedSSet.{u}) (p : E ⟶ B)
    (hp : (monomorphisms SSet.{u}).rlp p.right) :
    (monomorphisms SSet.{u}).rlp ((PointedSSet.ihom X).map p).right := by
  let i : Under.mk (𝟙 (Δ[0] : SSet.{u})) ⟶ X := Under.homMk X.hom
  have : Mono i.right := SSet.stdSimplex.isTerminalObj₀.mono_from X.hom
  exact rlp_monomorphisms_pullbackObjObjπ_of_rlp i p hp
    (Functor.PullbackObjObj.ofIsInitial internalHom i p Under.mkIdInitial)

end TauCeti.PointedSSet
