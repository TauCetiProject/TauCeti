/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.TrivialFibration
public import TauCeti.AlgebraicTopology.SimplicialSet.WeakHomotopyEquivalence
import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction

/-!
# Anodyne extensions are weak homotopy equivalences

Let `i : A ⟶ B` be an anodyne extension of simplicial sets and `p : E ⟶ X` a Kan fibration. The
pullback-hom of `i` and `p`, the map from `Fun(B, E)` to the pullback of `Fun(A, E)` and
`Fun(B, X)` over `Fun(A, X)`, is a trivial fibration: it has the right lifting property with
respect to all monomorphisms (`SSet.rlp_monomorphisms_pullbackObjObjπ`). By adjunction this is
the statement that the pushout-product of a monomorphism with `i` is anodyne, which is Mathlib's
`SSet.anodyneExtensions_pushoutObjObjι'`. This complements Mathlib's
`SSet.fibration_pullbackObjObjπ`, where `i` is only a monomorphism and the pullback-hom is only
a Kan fibration. Taking for `p` the map from a Kan complex `Z` to the point, restriction along
`i` is a trivial fibration `Fun(B, Z) ⟶ Fun(A, Z)` (`SSet.rlp_monomorphisms_pre_app`).

A trivial fibration induces a bijection on connected components
(`SSet.bijective_mapπ₀_of_rlp_monomorphisms`). Hence an anodyne extension `i` induces a bijection
`π₀ Fun(B, Z) → π₀ Fun(A, Z)` for every Kan complex `Z`: it is a weak homotopy equivalence in the
sense of `SSet.IsWeakHomotopyEquivalence` (`SSet.anodyneExtensions.isWeakHomotopyEquivalence`).
The anodyne extensions are the trivial cofibrations of the Kan–Quillen model structure, and this
is their inclusion in the weak equivalences, tested against Kan complexes.

## References

* P. Gabriel and M. Zisman, *Calculus of fractions and homotopy theory*, Ergebnisse der
  Mathematik 35, Springer, 1967, Chapter IV, Section 2.
* P. G. Goerss and J. F. Jardine, *Simplicial homotopy theory*, Progress in Mathematics 174,
  Birkhäuser, 1999, Sections I.4 and I.5.
* J. Lurie, *Kerodon*, Chapter 3, Section 3.1.
-/

public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed HomotopicalAlgebra Limits MorphismProperty

namespace SSet

open modelCategoryQuillen

variable {X₁ Y₁ E B : SSet.{u}} {i : X₁ ⟶ Y₁} {p : E ⟶ B}

/-- The pullback-hom of an anodyne extension `i` and a Kan fibration `p` has the right lifting
property with respect to all monomorphisms. -/
lemma rlp_monomorphisms_pullbackObjObjπ (hi : anodyneExtensions i) [Fibration p]
    (sq₁₃ : internalHom.PullbackObjObj i p) :
    (monomorphisms SSet.{u}).rlp sq₁₃.π := by
  intro _ _ j (_ : Mono j)
  let sq₁₂ := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet) i j
  rw [← internalHomAdjunction₂.hasLiftingProperty_iff sq₁₂]
  exact anodyneExtensions_pushoutObjObjι' sq₁₂ hi _ (mem_fibrations p)

/-- Restriction `Fun(Y₁, Z) ⟶ Fun(X₁, Z)` along an anodyne extension `i : X₁ ⟶ Y₁`, for a Kan
complex `Z`, has the right lifting property with respect to all monomorphisms. -/
lemma rlp_monomorphisms_pre_app (hi : anodyneExtensions i) (Z : SSet.{u}) [KanComplex Z] :
    (monomorphisms SSet.{u}).rlp ((pre i).app Z) :=
  rlp_monomorphisms_pullbackObjObjπ hi
    (Functor.PullbackObjObj.ofIsTerminal internalHom i (terminal.from Z) terminalIsTerminal)

/-- An anodyne extension is a weak homotopy equivalence. -/
lemma anodyneExtensions.isWeakHomotopyEquivalence (hi : anodyneExtensions i) :
    IsWeakHomotopyEquivalence i where
  bijective_mapπ₀_pre_app Z _ :=
    bijective_mapπ₀_of_rlp_monomorphisms (rlp_monomorphisms_pre_app hi Z)

end SSet
