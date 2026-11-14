/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Order.KrullDimension
import Mathlib.Topology.KrullDimension

/-!
# Codimension-one points of a scheme

A point of a scheme has codimension one when its coheight for the specialization order is one,
equivalently when it is the generic point of an irreducible closed subset of codimension one.
This file introduces the subtype of such points and records the one order-theoretic fact about
them that does not mention any further structure: a codimension-one point has no codimension-one
generization other than itself.

Codimension-one points index prime divisors, and they arise as centres of places of the function
field; this file holds only the common definition, independent of either theory.

## Main declarations

* `TauCeti.AlgebraicGeometry.CodimensionOnePoint`: the codimension-one points of a scheme.
* `TauCeti.AlgebraicGeometry.CodimensionOnePoint.eq_of_specializes`: a codimension-one
  generization of a codimension-one point is equal to it.
* `TauCeti.AlgebraicGeometry.CodimensionOnePoint.finite_setOfPred_notMem`: a nonempty open of an
  irreducible Noetherian scheme misses only finitely many codimension-one points.
-/

public section

open Order AlgebraicGeometry TopologicalSpace

namespace TauCeti

namespace AlgebraicGeometry

universe u

/-- A codimension-one point of a scheme: a point of coheight one for the specialization order,
that is, the generic point of an irreducible closed subset of codimension one. -/
abbrev CodimensionOnePoint (X : Scheme.{u}) : Type u :=
  {x : X // coheight x = 1}

/-- A codimension-one point admits no codimension-one generization other than itself. -/
lemma CodimensionOnePoint.eq_of_specializes {X : Scheme.{u}} {x y : CodimensionOnePoint X}
    (h : (y : X) ⤳ (x : X)) : y = x := by
  refine Subtype.ext (h.antisymm ?_).eq
  by_contra hxy
  have := coheight_add_one_le <|
    lt_of_le_not_ge (Scheme.le_iff_specializes.mpr h) (mt Scheme.le_iff_specializes.mp hxy)
  norm_num [x.property, y.property] at this

/-- A nonempty open subset of an irreducible scheme with Noetherian underlying space contains all
but finitely many codimension-one points. -/
lemma CodimensionOnePoint.finite_setOfPred_notMem {X : Scheme.{u}} [IrreducibleSpace X]
    [NoetherianSpace X] (U : X.Opens) [Nonempty U] :
    {x : CodimensionOnePoint X | (x : X) ∉ U}.Finite := by
  have hU := U.isOpen.isClosed_compl
  have : QuasiSober ((U : Set X)ᶜ : Set X) := hU.isClosedEmbedding_subtypeVal.quasiSober
  refine ((NoetherianSpace.finite_coheight_one_of_closure_ne_univ (p := (U : Set X)ᶜ) ?_).preimage
    Subtype.val_injective.injOn).subset fun x hx ↦ ⟨hx, x.2⟩
  rw [hU.closure_eq]
  exact fun h ↦ (Set.nonempty_coe_sort.mp ‹Nonempty U›).ne_empty (compl_eq_top.mp h)

end AlgebraicGeometry

end TauCeti
