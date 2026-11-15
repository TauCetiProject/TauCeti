/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.AffineD.FiniteRepType
public import TauCeti.RepresentationTheory.Quiver.AffineE6.FiniteRepType
public import TauCeti.RepresentationTheory.Quiver.AffineE7.FiniteRepType
public import TauCeti.RepresentationTheory.Quiver.AffineE8.FiniteRepType
public import TauCeti.RepresentationTheory.Quiver.FiniteRepType.Orientation

/-!
# Extended Dynkin trees in the underlying graph obstruct finite representation type

The extended Dynkin quivers `TauCeti.Quiver.AffineD m`, `TauCeti.Quiver.AffineE6`,
`TauCeti.Quiver.AffineE7` and `TauCeti.Quiver.AffineE8` have infinite representation type over every
field, each in one fixed orientation. Their underlying graphs, the extended Dynkin diagrams `D~ₘ₊₄`,
`E₆~`, `E₇~` and `E₈~`, are trees. This file shows that each of them obstructs finite representation
type wherever it occurs in the underlying graph of a quiver: if the underlying graph of `Q` contains
a copy of one of these trees, not necessarily induced, then `Q` has infinite representation type,
whatever the directions and multiplicities of the arrows of `Q` along the copy.

The deduction is `TauCeti.IsFiniteRepType.of_copy_underlyingGraph`: the arrows of `Q` along the copy
orient the tree as a subquiver of `Q`, and finite representation type of a tree does not depend on
its orientation.

These four trees are the extended Dynkin obstructions of Gabriel's theorem that are not cycles: a
finite tree which is not a Dynkin diagram contains a copy of one of them.

## Main results

* `TauCeti.not_isFiniteRepType_of_copy_affineD`: a quiver whose underlying graph contains `D~ₘ₊₄`
  has infinite representation type.
* `TauCeti.not_isFiniteRepType_of_copy_affineE6`, `TauCeti.not_isFiniteRepType_of_copy_affineE7`
  and `TauCeti.not_isFiniteRepType_of_copy_affineE8`: the same for `E₆~`, `E₇~` and `E₈~`.

## Implementation notes

The statements are for representations with vertex spaces in the universe of the base field, the
universe in which the infinite families of the four extended Dynkin quivers are built.

## References

* I. N. Bernstein, I. M. Gelfand, V. A. Ponomarev, *Coxeter functors and Gabriel's theorem*,
  Russian Math. Surveys **28** (1973), 17--32.
* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras*, Volume I, Chapter VII.
-/

public section

namespace TauCeti

open _root_.TauCeti.Quiver

universe u v w

variable {k : Type u} [Field k] {Q : Type v} [_root_.Quiver.{w} Q]

/-- **A copy of `D~ₘ₊₄` in the underlying graph obstructs finite representation type.** If the
underlying graph of `Q` contains a copy of the extended Dynkin diagram `D~ₘ₊₄`, the underlying graph
of `TauCeti.Quiver.AffineD m`, then `Q` has infinite representation type over every field. -/
theorem not_isFiniteRepType_of_copy_affineD (m : ℕ)
    (f : (underlyingGraph (AffineD m)).Copy (underlyingGraph Q)) :
    ¬ IsFiniteRepType.{u, v, w, u} k Q := fun h ↦
  not_isFiniteRepType_affineD k m (h.of_copy_underlyingGraph AffineD.subsingleton_hom_sum
    AffineD.isAcyclic_underlyingGraph f)

/-- **A copy of `E₆~` in the underlying graph obstructs finite representation type.** If the
underlying graph of `Q` contains a copy of the extended Dynkin diagram `E₆~`, the underlying graph
of `TauCeti.Quiver.AffineE6`, then `Q` has infinite representation type over every field. -/
theorem not_isFiniteRepType_of_copy_affineE6
    (f : (underlyingGraph AffineE6).Copy (underlyingGraph Q)) :
    ¬ IsFiniteRepType.{u, v, w, u} k Q := fun h ↦
  not_isFiniteRepType_affineE6 k (h.of_copy_underlyingGraph AffineE6.subsingleton_hom_sum
    AffineE6.isAcyclic_underlyingGraph f)

/-- **A copy of `E₇~` in the underlying graph obstructs finite representation type.** If the
underlying graph of `Q` contains a copy of the extended Dynkin diagram `E₇~`, the underlying graph
of `TauCeti.Quiver.AffineE7`, then `Q` has infinite representation type over every field. -/
theorem not_isFiniteRepType_of_copy_affineE7
    (f : (underlyingGraph AffineE7).Copy (underlyingGraph Q)) :
    ¬ IsFiniteRepType.{u, v, w, u} k Q := fun h ↦
  not_isFiniteRepType_affineE7 k (h.of_copy_underlyingGraph AffineE7.subsingleton_hom_sum
    AffineE7.isAcyclic_underlyingGraph f)

/-- **A copy of `E₈~` in the underlying graph obstructs finite representation type.** If the
underlying graph of `Q` contains a copy of the extended Dynkin diagram `E₈~`, the underlying graph
of `TauCeti.Quiver.AffineE8`, then `Q` has infinite representation type over every field. -/
theorem not_isFiniteRepType_of_copy_affineE8
    (f : (underlyingGraph AffineE8).Copy (underlyingGraph Q)) :
    ¬ IsFiniteRepType.{u, v, w, u} k Q := fun h ↦
  not_isFiniteRepType_affineE8 k (h.of_copy_underlyingGraph AffineE8.subsingleton_hom_sum
    AffineE8.isAcyclic_underlyingGraph f)

end TauCeti
