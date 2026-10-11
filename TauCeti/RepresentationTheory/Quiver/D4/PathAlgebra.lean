/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.D4.Basic
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Basic

/-!
# The path algebra of the `D₄` quiver

The `D₄` quiver has seven paths: the four trivial ones and the three arrows. So its path algebra
has rank seven over any semiring satisfying the strong rank condition. Over a division ring it
is seven-dimensional. Finite-dimensionality needs nothing specific to this quiver: it is acyclic,
so `TauCeti.finiteDimensional_pathAlgebra_of_isAcyclic` applies via `TauCeti.Quiver.D4.isAcyclic`.

## Main results

* `TauCeti.Quiver.D4.card_totalPath` and `TauCeti.Quiver.D4.finrank_pathAlgebra`: there are seven
  paths, so the path algebra has rank seven.

## References

See Derksen--Weyman, *An Introduction to Quiver Representations*, and
Assem--Simson--Skowroński, *Elements of the Representation Theory of Associative Algebras I*,
Ch. II.
-/

public section

namespace TauCeti

open _root_.Quiver

universe w

namespace Quiver.D4

/-- The `D₄` quiver has seven paths: the four trivial ones and the three arrows. -/
theorem card_totalPath : Fintype.card (Quiver.TotalPath D4) = 7 := by
  simp

/-- The path algebra of the `D₄` quiver has rank seven: four trivial paths and three
arrows. -/
@[simp]
theorem finrank_pathAlgebra (k : Type w) [Semiring k] [StrongRankCondition k] :
    Module.finrank k (pathAlgebra k D4) = 7 := by
  rw [TauCeti.finrank_pathAlgebra k D4, Nat.card_eq_fintype_card, card_totalPath]

end Quiver.D4

end TauCeti
