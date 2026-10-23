/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Kronecker.Basic
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Basic

/-!
# The path algebra of the generalized Kronecker quiver

The generalized Kronecker quiver on `n` arrows has `n + 2` paths: the two trivial paths and the
arrows themselves. Over a semiring satisfying the strong rank condition, its path algebra has
finite rank `n + 2`; for the Kronecker quiver `• ⇉ •` itself this is `4`.
The path classification and count are developed in
`TauCeti.RepresentationTheory.Quiver.Kronecker.Basic`.
Finite-dimensionality needs nothing specific to this quiver: it is acyclic, so
`TauCeti.finiteDimensional_pathAlgebra_of_isAcyclic` applies to it as it stands, via
`TauCeti.Quiver.Kronecker.isAcyclic`.

## Main results

* `TauCeti.Quiver.Kronecker.finrank_pathAlgebra`: the `n + 2` paths give the path algebra
  finite rank `n + 2`.
* `TauCeti.Quiver.Kronecker.finrank_pathAlgebra_eq_four` and
  `TauCeti.Quiver.Kronecker.finrank_pathAlgebra_eq_three`: for the Kronecker quiver `• ⇉ •` the
  path algebra has finite rank four, and for the `A₂` quiver `• → •` finite rank three.

## References

Derksen--Weyman, *An Introduction to Quiver Representations*, and Assem--Simson--Skowroński,
*Elements of the Representation Theory of Associative Algebras I*, Ch. II.
-/

public section

namespace TauCeti

open _root_.Quiver

universe v w

namespace Quiver.Kronecker

variable {A : Type v}

/-- The path algebra of the generalized Kronecker quiver on `n` arrows has finite rank `n + 2`
over a semiring satisfying the strong rank condition. For `• ⇉ •` this is `4`. -/
theorem finrank_pathAlgebra (k : Type w) [Semiring k] [StrongRankCondition k] [Fintype A] :
    Module.finrank k (pathAlgebra k (Kronecker A)) = Fintype.card A + 2 := by
  rw [TauCeti.finrank_pathAlgebra k (Kronecker A), Nat.card_eq_fintype_card, card_totalPath]

/-- The path algebra of the Kronecker quiver has finite rank four: two trivial paths and two
arrows, over a semiring satisfying the strong rank condition. -/
theorem finrank_pathAlgebra_eq_four [Fintype A] (h : Fintype.card A = 2) (k : Type w)
    [Semiring k] [StrongRankCondition k] : Module.finrank k (pathAlgebra k (Kronecker A)) = 4 := by
  rw [finrank_pathAlgebra k, h]

/-- The path algebra of the `A₂` quiver has finite rank three: the two trivial paths and the
arrow, over a semiring satisfying the strong rank condition. -/
theorem finrank_pathAlgebra_eq_three [Unique A] (k : Type w) [Semiring k] [StrongRankCondition k] :
    Module.finrank k (pathAlgebra k (Kronecker A)) = 3 := by
  let : Fintype A := Fintype.ofFinite A
  rw [finrank_pathAlgebra k, Fintype.card_unique]

end Quiver.Kronecker

end TauCeti
