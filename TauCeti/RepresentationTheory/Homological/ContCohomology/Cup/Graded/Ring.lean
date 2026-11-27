/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.DirectSum.Ring
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Assoc
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Unit

/-!
# The graded cohomology ring of an associative unital coefficient pairing

Let `P : TopPairing X X X` be a coefficient pairing of a topological representation `X` with
itself which is associative and has an invariant two-sided unit `u`. Then the cup product along
`P` makes the family `n ↦ Hⁿ(G, X)` a graded ring, with unit the degree-zero class of `u`. This
file packages that structure as Mathlib's `DirectSum.GRing`, so that `⨁ n, Hⁿ(G, X)` is a ring.

The unit and associativity laws are the all-degree cup-product identities
`TauCeti.TopPairing.cup_one_left`, `TauCeti.TopPairing.cup_one_right` and
`TauCeti.TopPairing.cup_assoc`; distributivity is the bilinearity of the cup product. No
commutativity is asserted: the cup product is only graded-commutative
(`TauCeti.TopPairing.cup_gradedComm`), so `DirectSum.GCommRing` is a statement about particular
coefficients.

## Main definitions

* `TauCeti.TopPairing.cohomologyGRing`: the graded ring structure on `n ↦ Hⁿ(G, X)` given by the
  cup product along `P`.

## Main results

* `TauCeti.TopPairing.cohomologyGRing_mul`, `TauCeti.TopPairing.cohomologyGRing_one`: the
  multiplication of homogeneous classes is the cup product along `P`, and the unit is the
  degree-zero class of `u`.
-/

public section

namespace TauCeti

open CategoryTheory
open TauCeti.ContinuousCohomology (degreeZeroClass)

universe u v w

namespace TopPairing

variable {R : Type u} [CommRing R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {X : TopRep.{max v w} R G}

/-- **The graded cohomology ring of a coefficient pairing.** For an associative pairing
`P : TopPairing X X X` with a `G`-invariant two-sided unit `u`, the cup product along `P` and the
degree-zero class of `u` make `n ↦ Hⁿ(G, X)` a graded ring. The multiplication of homogeneous
classes is `P.cup m n` (`TauCeti.TopPairing.cohomologyGRing_mul`) and the unit is
`degreeZeroClass X u hinv` (`TauCeti.TopPairing.cohomologyGRing_one`).

This is not an instance, since `P` and `u` do not occur in its type; it is reducible so that
instances defined from it unfold, see note [reducible non-instances]. -/
noncomputable abbrev cohomologyGRing (P : TopPairing X X X) (u : X.V)
    (hinv : ∀ g : G, X.ρ g u = u) (hleft : ∀ x : X.V, P.bil u x = x)
    (hright : ∀ x : X.V, P.bil x u = x)
    (hassoc : ∀ x y z : X.V, P.bil (P.bil x y) z = P.bil x (P.bil y z)) :
    DirectSum.GRing fun n ↦ continuousCohomology n X :=
  TauCeti.DirectSum.gRingOfMul
    (fun m n ↦ LinearMap.toAddMonoidHom'.comp (P.cup m n).toAddMonoidHom)
    (degreeZeroClass X u hinv)
    (fun x ↦ Sigma.ext (Nat.zero_add _)
      ((P.cup_one_left u hleft hinv _ x).heq.trans
        (ContinuousCohomology.degreeCast_hom_apply_heq _ x)))
    (fun x ↦ Sigma.ext (Nat.add_zero _) (P.cup_one_right u hright hinv _ x).heq)
    (fun x y z ↦ Sigma.ext (Nat.add_assoc _ _ _)
      ((P.cup_assoc P P P hassoc _ _ _ x y z).heq.trans
        (ContinuousCohomology.degreeCast_hom_apply_heq _ _)))

section Characteristic

variable (P : TopPairing X X X) (u : X.V) (hinv : ∀ g : G, X.ρ g u = u)
  (hleft : ∀ x : X.V, P.bil u x = x) (hright : ∀ x : X.V, P.bil x u = x)
  (hassoc : ∀ x y z : X.V, P.bil (P.bil x y) z = P.bil x (P.bil y z))

/-- The multiplication of homogeneous classes in `TauCeti.TopPairing.cohomologyGRing` is the cup
product along `P`. -/
@[simp] theorem cohomologyGRing_mul {m n : ℕ} (x : continuousCohomology m X)
    (y : continuousCohomology n X) :
    (P.cohomologyGRing u hinv hleft hright hassoc).mul x y = P.cup m n x y :=
  rfl

/-- The unit of `TauCeti.TopPairing.cohomologyGRing` is the degree-zero class of `u`. -/
@[simp] theorem cohomologyGRing_one :
    (P.cohomologyGRing u hinv hleft hright hassoc).one = degreeZeroClass X u hinv :=
  rfl

end Characteristic

end TopPairing

end TauCeti
