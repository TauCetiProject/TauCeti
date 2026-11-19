/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import TauCeti.Combinatorics.PlanarMatching.Monoidal
import all TauCeti.Combinatorics.Enumerative.PerfectMatching
import all TauCeti.Combinatorics.PlanarMatching.Basic
import all TauCeti.Combinatorics.PlanarMatching.TLDiagram
import all TauCeti.Combinatorics.PlanarMatching.Compose
import all TauCeti.Combinatorics.PlanarMatching.Tensor
import all TauCeti.Combinatorics.PlanarMatching.Category

/-!
# The rigid structure of the Temperley–Lieb diagram category

Every object of the Temperley–Lieb diagram category `TauCeti.TLDiagCat` is its own dual, so
`TLDiagCat` is a rigid monoidal category.

The generating object `TLDiagCat.of 1`, a single boundary point, is self-dual with coevaluation
the cup `TLDiagCat.cup : of 0 ⟶ of 2` and evaluation the cap `TLDiagCat.cap : of 2 ⟶ of 0`. The
two zigzag identities are computations with diagrams on three boundary points, checked by
evaluating the composite diagrams. The empty boundary `of 0` is the monoidal unit, with its
canonical self-duality, and the self-duality of `of (n + 2)` is the tensor product of the
self-dualities of `of 1` and `of (n + 1)` (Mathlib's `CategoryTheory.ExactPairing.tensor`),
transported along `of (n + 2) = of 1 ⊗ of (n + 1)`. Pictorially, the coevaluation of `of n` is
`n` nested cups and its evaluation `n` nested caps; the examples at the end check this for two
strands, and that closing the identity of `of 2` produces two circles.

## Main definitions

* `TauCeti.TLDiagCat.exactPairingOne`: the generating self-duality of `of 1`, by the cup and the
  cap.
* `TauCeti.TLDiagCat.exactPairingOf`: the self-duality of `of n`, for every `n`.
* `TauCeti.TLDiagCat.instExactPairing`: every object is self-dual.
* `TauCeti.TLDiagCat.instRigidCategory`: the Temperley–Lieb diagram category is rigid, with
  every object its own left and right dual.

## Main results

* `TauCeti.TLDiagCat.coevaluation_one`, `TauCeti.TLDiagCat.evaluation_one`: the self-duality of
  the generating object is given by the cup and the cap.
* `TauCeti.TLDiagCat.coevaluation_zero`, `TauCeti.TLDiagCat.evaluation_zero`: the self-duality of
  the empty boundary is trivial.
* `TauCeti.TLDiagCat.coevaluation_add_two`, `TauCeti.TLDiagCat.evaluation_add_two`: the
  self-duality of `of (n + 2)` is the tensor product of those of `of 1` and `of (n + 1)`.
* `TauCeti.TLDiagCat.rightDual_eq`, `TauCeti.TLDiagCat.leftDual_eq`: every object is its own
  dual.

## Implementation notes

The zigzag identities of the generating object, and the examples at the end of the file, are
proved by `decide +kernel`, which evaluates the composite diagrams. This needs the definitions of
composition and juxtaposition of diagrams, which this file imports with `import all`.

## References

* J. Chen, *The Temperley–Lieb categories and skein modules*, arXiv:1502.06845, §2.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti

namespace TLDiagCat

/-- The generating self-duality: the single boundary point `of 1` is dual to itself, with the cup
as coevaluation and the cap as evaluation. The zigzag identities are checked on the composite
diagrams with three boundary points. This is the instance at `of 1`, see `coevaluation_one` and
`evaluation_one`. -/
@[instance_reducible]
def exactPairingOne : ExactPairing (of 1) (of 1) where
  coevaluation' := cup
  evaluation' := cap
  coevaluation_evaluation' := hom_ext <| TLDiagram.ext
    (PlanarMatching.ext fun a => Fin.ext (by revert a; decide +kernel)) (by decide +kernel)
  evaluation_coevaluation' := hom_ext <| TLDiagram.ext
    (PlanarMatching.ext fun a => Fin.ext (by revert a; decide +kernel)) (by decide +kernel)

/-- The self-duality of `of n`, by recursion on `n`: the unit's for `n = 0`, the cup and cap for
`n = 1`, and for `n + 2` the tensor product of those of `of 1` and `of (n + 1)`, transported
along `of (n + 2) = of 1 ⊗ of (n + 1)`. -/
@[instance_reducible]
def exactPairingOf : (n : ℕ) → ExactPairing (of n) (of n)
  | 0 => exactPairingUnit
  | 1 => exactPairingOne
  | n + 2 =>
    letI := exactPairingOne
    letI := exactPairingOf (n + 1)
    exactPairingCongrLeft (X := of (n + 2)) (X' := of 1 ⊗ of (n + 1)) (Y := of (n + 1) ⊗ of 1)
      (eqToIso (TLDiagCat.ext (Nat.add_comm 1 (n + 1)).symm))

/-- **Every object of the Temperley–Lieb diagram category is self-dual.** The coevaluation and
evaluation of the generating object `of 1` are the cup and the cap (`coevaluation_one`,
`evaluation_one`), and those of `of (n + 2)` are built from those of `of 1` and `of (n + 1)`
(`coevaluation_add_two`, `evaluation_add_two`). -/
instance instExactPairing (X : TLDiagCat) : ExactPairing X X :=
  exactPairingOf X.as

/-- The coevaluation of the generating object is the cup. -/
@[simp]
theorem coevaluation_one : η_ (of 1) (of 1) = cup := (rfl)

/-- The evaluation of the generating object is the cap. -/
@[simp]
theorem evaluation_one : ε_ (of 1) (of 1) = cap := (rfl)

/-- The coevaluation of the empty boundary is its identity. -/
@[simp]
theorem coevaluation_zero : η_ (of 0) (of 0) = 𝟙 (of 0) := (rfl)

/-- The evaluation of the empty boundary is its identity. -/
@[simp]
theorem evaluation_zero : ε_ (of 0) (of 0) = 𝟙 (of 0) := (rfl)

/-- The coevaluation of `of (n + 2)` is that of the tensor product of the self-dualities of `of 1`
and `of (n + 1)`, followed by the identification `of 1 ⊗ of (n + 1) = of (n + 2)`. Mathlib's
`CategoryTheory.ExactPairing.tensor_coevaluation` expands the first factor: it nests the
coevaluation of `of (n + 1)` inside the cup. -/
theorem coevaluation_add_two (n : ℕ) :
    η_ (of (n + 2)) (of (n + 2)) = η_ (of 1 ⊗ of (n + 1)) (of (n + 1) ⊗ of 1) ≫
      eqToHom (TLDiagCat.ext (Nat.add_comm 1 (n + 1))) ▷ of (n + 2) := (rfl)

/-- The evaluation of `of (n + 2)` is the identification `of (n + 2) = of 1 ⊗ of (n + 1)`
followed by the evaluation of the tensor product of the self-dualities of `of 1` and
`of (n + 1)`. Mathlib's `CategoryTheory.ExactPairing.tensor_evaluation` expands the second
factor: it nests the cap inside the evaluation of `of (n + 1)`. -/
theorem evaluation_add_two (n : ℕ) :
    ε_ (of (n + 2)) (of (n + 2)) =
      of (n + 2) ◁ eqToHom (TLDiagCat.ext (Nat.add_comm 1 (n + 1)).symm) ≫
        ε_ (of 1 ⊗ of (n + 1)) (of (n + 1) ⊗ of 1) := (rfl)

/-- **The Temperley–Lieb diagram category is rigid**: every object is its own left and right
dual. -/
instance instRigidCategory : RigidCategory TLDiagCat where
  rightDual X := ⟨X⟩
  leftDual X := ⟨X⟩

/-- Every object is its own right dual. -/
@[simp]
theorem rightDual_eq (X : TLDiagCat) : Xᘁ = X := (rfl)

/-- Every object is its own left dual. -/
@[simp]
theorem leftDual_eq (X : TLDiagCat) : (ᘁX : TLDiagCat) = X := (rfl)

end TLDiagCat

/-- The coevaluation of two boundary points is the two nested cups: its matching is the nested
matching, pairing the top points `i` and `3 - i`, and it has no circle. -/
example : (η_ (TLDiagCat.of 2) (TLDiagCat.of 2)).diagram =
    ⟨PlanarMatching.cast (Nat.zero_add 4).symm (PlanarMatching.nested 2), 0⟩ :=
  TLDiagram.ext (PlanarMatching.ext fun a => Fin.ext (by revert a; decide +kernel))
    (by decide +kernel)

/-- The evaluation of two boundary points is the two nested caps. -/
example : (ε_ (TLDiagCat.of 2) (TLDiagCat.of 2)).diagram =
    ⟨PlanarMatching.cast (Nat.add_zero 4).symm (PlanarMatching.nested 2), 0⟩ :=
  TLDiagram.ext (PlanarMatching.ext fun a => Fin.ext (by revert a; decide +kernel))
    (by decide +kernel)

/-- Closing the identity of two boundary points, coevaluation followed by evaluation, gives two
circles. -/
example : η_ (TLDiagCat.of 2) (TLDiagCat.of 2) ≫ ε_ (TLDiagCat.of 2) (TLDiagCat.of 2) =
    TLDiagCat.circle ≫ TLDiagCat.circle :=
  TLDiagCat.hom_ext <| TLDiagram.ext (PlanarMatching.ext fun a => a.elim0) (by decide +kernel)

end TauCeti
