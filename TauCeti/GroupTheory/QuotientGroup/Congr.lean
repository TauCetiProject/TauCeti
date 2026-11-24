/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import TauCeti.Algebra.Group.Subgroup.Map

/-!
# Left-translation equivariance of coset-space transport

The coset-space bijections `TauCeti.QuotientGroup.congrComapOfSurjectiveMk` and
`TauCeti.QuotientGroup.congrOfMapEq` (defined in `TauCeti.Algebra.Group.Subgroup.Map`) act on
representatives by the underlying group homomorphism or isomorphism, so they are equivariant for
left translation on cosets.

These lemmas live in their own lightweight module so that:
* `TauCeti.Algebra.Group.Subgroup.Map` does not pull in `Mathlib.GroupTheory.GroupAction.Quotient`,
* `TauCeti.GroupTheory.QuotientGroup.Basic` does not publicly expose the `TauCeti.Subgroup`
  namespace (which would make `open Subgroup` ambiguous inside `namespace TauCeti` in downstream
  files), and
* callers needing only coset-translation equivariance do not depend on the
  permutation-representation and centralizer machinery in
  `TauCeti.Algebra.GroupAction.CosetRepresentation`.

## Main statements

* `TauCeti.QuotientGroup.congrComapOfSurjectiveMk_smul`: `congrComapOfSurjectiveMk` intertwines
  left translation by `g` with left translation by `ψ g`.
* `TauCeti.QuotientGroup.congrOfMapEq_smul`: `congrOfMapEq` intertwines left translation by `g`
  with left translation by `φ g`.
-/

public section

namespace TauCeti.QuotientGroup

variable {G G' : Type*} [Group G] [Group G']

/-- `TauCeti.QuotientGroup.congrComapOfSurjectiveMk` intertwines left translation by `g` with left
translation by `ψ g`. -/
@[simp] theorem congrComapOfSurjectiveMk_smul (ψ : G →* G') (B : Subgroup G')
    (hψ : Function.Surjective fun g : G ↦ (ψ g : G' ⧸ B)) (g : G) (q : G ⧸ B.comap ψ) :
    congrComapOfSurjectiveMk ψ B hψ (g • q) = ψ g • congrComapOfSurjectiveMk ψ B hψ q :=
  _root_.QuotientGroup.induction_on q fun _ ↦ by
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, congrComapOfSurjectiveMk_mk,
      congrComapOfSurjectiveMk_mk, map_mul, MulAction.Quotient.smul_mk, smul_eq_mul]

/-- `TauCeti.QuotientGroup.congrOfMapEq` intertwines left translation by `g` with left translation
by `φ g`. -/
@[simp] theorem congrOfMapEq_smul (φ : G ≃* G') {A : Subgroup G} {B : Subgroup G'}
    (h : A.map (φ : G →* G') = B) (g : G) (q : G ⧸ A) :
    congrOfMapEq φ h (g • q) = φ g • congrOfMapEq φ h q :=
  _root_.QuotientGroup.induction_on q fun _ ↦ by
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, congrOfMapEq_mk, congrOfMapEq_mk, map_mul,
      MulAction.Quotient.smul_mk, smul_eq_mul]

end TauCeti.QuotientGroup
