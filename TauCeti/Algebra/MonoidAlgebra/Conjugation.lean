/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Conjugation on the group algebra of a normal subgroup

Let `N` be a normal subgroup of a group `G`.  Conjugating by `g : G` is an automorphism of `N`
(`MulAut.conjNormal`), so it permutes the basis of the group algebra `A[N]` and therefore induces an
`R`-algebra automorphism of `A[N]`, for any `R`-algebra `A`.  This file packages that automorphism
as a monoid homomorphism `MonoidAlgebra.conjNormalAlgAut : G →* (A[N] ≃ₐ[R] A[N])`, obtained by
composing Mathlib's `MonoidAlgebra.domCongrAut` with `MulAut.conjNormal`.

## Main definitions

* `MonoidAlgebra.conjNormalAlgAut`: conjugation by `g : G` as an algebra automorphism of `A[N]`.

## Main statements

* `MonoidAlgebra.conjNormalAlgAut_apply`: conjugation by `g` is `MonoidAlgebra.domCongr` along
  `MulAut.conjNormal g`, which gives access to the `MonoidAlgebra.domCongr` API.
* `MonoidAlgebra.conjNormalAlgAut_single`: conjugation acts on the group-algebra basis by
  conjugating the group element.

Conjugating by `g` and then by `g⁻¹` is the identity; that cancellation is left to `simp`, which
proves it from `map_inv` and `AlgEquiv.symm_apply_apply`.
-/

public section

open scoped MonoidAlgebra

namespace MonoidAlgebra

variable (R A : Type*) {G : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Group G]
  (N : Subgroup G) [N.Normal]

/-- **Conjugation, read on the group algebra of a normal subgroup.**  Conjugating by `g : G`
permutes `N`, hence permutes the basis of `A[N]`; this is the resulting `R`-algebra automorphism.
Translation by a representation of `G` is semilinear over it. -/
noncomputable def conjNormalAlgAut : G →* (A[N] ≃ₐ[R] A[N]) :=
  (domCongrAut (R := R) (A := A) (M := N)).comp MulAut.conjNormal

variable {R A N}

/-- Conjugation by `g` is `MonoidAlgebra.domCongr` along the automorphism `MulAut.conjNormal g`
of `N`. -/
theorem conjNormalAlgAut_apply (g : G) :
    conjNormalAlgAut R A N g = domCongr R A (MulAut.conjNormal g) :=
  (rfl)

/-- Conjugation acts on the group-algebra basis by conjugating the group element. -/
@[simp]
theorem conjNormalAlgAut_single (g : G) (n : N) (a : A) :
    conjNormalAlgAut R A N g (single n a) = single (MulAut.conjNormal g n) a :=
  domCongr_single _ _ _

end MonoidAlgebra
