/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.AbelRuffini

/-!
# Binomial extensions have solvable automorphism groups

Mathlib proves that the Galois group `(X ^ n - C a).Gal` of a binomial is solvable
(`gal_X_pow_sub_C_isSolvable`), as a statement about the chosen splitting field
`(X ^ n - C a).SplittingField`. This file transports it to an arbitrary splitting field `L`, so
that a radical extension presented through `Polynomial.IsSplittingField` has a solvable
automorphism group.

## Main results

* `TauCeti.isSolvable_of_isSplittingField_X_pow_sub_C`: the automorphism group of any splitting
  field of `X ^ n - C a` is solvable.
-/

public section

open Polynomial

namespace TauCeti

/-- The automorphism group of a splitting field of `X ^ n - C a` is solvable. -/
theorem isSolvable_of_isSplittingField_X_pow_sub_C {F L : Type*} [Field F] [Field L]
    [Algebra F L] (n : ℕ) (a : F) [IsSplittingField F L (X ^ n - C a)] :
    Group.IsSolvable (L ≃ₐ[F] L) :=
  have : Group.IsSolvable ((X ^ n - C a).SplittingField ≃ₐ[F] (X ^ n - C a).SplittingField) :=
    gal_X_pow_sub_C_isSolvable n a
  Group.isSolvable_of_surjective
    (f := (AlgEquiv.autCongr (IsSplittingField.algEquiv L (X ^ n - C a))).symm.toMonoidHom)
    (MulEquiv.surjective _)

end TauCeti
