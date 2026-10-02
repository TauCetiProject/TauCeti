/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# The rank of a module tensored with a localization

Localizing a module at a submonoid of non-zero-divisors does not change its rank over the base
ring (`IsLocalizedModule.finrank_eq`), and tensoring with the localization `A` of `R` is such a
localization (`IsLocalization.tensorProduct_isLocalizedModule`). Mathlib states this for
`A ⊗[R] M`; this file records the same formula for `M ⊗[R] A`, the form in which a
rationalization `M ⊗[ℤ_p] ℚ_p` of a `ℤ_p`-module is written. Since `M ⊗[R] A` is an `A`-module
on which `R` acts through `A`, its `R`-rank is also its `A`-rank; for `A` a field this is the
dimension of the vector space `M ⊗[R] A`.

## Main results

* `TauCeti.IsLocalization.finrank_tensorProduct`: `finrank R (M ⊗[R] A) = finrank R M` for a
  localization `A` of `R` at a submonoid of non-zero-divisors.
-/

public section

namespace TauCeti.IsLocalization

open scoped TensorProduct

variable {R : Type*} [CommRing R] (S : Submonoid R) (A : Type*) [CommRing A] [Algebra R A]
  [IsLocalization S A] (hS : S ≤ nonZeroDivisors R) (M : Type*) [AddCommGroup M] [Module R M]

include hS in
/-- Tensoring with a localization at a submonoid of non-zero-divisors does not change the rank
over the base ring. -/
theorem finrank_tensorProduct : Module.finrank R (M ⊗[R] A) = Module.finrank R M :=
  (TensorProduct.comm R M A).finrank_eq.trans
    (IsLocalizedModule.finrank_eq S (TensorProduct.mk R A M 1) hS)

end TauCeti.IsLocalization
