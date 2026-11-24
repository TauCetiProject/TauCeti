/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Length
import Mathlib.LinearAlgebra.Quotient.Pi
import TauCeti.RingTheory.Ideal.Operations.Pi
import TauCeti.RingTheory.Length

/-!
# Lengths of the quotients `M ⧸ I • N`

For an ideal `I` of a ring `A` and a submodule `N` of an `A`-module `M`, this file records how
the lengths of the quotients `M ⧸ I • N` behave: `M ⧸ I • N` is filtered by `N ⧸ I • N` and
`M ⧸ N`, the length of `M ⧸ I • M` is invariant under linear equivalence, and it is additive over
finite products, since there `I • ⊤` is the product of the `I • ⊤` of the factors
(`Submodule.smul_top_eq_pi`). For `N = I ^ k • ⊤`, the quotient `M ⧸ I • N` is the truncation
`M ⧸ I ^ (k + 1) M` of the `I`-adic filtration, and the first fact computes the length of the
graded piece `I ^ k M ⧸ I ^ (k + 1) M` from the lengths of these truncations.

## Main results

* `TauCeti.length_quotient_smul_eq_length_quotient_smul_top_add`: `M ⧸ I • N` is filtered by
  `N ⧸ I • N` and `M ⧸ N`.
* `TauCeti.length_quotient_smul_top_congr`: the length of `M ⧸ I • M` is a linear-equivalence
  invariant.
* `TauCeti.length_pi_quotient_smul_top`: the length of `(∀ i, M i) ⧸ I • ⊤` is the sum of the
  lengths of the `M i ⧸ I • ⊤`.
-/

public section

namespace TauCeti

section Ring

variable {A M : Type*} [Ring A] [AddCommGroup M] [Module A M]

/-- For an ideal `I` and a submodule `N`, the quotient `M ⧸ I • N` is filtered by `N ⧸ I • N` and
`M ⧸ N`. -/
theorem length_quotient_smul_eq_length_quotient_smul_top_add (I : Ideal A) (N : Submodule A M) :
    Module.length A (M ⧸ I • N) =
      Module.length A (↥N ⧸ I • (⊤ : Submodule A N)) + Module.length A (M ⧸ N) := by
  have hmap : I • N = (I • (⊤ : Submodule A N)).map N.subtype := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]
  have hcomap : (I • N).comap N.subtype = I • ⊤ := by
    rw [hmap, Submodule.comap_map_eq_of_injective N.subtype_injective]
  rw [length_quotient_eq_length_quotient_comap_subtype_add Submodule.smul_le_right, hcomap]

/-- The length of `M ⧸ I • M` is a linear-equivalence invariant. -/
theorem length_quotient_smul_top_congr {N : Type*} [AddCommGroup N] [Module A N] (e : M ≃ₗ[A] N)
    (I : Ideal A) :
    Module.length A (M ⧸ I • (⊤ : Submodule A M)) =
      Module.length A (N ⧸ I • (⊤ : Submodule A N)) := by
  refine (Submodule.Quotient.equiv _ _ e ?_).length_eq
  rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]

end Ring

/-- Over a finite product, the length of the quotient by `I • ⊤` is the sum of the lengths of the
quotients of the factors by `I • ⊤`. -/
theorem length_pi_quotient_smul_top {A : Type*} [CommRing A] {ι : Type*} [Fintype ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)] (I : Ideal A) :
    Module.length A ((∀ i, M i) ⧸ I • (⊤ : Submodule A (∀ i, M i))) =
      ∑ i, Module.length A (M i ⧸ I • (⊤ : Submodule A (M i))) := by
  classical
  rw [Submodule.smul_top_eq_pi,
    (Submodule.quotientPi fun i ↦ I • (⊤ : Submodule A (M i))).length_eq,
    Module.length_pi_of_fintype]

end TauCeti
