/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Prod

/-!
# Complementary submodules under restriction and products

Two ways complementarity of a pair of submodules survives a construction.

**Restriction to a subspace.** Mathlib's `Submodule.isCompl_comap_subtype_of_isCompl_of_le`
restricts a complementary pair to a subspace that contains one of the two. This file records the
variant that applies when neither member of the pair lies in the subspace: a disjoint pair cuts a
subspace `U` into a complementary pair as soon as the two intersections with `U` span `U` — for a
general `U` a genuine hypothesis, not a consequence of spanning the ambient module.

**Products.** Complementarity is also preserved by products: a complementary pair in `E` and one in
`F` give a complementary pair in `E × F`. This is what lets a direct-sum decomposition be built
factor by factor, and it is used that way for the doubled totally real modules in
`TauCeti/LinearAlgebra/TotallyReal/Basic.lean`.

## Main results

* `TauCeti.Submodule.isCompl_comap_subtype`: a disjoint pair of submodules whose intersections with
  `U` span `U` restricts to a complementary pair of submodules of `U`.
* `IsCompl.prod`: a product of complementary pairs is complementary.
-/

public section

namespace TauCeti

universe u v

namespace Submodule

variable {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]

/-- A disjoint pair of submodules whose intersections with a subspace `U` span `U` cuts `U` into a
complementary pair of submodules. -/
theorem isCompl_comap_subtype {U A B : Submodule R M} (hAB : Disjoint A B)
    (hU : U ≤ U ⊓ A ⊔ U ⊓ B) :
    IsCompl (A.comap U.subtype) (B.comap U.subtype) := by
  constructor
  · rw [disjoint_iff, ← Submodule.comap_inf, disjoint_iff.mp hAB, Submodule.comap_bot,
      Submodule.ker_subtype]
  · rw [codisjoint_iff]
    refine Submodule.map_injective_of_injective U.subtype_injective ?_
    rw [Submodule.map_sup, Submodule.map_comap_subtype, Submodule.map_comap_subtype,
      Submodule.map_subtype_top]
    exact le_antisymm (sup_le inf_le_left inf_le_left) hU

end Submodule

section Prod

variable {R E F : Type*} [Semiring R] [AddCommMonoid E] [Module R E] [AddCommMonoid F] [Module R F]
variable {L₁ L₂ : Submodule R E} {M₁ M₂ : Submodule R F}

/-- Products of complementary submodules are complementary. -/
theorem _root_.IsCompl.prod (hL : IsCompl L₁ L₂) (hM : IsCompl M₁ M₂) :
    IsCompl (L₁.prod M₁) (L₂.prod M₂) := by
  refine IsCompl.of_eq ?_ ?_
  · rw [Submodule.prod_inf_prod, hL.inf_eq_bot, hM.inf_eq_bot, Submodule.prod_bot]
  · rw [Submodule.prod_sup_prod, hL.sup_eq_top, hM.sup_eq_top, Submodule.prod_top]

end Prod

end TauCeti
