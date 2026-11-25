/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Maps
public import TauCeti.Algebra.Bialgebra.ModuleAlgebra.SmashProduct

/-!
# Ideal properties of the smash product

This file records ideal-theoretic properties of the smash product `A # H`
(`TauCeti.LeftModuleAlgebra.SmashProduct`), separated from the core construction so that users
of `SmashProduct` do not transitively import ideal-map theory.

## Main results

* `TauCeti.LeftModuleAlgebra.SmashProduct.ker_includeH_eq_top`: when `A` is subsingleton, the
  canonical inclusion `includeH : H →ₐ[R] A # H` (`h ↦ 1 # h`) has kernel `⊤`.

## References

* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, §4.1.
* Y. Qi, *Hopfological algebra*, Example 2.8.
-/

public section

namespace TauCeti

namespace LeftModuleAlgebra

namespace SmashProduct

section Ideal

variable {R H A : Type*}
  [CommSemiring R] [Semiring H] [Bialgebra R H] [Semiring A] [Algebra R A]

/-- When `A` is subsingleton, `includeH : H →ₐ[R] A # H` has kernel `⊤`. -/
@[simp]
theorem ker_includeH_eq_top (μ : LeftModuleAlgebra R H A) [Subsingleton A] :
    RingHom.ker (includeH (μ := μ) : H →+* SmashProduct μ) = ⊤ :=
  (Ideal.eq_top_iff_one _).2 (RingHom.mem_ker.2 (Subsingleton.elim _ _))

end Ideal

end SmashProduct

end LeftModuleAlgebra

end TauCeti
