/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Bialgebra.ModuleAlgebra.SmashProduct.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Injectivity of the bialgebra inclusion into a smash product over a field

Over a field `K`, any nontrivial `K`-algebra `A` admits a `K`-linear functional sending `1 : A` to
`1 : K`, so the canonical inclusion `includeH : H →ₐ[K] A # H` (`h ↦ 1 # h`) into the smash
product is injective.

## Main results

* `TauCeti.LeftModuleAlgebra.includeH_injective`: `h ↦ 1 # h` is injective over any field when
  `A` is nontrivial.

## References

* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, §4.1.
* Y. Qi, *Hopfological algebra*, Example 2.8.
-/

public section

namespace TauCeti

namespace LeftModuleAlgebra

universe u v w

section FieldEmbedding

variable {K : Type u} {H : Type v} {A : Type w}
  [Field K] [Semiring H] [Bialgebra K H] [Semiring A] [Algebra K A]

/-- Over a field, `includeH : H →ₐ[K] A # H` is injective whenever `A` is nontrivial. -/
theorem includeH_injective (μ : LeftModuleAlgebra K H A) [Nontrivial A] :
    Function.Injective μ.includeH := by
  let _ := Module.addCommMonoidToAddCommGroup K (M := A)
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one K (one_ne_zero : (1 : A) ≠ 0)
  exact μ.includeH_injective_of_apply_one_eq_one φ hφ

end FieldEmbedding

end LeftModuleAlgebra

end TauCeti
