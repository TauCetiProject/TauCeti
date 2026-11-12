/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Additive homomorphisms as morphisms of integer modules

Bundling additive homomorphisms as integer-linear categorical morphisms preserves and
reflects vanishing of their composite. This transports zero-composite laws between
additive groups and `ModuleCat ℤ`.
-/

public section

open CategoryTheory

namespace AddMonoidHom

universe u

variable {M N P : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]

/-- The categorical composite of the integer-linear maps associated to additive homomorphisms
vanishes exactly when their additive composite vanishes. -/
theorem ofHom_toIntLinearMap_comp_eq_zero_iff (a : M →+ N) (b : N →+ P) :
    ModuleCat.ofHom a.toIntLinearMap ≫ ModuleCat.ofHom b.toIntLinearMap = 0 ↔
      b.comp a = 0 := by
  rw [← ModuleCat.ofHom_comp, ← ModuleCat.hom_injective.eq_iff]
  simp only [ModuleCat.hom_ofHom, ModuleCat.hom_zero, LinearMap.ext_iff,
    LinearMap.comp_apply, AddMonoidHom.coe_toIntLinearMap, LinearMap.zero_apply,
    AddMonoidHom.ext_iff, AddMonoidHom.comp_apply, AddMonoidHom.zero_apply]

end AddMonoidHom
