/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Adjunctions

/-!
# The forgetful functor from modules to types is lax monoidal

The forgetful functor `forget (ModuleCat R) : ModuleCat R ⥤ Type u` is right adjoint to the
monoidal free module functor `ModuleCat.free R` (`ModuleCat.adj`), so it inherits a lax monoidal
structure (`CategoryTheory.Adjunction.rightAdjointLaxMonoidal`) for the tensor product of modules
and the cartesian product of types.  Its unit picks out `1 : R` and its tensorator sends a pair
`(m, n)` to the pure tensor `m ⊗ₜ n` (`ModuleCat.forget_ε_apply`, `ModuleCat.forget_μ_apply`).

Applied degreewise, it turns a simplicial module into its underlying simplicial set compatibly
with the tensor products, which is how a category enriched in simplicial modules becomes a
simplicially enriched category.
-/

public section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal

universe u

namespace ModuleCat

variable (R : Type u) [CommRing R]

/-- The lax monoidal structure of the forgetful functor from `R`-modules to types, right adjoint
to the monoidal free module functor: its unit is `1 : R` (`ModuleCat.forget_ε_apply`) and its
tensorator is `(m, n) ↦ m ⊗ₜ n` (`ModuleCat.forget_μ_apply`). -/
noncomputable instance forgetLaxMonoidal : (forget (ModuleCat.{u} R)).LaxMonoidal :=
  (adj R).rightAdjointLaxMonoidal

/-- The unit of the lax monoidal forgetful functor is `1 : R`. -/
@[simp]
lemma forget_ε_apply (x : 𝟙_ (Type u)) : ε (forget (ModuleCat.{u} R)) x = (1 : R) := by
  simp [Adjunction.rightAdjointLaxMonoidal_ε]

variable {R} in
/-- The tensorator of the lax monoidal forgetful functor sends a pair to its pure tensor. -/
@[simp]
lemma forget_μ_apply {M N : ModuleCat.{u} R} (p : (forget (ModuleCat R)).obj M ⊗
    (forget (ModuleCat R)).obj N) :
    μ (forget (ModuleCat.{u} R)) M N p = p.1 ⊗ₜ p.2 := by
  rw [Adjunction.rightAdjointLaxMonoidal_μ, ← Adjunction.homEquiv_symm_id,
    ← Adjunction.homEquiv_symm_id]
  simp

end ModuleCat
