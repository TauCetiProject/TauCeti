/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Monoidal.Types.Basic

/-!
# The forgetful functor from modules to types is lax monoidal

For a commutative ring `R`, the forgetful functor `forget (ModuleCat R) : ModuleCat R ⥤ Type u`
is lax monoidal, from the tensor product of modules to the cartesian product of types: the unit
picks out `1 : R`, and the tensorator sends a pair `(m, n)` to the pure tensor `m ⊗ₜ n`.

Postcomposing with this functor turns a category enriched in `R`-modules, or in simplicial
`R`-modules, into one enriched in types, or in simplicial sets (via
`CategoryTheory.TransportEnrichment`); this is how the simplicial enrichment of a differential
graded category forgets the linear structure of its mapping simplicial modules.  Mathlib has the
corresponding instances for groups (`GrpCat.μ_forget_apply` and its variants), where the
tensor product is cartesian.

## Main definitions and results

* `ModuleCat.forgetLaxMonoidal`: the lax monoidal structure on `forget (ModuleCat R)`.
* `ModuleCat.ε_forget_apply` and `ModuleCat.μ_forget_apply`: its unit and tensorator on elements.
-/

public section

open CategoryTheory MonoidalCategory

universe u

namespace ModuleCat

variable (R : Type u) [CommRing R]

/-- The forgetful functor from `R`-modules to types is lax monoidal: the unit is `1 : R` and the
tensorator sends `(m, n)` to `m ⊗ₜ n` (`ModuleCat.ε_forget_apply`, `ModuleCat.μ_forget_apply`). -/
@[no_expose]
noncomputable instance forgetLaxMonoidal : (forget (ModuleCat.{u} R)).LaxMonoidal where
  ε := TypeCat.ofHom fun _ ↦ (1 : R)
  μ M N := TypeCat.ofHom fun p ↦ TensorProduct.tmul R (M := M) (N := N) p.1 p.2
  μ_natural_left _ _ := by ext; rfl
  μ_natural_right _ _ := by ext; rfl
  associativity _ _ _ := by ext; rfl
  left_unitality _ := by ext x; exact (one_smul R x.2).symm
  right_unitality _ := by ext x; exact (one_smul R x.1).symm

variable {R}

/-- The unit of the lax monoidal forgetful functor picks out `1 : R`. -/
@[simp]
lemma ε_forget_apply (x : 𝟙_ (Type u)) :
    Functor.LaxMonoidal.ε (forget (ModuleCat.{u} R)) x = (1 : R) :=
  (rfl)

/-- The tensorator of the lax monoidal forgetful functor sends a pair to its pure tensor. -/
@[simp]
lemma μ_forget_apply {M N : ModuleCat.{u} R} (m : M) (n : N) :
    Functor.LaxMonoidal.μ (forget (ModuleCat.{u} R)) M N (m, n) = m ⊗ₜ[R] n :=
  (rfl)

end ModuleCat
