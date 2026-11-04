/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Additive homomorphisms as morphisms of integer modules

Bundling additive homomorphisms as integer-linear categorical morphisms preserves and
reflects vanishing of their composite. This transports zero-composite laws between
additive groups and `ModuleCat ℤ`.

A module over a ring `S` with its scalars restricted along `ℤ → S` is the same integer module as
its underlying abelian group with the canonical action of `ℤ`
(`ModuleCat.restrictScalarsIntCastIso`). The two integer actions agree only propositionally, so
this isomorphism, rather than an equality of objects, transports statements between them.
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

namespace ModuleCat

universe v w

variable {S : Type w} [Ring S] (M : ModuleCat.{v} S)

/-- A module over `S` with its scalars restricted along `ℤ → S` is its underlying abelian group with
the canonical action of `ℤ`. Both maps are the identity of the underlying abelian group. -/
noncomputable def restrictScalarsIntCastIso :
    (restrictScalars (Int.castRingHom S)).obj M ≅ ModuleCat.of ℤ M where
  -- the integers act on the restriction through `ℤ → S`, by definition of restriction of scalars
  hom := ofHom (X := (restrictScalars (Int.castRingHom S)).obj M)
    { toFun := id
      map_add' _ _ := rfl
      map_smul' n x := Int.cast_smul_eq_zsmul S n x }
  inv := ofHom (Y := (restrictScalars (Int.castRingHom S)).obj M)
    { toFun := id
      map_add' _ _ := rfl
      map_smul' n x := (Int.cast_smul_eq_zsmul S n x).symm }

@[simp]
lemma restrictScalarsIntCastIso_hom_apply (x : (restrictScalars (Int.castRingHom S)).obj M) :
    (restrictScalarsIntCastIso M).hom x = (x : M) :=
  (rfl)

@[simp]
lemma restrictScalarsIntCastIso_inv_apply (x : M) :
    (restrictScalarsIntCastIso M).inv x = x :=
  (rfl)

end ModuleCat
