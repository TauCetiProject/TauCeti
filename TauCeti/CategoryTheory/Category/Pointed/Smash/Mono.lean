/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Category.Pointed.Smash.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import TauCeti.CategoryTheory.Monoidal.Mono

/-!
# Monomorphisms and the smash product of pointed types

Smashing two injective based maps gives an injective map: away from the basepoint a smash
class remembers both coordinates, and an injective based map reflects the basepoint.
Consequently smashing with a fixed pointed type preserves monomorphisms. This is the
set-level input for preservation of simplicial cofibrations by degreewise smash products.
-/

public section

universe u

open CategoryTheory MonoidalCategory

namespace Pointed

variable {X X' Y Y' : Pointed.{u}}

namespace smash

/-- The smash of two injective based maps is injective. -/
theorem map_injective (f : X ⟶ X') (g : Y ⟶ Y')
    (hf : Function.Injective f.toFun) (hg : Function.Injective g.toFun) :
    Function.Injective (map f g).toFun := by
  intro a b
  induction a using ind with | h x y =>
    induction b using ind with | h x' y' =>
      simp only [map_mk, mk_eq_mk_iff]
      have hfp : ∀ x, f.toFun x = X'.point ↔ x = X.point :=
        fun x ↦ by rw [← f.map_point, hf.eq_iff]
      have hgp : ∀ y, g.toFun y = Y'.point ↔ y = Y.point :=
        fun y ↦ by rw [← g.map_point, hg.eq_iff]
      simp only [hf.eq_iff, hg.eq_iff, hfp, hgp]
      exact id

end smash

/-- Smash products of monomorphisms of pointed types are monomorphisms. -/
instance mono_tensorHom (f : X ⟶ X') (g : Y ⟶ Y') [Mono f] [Mono g] :
    Mono (f ⊗ₘ g) := by
  -- The forgetful functor is a right adjoint, so it preserves the monos whose
  -- underlying injectivity is used below.
  let := typeToPointedForgetAdjunction.{u}.isRightAdjoint
  exact ConcreteCategory.mono_of_injective _ (smash.map_injective f g
    (injective_of_mono ((forget Pointed).map f))
    (injective_of_mono ((forget Pointed).map g)))

/-- Smashing on the left with a pointed type preserves monomorphisms. -/
instance (X : Pointed.{u}) : (tensorLeft X).PreservesMonomorphisms :=
  TauCeti.tensorLeft_preservesMonomorphisms (fun f g ↦ mono_tensorHom f g) X

/-- Smashing on the right with a pointed type preserves monomorphisms. -/
instance (X : Pointed.{u}) : (tensorRight X).PreservesMonomorphisms :=
  TauCeti.tensorRight_preservesMonomorphisms (fun f g ↦ mono_tensorHom f g) X

end Pointed
