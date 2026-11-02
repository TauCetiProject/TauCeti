/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Pointed.Smash.Basic
public import TauCeti.CategoryTheory.Category.Pointed.Smash.Mono
public import TauCeti.CategoryTheory.Category.Pointed.Limits

/-!
# Smash products preserve monomorphisms of pointed simplicial sets

The smash product preserves monomorphisms in both variables. In each simplicial degree this
is the corresponding fact for pointed types: an injective based map reflects the basepoint,
so collapsing the wedge does not introduce identifications outside it. Thus simplicial
cofibrations, whose underlying maps are monomorphisms, remain cofibrations after smashing
with any pointed simplicial set. No fibrancy or finiteness assumptions are needed.
-/

public section

universe u

open CategoryTheory MonoidalCategory

namespace TauCeti.PointedSSet

variable {X X' Y Y' : PointedSSet.{u}}

/-- The smash of two monomorphisms of pointed simplicial sets is a monomorphism. -/
instance mono_tensorHom (f : X ⟶ X') (g : Y ⟶ Y') [Mono f] [Mono g] :
    Mono (f ⊗ₘ g) := by
  let F := simplicialPointedEquivalence.{u}.functor
  have : Mono (F.map f) := F.map_mono f
  have : Mono (F.map g) := F.map_mono g
  have : Mono (F.map f ⊗ₘ F.map g) := by
    apply (NatTrans.mono_iff_mono_app _).2
    intro n
    rw [Monoidal.tensorHom_app]
    exact Pointed.mono_tensorHom _ _
  apply F.mono_of_mono_map
  rw [Functor.Monoidal.map_tensor]
  infer_instance

/-- Smashing on the left with a pointed simplicial set preserves monomorphisms. -/
instance (X : PointedSSet.{u}) : (tensorLeft X).PreservesMonomorphisms :=
  TauCeti.tensorLeft_preservesMonomorphisms (fun f g ↦ mono_tensorHom f g) X

/-- Smashing on the right with a pointed simplicial set preserves monomorphisms. -/
instance (X : PointedSSet.{u}) : (tensorRight X).PreservesMonomorphisms :=
  TauCeti.tensorRight_preservesMonomorphisms (fun f g ↦ mono_tensorHom f g) X

end TauCeti.PointedSSet
