/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import TauCeti.Algebra.Module.Equiv.SpanSingleton

/-!
# Elements of modules as morphisms out of the base ring

An element `m` of an `R`-module `M` is the morphism `R ⟶ M`, `a ↦ a • m`, of the category of
`R`-modules (`LinearMap.toSpanSingleton`). Following it by a morphism `f` gives the morphism of
`f m` (`ModuleCat.ofHom_toSpanSingleton_comp`), the categorical form of
`LinearMap.comp_toSpanSingleton`. An isomorphism of modules carries generators to generators
(`ModuleCat.span_singleton_apply_eq_top_iff`), the categorical form of
`LinearEquiv.span_singleton_apply_eq_top_iff`.

## Main results

* `ModuleCat.ofHom_toSpanSingleton_comp`: `(a ↦ a • m) ≫ f` is `a ↦ a • f m`.
* `ModuleCat.span_singleton_apply_eq_top_iff`: `f x` spans the codomain of an isomorphism `f` if
  and only if `x` spans its domain.
-/

public section

open CategoryTheory

universe v u

namespace ModuleCat

/-- Following the morphism `R ⟶ M`, `a ↦ a • m`, by a morphism `f` gives `a ↦ a • f m`. -/
theorem ofHom_toSpanSingleton_comp {R : Type u} [Ring R] {M N : ModuleCat.{u} R} (m : M)
    (f : M ⟶ N) :
    ofHom (LinearMap.toSpanSingleton R M m) ≫ f = ofHom (LinearMap.toSpanSingleton R N (f m)) :=
  hom_ext (LinearMap.comp_toSpanSingleton f.hom m)

/-- An isomorphism of modules carries generators to generators: `f x` spans the codomain if and
only if `x` spans the domain. -/
theorem span_singleton_apply_eq_top_iff {R : Type u} [Ring R] {M N : ModuleCat.{v} R}
    (f : M ⟶ N) [IsIso f] {x : M} :
    Submodule.span R {f x} = ⊤ ↔ Submodule.span R {x} = ⊤ :=
  (asIso f).toLinearEquiv.span_singleton_apply_eq_top_iff

end ModuleCat
