/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.CartanMap.Basic
public import TauCeti.RepresentationTheory.AsModule
public import TauCeti.RepresentationTheory.BaseChange

/-!
# The reduction class of a representation

Let `G` be a monoid, `O` a commutative ring and `k` a commutative `O`-algebra, typically a field.
A representation `ρ` of `G` on an `O`-module `W` has a **reduction** `k ⊗_O W`, with `G` acting on
the second factor (`Representation.baseChange`). When it is finitely generated over `k`, for
instance because `W` is finitely generated over `O`, it has a class

`TauCeti.reductionK0 k ρ = [k ⊗_O W] ∈ G₀(k[G])`

in the exact Grothendieck group of finitely generated `k[G]`-modules. Typical cases are `O = ℤ`,
where `W` is an abelian group, and the residue field `k` of a discrete valuation ring `O`.

## Main definitions

* `TauCeti.reductionK0`: the class in `G₀(k[G])` of the reduction `k ⊗_O W`.

## Main results

* `TauCeti.reductionK0_congr`: equivalent representations have equal reduction classes.
* `TauCeti.reductionK0_eq_zero_of_subsingleton`: the reduction class of a zero module is zero.
-/

public section

namespace TauCeti

open TensorProduct
open scoped MonoidAlgebra

universe u

variable (k : Type u) [CommRing k] {G : Type u} [Monoid G] {O : Type*} [CommRing O] [Algebra O k]

/-- The module of a reduction `k ⊗_O W` that is finitely generated over `k`, for instance because
`W` is finitely generated over `O`, is finitely generated over `k[G]`. -/
instance instModuleFiniteAsModuleBaseChange {W : Type u} [AddCommGroup W] [Module O W]
    [Module.Finite k (k ⊗[O] W)] (ρ : Representation O G W) :
    Module.Finite k[G] (Representation.baseChange k ρ).asModule :=
  Module.Finite.of_restrictScalars_finite k k[G] _

variable {W : Type u} [AddCommGroup W] [Module O W] [Module.Finite k (k ⊗[O] W)]

/-- **The reduction class** of a representation `ρ` of `G` on an `O`-module `W` whose reduction
`k ⊗_O W` is finitely generated over `k`, for instance because `W` is finitely generated over `O`:
the class in `G₀(k[G])` of its scalar extension `k ⊗_O W`, with `G` acting on the second factor.
For `O = ℤ`, `W` is an abelian group. -/
noncomputable def reductionK0 (ρ : Representation O G W) :
    ExactK0 (finiteModulesExactStructure k[G]) :=
  ExactK0.of (FGModuleCat.of k[G] (Representation.baseChange k ρ).asModule)

/-- The reduction class is the class of the `k[G]`-module of the base-changed representation. -/
theorem reductionK0_def (ρ : Representation O G W) :
    reductionK0 k ρ = ExactK0.of (FGModuleCat.of k[G] (Representation.baseChange k ρ).asModule) :=
  (rfl)

/-- Equivalent scalar extensions have equal reduction classes. -/
theorem reductionK0_congr_baseChange {W' : Type u} [AddCommGroup W'] [Module O W']
    [Module.Finite k (k ⊗[O] W')] {ρ : Representation O G W} {σ : Representation O G W'}
    (e : (Representation.baseChange k ρ).Equiv (Representation.baseChange k σ)) :
    reductionK0 k ρ = reductionK0 k σ := by
  rw [reductionK0_def, reductionK0_def]
  exact ExactK0.of_congr (Representation.asModuleLinearEquivOfEquiv e).toFGModuleCatIso

/-- Equivalent representations have equal reduction classes. -/
theorem reductionK0_congr {W' : Type u} [AddCommGroup W'] [Module O W']
    [Module.Finite k (k ⊗[O] W')]
    {ρ : Representation O G W} {σ : Representation O G W'} (e : ρ.Equiv σ) :
    reductionK0 k ρ = reductionK0 k σ :=
  reductionK0_congr_baseChange k (e.baseChange k)

/-- The reduction class of a zero module is zero. -/
@[simp]
theorem reductionK0_eq_zero_of_subsingleton [Subsingleton W] (ρ : Representation O G W) :
    reductionK0 k ρ = 0 := by
  have : Subsingleton (Representation.baseChange k ρ).asModule :=
    (Representation.baseChange k ρ).asModuleEquiv.injective.subsingleton
  exact ExactK0.of_eq_zero_of_isZero <| CategoryTheory.Limits.IsZero.of_full_of_faithful_of_isZero
    (ModuleCat.isFG k[G]).ι _
      (ModuleCat.isZero_of_subsingleton
        (ModuleCat.of k[G] (Representation.baseChange k ρ).asModule))

end TauCeti
