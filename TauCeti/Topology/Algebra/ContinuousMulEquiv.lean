/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Constructions
public import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# Topological isomorphisms between multiplicative type tags of products

The multiplicative type tag of a product of additive topological groups is topologically
isomorphic to the product of the multiplicative type tags, and when `T` has a unique element,
`Multiplicative (M × T)` is topologically isomorphic to `Multiplicative M`. These are
`MulEquiv.prodMultiplicative` and `AddEquiv.prodUnique` between the multiplicative type tags,
upgraded to `ContinuousMulEquiv`s: the first transports properties of topological groups, such as
being pro-`p`, between the two shapes of a product, and the second collapses a product
decomposition of a topological group whose second factor turns out to be trivial.

## Main definitions

* `TauCeti.ContinuousMulEquiv.prodMultiplicative`: the topological isomorphism
  `Multiplicative (M × N) ≃ₜ* Multiplicative M × Multiplicative N`, with its evaluation lemmas
  `prodMultiplicative_apply` and `prodMultiplicative_symm_apply`.
* `TauCeti.ContinuousMulEquiv.multiplicativeProdUnique`: the topological isomorphism
  `Multiplicative (M × T) ≃ₜ* Multiplicative M` for `[Unique T]`, with its evaluation lemmas
  `multiplicativeProdUnique_apply` and `multiplicativeProdUnique_symm_apply`.
-/

public section

namespace TauCeti

open Multiplicative

section Prod

variable (M N : Type*) [Add M] [Add N] [TopologicalSpace M] [TopologicalSpace N]

/-- The multiplicative type tag of a product is the product of the multiplicative type tags, as a
topological isomorphism. This is `MulEquiv.prodMultiplicative` as a `ContinuousMulEquiv`. -/
def ContinuousMulEquiv.prodMultiplicative :
    Multiplicative (M × N) ≃ₜ* Multiplicative M × Multiplicative N where
  toMulEquiv := MulEquiv.prodMultiplicative M N
  continuous_toFun :=
    (continuous_ofAdd.comp (continuous_fst.comp continuous_toAdd)).prodMk
      (continuous_ofAdd.comp (continuous_snd.comp continuous_toAdd))
  continuous_invFun :=
    continuous_ofAdd.comp
      ((continuous_toAdd.comp continuous_fst).prodMk (continuous_toAdd.comp continuous_snd))

@[simp]
theorem ContinuousMulEquiv.prodMultiplicative_apply (x : Multiplicative (M × N)) :
    ContinuousMulEquiv.prodMultiplicative M N x = (ofAdd x.toAdd.1, ofAdd x.toAdd.2) :=
  (rfl)

@[simp]
theorem ContinuousMulEquiv.prodMultiplicative_symm_apply (x : Multiplicative M × Multiplicative N) :
    (ContinuousMulEquiv.prodMultiplicative M N).symm x = ofAdd (x.1.toAdd, x.2.toAdd) :=
  (rfl)

end Prod

section Unique

variable (M T : Type*) [AddZeroClass M] [AddZeroClass T] [TopologicalSpace M] [TopologicalSpace T]
  [Unique T]

/-- Dropping a trivial factor: when `T` has a unique element, `Multiplicative (M × T)` is
topologically isomorphic to `Multiplicative M`. This is `AddEquiv.prodUnique` as a
`ContinuousMulEquiv` between the multiplicative type tags. -/
def ContinuousMulEquiv.multiplicativeProdUnique : Multiplicative (M × T) ≃ₜ* Multiplicative M where
  toMulEquiv := AddEquiv.toMultiplicative AddEquiv.prodUnique
  continuous_toFun := (continuous_ofAdd.comp (continuous_fst.comp continuous_toAdd)).congr
    fun x ↦ by simp [AddEquiv.prodUnique_apply]
  continuous_invFun := (continuous_ofAdd.comp (continuous_toAdd.prodMk
    (continuous_const (y := (default : T))))).congr fun v ↦ by simp [AddEquiv.prodUnique_symm_apply]

variable {M T}

@[simp]
theorem ContinuousMulEquiv.multiplicativeProdUnique_apply (x : Multiplicative (M × T)) :
    ContinuousMulEquiv.multiplicativeProdUnique M T x = ofAdd x.toAdd.1 :=
  (rfl)

@[simp]
theorem ContinuousMulEquiv.multiplicativeProdUnique_symm_apply (v : Multiplicative M) :
    (ContinuousMulEquiv.multiplicativeProdUnique M T).symm v = ofAdd (v.toAdd, default) :=
  (rfl)

end Unique

end TauCeti
