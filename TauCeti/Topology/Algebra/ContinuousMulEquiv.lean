/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Constructions
public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.Algebra.Group.ULift

/-!
# Topological isomorphisms between type tags

The multiplicative type tag of a product of additive topological groups is topologically
isomorphic to the product of the multiplicative type tags, both for binary products and for
dependent products, and when `T` has a unique element, `Multiplicative (M × T)` is topologically
isomorphic to `Multiplicative M`. These are `MulEquiv.prodMultiplicative`,
`MulEquiv.piMultiplicative` and `AddEquiv.prodUnique` between the multiplicative type tags,
upgraded to `ContinuousMulEquiv`s: the first two transport properties of topological groups, such
as being pro-`p`, between the two shapes of a product, and the last collapses a product
decomposition of a topological group whose second factor turns out to be trivial. The universe
lift `ULift M` of a topological monoid is topologically isomorphic to `M`, which is
`MulEquiv.ulift` upgraded to a `ContinuousMulEquiv`; it lets a universal property whose target must
live in a fixed universe be applied to a group in a smaller one.

## Main definitions

* `TauCeti.ContinuousMulEquiv.prodMultiplicative`: the topological isomorphism
  `Multiplicative (M × N) ≃ₜ* Multiplicative M × Multiplicative N`, with its evaluation lemmas
  `prodMultiplicative_apply` and `prodMultiplicative_symm_apply`.
* `TauCeti.ContinuousMulEquiv.piMultiplicative`: the topological isomorphism
  `Multiplicative (∀ i, K i) ≃ₜ* ∀ i, Multiplicative (K i)`, with its evaluation lemmas
  `piMultiplicative_apply` and `piMultiplicative_symm_apply`.
* `TauCeti.ContinuousMulEquiv.multiplicativeProdUnique`: the topological isomorphism
  `Multiplicative (M × T) ≃ₜ* Multiplicative M` for `[Unique T]`, with its evaluation lemmas
  `multiplicativeProdUnique_apply` and `multiplicativeProdUnique_symm_apply`.
* `ContinuousAddEquiv.toMultiplicative`: a topological isomorphism `M ≃ₜ+ N` of additive groups
  as a topological isomorphism `Multiplicative M ≃ₜ* Multiplicative N`, with its evaluation
  lemmas `toMultiplicative_apply` and `toMultiplicative_symm_apply`.
* `TauCeti.ContinuousMulEquiv.ulift`: the topological isomorphism `ULift M ≃ₜ* M`, with its
  evaluation lemmas `ulift_apply` and `ulift_symm_apply`.
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

section Pi

variable {ι : Type*} (K : ι → Type*) [∀ i, Add (K i)] [∀ i, TopologicalSpace (K i)]

/-- The multiplicative type tag of a dependent product is the product of the multiplicative type
tags, as a topological isomorphism. This is `MulEquiv.piMultiplicative` as a
`ContinuousMulEquiv`. -/
def ContinuousMulEquiv.piMultiplicative :
    Multiplicative (∀ i, K i) ≃ₜ* ∀ i, Multiplicative (K i) where
  toMulEquiv := MulEquiv.piMultiplicative K
  continuous_toFun :=
    continuous_pi fun i ↦ continuous_ofAdd.comp ((continuous_apply i).comp continuous_toAdd)
  continuous_invFun :=
    continuous_ofAdd.comp (continuous_pi fun i ↦ continuous_toAdd.comp (continuous_apply i))

@[simp]
theorem ContinuousMulEquiv.piMultiplicative_apply (x : Multiplicative (∀ i, K i)) (i : ι) :
    ContinuousMulEquiv.piMultiplicative K x i = ofAdd (x.toAdd i) :=
  (rfl)

@[simp]
theorem ContinuousMulEquiv.piMultiplicative_symm_apply (x : ∀ i, Multiplicative (K i)) :
    (ContinuousMulEquiv.piMultiplicative K).symm x = ofAdd fun i ↦ (x i).toAdd :=
  (rfl)

end Pi

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

section ToMultiplicative

variable {M N : Type*} [Add M] [Add N] [TopologicalSpace M] [TopologicalSpace N]

/-- A topological isomorphism `M ≃ₜ+ N` of additive topological groups, as a topological
isomorphism `Multiplicative M ≃ₜ* Multiplicative N` of the multiplicative type tags. This is
`AddEquiv.toMultiplicative` as a `ContinuousMulEquiv`. -/
def _root_.ContinuousAddEquiv.toMultiplicative (e : M ≃ₜ+ N) :
    Multiplicative M ≃ₜ* Multiplicative N where
  toMulEquiv := AddEquiv.toMultiplicative e.toAddEquiv
  continuous_toFun := continuous_ofAdd.comp (e.continuous.comp continuous_toAdd)
  continuous_invFun := continuous_ofAdd.comp (e.symm.continuous.comp continuous_toAdd)

@[simp]
theorem _root_.ContinuousAddEquiv.toMultiplicative_apply (e : M ≃ₜ+ N) (x : Multiplicative M) :
    e.toMultiplicative x = ofAdd (e x.toAdd) :=
  (rfl)

@[simp]
theorem _root_.ContinuousAddEquiv.toMultiplicative_symm_apply (e : M ≃ₜ+ N)
    (y : Multiplicative N) : e.toMultiplicative.symm y = ofAdd (e.symm y.toAdd) :=
  (rfl)

end ToMultiplicative

section ULift

universe u v

variable {M : Type u} [Mul M] [TopologicalSpace M]

/-- The universe lift of a topological monoid is topologically isomorphic to it. This is
`MulEquiv.ulift` as a `ContinuousMulEquiv`. -/
def ContinuousMulEquiv.ulift : ULift.{v} M ≃ₜ* M where
  toMulEquiv := MulEquiv.ulift
  continuous_toFun := continuous_uliftDown
  continuous_invFun := continuous_uliftUp

@[simp]
theorem ContinuousMulEquiv.ulift_apply (x : ULift.{v} M) : ContinuousMulEquiv.ulift x = x.down :=
  (rfl)

@[simp]
theorem ContinuousMulEquiv.ulift_symm_apply (x : M) :
    (ContinuousMulEquiv.ulift : ULift.{v} M ≃ₜ* M).symm x = ULift.up.{v} x :=
  (rfl)

end ULift

end TauCeti
