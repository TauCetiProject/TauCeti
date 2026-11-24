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
`MulEquiv.piMultiplicative` and `Equiv.prodUnique` between the multiplicative type tags,
upgraded to `ContinuousMulEquiv`s: the first two transport properties of topological groups, such
as being pro-`p` or amenable, between the two shapes of a product, and the last collapses a
product decomposition of a topological group whose second factor turns out to be trivial. Likewise,
`ContinuousMulEquiv.multiplicativeAdditive` upgrades the round-trip equivalence
`MulEquiv.multiplicativeAdditive` (`Multiplicative (Additive M) ≃ₜ* M`), and the universe lift
`ULift M` of a topological monoid is topologically isomorphic to `M`, which is `MulEquiv.ulift`
upgraded to a `ContinuousMulEquiv`; it lets a universal property whose target must live in a fixed
universe be applied to a group in a smaller one.

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
* `TauCeti.ContinuousMulEquiv.multiplicativeAdditive`: the round-trip topological isomorphism
  `Multiplicative (Additive M) ≃ₜ* M`, with its evaluation lemmas `multiplicativeAdditive_apply`
  and `multiplicativeAdditive_symm_apply`.
* `TauCeti.ContinuousMulEquiv.ulift`: the topological isomorphism `ULift M ≃ₜ* M`, with its
  evaluation lemmas `ulift_apply` and `ulift_symm_apply`.
* `ContinuousMulEquiv.prodCongr`, `ContinuousAddEquiv.prodCongr`: product of two topological
  monoid isomorphisms, upgrading `MulEquiv.prodCongr` and `AddEquiv.prodCongr`.
-/

public section

namespace TauCeti

open Additive Multiplicative

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

variable (M T : Type*) [Add M] [Add T] [TopologicalSpace M] [TopologicalSpace T] [Unique T]

/-- Dropping a trivial factor: when `T` has a unique element, `Multiplicative (M × T)` is
topologically isomorphic to `Multiplicative M`. This is `Equiv.prodUnique` between the
multiplicative type tags, as a `ContinuousMulEquiv`; unlike `AddEquiv.prodUnique` it needs no
zero on `M` or `T`. -/
def ContinuousMulEquiv.multiplicativeProdUnique : Multiplicative (M × T) ≃ₜ* Multiplicative M where
  toEquiv := toAdd.trans ((Equiv.prodUnique M T).trans ofAdd)
  map_mul' _ _ := rfl
  continuous_toFun := continuous_ofAdd.comp (continuous_fst.comp continuous_toAdd)
  continuous_invFun := continuous_ofAdd.comp (continuous_toAdd.prodMk continuous_const)

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

section RoundTrip

/-- `Multiplicative (Additive M)` is topologically isomorphic to `M`. This is
`MulEquiv.multiplicativeAdditive` as a `ContinuousMulEquiv`. -/
def ContinuousMulEquiv.multiplicativeAdditive (M : Type*) [Mul M] [TopologicalSpace M] :
    Multiplicative (Additive M) ≃ₜ* M where
  toMulEquiv := MulEquiv.multiplicativeAdditive M
  continuous_toFun := continuous_toMul.comp continuous_toAdd
  continuous_invFun := continuous_ofAdd.comp continuous_ofMul

/-- Forward evaluation of `ContinuousMulEquiv.multiplicativeAdditive`. -/
@[simp]
theorem ContinuousMulEquiv.multiplicativeAdditive_apply {M : Type*} [Mul M] [TopologicalSpace M]
    (x : Multiplicative (Additive M)) :
    ContinuousMulEquiv.multiplicativeAdditive M x = x.toAdd.toMul :=
  (rfl)

/-- Inverse evaluation of `ContinuousMulEquiv.multiplicativeAdditive`. -/
@[simp]
theorem ContinuousMulEquiv.multiplicativeAdditive_symm_apply {M : Type*} [Mul M]
    [TopologicalSpace M] (x : M) :
    (ContinuousMulEquiv.multiplicativeAdditive M).symm x = ofAdd (ofMul x) :=
  (rfl)

end RoundTrip

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

namespace ContinuousMulEquiv

section ProdCongr

variable {M₁ M₂ M₃ M₄ : Type*} [TopologicalSpace M₁] [TopologicalSpace M₂]
  [TopologicalSpace M₃] [TopologicalSpace M₄]

section Mul

variable [Mul M₁] [Mul M₂] [Mul M₃] [Mul M₄] (e₁ : M₁ ≃ₜ* M₂) (e₂ : M₃ ≃ₜ* M₄)

/-- Product of two continuous multiplicative equivalences, upgrading `MulEquiv.prodCongr`. -/
@[to_additive prodCongr /-- Product of two continuous additive equivalences, upgrading
`AddEquiv.prodCongr`. -/]
def prodCongr : M₁ × M₃ ≃ₜ* M₂ × M₄ where
  toEquiv := e₁.toEquiv.prodCongr e₂.toEquiv
  map_mul' _ _ := Prod.ext (map_mul e₁ _ _) (map_mul e₂ _ _)
  continuous_toFun := e₁.continuous.prodMap e₂.continuous
  continuous_invFun := e₁.symm.continuous.prodMap e₂.symm.continuous

/-- Evaluating `ContinuousMulEquiv.prodCongr` applies the two equivalences coordinatewise. -/
@[to_additive (attr := simp) prodCongr_apply /-- Evaluating `ContinuousAddEquiv.prodCongr` applies
the two equivalences coordinatewise. -/]
theorem prodCongr_apply (p : M₁ × M₃) : e₁.prodCongr e₂ p = (e₁ p.1, e₂ p.2) := (rfl)

/-- The inverse of `ContinuousMulEquiv.prodCongr` is the product of the inverses. -/
@[to_additive (attr := simp) prodCongr_symm /-- The inverse of `ContinuousAddEquiv.prodCongr` is
the product of the inverses. -/]
theorem prodCongr_symm : (e₁.prodCongr e₂).symm = e₁.symm.prodCongr e₂.symm := (rfl)

end Mul

/-- The underlying `MulEquiv` of `ContinuousMulEquiv.prodCongr` is `MulEquiv.prodCongr`. -/
@[to_additive (attr := simp) toAddEquiv_prodCongr /-- The underlying `AddEquiv` of
`ContinuousAddEquiv.prodCongr` is `AddEquiv.prodCongr`. -/]
theorem toMulEquiv_prodCongr [MulOneClass M₁] [MulOneClass M₂] [MulOneClass M₃] [MulOneClass M₄]
    (e₁ : M₁ ≃ₜ* M₂) (e₂ : M₃ ≃ₜ* M₄) :
    (e₁.prodCongr e₂ : M₁ × M₃ ≃* M₂ × M₄) = (e₁ : M₁ ≃* M₂).prodCongr (e₂ : M₃ ≃* M₄) := (rfl)

end ProdCongr

end ContinuousMulEquiv
