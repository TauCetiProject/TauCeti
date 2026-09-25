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
# Dropping a trivial factor from a topological product

When `T` has a unique element, `Multiplicative (M × T)` is topologically isomorphic to
`Multiplicative M`. This is `AddEquiv.prodUnique` between the multiplicative type tags, upgraded
to a `ContinuousMulEquiv`; it collapses a product decomposition of a topological group whose
second factor turns out to be trivial.

## Main definitions

* `TauCeti.ContinuousMulEquiv.multiplicativeProdUnique`: the topological isomorphism
  `Multiplicative (M × T) ≃ₜ* Multiplicative M` for `[Unique T]`, with its evaluation lemmas
  `multiplicativeProdUnique_apply` and `multiplicativeProdUnique_symm_apply`.
-/

public section

namespace TauCeti

open Multiplicative

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

end TauCeti
