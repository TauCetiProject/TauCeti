/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.CoprodI

/-!
# Isomorphisms of free products of monoids

A family of isomorphisms `M i ≃* N i` induces an isomorphism `CoprodI M ≃* CoprodI N` of the free
products, acting on each factor by the given isomorphism.  This is the indexed counterpart of
Mathlib's `MulEquiv.coprodCongr` for the free product of two monoids.  It is used to rewrite a
free product of fundamental groups one factor at a time, for instance to recognise the
fundamental group of a wedge of circles as a free group.

## Main declarations

* `MulEquiv.coprodICongr`: the isomorphism of free products induced by a family of isomorphisms.
-/

public section

namespace TauCeti

open Monoid

variable {ι : Type*} {M N : ι → Type*} [∀ i, Monoid (M i)] [∀ i, Monoid (N i)]

/-- A family of isomorphisms of monoids `M i ≃* N i` induces an isomorphism of their free
products, acting on the `i`-th factor by the `i`-th isomorphism. -/
def _root_.MulEquiv.coprodICongr (e : ∀ i, M i ≃* N i) : CoprodI M ≃* CoprodI N :=
  MonoidHom.toMulEquiv (CoprodI.lift fun i => CoprodI.of.comp (e i).toMonoidHom)
    (CoprodI.lift fun i => CoprodI.of.comp (e i).symm.toMonoidHom)
    (CoprodI.ext_hom _ _ fun i => MonoidHom.ext fun m => by simp)
    (CoprodI.ext_hom _ _ fun i => MonoidHom.ext fun m => by simp)

@[simp]
theorem _root_.MulEquiv.coprodICongr_apply_of (e : ∀ i, M i ≃* N i) {i : ι} (m : M i) :
    MulEquiv.coprodICongr e (CoprodI.of m) = CoprodI.of (e i m) := by
  simp [MulEquiv.coprodICongr]

@[simp]
theorem _root_.MulEquiv.coprodICongr_symm (e : ∀ i, M i ≃* N i) :
    (MulEquiv.coprodICongr e).symm = MulEquiv.coprodICongr fun i => (e i).symm :=
  (rfl)

end TauCeti
