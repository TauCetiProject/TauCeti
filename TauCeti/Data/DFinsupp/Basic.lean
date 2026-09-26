/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.DFinsupp.Module

/-!
# Dependent finitely supported functions

Construct a `DFinsupp` from a dependent function with finite support.
-/

public section

namespace TauCeti

/-- A dependent function with finite support, regarded as a dependent finitely supported
function. -/
noncomputable def dfinsuppOfFiniteSupport {I : Type*} {β : I → Type*} [∀ i, Zero (β i)]
    (f : ∀ i, β i) (hf : {i | f i ≠ 0}.Finite) : Π₀ i, β i := by
  classical
  exact DFinsupp.mk hf.toFinset fun i ↦ f i

/-- Evaluating `dfinsuppOfFiniteSupport f hf` returns the original function `f`. -/
@[simp]
lemma dfinsuppOfFiniteSupport_apply {I : Type*} {β : I → Type*} [∀ i, Zero (β i)]
    (f : ∀ i, β i) (hf : {i | f i ≠ 0}.Finite) (i : I) :
    dfinsuppOfFiniteSupport f hf i = f i := by
  classical
  simp only [dfinsuppOfFiniteSupport, DFinsupp.mk_apply]
  split_ifs with hi
  · rfl
  · have : f i = 0 := not_ne_iff.mp (by
      simpa only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hi)
    exact this.symm

end TauCeti
