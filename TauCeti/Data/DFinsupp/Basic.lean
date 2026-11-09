/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.DFinsupp.Defs

/-!
# Dependent finitely supported functions

Construct a `DFinsupp` from a dependent function with finite support: the dependent analogue of
`Finsupp.ofSupportFinite`.
-/

public section

namespace DFinsupp

variable {ι : Type*} {β : ι → Type*} [∀ i, Zero (β i)]

/-- The dependent finitely supported function induced by a dependent function `f` whose support
`{i | f i ≠ 0}` is finite. This is the dependent analogue of `Finsupp.ofSupportFinite`. -/
noncomputable def ofSupportFinite (f : ∀ i, β i) (hf : {i | f i ≠ 0}.Finite) : Π₀ i, β i :=
  ⟨f, Trunc.mk ⟨hf.toFinset.val, fun _ ↦ or_iff_not_imp_right.2 hf.mem_toFinset.2⟩⟩

/-- Evaluating `DFinsupp.ofSupportFinite f hf` returns the original function `f`. -/
@[simp]
lemma ofSupportFinite_apply (f : ∀ i, β i) (hf : {i | f i ≠ 0}.Finite) (i : ι) :
    ofSupportFinite f hf i = f i :=
  (rfl)

end DFinsupp
