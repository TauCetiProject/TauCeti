/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.Order.SupIndep

import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Linear independence under injective reindexing and along independent submodules

A family `v` is linearly independent on the image `f '' s` of a set under a map injective on `s`
exactly when `v ∘ f` is linearly independent on `s`. This is the linear counterpart of Mathlib's
`affineIndepOn_image_iff`, combining `LinearIndepOn.comp_of_image` and
`LinearIndepOn.image_of_comp`.

Over a ring, linearly independent families `f j` lying inside an `iSupIndep` family of submodules
`W j` assemble into a single linearly independent sigma-indexed family.

## Main results

* `TauCeti.linearIndepOn_image_iff`: linear independence on `f '' s` versus of `v ∘ f` on `s`.
* `TauCeti.linearIndependent_sigma_of_iSupIndep`: gluing linearly independent families along an
  independent family of submodules.
-/

public section

namespace TauCeti

section Semiring

variable {ι ι' R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- A family `v` is linearly independent on `f '' s` exactly when `v ∘ f` is linearly independent
on `s`, for `f` injective on `s`. -/
theorem linearIndepOn_image_iff {s : Set ι} {f : ι → ι'} (v : ι' → M) (hf : Set.InjOn f s) :
    LinearIndepOn R v (f '' s) ↔ LinearIndepOn R (v ∘ f) s :=
  ⟨fun h ↦ h.comp_of_image hf, fun h ↦ h.image_of_comp f v⟩

end Semiring

/-- Gluing linearly independent families across an independent family of submodules: if each family
`f j` is linearly independent and lands in `W j` for an `iSupIndep` family `W`, then the combined
sigma-indexed family is linearly independent. -/
theorem linearIndependent_sigma_of_iSupIndep {R M η : Type*} [Ring R] [AddCommGroup M]
    [Module R M] {ι : η → Type*} {f : ∀ j : η, ι j → M} {W : η → Submodule R M}
    (hli : ∀ j, LinearIndependent R (f j)) (hW : iSupIndep W) (hfW : ∀ j k, f j k ∈ W j) :
    LinearIndependent R (fun jk : Σ j, ι j ↦ f jk.1 jk.2) := by
  refine linearIndependent_iUnion_finite hli fun i t _ hit ↦
    (hW.disjoint_biSup hit).mono ?_ (iSup₂_mono fun j _ ↦ ?_)
  · exact Submodule.span_le.mpr (Set.range_subset_iff.mpr (hfW i))
  · exact Submodule.span_le.mpr (Set.range_subset_iff.mpr (hfW j))

end TauCeti
