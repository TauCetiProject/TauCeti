/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic

/-!
# The identity as a localization map

If every element of a submonoid `S` of a commutative semiring `R` acts bijectively on an
`R`-module `M`, then localizing `M` at `S` changes nothing: the identity of `M` is a localization
map at `S`.

## Main statements

* `TauCeti.isLocalizedModule_id_of_bijective_smul`: if every element of a submonoid `S` acts
  bijectively, the identity is a localization map at `S`.
-/

public section

namespace TauCeti

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- If every element of a submonoid `S` acts bijectively on `M`, the identity of `M` is a
localization map at `S`. -/
theorem isLocalizedModule_id_of_bijective_smul {S : Submonoid R}
    (h : ∀ s ∈ S, Function.Bijective fun x : M ↦ s • x) :
    IsLocalizedModule S (LinearMap.id : M →ₗ[R] M) where
  map_units s := by
    rw [Module.End.isUnit_iff, funext (Module.algebraMap_end_apply R R M (s : R))]
    exact h s s.2
  surj x := ⟨⟨x, 1⟩, by simp⟩
  exists_of_eq hxy := ⟨1, by simpa using hxy⟩

end TauCeti
