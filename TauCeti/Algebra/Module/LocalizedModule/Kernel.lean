/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Module.FinitePresentation

/-!
# The kernel of a localization map is killed by one scalar

The kernel of a localization map `f : M →ₗ[R] M'` at a submonoid `S` consists of the elements
killed by some element of `S`. When the kernel is finitely generated, the product of the elements
killing a finite generating set kills all of it, so a single `s ∈ S` kills the whole kernel.

## Main results

* `IsLocalizedModule.exists_mem_smul_eq_zero_of_mem_ker`: a single `s ∈ S` kills every element of
  a finitely generated kernel of a localization map at `S`.
-/

public section

namespace IsLocalizedModule

variable {R M M' : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M']
  [Module R M'] (S : Submonoid R) (f : M →ₗ[R] M') [IsLocalizedModule S f]

/-- **The kernel of a localization map is killed by one scalar.** If `f` is a localization map at
`S` with finitely generated kernel, a single `s ∈ S` kills every element of the kernel. -/
theorem exists_mem_smul_eq_zero_of_mem_ker [Module.Finite R (LinearMap.ker f)] :
    ∃ s ∈ S, ∀ m ∈ LinearMap.ker f, s • m = 0 := by
  obtain ⟨s, hs⟩ := Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule S f
    (LinearMap.ker f).subtype 0 (by rw [LinearMap.comp_ker_subtype, LinearMap.comp_zero])
  exact ⟨s, s.property, fun m hm ↦ by simpa [Submonoid.smul_def] using congr($hs ⟨m, hm⟩)⟩

end IsLocalizedModule
