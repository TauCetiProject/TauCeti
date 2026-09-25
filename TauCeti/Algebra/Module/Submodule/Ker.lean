/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Ker

import Mathlib.LinearAlgebra.Span.Defs

/-!
# Splitting a vector along the kernels of commuting endomorphisms

Let `r₁` and `r₂` be endomorphisms of a module `M` with `ker r₁ ⊓ ker r₂ = ⊥`, let `l₁` and `l₂`
be endomorphisms commuting with both, and let `Y ≤ ker r₁` and `Z ≤ ker r₂` be submodules. If
`ξ ∈ Y ⊔ Z` satisfies `r₁ ξ ∈ ker l₂` and `r₂ ξ ∈ ker l₁`, then `ξ ∈ (Y ⊓ ker l₁) ⊔ (Z ⊓ ker l₂)`.

This is the exactness step in the proof of §3 Theorem 2 of Popa and Zagier, with `r₁`, `r₂` the
right multiplications by `π_S`, `π_U` on their `ℛ` (whose kernels meet trivially by the
right-action form of their Lemma 2), `l₁`, `l₂` the left multiplications by `1 - π_S`, `1 - π_U`,
`Y = ℛ (1 - π_S)` and `Z = ℛ (1 - π_U)`: an element of `Y + Z` in their `ℬ` (6) is in their `𝒥` (7).

## Main results

* `TauCeti.End.mem_inf_ker_sup_inf_ker_of_mem_sup`: the splitting statement above.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. 762 (2020), 105–122, arXiv:1711.00327, Section 3, proof of Theorem 2.
-/

public section

namespace TauCeti.End

open Module LinearMap

/-- **Splitting along disjoint kernels of commuting endomorphisms**: let `r₁` and `r₂` have
disjoint kernels and let `l₁`, `l₂` commute with both. If `ξ ∈ Y ⊔ Z` for submodules `Y ≤ ker r₁`
and `Z ≤ ker r₂`, and `r₁ ξ ∈ ker l₂`, `r₂ ξ ∈ ker l₁`, then `ξ ∈ Y ⊓ ker l₁ ⊔ Z ⊓ ker l₂`. -/
theorem mem_inf_ker_sup_inf_ker_of_mem_sup {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {l₁ l₂ r₁ r₂ : End R M} (h₁₁ : Commute l₁ r₁) (h₁₂ : Commute l₁ r₂) (h₂₁ : Commute l₂ r₁)
    (h₂₂ : Commute l₂ r₂) (hr : Disjoint (ker r₁) (ker r₂)) {Y Z : Submodule R M} (hY : Y ≤ ker r₁)
    (hZ : Z ≤ ker r₂) {ξ : M} (hξ : ξ ∈ Y ⊔ Z) (hr₁ξ : r₁ ξ ∈ ker l₂) (hr₂ξ : r₂ ξ ∈ ker l₁) :
    ξ ∈ Y ⊓ ker l₁ ⊔ Z ⊓ ker l₂ := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hξ
  have hy' : r₁ y = 0 := hY hy
  have hz' : r₂ z = 0 := hZ hz
  have hc : ∀ {l r : End R M}, Commute l r → ∀ x, r (l x) = l (r x) := fun h ↦
    LinearMap.congr_fun h.eq.symm
  -- `r₁` and `r₂` both kill `l₁ y`, as `r₁ y = 0` and `r₂ y = r₂ ξ ∈ ker l₁`, so `l₁ y = 0` as
  -- their kernels are disjoint; dually `l₂ z = 0`
  exact Submodule.add_mem_sup
    ⟨hy, Submodule.disjoint_def.1 hr _ (by simp [hc h₁₁, hy']) (by simpa [hc h₁₂, hz'] using hr₂ξ)⟩
    ⟨hz, Submodule.disjoint_def.1 hr _ (by simpa [hc h₂₁, hy'] using hr₁ξ) (by simp [hc h₂₂, hz'])⟩

end TauCeti.End
