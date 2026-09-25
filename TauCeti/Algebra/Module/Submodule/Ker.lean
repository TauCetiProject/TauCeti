/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Lattice

import Mathlib.LinearAlgebra.Span.Defs

/-!
# Splitting a vector along the kernels of commuting endomorphisms

Let `r₁` and `r₂` be endomorphisms of a module `M` with `ker r₁ ⊓ ker r₂ = ⊥`, and let `l₁`, `l₂`
be endomorphisms commuting with both. If `ξ = y + z` with `r₁ y = 0` and `r₂ z = 0`, and moreover
`r₁ ξ ∈ ker l₂` and `r₂ ξ ∈ ker l₁`, then `l₁ y` is killed by `r₁` and by `r₂`, hence `l₁ y = 0`,
and likewise `l₂ z = 0`.

This is the exactness step in the proof of §3 Theorem 2 of Popa and Zagier. There `ℛ = ℚ[ℳ]` is
spanned by integral matrices of positive determinant modulo `±1`, on which `PSL(2, ℤ)` acts on
both sides, and `π_S = (1 + S) / 2`, `π_U = (1 + U + U²) / 3`. Take `r₁`, `r₂` to be the right
multiplications by `π_S`, `π_U`, whose kernels meet trivially by the acyclicity of Lemma 2 for the
right action, and `l₁`, `l₂` the left multiplications by `1 - π_S`, `1 - π_U`, whose kernels are
`π_S ℛ` and `π_U ℛ`. Let `Y = ℛ (1 - π_S)` and `Z = ℛ (1 - π_U)`; as `S` and `U` generate
`PSL(2, ℤ)`, the elements of `Y + Z` are those whose sums over all right cosets vanish. Then an
element `ξ ∈ Y + Z` of their set `ℬ = {ξ | ξ π_S ∈ π_U ℛ, ξ π_U ∈ π_S ℛ}` (their (6)) lies in
`(π_S ℛ ∩ ℛ (1 - π_S)) + (π_U ℛ ∩ ℛ (1 - π_U)) = π_S ℛ (1 - π_S) + π_U ℛ (1 - π_U)`, which is
their `𝒥` (7).

## Main results

* `TauCeti.End.mem_inf_ker_sup_inf_ker_of_mem_sup`: if `ξ ∈ Y ⊔ Z` with `Y ≤ ker r₁`,
  `Z ≤ ker r₂`, `r₁ ξ ∈ ker l₂` and `r₂ ξ ∈ ker l₁`, then `ξ ∈ Y ⊓ ker l₁ ⊔ Z ⊓ ker l₂`.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. 762 (2020), 105–122, arXiv:1711.00327, Section 3, proof of Theorem 2.
-/

public section

namespace TauCeti.End

open Module LinearMap

/-- **Exactness in Popa–Zagier's §3 Theorem 2, for commuting operators**: let `r₁` and `r₂` have
disjoint kernels and let `l₁`, `l₂` commute with both. If `ξ ∈ Y ⊔ Z` for submodules `Y ≤ ker r₁`
and `Z ≤ ker r₂`, and `r₁ ξ ∈ ker l₂`, `r₂ ξ ∈ ker l₁`, then `ξ ∈ Y ⊓ ker l₁ ⊔ Z ⊓ ker l₂`. -/
theorem mem_inf_ker_sup_inf_ker_of_mem_sup {R M : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] {l₁ l₂ r₁ r₂ : End R M} (h₁₁ : Commute l₁ r₁) (h₁₂ : Commute l₁ r₂)
    (h₂₁ : Commute l₂ r₁) (h₂₂ : Commute l₂ r₂) (hr : Disjoint (ker r₁) (ker r₂))
    {Y Z : Submodule R M} (hY : Y ≤ ker r₁) (hZ : Z ≤ ker r₂) {ξ : M} (hξ : ξ ∈ Y ⊔ Z)
    (hr₁ξ : r₁ ξ ∈ ker l₂) (hr₂ξ : r₂ ξ ∈ ker l₁) : ξ ∈ Y ⊓ ker l₁ ⊔ Z ⊓ ker l₂ := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hξ
  have hy' : r₁ y = 0 := hY hy
  have hz' : r₂ z = 0 := hZ hz
  have hc : ∀ {l r : End R M}, Commute l r → ∀ x, r (l x) = l (r x) := fun h x ↦
    LinearMap.congr_fun h.eq.symm x
  -- `r₁` and `r₂` kill `l₁ y`, as `r₁ y = 0` and `r₂ y = r₂ ξ ∈ ker l₁`; dually for `l₂ z`
  have h₁ : l₁ y = 0 := Submodule.disjoint_def.1 hr _ (by rw [mem_ker, hc h₁₁, hy', map_zero])
    (by rw [mem_ker, hc h₁₂]; simpa [hz'] using hr₂ξ)
  have h₂ : l₂ z = 0 := Submodule.disjoint_def.1 hr _
    (by rw [mem_ker, hc h₂₁]; simpa [hy'] using hr₁ξ) (by rw [mem_ker, hc h₂₂, hz', map_zero])
  exact Submodule.add_mem_sup ⟨hy, h₁⟩ ⟨hz, h₂⟩

end TauCeti.End
