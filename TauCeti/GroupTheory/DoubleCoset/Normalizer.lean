/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.DoubleCoset

import Mathlib.Tactic.Group

/-!
# Double cosets at a normalizing element

A double coset `ΓgΓ` is in general a union of several cosets on either side. When `g`
normalizes `Γ` it is a *single* coset, and the two sides agree:

`ΓgΓ = Γ(gΓg⁻¹)g = ΓΓg = Γg`.

This file records that collapse, together with the observation that a double coset at a
normalizing element consists of normalizing elements. Both are used wherever a Hecke double
coset attached to an element of the normalizer has to be recognised as a single coset — for
`Γ₁(N) ⊴ Γ₀(N)`, this is what makes the diamond operators double-coset operators.

## Main results

* `DoubleCoset.doubleCoset_eq_rightCoset_of_mem_normalizer`: `ΓgΓ = Γg` for `g` normalizing `Γ`.
* `DoubleCoset.mem_normalizer_of_mem_doubleCoset`: every element of such a `ΓgΓ` again
  normalizes `Γ`, so the collapse propagates to any representative of the double coset.
* `DoubleCoset.mem_rightCoset_conj_iff_of_mem_normalizer`,
  `DoubleCoset.conj_mem_doubleCoset_conj_iff_of_mem_normalizer`: conjugation by `g` in the
  normalizer carries the right cosets `Γa` and the double cosets `HaK` (`g` normalizing `H` and
  `K`) to the right and double cosets of the conjugate `g⁻¹ag`.
-/

public section

open MulOpposite

open scoped Pointwise

namespace DoubleCoset

variable {G : Type*} [Group G] {Γ : Subgroup G} {g : G}

/-- **A double coset at a normalizing element is a single right coset.** For `g` in the
normalizer of `Γ` the two flanking copies of `Γ` merge: the right-hand factor `b` of
`a * g * b` is absorbed by rewriting `g * b = (g * b * g⁻¹) * g`.

The left-coset form is the same statement, `Γ g Γ = g Γ`, read through `gΓ = Γg`; only the
right-coset form is stated, because that is the handedness in which Hecke operators decompose
a double coset. -/
theorem doubleCoset_eq_rightCoset_of_mem_normalizer (hg : g ∈ Subgroup.normalizer (Γ : Set G)) :
    doubleCoset g Γ Γ = op g • (Γ : Set G) := by
  ext x
  rw [mem_doubleCoset, mem_rightCoset_iff]
  refine ⟨?_, fun hx ↦ ⟨x * g⁻¹, hx, 1, Γ.one_mem, by simp⟩⟩
  rintro ⟨a, ha, b, hb, rfl⟩
  have hconj : g * b * g⁻¹ ∈ Γ := (Subgroup.mem_normalizer_iff.mp hg b).mp hb
  have hrw : a * g * b * g⁻¹ = a * (g * b * g⁻¹) := by group
  exact hrw ▸ Γ.mul_mem ha hconj

/-- **A double coset at a normalizing element consists of normalizing elements.** Every
`a * g * b` with `a, b ∈ Γ` lies in the normalizer of `Γ`, which contains both `Γ` and `g`.
Consequently `doubleCoset_eq_rightCoset_of_mem_normalizer` applies to *any* representative of
the double coset, not only to the chosen `g`. -/
theorem mem_normalizer_of_mem_doubleCoset (hg : g ∈ Subgroup.normalizer (Γ : Set G)) {x : G}
    (hx : x ∈ doubleCoset g Γ Γ) : x ∈ Subgroup.normalizer (Γ : Set G) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_doubleCoset.mp hx
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.le_normalizer ha) hg)
    (Subgroup.le_normalizer hb)

/-- **Conjugation by a normalizing element carries right cosets to right cosets**:
`x ∈ Γ(g⁻¹ag)` exactly when `gxg⁻¹ ∈ Γa`. -/
theorem mem_rightCoset_conj_iff_of_mem_normalizer (hg : g ∈ Subgroup.normalizer (Γ : Set G))
    (a x : G) : x ∈ op (g⁻¹ * a * g) • (Γ : Set G) ↔ g * x * g⁻¹ ∈ op a • (Γ : Set G) := by
  rw [mem_rightCoset_iff, mem_rightCoset_iff, SetLike.mem_coe, SetLike.mem_coe,
    Subgroup.mem_normalizer_iff.mp hg]
  exact iff_of_eq (congrArg (· ∈ Γ) (by group))

/-- **Conjugation by an element normalizing both flanks carries double cosets to double
cosets**: `g⁻¹xg ∈ H(g⁻¹ag)K` exactly when `x ∈ HaK`. -/
theorem conj_mem_doubleCoset_conj_iff_of_mem_normalizer {H K : Subgroup G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G))
    (a x : G) : g⁻¹ * x * g ∈ doubleCoset (g⁻¹ * a * g) H K ↔ x ∈ doubleCoset a H K := by
  -- `h ↦ ghg⁻¹` preserves a subgroup normalized by `g`, in both directions
  have hout : ∀ L : Subgroup G, g ∈ Subgroup.normalizer (L : Set G) → ∀ h ∈ L,
      g * h * g⁻¹ ∈ L := fun L hL h hh ↦ (Subgroup.mem_normalizer_iff.mp hL h).mp hh
  have hin : ∀ L : Subgroup G, g ∈ Subgroup.normalizer (L : Set G) → ∀ h ∈ L,
      g⁻¹ * h * g ∈ L := fun L hL h hh ↦ by
    simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hL) h).mp hh
  simp only [mem_doubleCoset, SetLike.mem_coe]
  constructor
  · rintro ⟨h, hh, h', hh', he⟩
    refine ⟨g * h * g⁻¹, hout H hH h hh, g * h' * g⁻¹, hout K hK h' hh', ?_⟩
    calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = g * h * g⁻¹ * a * (g * h' * g⁻¹) := by rw [he]; group
  · rintro ⟨h, hh, h', hh', rfl⟩
    exact ⟨g⁻¹ * h * g, hin H hH h hh, g⁻¹ * h' * g, hin K hK h' hh', by group⟩

end DoubleCoset
