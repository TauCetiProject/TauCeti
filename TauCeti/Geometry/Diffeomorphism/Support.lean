/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Diffeomorphism.RelativeCongr

/-!
# Supports of diffeomorphisms

For a self-diffeomorphism, its point-set support is the set of points it moves. This file records
the elementary algebra of supports.

This is a small algebraic prerequisite for the geometric-topology roadmap
(`TauCetiRoadmap/GeometricTopology/README.md`, layer 3, "diffeomorphism groups with the C^∞
topology"). Relative groups such as `Diff(M, ∂M)` are pointwise fixing subgroups; equivalently,
they are groups of diffeomorphisms supported in the complement of the relative set, i.e. with
support contained in the ambient set. Membership in such a group is `support φ ⊆ s`, which is
`_root_.mem_fixingSubgroup_compl_iff_movedBy_subset` applied to the fixing subgroup of `sᶜ`.

## Main definitions

* `TauCeti.Diffeomorph.support φ`: the set of points moved by a self-diffeomorphism `φ`.

The proofs use only the existing Tau Ceti diffeomorphism group and conjugation API, plus
Mathlib's set infrastructure.
-/

public section

namespace TauCeti

open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {n : ℕ∞ω}

namespace Diffeomorph

/-- The support of a self-diffeomorphism: the set of points it moves. -/
def support (φ : M ≃ₘ^n⟮I, I⟯ M) : Set M :=
  {x | φ x ≠ x}

@[simp]
theorem mem_support_iff {φ : M ≃ₘ^n⟮I, I⟯ M} {x : M} :
    x ∈ support φ ↔ φ x ≠ x :=
  Iff.rfl

theorem notMem_support_iff {φ : M ≃ₘ^n⟮I, I⟯ M} {x : M} :
    x ∉ support φ ↔ φ x = x := by
  rw [support, Set.mem_setOf_eq, not_not]

@[simp]
theorem support_one : support (1 : M ≃ₘ^n⟮I, I⟯ M) = ∅ := by
  ext x
  simp [support]

/-- A self-diffeomorphism has empty support exactly when it is the identity. -/
@[simp]
theorem support_eq_empty_iff {φ : M ≃ₘ^n⟮I, I⟯ M} : support φ = ∅ ↔ φ = 1 := by
  constructor
  · intro h
    ext x
    have hx : x ∉ support φ := by simp [h]
    exact notMem_support_iff.mp hx
  · intro h
    simp [h]

/-- A product can move a point only if one of its factors moves the relevant point. -/
theorem support_mul_subset (φ ψ : M ≃ₘ^n⟮I, I⟯ M) :
    support (φ * ψ) ⊆ support ψ ∪ ψ⁻¹' support φ := by
  intro x hx
  by_cases hψ : ψ x = x
  · right
    rw [Set.mem_preimage, mem_support_iff]
    intro hφ
    exact hx (by simpa [Diffeomorph.mul_apply, hψ] using hφ)
  · left
    exact hψ

/-- The support of the inverse is the image of the support under the diffeomorphism. -/
theorem support_inv_eq_image (φ : M ≃ₘ^n⟮I, I⟯ M) : support φ⁻¹ = φ '' support φ := by
  ext x
  constructor
  · intro hx
    refine ⟨φ⁻¹ x, ?_, by simp⟩
    rw [mem_support_iff]
    intro hfix
    exact hx (by simpa [Diffeomorph.inv_apply] using hfix.symm)
  · rintro ⟨y, hy, rfl⟩
    rw [mem_support_iff, Diffeomorph.inv_apply]
    intro hfix
    exact hy (by simpa using hfix.symm)

/-- Conjugating a diffeomorphism sends its support to the image support. -/
theorem support_diffCongr (e : M ≃ₘ^n⟮I, J⟯ N) (φ : M ≃ₘ^n⟮I, I⟯ M) :
    support (diffCongr e φ) = e '' support φ := by
  ext y
  constructor
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    rw [mem_support_iff]
    intro hfix
    exact hy (by
      rw [diffCongr_apply_apply, hfix]
      simp)
  · rintro ⟨x, hx, rfl⟩
    rw [mem_support_iff, diffCongr_apply_apply]
    simpa using hx

end Diffeomorph

end TauCeti
