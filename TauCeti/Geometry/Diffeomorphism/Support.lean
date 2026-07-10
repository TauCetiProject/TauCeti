/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Diffeomorphism.RelativeCongr

/-!
# Supports of diffeomorphisms

For a self-diffeomorphism, its point-set support is the set of points it moves. This file records
the elementary algebra of supports and packages the subgroup of diffeomorphisms supported in a
chosen subset.

This is a small algebraic prerequisite for the geometric-topology roadmap
(`TauCetiRoadmap/GeometricTopology/README.md`, layer 3, "diffeomorphism groups with the C^∞
topology"). Relative groups such as `Diff(M, ∂M)` are pointwise fixing subgroups; equivalently,
they are groups of diffeomorphisms supported in the complement of the relative set. The future
`C^∞` topology can then state closed relative subgroups and compact-support variants on top of
this algebraic API.

## Main definitions

* `TauCeti.Diffeomorph.support φ`: the set of points moved by a self-diffeomorphism `φ`.
* `TauCeti.Diffeomorph.supportedSubgroup s`: self-diffeomorphisms whose support is contained in
  `s`.

The proofs use only the existing Tau Ceti diffeomorphism group and relative-conjugation API, plus
Mathlib's set and subgroup infrastructure.
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

@[simp]
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

/-- A self-diffeomorphism is supported in `s` when it moves no point outside `s`. -/
def supportedSubgroup (s : Set M) : Subgroup (M ≃ₘ^n⟮I, I⟯ M) :=
  fixingSubgroup (I := I) (n := n) sᶜ

@[simp]
theorem mem_supportedSubgroup_iff {s : Set M} {φ : M ≃ₘ^n⟮I, I⟯ M} :
    φ ∈ supportedSubgroup (I := I) (n := n) s ↔ support φ ⊆ s := by
  rw [supportedSubgroup, mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    by_contra hxs
    exact hx (h x hxs)
  · intro h x hx
    by_contra hfix
    exact hx (h hfix)

/-- Membership in `supportedSubgroup s` can be proved by showing all moved points lie in `s`. -/
theorem mem_supportedSubgroup_of_support_subset {s : Set M} {φ : M ≃ₘ^n⟮I, I⟯ M}
    (hφ : support φ ⊆ s) : φ ∈ supportedSubgroup (I := I) (n := n) s :=
  mem_supportedSubgroup_iff.mpr hφ

/-- A diffeomorphism supported in `s` fixes every point outside `s`. -/
theorem apply_eq_of_mem_supportedSubgroup {s : Set M} {φ : M ≃ₘ^n⟮I, I⟯ M}
    (hφ : φ ∈ supportedSubgroup (I := I) (n := n) s) {x : M} (hx : x ∉ s) : φ x = x :=
  (mem_fixingSubgroup_iff.mp hφ) x hx

/-- Diffeomorphisms supported in the empty set form the trivial subgroup. -/
@[simp]
theorem supportedSubgroup_empty :
    supportedSubgroup (I := I) (M := M) (n := n) (∅ : Set M) = ⊥ := by
  rw [supportedSubgroup]
  simp

/-- Every self-diffeomorphism is supported in the whole space. -/
@[simp]
theorem supportedSubgroup_univ :
    supportedSubgroup (I := I) (M := M) (n := n) (Set.univ : Set M) = ⊤ := by
  rw [supportedSubgroup]
  simp

/-- Support containment is monotone in the supporting set. -/
theorem supportedSubgroup_mono {s t : Set M} (hst : s ⊆ t) :
    supportedSubgroup (I := I) (n := n) s ≤ supportedSubgroup (I := I) (n := n) t := by
  intro φ hφ
  exact mem_supportedSubgroup_iff.mpr ((mem_supportedSubgroup_iff.mp hφ).trans hst)

/-- Conjugation transports the subgroup supported in `s` to the subgroup supported in `e '' s`. -/
theorem map_supportedSubgroup_diffCongr (e : M ≃ₘ^n⟮I, J⟯ N) (s : Set M) :
    (supportedSubgroup (I := I) (n := n) s).map (diffCongr e).toMonoidHom =
      supportedSubgroup (I := J) (n := n) (e '' s) := by
  ext ψ
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    rw [mem_supportedSubgroup_iff]
    have hsupp : support (diffCongr e φ) ⊆ e '' s := by
      rw [support_diffCongr]
      exact Set.image_mono (mem_supportedSubgroup_iff.mp hφ)
    simpa using hsupp
  · intro hψ
    refine ⟨diffCongr e.symm ψ, ?_, ?_⟩
    · have hsupp : support (diffCongr e.symm ψ) ⊆ s := by
        rw [support_diffCongr]
        intro x hx
        rcases hx with ⟨y, hy, rfl⟩
        rcases mem_supportedSubgroup_iff.mp hψ hy with ⟨z, hz, rfl⟩
        simpa using hz
      exact mem_supportedSubgroup_iff.mpr hsupp
    · ext y
      simp [diffCongr_apply_apply]

end Diffeomorph

end TauCeti
