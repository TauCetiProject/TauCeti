/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Diffeomorphism.Congr
public import TauCeti.Geometry.Diffeomorphism.FixingSubgroup

/-!
# Transporting relative diffeomorphism groups

A diffeomorphism `e : M ≃ₘ^n⟮I, J⟯ N` identifies the relative diffeomorphism group fixing a
subset `s : Set M` pointwise with the relative diffeomorphism group fixing `e '' s` pointwise.
This file records that restriction of `Diffeomorph.diffCongr` to pointwise fixing subgroups.

This is a small algebraic prerequisite for the geometric-topology roadmap
(`TauCetiRoadmap/GeometricTopology/README.md`, layer 3, "diffeomorphism groups with the C^∞
topology"), where relative groups such as `Diff(M, ∂M)` are pointwise fixing subgroups. The
`C^∞` topology and closed-subgroup statements remain later layer-3 work.

## Main definitions

* `TauCeti.Diffeomorph.relativeDiffCongr e s`: the group isomorphism
  `Diff(M, s) ≃* Diff(N, e '' s)` induced by conjugation with `e`.

## Main results

* `TauCeti.Diffeomorph.diffCongr_mem_fixingSubgroup_image`: conjugating a diffeomorphism fixing
  `s` gives one fixing `e '' s`.
* `TauCeti.Diffeomorph.relativeDiffCongr_apply`: the underlying diffeomorphism is
  `Diffeomorph.diffCongr e`.
* `TauCeti.Diffeomorph.relativeDiffCongr_apply_apply`: pointwise,
  `relativeDiffCongr e s φ y = e (φ (e.symm y))`.
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

/-- Conjugating by `e` sends diffeomorphisms fixing `s` pointwise to diffeomorphisms fixing
`e '' s` pointwise. -/
theorem diffCongr_mem_fixingSubgroup_image (e : M ≃ₘ^n⟮I, J⟯ N) {s : Set M}
    {φ : M ≃ₘ^n⟮I, I⟯ M} (hφ : φ ∈ fixingSubgroup (I := I) (n := n) s) :
    diffCongr e φ ∈ fixingSubgroup (I := J) (n := n) (e '' s) := by
  rw [mem_fixingSubgroup_iff]
  rintro y ⟨x, hx, rfl⟩
  simp [diffCongr_apply_apply, apply_eq_of_mem_fixingSubgroup hφ hx]

/-- Conjugating by `e.symm` sends diffeomorphisms fixing `e '' s` pointwise back to
diffeomorphisms fixing `s` pointwise. -/
theorem diffCongr_symm_mem_fixingSubgroup (e : M ≃ₘ^n⟮I, J⟯ N) {s : Set M}
    {ψ : N ≃ₘ^n⟮J, J⟯ N} (hψ : ψ ∈ fixingSubgroup (I := J) (n := n) (e '' s)) :
    diffCongr e.symm ψ ∈ fixingSubgroup (I := I) (n := n) s := by
  rw [mem_fixingSubgroup_iff]
  intro x hx
  have hfix : ψ (e x) = e x :=
    apply_eq_of_mem_fixingSubgroup hψ (Set.mem_image_of_mem e hx)
  calc
    diffCongr e.symm ψ x = e.symm (ψ (e.symm.symm x)) := by
      rw [diffCongr_apply_apply]
    _ = e.symm (ψ (e x)) :=
      congrArg (fun y => e.symm (ψ y)) (e.toEquiv.symm_symm_apply x)
    _ = x := by simpa using congrArg e.symm hfix

/-- Conjugation by a diffeomorphism identifies the relative diffeomorphism group fixing `s`
pointwise with the relative diffeomorphism group fixing the image subset `e '' s` pointwise. -/
def relativeDiffCongr (e : M ≃ₘ^n⟮I, J⟯ N) (s : Set M) :
    fixingSubgroup (I := I) (n := n) s ≃*
      fixingSubgroup (I := J) (n := n) (e '' s) where
  toFun φ := ⟨diffCongr e φ, diffCongr_mem_fixingSubgroup_image e φ.property⟩
  invFun ψ := ⟨diffCongr e.symm ψ, diffCongr_symm_mem_fixingSubgroup e ψ.property⟩
  left_inv φ := by
    ext x
    simp [diffCongr_apply_apply]
  right_inv ψ := by
    ext y
    simp [diffCongr_apply_apply]
  map_mul' φ ψ := by
    ext y
    simp [diffCongr_apply_apply]

/-- Applying `relativeDiffCongr` and then forgetting the subgroup is `Diffeomorph.diffCongr`. -/
@[simp]
theorem relativeDiffCongr_apply (e : M ≃ₘ^n⟮I, J⟯ N) (s : Set M)
    (φ : fixingSubgroup (I := I) (n := n) s) :
    (relativeDiffCongr e s φ : N ≃ₘ^n⟮J, J⟯ N) = diffCongr e φ := by
  ext y
  rfl

/-- Pointwise formula for the relative conjugation equivalence. -/
@[simp]
theorem relativeDiffCongr_apply_apply (e : M ≃ₘ^n⟮I, J⟯ N) (s : Set M)
    (φ : fixingSubgroup (I := I) (n := n) s) (y : N) :
    ((relativeDiffCongr e s φ : N ≃ₘ^n⟮J, J⟯ N) y) =
      e ((φ : M ≃ₘ^n⟮I, I⟯ M) (e.symm y)) := by
  rw [relativeDiffCongr_apply]
  exact diffCongr_apply_apply e φ y

/-- Applying the inverse of `relativeDiffCongr` and then forgetting the subgroup is conjugation by
`e.symm`. -/
@[simp]
theorem relativeDiffCongr_symm_apply (e : M ≃ₘ^n⟮I, J⟯ N) (s : Set M)
    (ψ : fixingSubgroup (I := J) (n := n) (e '' s)) :
    ((relativeDiffCongr e s).symm ψ : M ≃ₘ^n⟮I, I⟯ M) = diffCongr e.symm ψ := by
  ext x
  rfl

end Diffeomorph

end TauCeti
