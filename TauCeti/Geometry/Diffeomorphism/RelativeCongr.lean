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
subset `s : Set M` pointwise with the relative diffeomorphism group fixing any named target
subset `t : Set N` known to be `e '' s`. This file records that restriction of
`Diffeomorph.diffCongr` to pointwise fixing subgroups.

This is a small algebraic prerequisite for the geometric-topology roadmap
(`TauCetiRoadmap/GeometricTopology/README.md`, layer 3, "diffeomorphism groups with the C^∞
topology"), where relative groups such as `Diff(M, ∂M)` are pointwise fixing subgroups. The
`C^∞` topology and closed-subgroup statements remain later layer-3 work.

The main subgroup-map statement and relative equivalence are the diffeomorphism-specialized
analogues of Mathlib's pointwise-fixer conjugation API
`Set.conj_mem_fixingSubgroup`, `fixingSubgroup_map_conj_eq`, and
`fixingSubgroupEquivFixingSubgroup` from
`Mathlib/GroupTheory/GroupAction/SubMulAction/OfFixingSubgroup.lean`, using
`Diffeomorph.diffCongr` for conjugation by a diffeomorphism.

## Main definitions

* `TauCeti.Diffeomorph.relativeDiffCongrOfImageEq e hst`: the group isomorphism
  `Diff(M, s) ≃* Diff(N, t)` induced by conjugation with `e`, when `hst : e '' s = t`.
* `TauCeti.Diffeomorph.relativeDiffCongr e s`: the specialization
  `Diff(M, s) ≃* Diff(N, e '' s)` induced by conjugation with `e`.

## Main results

* `TauCeti.Diffeomorph.map_fixingSubgroup_diffCongr_of_image_eq`: conjugation maps the pointwise
  fixer of `s` onto the pointwise fixer of `t`, when `e '' s = t`.
* `TauCeti.Diffeomorph.map_fixingSubgroup_diffCongr`: conjugation maps the pointwise fixer of
  `s` onto the pointwise fixer of `e '' s`.
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

/-- Conjugation by `e` maps the subgroup fixing `s` pointwise onto the subgroup fixing `e '' s`
pointwise. -/
theorem map_fixingSubgroup_diffCongr (e : M ≃ₘ^n⟮I, J⟯ N) (s : Set M) :
    (fixingSubgroup (I := I) (n := n) s).map (diffCongr e).toMonoidHom =
      fixingSubgroup (I := J) (n := n) (e '' s) := by
  ext ψ
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    rw [mem_fixingSubgroup_iff]
    rintro y ⟨x, hx, rfl⟩
    simp [diffCongr_apply_apply, apply_eq_of_mem_fixingSubgroup hφ hx]
  · intro hψ
    refine ⟨diffCongr e.symm ψ, ?_, ?_⟩
    · apply mem_fixingSubgroup_of_forall
      intro x hx
      have hfix : ψ (e x) = e x :=
        apply_eq_of_mem_fixingSubgroup hψ (Set.mem_image_of_mem e hx)
      calc
        diffCongr e.symm ψ x = e.symm (ψ (e.symm.symm x)) := by
          rw [diffCongr_apply_apply]
        _ = e.symm (ψ (e x)) :=
          congrArg (fun y => e.symm (ψ y)) (e.toEquiv.symm_symm_apply x)
        _ = x := by simpa using congrArg e.symm hfix
    · ext y
      simp [diffCongr_apply_apply]

/-- Conjugation by `e` maps the subgroup fixing `s` pointwise onto the subgroup fixing a named
target `t` pointwise, when `t` is the image of `s`. -/
theorem map_fixingSubgroup_diffCongr_of_image_eq (e : M ≃ₘ^n⟮I, J⟯ N) {s : Set M} {t : Set N}
    (hst : e '' s = t) :
    (fixingSubgroup (I := I) (n := n) s).map (diffCongr e).toMonoidHom =
      fixingSubgroup (I := J) (n := n) t := by
  rw [← hst]
  exact map_fixingSubgroup_diffCongr e s

/-- Conjugating by `e` sends diffeomorphisms fixing `s` pointwise to diffeomorphisms fixing
`e '' s` pointwise. -/
theorem diffCongr_mem_fixingSubgroup_image (e : M ≃ₘ^n⟮I, J⟯ N) {s : Set M}
    {φ : M ≃ₘ^n⟮I, I⟯ M} (hφ : φ ∈ fixingSubgroup (I := I) (n := n) s) :
    diffCongr e φ ∈ fixingSubgroup (I := J) (n := n) (e '' s) := by
  rw [← map_fixingSubgroup_diffCongr e s]
  exact ⟨φ, hφ, rfl⟩

/-- Conjugating by `e.symm` sends diffeomorphisms fixing `e '' s` pointwise back to
diffeomorphisms fixing `s` pointwise. -/
theorem diffCongr_symm_mem_fixingSubgroup (e : M ≃ₘ^n⟮I, J⟯ N) {s : Set M}
    {ψ : N ≃ₘ^n⟮J, J⟯ N} (hψ : ψ ∈ fixingSubgroup (I := J) (n := n) (e '' s)) :
    diffCongr e.symm ψ ∈ fixingSubgroup (I := I) (n := n) s := by
  have hmap : ψ ∈ (fixingSubgroup (I := I) (n := n) s).map (diffCongr e).toMonoidHom := by
    rw [map_fixingSubgroup_diffCongr e s]
    exact hψ
  rcases hmap with ⟨φ, hφ, rfl⟩
  simpa [diffCongr_symm] using hφ

/-- Conjugation by a diffeomorphism identifies the relative diffeomorphism group fixing `s`
pointwise with the relative diffeomorphism group fixing a named target `t` pointwise, when `t` is
the image of `s`. -/
def relativeDiffCongrOfImageEq (e : M ≃ₘ^n⟮I, J⟯ N) {s : Set M} {t : Set N}
    (hst : e '' s = t) :
    fixingSubgroup (I := I) (n := n) s ≃*
      fixingSubgroup (I := J) (n := n) t :=
  ((diffCongr e).subgroupMap (fixingSubgroup (I := I) (n := n) s)).trans
    (MulEquiv.subgroupCongr (map_fixingSubgroup_diffCongr_of_image_eq e hst))

/-- Conjugation by a diffeomorphism identifies the relative diffeomorphism group fixing `s`
pointwise with the relative diffeomorphism group fixing the image subset `e '' s` pointwise. -/
def relativeDiffCongr (e : M ≃ₘ^n⟮I, J⟯ N) (s : Set M) :
    fixingSubgroup (I := I) (n := n) s ≃*
      fixingSubgroup (I := J) (n := n) (e '' s) :=
  relativeDiffCongrOfImageEq e (s := s) rfl

/-- Applying `relativeDiffCongrOfImageEq` and then forgetting the subgroup is
`Diffeomorph.diffCongr`. -/
@[simp]
theorem relativeDiffCongrOfImageEq_apply (e : M ≃ₘ^n⟮I, J⟯ N) {s : Set M} {t : Set N}
    (hst : e '' s = t) (φ : fixingSubgroup (I := I) (n := n) s) :
    (relativeDiffCongrOfImageEq e hst φ : N ≃ₘ^n⟮J, J⟯ N) = diffCongr e φ := by
  ext y
  rfl

/-- Applying `relativeDiffCongr` and then forgetting the subgroup is `Diffeomorph.diffCongr`. -/
@[simp]
theorem relativeDiffCongr_apply (e : M ≃ₘ^n⟮I, J⟯ N) (s : Set M)
    (φ : fixingSubgroup (I := I) (n := n) s) :
    (relativeDiffCongr e s φ : N ≃ₘ^n⟮J, J⟯ N) = diffCongr e φ := by
  exact relativeDiffCongrOfImageEq_apply e rfl φ

/-- Pointwise formula for the named-target relative conjugation equivalence. -/
@[grind =]
theorem relativeDiffCongrOfImageEq_apply_apply (e : M ≃ₘ^n⟮I, J⟯ N) {s : Set M} {t : Set N}
    (hst : e '' s = t) (φ : fixingSubgroup (I := I) (n := n) s) (y : N) :
    ((relativeDiffCongrOfImageEq e hst φ : N ≃ₘ^n⟮J, J⟯ N) y) =
      e ((φ : M ≃ₘ^n⟮I, I⟯ M) (e.symm y)) := by
  rw [relativeDiffCongrOfImageEq_apply]
  exact diffCongr_apply_apply e φ y

/-- Pointwise formula for the relative conjugation equivalence. -/
@[grind =]
theorem relativeDiffCongr_apply_apply (e : M ≃ₘ^n⟮I, J⟯ N) (s : Set M)
    (φ : fixingSubgroup (I := I) (n := n) s) (y : N) :
    ((relativeDiffCongr e s φ : N ≃ₘ^n⟮J, J⟯ N) y) =
      e ((φ : M ≃ₘ^n⟮I, I⟯ M) (e.symm y)) := by
  rw [relativeDiffCongr_apply]
  exact diffCongr_apply_apply e φ y

/-- Applying the inverse of `relativeDiffCongrOfImageEq` and then forgetting the subgroup is
conjugation by `e.symm`. -/
@[simp]
theorem relativeDiffCongrOfImageEq_symm_apply (e : M ≃ₘ^n⟮I, J⟯ N) {s : Set M} {t : Set N}
    (hst : e '' s = t) (ψ : fixingSubgroup (I := J) (n := n) t) :
    ((relativeDiffCongrOfImageEq e hst).symm ψ : M ≃ₘ^n⟮I, I⟯ M) = diffCongr e.symm ψ := by
  ext x
  rfl

/-- Applying the inverse of `relativeDiffCongr` and then forgetting the subgroup is conjugation by
`e.symm`. -/
@[simp]
theorem relativeDiffCongr_symm_apply (e : M ≃ₘ^n⟮I, J⟯ N) (s : Set M)
    (ψ : fixingSubgroup (I := J) (n := n) (e '' s)) :
    ((relativeDiffCongr e s).symm ψ : M ≃ₘ^n⟮I, I⟯ M) = diffCongr e.symm ψ := by
  exact relativeDiffCongrOfImageEq_symm_apply e rfl ψ

/-- Pointwise formula for the inverse named-target relative conjugation equivalence. -/
@[grind =]
theorem relativeDiffCongrOfImageEq_symm_apply_apply (e : M ≃ₘ^n⟮I, J⟯ N)
    {s : Set M} {t : Set N} (hst : e '' s = t)
    (ψ : fixingSubgroup (I := J) (n := n) t) (x : M) :
    (((relativeDiffCongrOfImageEq e hst).symm ψ : M ≃ₘ^n⟮I, I⟯ M) x) =
      e.symm ((ψ : N ≃ₘ^n⟮J, J⟯ N) (e x)) := by
  rw [relativeDiffCongrOfImageEq_symm_apply]
  exact diffCongr_apply_apply e.symm ψ x

/-- Pointwise formula for the inverse relative conjugation equivalence. -/
@[grind =]
theorem relativeDiffCongr_symm_apply_apply (e : M ≃ₘ^n⟮I, J⟯ N) (s : Set M)
    (ψ : fixingSubgroup (I := J) (n := n) (e '' s)) (x : M) :
    (((relativeDiffCongr e s).symm ψ : M ≃ₘ^n⟮I, I⟯ M) x) =
      e.symm ((ψ : N ≃ₘ^n⟮J, J⟯ N) (e x)) := by
  rw [relativeDiffCongr_symm_apply]
  exact diffCongr_apply_apply e.symm ψ x

end Diffeomorph

end TauCeti
