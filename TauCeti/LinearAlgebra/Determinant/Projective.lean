/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.RingTheory.Finiteness.Projective
public import TauCeti.LinearAlgebra.End.Split
import TauCeti.LinearAlgebra.Determinant.Basic

/-!
# Determinants of endomorphisms of finite projective modules

Mathlib's `LinearMap.det` is the determinant of an endomorphism of a module with a finite basis,
and is `1` on every other module. This file defines the determinant
`LinearMap.projectiveDet : Module.End R M →* R` of an endomorphism of a finite projective module
`M`, that is, of a finite locally free module, which need not be free.

Choose a free module `F` of finite rank with linear maps `π : F →ₗ[R] M` and `σ : M →ₗ[R] F` such
that `π ∘ₗ σ = id`. Then `F` is the internal direct sum of the image `σ(M) ≅ M` and the kernel of
`π`, and the endomorphism `σ ∘ₗ f ∘ₗ π + (1 - σ ∘ₗ π)` of `F` is `f` on the first summand and the
identity on the second. Its determinant does not depend on `F`, `π` and `σ`
(`LinearMap.projectiveDet_eq_det_of_comp_eq_id`), by the Weinstein–Aronszajn identity
`det (1 + X ∘ₗ Y) = det (1 + Y ∘ₗ X)` for linear maps `X` and `Y` between free modules of finite
rank (`LinearMap.det_one_add_comp_comm`). This determinant is `projectiveDet f`. Its image in a
localization `R_𝔭`, over which `M_𝔭` is free, is the determinant of the matrix of `f_𝔭` in a basis
(`LinearMap.projectiveDet_baseChange` and `LinearMap.projectiveDet_eq_det`), so it agrees with the
determinant defined through local trivializations.

The determinant is multiplicative, agrees with `LinearMap.det` on free modules, commutes with
arbitrary base change, is invariant under conjugation by linear equivalences, and detects
invertibility. It is the determinant underlying the norm of a finite locally free algebra,
`Algebra.projectiveNorm`.

## Main definitions

* `LinearMap.projectiveDet`: the determinant of an endomorphism of a finite projective module.

## Main results

* `LinearMap.projectiveDet_eq_det_of_comp_eq_id`: `projectiveDet f` is the determinant of
  `σ ∘ₗ f ∘ₗ π + (1 - σ ∘ₗ π)` for every splitting `π ∘ₗ σ = id` through a free module of finite
  rank.
* `LinearMap.projectiveDet_comp` and `LinearMap.projectiveDet_id`: the determinant is
  multiplicative.
* `LinearMap.projectiveDet_eq_det`: on a free module of finite rank, `projectiveDet` is
  `LinearMap.det`.
* `LinearMap.projectiveDet_baseChange`: the determinant commutes with base change along any
  ring homomorphism.
* `LinearMap.projectiveDet_conj`: the determinant is invariant under conjugation by a linear
  equivalence.
* `LinearMap.isUnit_iff_isUnit_projectiveDet`: an endomorphism is invertible if and only if its
  determinant is a unit.

## References

* O. Goldman, *Determinants in projective modules*, Nagoya Math. J. 18 (1961), 27–36.
* The Stacks Project, Tag 0BIF (the norm of a finite locally free algebra).
-/

public section

open Module

namespace LinearMap

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

section Split

variable {F : Type*} [AddCommGroup F] [Module R F]

-- The determinant of `splitEnd π σ h f` does not depend on the splitting.
private theorem det_splitEnd_eq {F' : Type*} [AddCommGroup F'] [Module R F'] [Module.Free R F]
    [Module.Finite R F] [Module.Free R F'] [Module.Finite R F'] (π : F →ₗ[R] M)
    (σ : M →ₗ[R] F) (h : π ∘ₗ σ = id) (π' : F' →ₗ[R] M) (σ' : M →ₗ[R] F')
    (h' : π' ∘ₗ σ' = id) (f : Module.End R M) :
    LinearMap.det (splitEnd π σ h f) = LinearMap.det (splitEnd π' σ' h' f) := by
  have hx (x : M) : π (σ x) = x := congr($h x)
  have hx' (x : M) : π' (σ' x) = x := congr($h' x)
  -- with `X = σ ∘ₗ π'` and `Y = σ' ∘ₗ (f - 1) ∘ₗ π`, `X ∘ₗ Y = σ ∘ₗ (f - 1) ∘ₗ π` and
  -- `Y ∘ₗ X = σ' ∘ₗ (f - 1) ∘ₗ π'`
  have hXY : (σ ∘ₗ π') ∘ₗ (σ' ∘ₗ (f - 1) ∘ₗ π) = σ ∘ₗ (f - 1) ∘ₗ π := by
    ext x
    simp [hx']
  have hYX : (σ' ∘ₗ (f - 1) ∘ₗ π) ∘ₗ (σ ∘ₗ π') = σ' ∘ₗ (f - 1) ∘ₗ π' := by
    ext x
    simp [hx]
  rw [splitEnd_eq_one_add, splitEnd_eq_one_add, ← hXY, ← hYX, det_one_add_comp_comm]

end Split

variable [Module.Finite R M]

section Projective

variable [Module.Projective R M]

/-- The **determinant** of an endomorphism `f` of a finite projective module `M`: for a free module
`F` of finite rank with `π : F →ₗ[R] M` and `σ : M →ₗ[R] F` such that `π ∘ₗ σ = id`, it is the
determinant of the endomorphism `σ ∘ₗ f ∘ₗ π + (1 - σ ∘ₗ π)` of `F`, which is `f` on `σ(M)` and
the identity on `ker π`. It does not depend on the choice of `F`, `π` and `σ`
(`projectiveDet_eq_det_of_comp_eq_id`), and it is `LinearMap.det` when `M` is free
(`projectiveDet_eq_det`). -/
noncomputable def projectiveDet : Module.End R M →* R :=
  have h := Module.Finite.exists_comp_eq_id_of_projective R M
  LinearMap.det.comp (splitEnd h.choose_spec.choose h.choose_spec.choose_spec.choose
    h.choose_spec.choose_spec.choose_spec.2.2)

/-- The determinant `projectiveDet f` is the determinant of `σ ∘ₗ f ∘ₗ π + (1 - σ ∘ₗ π)`, for any
free module `F` of finite rank with linear maps `π : F →ₗ[R] M` and `σ : M →ₗ[R] F` such that
`π ∘ₗ σ = id`. -/
theorem projectiveDet_eq_det_of_comp_eq_id {F : Type*} [AddCommGroup F] [Module R F]
    [Module.Free R F] [Module.Finite R F] (π : F →ₗ[R] M) (σ : M →ₗ[R] F) (h : π ∘ₗ σ = id)
    (f : Module.End R M) :
    projectiveDet f = LinearMap.det (σ ∘ₗ f ∘ₗ π + (1 - σ ∘ₗ π)) := by
  rw [← splitEnd_apply π σ h]
  exact det_splitEnd_eq _ _ _ π σ h f

/-- The determinant of a composite is the product of the determinants. -/
@[simp]
theorem projectiveDet_comp (f g : Module.End R M) :
    projectiveDet (f ∘ₗ g) = projectiveDet f * projectiveDet g :=
  projectiveDet.map_mul f g

/-- The determinant of the identity is `1`. -/
@[simp]
theorem projectiveDet_id : projectiveDet (id : Module.End R M) = 1 :=
  projectiveDet.map_one

/-- The determinant of an endomorphism of a finite projective module commutes with base change:
the determinant of `f.baseChange A` is the image of the determinant of `f`. -/
@[simp]
theorem projectiveDet_baseChange (A : Type*) [CommRing A] [Algebra R A] (f : Module.End R M) :
    projectiveDet (f.baseChange A) = algebraMap R A (projectiveDet f) := by
  obtain ⟨n, π, σ, -, -, h⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  have hA : π.baseChange A ∘ₗ σ.baseChange A = id := by
    rw [← baseChange_comp, h, baseChange_id]
  rw [projectiveDet_eq_det_of_comp_eq_id _ _ hA, projectiveDet_eq_det_of_comp_eq_id π σ h,
    ← det_baseChange]
  simp [baseChange_add, baseChange_sub, baseChange_comp, baseChange_one]

/-- The determinant of an endomorphism of a finite projective module is invariant under
conjugation by a linear equivalence. -/
@[simp]
theorem projectiveDet_conj [Module.Finite R N] [Module.Projective R N] (f : Module.End R M)
    (e : M ≃ₗ[R] N) :
    projectiveDet ((e : M →ₗ[R] N) ∘ₗ f ∘ₗ (e.symm : N →ₗ[R] M)) = projectiveDet f := by
  obtain ⟨n, π, σ, -, -, h⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  have he : ((e : M →ₗ[R] N) ∘ₗ π) ∘ₗ (σ ∘ₗ (e.symm : N →ₗ[R] M)) = id := by
    ext x
    simp [← comp_apply π σ, h]
  rw [projectiveDet_eq_det_of_comp_eq_id _ _ he, projectiveDet_eq_det_of_comp_eq_id π σ h]
  congr 1
  ext x
  simp

/-- An endomorphism of a finite projective module is invertible if and only if its determinant is
a unit. -/
theorem isUnit_iff_isUnit_projectiveDet (f : Module.End R M) :
    IsUnit f ↔ IsUnit (projectiveDet f) := by
  obtain ⟨n, π, σ, -, -, h⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  rw [projectiveDet_eq_det_of_comp_eq_id π σ h, ← splitEnd_apply π σ h,
    ← isUnit_iff_isUnit_det, isUnit_splitEnd_iff]

end Projective

/-- On a free module of finite rank, `projectiveDet` is the determinant `LinearMap.det`. -/
@[simp]
theorem projectiveDet_eq_det [Module.Free R M] (f : Module.End R M) :
    projectiveDet f = LinearMap.det f := by
  rw [projectiveDet_eq_det_of_comp_eq_id id id (id_comp _)]
  simp [Module.End.one_eq_id]

end LinearMap
