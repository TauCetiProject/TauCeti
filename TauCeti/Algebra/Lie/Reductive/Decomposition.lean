/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import TauCeti.Algebra.Lie.Prod
public import TauCeti.Algebra.Lie.Solvable.Basic
import TauCeti.LinearAlgebra.Eigenspace.Transport

/-!
# Automorphism decomposition on `Z(L) ⊕ [L, L]`

When the centre `Z(L)` and derived ideal `[L, L]` of a Lie algebra `L` are complementary,
`LieEquiv.ofIsCompl` reconstructs an automorphism of `L` from automorphisms of `Z(L)` and `[L, L]`.
This file records the restriction and uniqueness laws for that reconstruction, as well as the
eigenspace splitting `LieEquiv.eigenspaceCenterDerivedEquiv` for an arbitrary scalar, independently
of any Cartan-involution predicate.

## Main results

* `LieEquiv.centerCongr_ofIsCompl`: restricting `LieEquiv.ofIsCompl h θZ θD` to `Z(L)` recovers
  `θZ`.
* `LieEquiv.derivedSeriesCongr_ofIsCompl`: restricting `LieEquiv.ofIsCompl h θZ θD` to `[L, L]`
  recovers `θD`.
* `LieEquiv.eq_ofIsCompl_centerCongr_derivedSeriesCongr`: any automorphism of `L = Z(L) ⊕ [L, L]`
  equals the reconstruction from its restrictions to `Z(L)` and `[L, L]`.
* `LieEquiv.eigenspaceCenterDerivedEquiv`, `LieEquiv.coe_eigenspaceCenterDerivedEquiv_apply`:
  addition identifies the product of the `μ`-eigenspaces on `Z(L)` and `[L, L]` with the
  `μ`-eigenspace on `L`.
-/

public section

open LieAlgebra

namespace LieEquiv

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- Restricting `ofIsCompl` on `Z(L) ⊕ [L, L]` to the centre recovers `θZ`. -/
@[simp]
theorem centerCongr_ofIsCompl (h : IsCompl (center R L) (derivedSeries R L 1))
    (θZ : center R L ≃ₗ⁅R⁆ center R L) (θD : derivedSeries R L 1 ≃ₗ⁅R⁆ derivedSeries R L 1) :
    (ofIsCompl h θZ θD).centerCongr = θZ := by
  ext x
  simp

/-- Restricting `ofIsCompl` on `Z(L) ⊕ [L, L]` to the derived ideal recovers `θD`. -/
@[simp]
theorem derivedSeriesCongr_ofIsCompl (h : IsCompl (center R L) (derivedSeries R L 1))
    (θZ : center R L ≃ₗ⁅R⁆ center R L) (θD : derivedSeries R L 1 ≃ₗ⁅R⁆ derivedSeries R L 1) :
    (ofIsCompl h θZ θD).derivedSeriesCongr 1 = θD := by
  ext x
  simp

/-- Any automorphism of `L = Z(L) ⊕ [L, L]` is determined by its restrictions to the centre and
the derived ideal. -/
theorem eq_ofIsCompl_centerCongr_derivedSeriesCongr (θ : L ≃ₗ⁅R⁆ L)
    (h : IsCompl (center R L) (derivedSeries R L 1)) :
    θ = ofIsCompl h θ.centerCongr (θ.derivedSeriesCongr 1) := by
  ext x
  obtain ⟨⟨z, d⟩, rfl⟩ :=
    (LieIdeal.prodEquivOfIsCompl (center R L) (derivedSeries R L 1) h).surjective x
  simp [map_add]

/-- When `L = Z(L) ⊕ [L, L]`, addition identifies the product of the `μ`-eigenspaces of an
automorphism restricted to `Z(L)` and `[L, L]` with its `μ`-eigenspace on `L`. -/
noncomputable def eigenspaceCenterDerivedEquiv (θ : L ≃ₗ⁅R⁆ L)
    (h : IsCompl (center R L) (derivedSeries R L 1)) (μ : R) :
    (Module.End.eigenspace (θ.centerCongr.toLinearEquiv : Module.End R (center R L)) μ ×
      Module.End.eigenspace
        ((θ.derivedSeriesCongr 1).toLinearEquiv : Module.End R (derivedSeries R L 1)) μ) ≃ₗ[R]
      Module.End.eigenspace (θ.toLinearEquiv : Module.End R L) μ :=
  let fZ : Module.End R (center R L) := θ.centerCongr.toLinearEquiv
  let fD : Module.End R (derivedSeries R L 1) := (θ.derivedSeriesCongr 1).toLinearEquiv
  let fL : Module.End R L := θ.toLinearEquiv
  let a := (LieIdeal.prodEquivOfIsCompl (center R L) (derivedSeries R L 1) h).toLinearEquiv
  have hprod : Module.End.eigenspace (fZ.prodMap fD) μ =
      (Module.End.eigenspace fZ μ).prod (Module.End.eigenspace fD μ) := by
    rw [Module.End.eigenspace_def, Module.End.eigenspace_def, Module.End.eigenspace_def,
      ← LinearMap.ker_prodMap]
    congr 1
  have hinter : ∀ p, a ((fZ.prodMap fD) p) = fL (a p) := fun ⟨z, d⟩ ↦ by
    simp [a, fZ, fD, fL, map_add]
  have hmap : (Module.End.eigenspace (fZ.prodMap fD) μ).map (a : _ →ₗ[R] L) =
      Module.End.eigenspace fL μ := by
    rw [TauCeti.eigenspace_eq_comap_of_intertwine hinter μ,
      Submodule.map_comap_eq_of_surjective a.surjective]
  ((Submodule.prodEquiv (Module.End.eigenspace fZ μ) (Module.End.eigenspace fD μ)).symm.trans
    (LinearEquiv.ofEq _ _ hprod.symm)).trans
    (a.ofSubmodules _ _ hmap)

/-- `eigenspaceCenterDerivedEquiv` acts by addition in `L`. -/
@[simp]
theorem coe_eigenspaceCenterDerivedEquiv_apply (θ : L ≃ₗ⁅R⁆ L)
    (h : IsCompl (center R L) (derivedSeries R L 1)) (μ : R)
    (p : Module.End.eigenspace (θ.centerCongr.toLinearEquiv : Module.End R (center R L)) μ ×
      Module.End.eigenspace
        ((θ.derivedSeriesCongr 1).toLinearEquiv : Module.End R (derivedSeries R L 1)) μ) :
    (θ.eigenspaceCenterDerivedEquiv h μ p : L) = (p.1.val : L) + (p.2.val : L) := by
  unfold eigenspaceCenterDerivedEquiv
  dsimp only
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.ofSubmodules,
    LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply, LinearEquiv.submoduleMap_apply,
    LinearEquiv.coe_ofEq_apply]
  exact LieIdeal.prodEquivOfIsCompl_apply (center R L) (derivedSeries R L 1) h
    (p.1.val, p.2.val)

end LieEquiv
