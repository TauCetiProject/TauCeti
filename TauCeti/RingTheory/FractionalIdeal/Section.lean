/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.FractionalIdeal.Operations

import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Finiteness.Basic
import TauCeti.Algebra.Module.Torsion.Localization

/-!
# Fractional ideal of a generic section

A nonzero vector in the generic fibre of a finite rank-one module identifies that fibre with
the fraction field. The image of the integral module in these coordinates is a fractional ideal.
For a torsion-free module the coordinate map identifies the integral module with this ideal.
-/

public noncomputable section

open scoped TensorProduct nonZeroDivisors

namespace TauCeti.FractionalIdeal

open _root_.FractionalIdeal

variable {R K M : Type*} [CommRing R] [Field K] [Algebra R K]
  [AddCommGroup M] [Module R M]

/-- The coordinates of integral vectors in the basis given by a generic section. -/
private def sectionCoordinates (hM : Module.finrank K (K ⊗[R] M) = 1)
    {t : K ⊗[R] M} (ht : t ≠ 0) : M →ₗ[R] K :=
  (((FiniteDimensional.basisSingleton Unit hM t ht).coord ()).restrictScalars R).comp
    (TensorProduct.mk R K M 1)

private theorem sectionCoordinates_smul (hM : Module.finrank K (K ⊗[R] M) = 1)
    {t : K ⊗[R] M} (ht : t ≠ 0) (x : M) :
    sectionCoordinates hM ht x • t = 1 ⊗ₜ[R] x := by
  simpa [sectionCoordinates, Module.Basis.coord_apply] using
    (FiniteDimensional.basisSingleton Unit hM t ht).sum_repr (1 ⊗ₜ[R] x)

variable [IsFractionRing R K] [Module.Finite R M]

/-- The fractional ideal of scalars `a` for which `a • t` lies in the image of the integral
module `M`, where `t` is a nonzero section of its rank-one generic fibre. -/
def ofSection (hM : Module.finrank K (K ⊗[R] M) = 1) {t : K ⊗[R] M} (ht : t ≠ 0) :
    FractionalIdeal R⁰ K :=
  ⟨LinearMap.range (sectionCoordinates hM ht),
    isFractional_of_fg (Submodule.fg_range _)⟩

/-- A scalar is in the fractional ideal of `t` exactly when its multiple of `t` is integral. -/
theorem mem_ofSection_iff (hM : Module.finrank K (K ⊗[R] M) = 1) {t : K ⊗[R] M}
    (ht : t ≠ 0) {a : K} :
    a ∈ ofSection hM ht ↔ ∃ x : M, a • t = 1 ⊗ₜ[R] x := by
  -- Membership in the fractional ideal is membership in its defining range.
  change (∃ x : M, sectionCoordinates hM ht x = a) ↔ _
  refine ⟨fun ⟨x, hx⟩ ↦ ⟨x, hx ▸ sectionCoordinates_smul hM ht x⟩, ?_⟩
  rintro ⟨x, hx⟩
  exact ⟨x, smul_left_injective K ht ((sectionCoordinates_smul hM ht x).trans hx.symm)⟩

/-- The fractional ideal of a nonzero generic section is nonzero, by clearing denominators. -/
theorem ofSection_ne_zero (hM : Module.finrank K (K ⊗[R] M) = 1) {t : K ⊗[R] M}
    (ht : t ≠ 0) : ofSection hM ht ≠ 0 := by
  obtain ⟨⟨x, s⟩, hs⟩ := IsLocalizedModule.surj R⁰ (TensorProduct.mk R K M 1) t
  have ha : algebraMap R K s ∈ ofSection hM ht :=
    (mem_ofSection_iff hM ht).2 ⟨x, by simpa [Submonoid.smul_def, algebraMap_smul] using hs⟩
  intro h
  exact (IsLocalization.map_units K s).ne_zero (by simpa [h] using ha)

/-- The coefficient ideal changes by the inverse principal ideal when its generic section
is scaled. -/
theorem ofSection_smul (hM : Module.finrank K (K ⊗[R] M) = 1) {t : K ⊗[R] M}
    (ht : t ≠ 0) {a : K} (ha : a ≠ 0) :
    ofSection hM (smul_ne_zero ha ht) = spanSingleton R⁰ a⁻¹ * ofSection hM ht := by
  refine eq_spanSingleton_mul.2 ⟨?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx⟩ := (mem_ofSection_iff hM (smul_ne_zero ha ht)).1 hy
    exact ⟨y * a, (mem_ofSection_iff hM ht).2 ⟨x, by simpa only [smul_smul] using hx⟩,
      by rw [mul_left_comm, inv_mul_cancel₀ ha, mul_one]⟩
  · intro y hy
    obtain ⟨x, hx⟩ := (mem_ofSection_iff hM ht).1 hy
    exact (mem_ofSection_iff hM (smul_ne_zero ha ht)).2
      ⟨x, by simpa only [smul_smul, mul_assoc, mul_left_comm a⁻¹ y, inv_mul_cancel₀ ha,
        mul_one] using hx⟩

/-- For a torsion-free rank-one module, taking coordinates in the generic section gives an
isomorphism onto its fractional ideal. -/
def linearEquivOfSection [Module.IsTorsionFree R M] (hM : Module.finrank K (K ⊗[R] M) = 1)
    {t : K ⊗[R] M} (ht : t ≠ 0) : M ≃ₗ[R] ofSection hM ht :=
  LinearEquiv.ofInjective (sectionCoordinates hM ht) fun x y h ↦
    Module.IsTorsionFree.mk_one_injective_of_isFractionRing K
      ((sectionCoordinates_smul hM ht x).symm.trans
        ((congrArg (· • t) h).trans (sectionCoordinates_smul hM ht y)))

/-- The coordinate of an integral vector times the chosen generic section recovers the
vector in the generic fibre. -/
@[simp]
theorem linearEquivOfSection_apply_smul [Module.IsTorsionFree R M]
    (hM : Module.finrank K (K ⊗[R] M) = 1) {t : K ⊗[R] M} (ht : t ≠ 0) (x : M) :
    (linearEquivOfSection hM ht x : K) • t = 1 ⊗ₜ[R] x :=
  sectionCoordinates_smul hM ht x

/-- An integral section has coordinate one in the basis it induces on the generic fibre. -/
@[simp]
theorem coe_linearEquivOfSection_one_tmul [Module.IsTorsionFree R M]
    (hM : Module.finrank K (K ⊗[R] M) = 1) {x : M} (ht : (1 : K) ⊗ₜ[R] x ≠ 0) :
    (linearEquivOfSection hM ht x : K) = 1 :=
  smul_left_injective K ht ((linearEquivOfSection_apply_smul hM ht x).trans (one_smul K _).symm)

end TauCeti.FractionalIdeal
