/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import TauCeti.LinearAlgebra.SesquilinearForm.DualSubmodule
import TauCeti.RingTheory.DedekindDomain.Different.Basic

/-!
# Pairings of vectors in the trace dual of a number field lattice

If a nonzero ideal `J` carries the integral dual of a lattice into the lattice itself, the pairing
of two vectors in its rational trace dual belongs to `(𝔇² J)⁻¹`, where `𝔇` is the absolute
different. For a positive definite Hermitian lattice this controls the denominator of the
self-pairing, so a field norm estimate gives a lower bound for the trace length.

The denominator calculation is the one used for short bases in
`grh/src/Lib/Adelic/Reduction/FirstMinimumShortBases.lean` of
[lsernau/grh-lean][short-proof].

[short-proof]: https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207
-/

public section

open scoped NumberField nonZeroDivisors
open FractionalIdeal

namespace LinearMap

variable {K V : Type*} [Field K] [NumberField K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

/-- A linear functional is trace-integral on an integer submodule exactly when it takes
that submodule into the inverse different. -/
theorem forall_trace_apply_mem_range_iff (f : V →ₗ[K] K) (L : Submodule (𝓞 K) V) :
    (∀ z ∈ L, Algebra.trace ℚ K (f z) ∈ (algebraMap ℤ ℚ).range) ↔
      ∀ z ∈ L, f z ∈ (↑(differentIdeal ℤ (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
  let M := L.map (f.restrictScalars (𝓞 K))
  have h := (Submodule.le_traceDual_iff_map_le_one
    (A := ℤ) (K := ℚ) (I := M) (J := (1 : Submodule (𝓞 K) K))).symm
  rw [mul_one, ← coeToSubmodule_dual_one, ← inv_inv (dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K)),
    ← coeIdeal_differentIdeal ℤ ℚ K] at h
  simp only [M, Submodule.restrictScalars_map] at h
  rw [Submodule.map_le_iff_le_comap, Submodule.map_le_iff_le_comap,
    Submodule.map_le_iff_le_comap] at h
  simpa only [IsConcreteLE.le_iff, Submodule.mem_comap, Submodule.restrictScalars_mem,
    LinearMap.restrictScalars_apply, Submodule.mem_one, RingHom.mem_range,
    mem_coeToSubmodule] using h

variable {σ : K ≃ₐ[ℚ] K} (B : V →ₛₗ[σ.toRingHom] V →ₗ[K] K)
  {hσ : ∀ r : 𝓞 K, σ (algebraMap (𝓞 K) K r) ∈ (1 : Submodule (𝓞 K) K)}

/-- Multiplying a trace-dual vector by a scalar whose image under `σ` lies in the different
places the vector in the integral dual for the original sesquilinear form. -/
theorem smul_mem_dualSubmodule_of_forall_trace_mem {L : Submodule (𝓞 K) V} {x : V} {a : K}
    (hx : ∀ z ∈ L, Algebra.trace ℚ K (B x z) ∈ (algebraMap ℤ ℚ).range)
    (ha : σ a ∈ (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)) :
    a • x ∈ B.dualSubmodule hσ L := by
  apply mem_dualSubmodule.mpr
  intro z hz
  have hx' := ((B x).forall_trace_apply_mem_range_iff L).mp hx z hz
  rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, ← coeToSubmodule_one, mem_coeToSubmodule,
    mul_comm]
  exact (mem_inv_iff (by simp [coeIdeal_differentIdeal ℤ ℚ K])).mp hx' _ ha

/-- If `J` carries the integral dual into `L`, the original pairing of two trace-dual
vectors belongs to the inverse of `𝔇² J`. No nondegeneracy or positivity of the form
is needed for this denominator bound. -/
theorem apply_mem_inv_differentIdeal_sq_mul_of_forall_trace_mem {L : Submodule (𝓞 K) V}
    {J : Ideal (𝓞 K)} (hJ₀ : J ≠ ⊥) (hJ : J • B.dualSubmodule hσ L ≤ L) {x y : V}
    (hx : ∀ z ∈ L, Algebra.trace ℚ K (B x z) ∈ (algebraMap ℤ ℚ).range)
    (hy : ∀ z ∈ L, Algebra.trace ℚ K (B y z) ∈ (algebraMap ℤ ℚ).range) :
    B x y ∈ ((↑(differentIdeal ℤ (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ^ 2 *
      (J : FractionalIdeal (𝓞 K)⁰ K))⁻¹ := by
  let D : FractionalIdeal (𝓞 K)⁰ K := differentIdeal ℤ (𝓞 K)
  have hD : D ≠ 0 := by simp [D, coeIdeal_differentIdeal ℤ ℚ K]
  rw [mem_inv_iff (mul_ne_zero (pow_ne_zero _ hD) (coeIdeal_eq_zero.not.mpr hJ₀))]
  intro w hw
  rw [pow_two, mul_assoc] at hw
  have hadd {u v : K} (hu : B x y * u ∈ (1 : FractionalIdeal (𝓞 K)⁰ K))
      (hv : B x y * v ∈ (1 : FractionalIdeal (𝓞 K)⁰ K)) :
      B x y * (u + v) ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [mul_add, ← mem_coeToSubmodule]
    exact add_mem (mem_coeToSubmodule.mpr hu) (mem_coeToSubmodule.mpr hv)
  refine FractionalIdeal.mul_induction_on hw (fun a ha w hw ↦ ?_) (fun _ _ ↦ hadd)
  -- Use `σ⁻¹ a` on the first side so semilinearity contributes the factor `a`.
  have ha_dual := B.smul_mem_dualSubmodule_of_forall_trace_mem (hσ := hσ) hx
    (by simpa only [σ.apply_symm_apply] using ha : σ (σ.symm a) ∈ D)
  refine FractionalIdeal.mul_induction_on hw (fun b hb c hc ↦ ?_) (fun u v hu hv ↦ ?_)
  · obtain ⟨j, hj, rfl⟩ := (mem_coeIdeal _).mp hc
    have hbσ : σ b ∈ D := by
      obtain ⟨r, hr, rfl⟩ := (mem_coeIdeal _).mp hb
      refine (mem_coeIdeal _).mpr ⟨galRestrict ℤ ℚ K (𝓞 K) σ r,
        TauCeti.galRestrict_apply_mem_differentIdeal_iff.mpr hr, ?_⟩
      exact algebraMap_galRestrict_apply ℤ σ r
    have hb_dual := B.smul_mem_dualSubmodule_of_forall_trace_mem (hσ := hσ) hy hbσ
    have h := mem_dualSubmodule.mp ha_dual _ (hJ (Submodule.smul_mem_smul hj hb_dual))
    have hσa : σ.toRingHom (σ.symm a) = a := σ.apply_symm_apply a
    simp only [← algebraMap_smul K j, map_smulₛₗ, LinearMap.smul_apply, RingHom.id_apply,
      hσa, smul_eq_mul] at h
    rw [← mem_coeToSubmodule, coeToSubmodule_one]
    convert h using 1
    ac_rfl
  · rw [mul_add a]
    exact hadd hu hv

end LinearMap
