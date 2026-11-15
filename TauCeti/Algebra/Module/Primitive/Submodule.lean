/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Primitive.Basic

/-!
# Primitive vectors in submodules and images of integer linear maps

A submodule `N` of a free integer module `M` contains a primitive vector of `M` if and only if `N`
is nonzero and no prime `p` divides every element of `N` in `M`. Applied to `LinearMap.range f`, an
integer-linear map `f : L →ₗ[ℤ] M` into a free integer module hits a primitive vector if and only
if `f ≠ 0` and no prime divides every value of `f` in `M`.

Both characterizations hold at arbitrary (possibly infinite) rank without any finite-generation
hypothesis. Freeness of `M` is essential: the torsion group `⨁_{p prime} ZMod p` is nonzero and not
globally divisible by any single prime, yet admits no nonzero homomorphism to `ℤ`.

## Main results

* `Submodule.exists_isPrimitive_iff`: characterization of submodules of a free `ℤ`-module
  containing a primitive ambient vector.
* `LinearMap.exists_isPrimitive_apply_iff`: characterization of `ℤ`-linear maps into a free
  `ℤ`-module whose image contains a primitive vector.
-/

public section

namespace Submodule

open Submodule.IsPrincipal

private theorem dvd_apply_of_maximal_map
    {M : Type*} [AddCommGroup M] {N : Submodule ℤ M}
    {ϕ : M →ₗ[ℤ] ℤ} (hϕ : ∀ ψ : M →ₗ[ℤ] ℤ, ¬N.map ϕ < N.map ψ)
    {y : M} (hyN : y ∈ N) (hϕy : ϕ y = generator (N.map ϕ)) (ψ : M →ₗ[ℤ] ℤ) :
    generator (N.map ϕ) ∣ ψ y := by
  let a : ℤ := generator (N.map ϕ)
  let I : Ideal ℤ := Ideal.span {a, ψ y}
  let d : ℤ := generator I
  have hd_left : d ∣ a := (mem_iff_generator_dvd I).mp (Ideal.subset_span (by simp))
  have hd_right : d ∣ ψ y := (mem_iff_generator_dvd I).mp (Ideal.subset_span (by simp))
  obtain ⟨r₁, r₂, hd⟩ : ∃ r₁ r₂ : ℤ, r₁ * a + r₂ * ψ y = d := by
    simpa [mul_comm] using Submodule.mem_span_pair.mp (generator_mem I)
  let ψ' : M →ₗ[ℤ] ℤ := r₁ • ϕ + r₂ • ψ
  have hd_mem : d ∈ N.map ψ' := ⟨y, hyN, by simpa [ψ', a, hϕy] using hd⟩
  have hle : N.map ϕ ≤ N.map ψ' := by
    rw [← span_singleton_generator (N.map ϕ)]
    exact (Ideal.span_singleton_le_span_singleton.mpr hd_left).trans
      ((Submodule.span_singleton_le_iff_mem d (N.map ψ')).mpr hd_mem)
  have hmap : N.map ψ' = N.map ϕ := (hle.eq_of_not_lt (hϕ ψ')).symm
  have ha_dvd_d : a ∣ d := (mem_iff_generator_dvd (N.map ϕ)).mp (hmap ▸ hd_mem)
  exact dvd_trans ha_dvd_d hd_right

private theorem exists_linearMap_apply_eq_and_dvd
    {M : Type*} [AddCommGroup M] [Module.Free ℤ M] {N : Submodule ℤ M} (hN : N ≠ ⊥) :
    ∃ (ϕ : M →ₗ[ℤ] ℤ) (a : ℤ) (y : M),
      y ∈ N ∧ a ≠ 0 ∧ ϕ y = a ∧ ∀ (ψ : M →ₗ[ℤ] ℤ), ∀ x ∈ N, a ∣ ψ x := by
  obtain ⟨I, hI, hmax⟩ :=
    set_has_maximal_iff_noetherian.mpr (inferInstance : IsNoetherian ℤ ℤ)
      (Set.range fun ψ : M →ₗ[ℤ] ℤ => N.map ψ) ⟨_, ⟨0, rfl⟩⟩
  obtain ⟨ϕ, rfl⟩ := hI
  have hϕ : ∀ ψ : M →ₗ[ℤ] ℤ, ¬N.map ϕ < N.map ψ := fun ψ hlt => hmax _ ⟨ψ, rfl⟩ hlt
  let a : ℤ := generator (N.map ϕ)
  have ha0 : a ≠ 0 := fun hzero =>
    hN (eq_bot_of_generator_maximal_map_eq_zero (Module.Free.chooseBasis ℤ M) hϕ hzero)
  obtain ⟨y, hyN, hϕy⟩ := Submodule.mem_map.mp (generator_mem (N.map ϕ))
  refine ⟨ϕ, a, y, hyN, ha0, hϕy, fun ψ x hxN => ?_⟩
  obtain ⟨q, hq⟩ := (mem_iff_generator_dvd (N.map ϕ)).mp (Submodule.mem_map_of_mem hxN)
  have hdvd_y : a ∣ ψ y := dvd_apply_of_maximal_map hϕ hyN hϕy ψ
  have hzN : y + (x - q • y) ∈ N := N.add_mem hyN (N.sub_mem hxN (N.smul_mem q hyN))
  have hϕz : ϕ (y + (x - q • y)) = a := by
    rw [map_add, map_sub, map_smul, hϕy, hq, smul_eq_mul]
    ring
  have hdvd_z : a ∣ ψ y + (ψ x - q * ψ y) := by
    simpa [map_add, map_sub, map_smul] using dvd_apply_of_maximal_map hϕ hzN hϕz ψ
  have hdvd_sub : a ∣ ψ x - q * ψ y := (dvd_add_right hdvd_y).mp hdvd_z
  simpa using dvd_add hdvd_sub (dvd_mul_of_dvd_right hdvd_y q)

/-- A submodule of a free integer module contains a primitive ambient vector if and only if it is
nonzero and not globally divisible in the ambient module by any prime. No finite-rank assumption on
the ambient free module is needed. -/
theorem exists_isPrimitive_iff
    {M : Type*} [AddCommGroup M] [Module.Free ℤ M] (N : Submodule ℤ M) :
    (∃ v ∈ N, TauCeti.IsPrimitive v) ↔
      N ≠ ⊥ ∧ ∀ p : ℕ, p.Prime → ∃ v ∈ N, ¬ ∃ w : M, p • w = v := by
  constructor
  · rintro ⟨v, hvN, hv⟩
    refine ⟨?_, fun p hp => ⟨v, hvN, fun ⟨w, hw⟩ => hp.ne_one (hv.eq_one_of_eq_nsmul hw.symm)⟩⟩
    rintro rfl
    exact hv.ne_zero (by simpa using hvN)
  · rintro ⟨hN, hdiv⟩
    classical
    obtain ⟨ϕ, a, y, hyN, ha0, hϕy, hdvd⟩ := exists_linearMap_apply_eq_and_dvd hN
    by_cases hunit : IsUnit a
    · obtain ⟨u, rfl⟩ := hunit
      refine ⟨y, hyN, TauCeti.isPrimitive_def.mpr ⟨(↑u⁻¹ : ℤ) • ϕ, ?_⟩⟩
      rw [LinearMap.smul_apply, smul_eq_mul, hϕy, Units.inv_mul]
    · have hne1 : a.natAbs ≠ 1 := fun h1 => hunit (Int.isUnit_iff_natAbs_eq.mpr h1)
      let p : ℕ := a.natAbs.minFac
      have hp : p.Prime := Nat.minFac_prime hne1
      have hpa : (p : ℤ) ∣ a :=
        Int.dvd_trans (Int.natCast_dvd_natCast.mpr (Nat.minFac_dvd a.natAbs)) Int.natAbs_dvd_self
      obtain ⟨v, hvN, hv⟩ := hdiv p hp
      exfalso
      apply hv
      let b := Module.Free.chooseBasis ℤ M
      have hcoord (i) : (p : ℤ) ∣ b.repr v i := dvd_trans hpa (hdvd (b.coord i) v hvN)
      refine ⟨b.repr.symm ((b.repr v).mapRange (· / (p : ℤ)) (Int.zero_ediv _)), ?_⟩
      rw [← Nat.cast_smul_eq_nsmul ℤ p]
      apply b.repr.injective
      ext i
      simp [Int.mul_ediv_cancel' (hcoord i)]

end Submodule

namespace LinearMap

/-- An integer-linear map into a free integer module takes a primitive value if and only if it is
nonzero and no prime divides all of its values in the codomain. -/
theorem exists_isPrimitive_apply_iff
    {L M : Type*} [AddCommGroup L] [AddCommGroup M] [Module.Free ℤ M] (f : L →ₗ[ℤ] M) :
    (∃ x : L, TauCeti.IsPrimitive (f x)) ↔
      f ≠ 0 ∧ ∀ p : ℕ, p.Prime → ∃ x : L, ¬ ∃ w : M, p • w = f x := by
  simpa [LinearMap.range_eq_bot, exists_exists_eq_and] using
    (LinearMap.range f).exists_isPrimitive_iff

end LinearMap
