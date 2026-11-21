/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Primitive.Basic
import TauCeti.LinearAlgebra.FreeModule.PID

/-!
# Primitive vectors in submodules and images of integer linear maps

A submodule `N` of a free integer module `M` contains a primitive vector of `M` if and only if no
prime `p` divides every element of `N` in `M`. Applied to `LinearMap.range f`, an integer-linear
map `f : L →ₗ[ℤ] M` into a free integer module hits a primitive vector if and only if no prime
divides every value of `f` in `M`.

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

/-- A submodule of a free integer module contains a primitive ambient vector if and only if it is
not globally divisible in the ambient module by any prime. No finite-rank assumption on the
ambient free module is needed. -/
theorem exists_isPrimitive_iff
    {M : Type*} [AddCommGroup M] [Module.Free ℤ M] (N : Submodule ℤ M) :
    (∃ v ∈ N, TauCeti.IsPrimitive v) ↔
      ∀ p : ℕ, p.Prime → ∃ v ∈ N, ¬ ∃ w : M, p • w = v := by
  constructor
  · rintro ⟨v, hvN, hv⟩ p hp
    exact ⟨v, hvN, fun ⟨w, hw⟩ => hp.ne_one (hv.eq_one_of_eq_nsmul hw.symm)⟩
  · intro hdiv
    classical
    obtain ⟨ϕ, hϕ⟩ := N.exists_forall_map_le
    obtain ⟨y, hyN, hϕy⟩ := Submodule.mem_map.mp (generator_mem (N.map ϕ))
    set a : ℤ := generator (N.map ϕ)
    by_cases hunit : IsUnit a
    · obtain ⟨u, hu⟩ := hunit
      refine ⟨y, hyN, TauCeti.isPrimitive_def.mpr ⟨(↑u⁻¹ : ℤ) • ϕ, ?_⟩⟩
      rw [LinearMap.smul_apply, smul_eq_mul, hϕy, ← hu, Units.inv_mul]
    · have hne1 : a.natAbs ≠ 1 := fun h1 => hunit (Int.isUnit_iff_natAbs_eq.mpr h1)
      let p : ℕ := a.natAbs.minFac
      have hp : p.Prime := Nat.minFac_prime hne1
      have hpa : (p : ℤ) ∣ a :=
        Int.dvd_trans (Int.natCast_dvd_natCast.mpr (Nat.minFac_dvd a.natAbs)) Int.natAbs_dvd_self
      obtain ⟨v, hvN, hv⟩ := hdiv p hp
      exfalso
      apply hv
      let b := Module.Free.chooseBasis ℤ M
      have hcoord (i) : (p : ℤ) ∣ b.repr v i :=
        dvd_trans hpa ((mem_iff_generator_dvd (N.map ϕ)).mp (hϕ (b.coord i) (mem_map_of_mem hvN)))
      refine ⟨b.repr.symm ((b.repr v).mapRange (· / (p : ℤ)) (Int.zero_ediv _)), ?_⟩
      rw [← Nat.cast_smul_eq_nsmul ℤ p]
      apply b.repr.injective
      ext i
      simp [Int.mul_ediv_cancel' (hcoord i)]

end Submodule

namespace LinearMap

/-- An integer-linear map into a free integer module takes a primitive value if and only if no
prime divides all of its values in the codomain. -/
theorem exists_isPrimitive_apply_iff
    {L M : Type*} [AddCommGroup L] [AddCommGroup M] [Module.Free ℤ M] (f : L →ₗ[ℤ] M) :
    (∃ x : L, TauCeti.IsPrimitive (f x)) ↔
      ∀ p : ℕ, p.Prime → ∃ x : L, ¬ ∃ w : M, p • w = f x := by
  simpa [exists_exists_eq_and] using (LinearMap.range f).exists_isPrimitive_iff

end LinearMap
