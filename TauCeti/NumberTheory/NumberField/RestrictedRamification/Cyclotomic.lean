/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.RestrictedRamification.Roots
public import TauCeti.Topology.Algebra.Group.Profinite.Order
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import TauCeti.NumberTheory.NumberField.Cyclotomic.Finrank

/-!
# Cyclotomic extensions inside `K_S` and the primes dividing `[K_S : K]`

Let `K` be a number field, `Ω` an extension of `K` and `S` a set of finite places of `K`. If every
`n ∈ T` is a unit at each finite place outside `S`, the roots of unity of orders in `T` lie in the
maximal extension `K_S` of `K` unramified outside `S`
(`TauCeti.RestrictedRamification.adjoin_setOf_pow_eq_one_le_maxUnramifiedOutside`). In particular,
if `S` contains the places above `ℓ ≠ 0`, then `K(μ_{ℓ^∞}) ≤ K_S`
(`TauCeti.RestrictedRamification.adjoin_setOf_pow_pow_eq_one_le_maxUnramifiedOutside`).

The degrees `[K(μ_{ℓ^m}) : K]` have unbounded `ℓ`-adic valuation
(`IsPrimitiveRoot.pow_dvd_finrank_adjoin`). When `Ω` is separably closed and normal over `K`,
the finite Galois subextensions `K(μ_{ℓ^m})` of `K_S` give finite quotients of `G_{K,S}` of these
orders, so `ℓ^∞` divides the supernatural order of `G_{K,S}`
(`TauCeti.RestrictedRamification.profiniteOrder_galoisGroupS_apply_eq_top`): `ℓ` lies in the set
`P` of primes `ℓ` with `ℓ^∞ ∣ [K_S : K]`.

## Main results

* `TauCeti.RestrictedRamification.adjoin_setOf_pow_eq_one_le_maxUnramifiedOutside`: roots of
  unity of orders that are units outside `S` generate a subfield of `K_S`.
* `TauCeti.RestrictedRamification.adjoin_setOf_pow_pow_eq_one_le_maxUnramifiedOutside`:
  `K(μ_{ℓ^∞}) ≤ K_S` when `S` contains the places above `ℓ`.
* `TauCeti.RestrictedRamification.profiniteOrder_galoisGroupS_apply_eq_top`: `ℓ ∈ P`, that is,
  the `ℓ`-part of the supernatural order of `G_{K,S}` is `ℓ^∞`.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., Chapter I, §4.
-/

public section

open IntermediateField IsDedekindDomain Module

open scoped NumberField

namespace TauCeti.RestrictedRamification

variable {K Ω : Type*} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))}

/-- **Roots of unity lie in `K_S`.** If every `n ∈ T` is nonzero and lies in no finite place
outside `S`, the field generated over `K` by the `n`-th roots of unity, `n ∈ T`, lies in `K_S`. -/
theorem adjoin_setOf_pow_eq_one_le_maxUnramifiedOutside {T : Set ℕ} (hT : 0 ∉ T)
    (h : ∀ n ∈ T, ∀ v ∉ S, (n : 𝓞 K) ∉ v.asIdeal) :
    adjoin K {x : Ω | ∃ n ∈ T, x ^ n = 1} ≤ maxUnramifiedOutside K Ω S := by
  rw [adjoin_le_iff]
  rintro x ⟨n, hn, hx⟩
  exact mem_maxUnramifiedOutside_of_pow_eq_one hx (fun h0 ↦ hT (h0 ▸ hn)) (h n hn)

/-- **`K(μ_{ℓ^∞}) ≤ K_S`.** If `ℓ ≠ 0` lies in no finite place outside `S`, the field generated
over `K` by the roots of unity of order a power of `ℓ` lies in `K_S`. -/
theorem adjoin_setOf_pow_pow_eq_one_le_maxUnramifiedOutside {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    (h : ∀ v ∉ S, (ℓ : 𝓞 K) ∉ v.asIdeal) :
    adjoin K {x : Ω | ∃ n : ℕ, x ^ (ℓ ^ n) = 1} ≤ maxUnramifiedOutside K Ω S := by
  have := adjoin_setOf_pow_eq_one_le_maxUnramifiedOutside (K := K) (Ω := Ω) (S := S)
    (T := Set.range (ℓ ^ ·)) (fun ⟨n, hn⟩ ↦ pow_ne_zero n hℓ hn)
    (fun _ ⟨n, hn⟩ v hv hmem ↦ h v hv <| by
      rw [← hn, Nat.cast_pow] at hmem
      exact v.isPrime.mem_of_pow_mem n hmem)
  simpa only [Set.exists_range_iff] using this

/-- **`ℓ ∈ P`.** If `Ω` is separably closed and normal over `K`, and the finite places outside `S`
do not lie above the prime `ℓ`, then `ℓ^∞` divides the supernatural order of `G_{K,S}`: the
fields `K(μ_{ℓ^m}) ≤ K_S` give finite quotients of `G_{K,S}` of order divisible by any power
of `ℓ`. -/
theorem profiniteOrder_galoisGroupS_apply_eq_top [Normal K Ω] [IsSepClosed Ω] (ℓ : Nat.Primes)
    (h : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K) ∉ v.asIdeal) :
    profiniteOrder (galoisGroupS K Ω S) ℓ = ⊤ := by
  rw [profiniteOrder_apply_eq_top_iff]
  intro n
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  set N := (ℓ : ℕ) ^ (n + finrank ℚ K + 1) with hNdef
  have hN : N ≠ 0 := pow_ne_zero _ ℓ.prop.ne_zero
  have : NeZero N := ⟨hN⟩
  have : NeZero (N : Ω) := ⟨Nat.cast_ne_zero.2 hN⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot Ω N
  have hmem : ζ ∈ maxUnramifiedOutside K Ω S :=
    mem_maxUnramifiedOutside_of_pow_eq_one hζ.pow_eq_one hN fun v hv hv' ↦ h v hv <|
      v.isPrime.mem_of_pow_mem _ (by rwa [hNdef, Nat.cast_pow] at hv')
  let ζ' : maxUnramifiedOutside K Ω S := ⟨ζ, hmem⟩
  have hζ' : IsPrimitiveRoot ζ' N :=
    hζ.of_map_of_injective (f := (maxUnramifiedOutside K Ω S).val) Subtype.val_injective
  -- `K⟮ζ'⟯ / K` is Galois, so its fixing subgroup is normal.
  have := hζ'.intermediateField_adjoin_isCyclotomicExtension K
  have : IsGalois K K⟮ζ'⟯ := IsCyclotomicExtension.isGalois {N} K K⟮ζ'⟯
  let U : OpenNormalSubgroup (galoisGroupS K Ω S) :=
    { toSubgroup := K⟮ζ'⟯.fixingSubgroup
      isOpen' := K⟮ζ'⟯.fixingSubgroup_isOpen }
  refine ⟨U, ?_⟩
  rw [← Subgroup.index, ← finrank_eq_fixingSubgroup_index]
  exact hζ'.pow_dvd_finrank_adjoin ℓ.prop.ne_zero

end TauCeti.RestrictedRamification
