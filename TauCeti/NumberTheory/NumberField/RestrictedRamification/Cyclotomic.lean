/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.RestrictedRamification.Roots
public import TauCeti.Topology.Algebra.Group.Profinite.Order
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import TauCeti.FieldTheory.Galois.Restriction

/-!
# Cyclotomic extensions inside `K_S` and the primes dividing `[K_S : K]`

Let `K` be a number field, `Ω` an extension of `K` and `S` a set of finite places of `K`. If every
`n ∈ T` is a unit at each finite place outside `S`, the roots of unity of orders in `T` lie in the
maximal extension `K_S` of `K` unramified outside `S`
(`TauCeti.RestrictedRamification.adjoin_rootsOfUnity_le_maxUnramifiedOutside`). In particular, if
`S` contains the places above `ℓ ≠ 0`, then `K(μ_{ℓ^∞}) ≤ K_S`
(`TauCeti.RestrictedRamification.adjoin_powRootsOfUnity_le_maxUnramifiedOutside`).

The degrees `[K(μ_{ℓ^m}) : K]` have unbounded `ℓ`-adic valuation: `[ℚ(μ_{ℓ^m}) : ℚ] = φ(ℓ^m)`
divides `[K : ℚ] · [K(μ_{ℓ^m}) : K]`. When `Ω` is separably closed and normal over `K`, the
finite Galois subextensions `K(μ_{ℓ^m})` of `K_S` give finite quotients of `G_{K,S}` of these
orders, so `ℓ^∞` divides the supernatural order of `G_{K,S}`
(`TauCeti.RestrictedRamification.profiniteOrder_galoisGroupS_apply_eq_top`): `ℓ` lies in the set
`P` of primes `ℓ` with `ℓ^∞ ∣ [K_S : K]`.

## Main results

* `TauCeti.RestrictedRamification.adjoin_rootsOfUnity_le_maxUnramifiedOutside`: roots of unity of
  orders that are units outside `S` generate a subfield of `K_S`.
* `TauCeti.RestrictedRamification.adjoin_powRootsOfUnity_le_maxUnramifiedOutside`:
  `K(μ_{ℓ^∞}) ≤ K_S` when `S` contains the places above `ℓ`.
* `TauCeti.RestrictedRamification.totient_dvd_finrank_mul_finrank_adjoin`: for a primitive
  `N`-th root of unity `ζ`, `φ(N) ∣ [K : ℚ] · [K(ζ) : K]`.
* `TauCeti.RestrictedRamification.pow_dvd_finrank_adjoin_of_isPrimitiveRoot`: for a primitive
  `ℓ^(n + [K : ℚ] + 1)`-th root of unity `ζ`, `ℓ^n ∣ [K(ζ) : K]`.
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
theorem adjoin_rootsOfUnity_le_maxUnramifiedOutside {T : Set ℕ} (hT : 0 ∉ T)
    (h : ∀ n ∈ T, ∀ v ∉ S, (n : 𝓞 K) ∉ v.asIdeal) :
    adjoin K {x : Ω | ∃ n ∈ T, x ^ n = 1} ≤ maxUnramifiedOutside K Ω S := by
  rw [adjoin_le_iff]
  rintro x ⟨n, hn, hx⟩
  exact mem_maxUnramifiedOutside_of_pow_eq_one hx (fun h0 ↦ hT (h0 ▸ hn)) (h n hn)

/-- **`K(μ_{ℓ^∞}) ≤ K_S`.** If `ℓ ≠ 0` lies in no finite place outside `S`, the field generated
over `K` by the roots of unity of order a power of `ℓ` lies in `K_S`. -/
theorem adjoin_powRootsOfUnity_le_maxUnramifiedOutside {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    (h : ∀ v ∉ S, (ℓ : 𝓞 K) ∉ v.asIdeal) :
    adjoin K {x : Ω | ∃ n : ℕ, x ^ (ℓ ^ n) = 1} ≤ maxUnramifiedOutside K Ω S := by
  have := adjoin_rootsOfUnity_le_maxUnramifiedOutside (K := K) (Ω := Ω) (S := S)
    (T := Set.range (ℓ ^ ·)) (fun ⟨n, hn⟩ ↦ pow_ne_zero n hℓ hn)
    (fun _ ⟨n, hn⟩ v hv hmem ↦ h v hv <| by
      rw [← hn, Nat.cast_pow] at hmem
      exact v.isPrime.mem_of_pow_mem n hmem)
  simpa only [Set.exists_range_iff] using this

omit [NumberField K] in
/-- **Degrees of cyclotomic extensions.** If `ζ` is a primitive `N`-th root of unity in an
extension `E` of a field `K` of characteristic zero with `[K : ℚ]` finite, then
`φ(N) ∣ [K : ℚ] · [K(ζ) : K]`, since `[ℚ(ζ) : ℚ] = φ(N)`. -/
theorem totient_dvd_finrank_mul_finrank_adjoin [CharZero K] [FiniteDimensional ℚ K] {E : Type*}
    [Field E] [Algebra K E] {ζ : E} {N : ℕ} (hζ : IsPrimitiveRoot ζ N) (hN : 0 < N) :
    N.totient ∣ finrank ℚ K * finrank K K⟮ζ⟯ := by
  have hint : IsIntegral K ζ := hζ.isIntegral hN |>.tower_top
  have := adjoin.finiteDimensional hint
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  let ζ' : K⟮ζ⟯ := AdjoinSimple.gen K ζ
  have hζ' : IsPrimitiveRoot ζ' N := hζ.of_map_of_injective (f := K⟮ζ⟯.val) Subtype.val_injective
  rw [finrank_mul_finrank ℚ K K⟮ζ⟯, ← Polynomial.natDegree_cyclotomic N ℚ,
    Polynomial.cyclotomic_eq_minpoly_rat hζ' hN]
  exact minpoly.degree_dvd (hζ'.isIntegral hN).tower_top

/-- If `ℓ^(n + d) ∣ d * e` with `d ≠ 0`, then `ℓ^n ∣ e`: at each prime `p`, the exponent of `p`
in `d` is less than `d`. -/
private theorem pow_dvd_of_pow_add_dvd_mul {ℓ n d e : ℕ} (hd : d ≠ 0)
    (h : ℓ ^ (n + d) ∣ d * e) : ℓ ^ n ∣ e := by
  rcases eq_or_ne e 0 with rfl | he
  · exact dvd_zero _
  rcases eq_or_ne ℓ 0 with rfl | hℓ
  · rw [zero_pow (by omega), zero_dvd_iff, mul_eq_zero] at h
    exact absurd (h.resolve_left hd) he
  rw [← Nat.factorization_le_iff_dvd (pow_ne_zero _ hℓ) he]
  rw [← Nat.factorization_le_iff_dvd (pow_ne_zero _ hℓ) (mul_ne_zero hd he)] at h
  intro p
  have hp := h p
  have hdp := Nat.factorization_lt p hd
  simp only [Nat.factorization_pow, Nat.factorization_mul hd he, Finsupp.smul_apply, smul_eq_mul,
    Finsupp.add_apply] at hp ⊢
  rcases Nat.eq_zero_or_pos (ℓ.factorization p) with h0 | h0
  · simp [h0]
  nlinarith

/-- `ℓ^m ∣ φ(ℓ^(m + 1))`. -/
private theorem pow_dvd_totient_pow_succ (ℓ m : ℕ) : ℓ ^ m ∣ (ℓ ^ (m + 1)).totient := by
  induction m with
  | zero => exact one_dvd _
  | succ m ih =>
    rw [pow_succ' ℓ (m + 1), Nat.totient_mul_of_dvd (dvd_pow_self ℓ m.succ_ne_zero)]
    simpa only [pow_succ'] using mul_dvd_mul_left ℓ ih

omit [NumberField K] in
/-- **Cyclotomic degrees have unbounded `ℓ`-adic valuation.** If `ζ` is a primitive
`ℓ^(n + [K : ℚ] + 1)`-th root of unity over a field `K` of characteristic zero with `[K : ℚ]`
finite, then `ℓ^n ∣ [K(ζ) : K]`. -/
theorem pow_dvd_finrank_adjoin_of_isPrimitiveRoot [CharZero K] [FiniteDimensional ℚ K]
    {E : Type*} [Field E] [Algebra K E] {ζ : E} {ℓ n : ℕ} (hℓ : ℓ ≠ 0)
    (hζ : IsPrimitiveRoot ζ (ℓ ^ (n + finrank ℚ K + 1))) :
    ℓ ^ n ∣ finrank K K⟮ζ⟯ := by
  have h := totient_dvd_finrank_mul_finrank_adjoin (K := K) hζ (pow_pos (Nat.pos_of_ne_zero hℓ) _)
  exact pow_dvd_of_pow_add_dvd_mul finrank_pos.ne' ((pow_dvd_totient_pow_succ ℓ _).trans h)

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
  have := hζ'.intermediateField_adjoin_isCyclotomicExtension K
  have : IsGalois K K⟮ζ'⟯ := IsCyclotomicExtension.isGalois {N} K K⟮ζ'⟯
  have : FiniteDimensional K K⟮ζ'⟯ := IsCyclotomicExtension.finiteDimensional {N} K K⟮ζ'⟯
  let U : OpenNormalSubgroup (galoisGroupS K Ω S) :=
    { toSubgroup := K⟮ζ'⟯.fixingSubgroup
      isOpen' := K⟮ζ'⟯.fixingSubgroup_isOpen }
  refine ⟨U, ?_⟩
  have e := (QuotientGroup.quotientMulEquivOfEq K⟮ζ'⟯.restrictNormalHom_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      (AlgEquiv.restrictNormalHom_surjective (maxUnramifiedOutside K Ω S)))
  rw [Nat.card_congr e.toEquiv, IsGalois.card_aut_eq_finrank]
  exact pow_dvd_finrank_adjoin_of_isPrimitiveRoot ℓ.prop.ne_zero hζ'

end TauCeti.RestrictedRamification
