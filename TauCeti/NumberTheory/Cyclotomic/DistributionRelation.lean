/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.Gal
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import TauCeti.Data.ZMod.Units
import TauCeti.FieldTheory.Minpoly
import TauCeti.NumberTheory.Cyclotomic.Aut
import TauCeti.NumberTheory.Cyclotomic.Basic
import TauCeti.NumberTheory.Cyclotomic.Irreducible
import TauCeti.RingTheory.Norm.Basic
import TauCeti.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# The distribution relation for `1 - ζ`

Let `K = F(μ_m) ⊆ L = F(μ_{mℓ})` be cyclotomic extensions of a field `F` over which `Φ_{mℓ}` is
irreducible (for instance `F = ℚ`). Let `ζ ∈ L` be a primitive `mℓ`-th root of unity and `η ∈ K`
with `η = ζ ^ ℓ`, a primitive `m`-th root of unity. This file computes the minimal polynomial of
`ζ` over `K` and the relative norm of `1 - ζ`:

* if `ℓ ∣ m` (for any `ℓ`, not necessarily prime), then `[L : K] = ℓ`, the minimal polynomial
  is `X ^ ℓ - η`, and `N_{L/K}(1 - ζ) = 1 - η`;
* if `ℓ` is prime, `ℓ ∤ m` and `ℓ * ℓ' ≡ 1 [MOD m]`, then `[L : K] = ℓ - 1`, the minimal
  polynomial times `X - η ^ ℓ'` is `X ^ ℓ - η`, and `N_{L/K}(1 - ζ) * (1 - η ^ ℓ') = 1 - η`.
  Here `η ^ ℓ'` is the image of `η` under the inverse of the arithmetic Frobenius
  `σ_ℓ : η ↦ η ^ ℓ`, so the relation reads `N_{L/K}(1 - ζ) = (1 - η) ^ (1 - σ_ℓ⁻¹)` for `m > 1`.

These are the norm relations satisfied by the cyclotomic numbers `1 - ζ_n`, the starting point
of the Euler system of cyclotomic units. The relations hold for every prime `ℓ`, including
`ℓ = 2`, in the `1 - ζ` normalization. In the normalization `ζ - 1` they acquire the sign
`(-1) ^ [L : K]`, recorded in `IsPrimitiveRoot.norm_sub_one_of_dvd` and
`IsPrimitiveRoot.norm_sub_one_mul_pow_sub_one_of_not_dvd`. Finally, the norm of `1 - ζ` for a
primitive `n`-th root of unity over a field where `Φ_n` is irreducible is `Φ_n(1)`, and equals
`ℓ` when `n = ℓ` is prime; unlike the `ζ - 1` form, this needs no exception at `ℓ = 2`.

## Main results

* `IsPrimitiveRoot.norm_one_sub_eq_eval_minpoly`: `N(1 - ζ)` is the value at `1` of the minimal
  polynomial of `ζ`, for any cyclotomic extension.
* `IsPrimitiveRoot.norm_one_sub_eq_eval_cyclotomic`, `IsPrimitiveRoot.norm_one_sub_of_prime`:
  `N(1 - ζ_n) = Φ_n(1)`, and `N(1 - ζ_ℓ) = ℓ` for every prime `ℓ`.
* `IsPrimitiveRoot.minpoly_eq_X_pow_sub_C_of_dvd`,
  `IsPrimitiveRoot.minpoly_mul_X_sub_C_of_not_dvd`: the minimal polynomial of `ζ_{mℓ}` over
  `F(μ_m)`.
* `IsCyclotomicExtension.finrank_eq_of_dvd`,
  `IsCyclotomicExtension.finrank_eq_of_prime_not_dvd`: `[F(μ_{mℓ}) : F(μ_m)]`.
* `TauCeti.irreducible_cyclotomic_of_dvd`: if `Φ_n` is irreducible over `F` with `n ≠ 0` in `F`,
  then so is `Φ_m` for every `m ∣ n`.
* `IsPrimitiveRoot.norm_one_sub_of_dvd`, `IsPrimitiveRoot.norm_one_sub_mul_one_sub_pow_of_not_dvd`
  and `IsPrimitiveRoot.norm_one_sub_eq_div_of_not_dvd`: the distribution relation.
* `IsPrimitiveRoot.norm_one_sub_mul_autEquivPow_symm_inv_apply`: the same relation with the
  inverse arithmetic Frobenius given by `IsCyclotomicExtension.autEquivPow`.

## References

* K. Rubin, *Euler Systems*, Annals of Mathematics Studies 147, Chapter III, §2.1, display (2).
* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*,
  arXiv:2309.15692v2, §10.2, proof of Lemma 10.3.
-/

public section

open Polynomial

namespace IsPrimitiveRoot

section Conductor

variable {K L : Type*} [Field K] [CommRing L] [IsDomain L] [Algebra K L] {n : ℕ} [NeZero n]
  {ζ : L}

/-- The norm of `1 - ζ` for a primitive `n`-th root of unity `ζ` generating `L / K` is the value at
`1` of the minimal polynomial of `ζ`. No irreducibility of `Φ_n` over `K` is needed. -/
theorem norm_one_sub_eq_eval_minpoly [IsCyclotomicExtension {n} K L]
    (hζ : IsPrimitiveRoot ζ n) : Algebra.norm K (1 - ζ) = (minpoly K ζ).eval 1 := by
  have h := (hζ.powerBasis K).norm_algebraMap_sub_gen 1
  rwa [map_one, powerBasis_gen] at h

/-- The norm of `1 - ζ` for a primitive `n`-th root of unity `ζ` generating `L / K` is `Φ_n(1)`,
when `Φ_n` is irreducible over `K`. Unlike Mathlib's
`IsPrimitiveRoot.sub_one_norm_eq_eval_cyclotomic` for `ζ - 1`, no condition `2 < n` is needed. -/
theorem norm_one_sub_eq_eval_cyclotomic [IsCyclotomicExtension {n} K L]
    (hζ : IsPrimitiveRoot ζ n) (hirr : Irreducible (cyclotomic n K)) :
    Algebra.norm K (1 - ζ) = (cyclotomic n K).eval 1 := by
  have := IsCyclotomicExtension.neZero' n K L
  rw [hζ.norm_one_sub_eq_eval_minpoly, ← hζ.minpoly_eq_cyclotomic_of_irreducible hirr]

/-- **The norm of `1 - ζ_ℓ` is `ℓ`** for every prime `ℓ`, including `ℓ = 2`, when `Φ_ℓ` is
irreducible over `K`. -/
theorem norm_one_sub_of_prime {ℓ : ℕ} [Fact ℓ.Prime] [IsCyclotomicExtension {ℓ} K L]
    (hζ : IsPrimitiveRoot ζ ℓ) (hirr : Irreducible (cyclotomic ℓ K)) :
    Algebra.norm K (1 - ζ) = ℓ := by
  rw [hζ.norm_one_sub_eq_eval_cyclotomic hirr, eval_one_cyclotomic_prime]

/-- The norm of `ζ_ℓ - 1` is `(-1) ^ (ℓ - 1) * ℓ` for every prime `ℓ`, when `Φ_ℓ` is irreducible
over `K`. For odd `ℓ` the sign is `1`, as in Mathlib's
`IsPrimitiveRoot.norm_sub_one_of_prime_ne_two'`; for `ℓ = 2` it is `-1`. -/
theorem norm_sub_one_of_prime {ℓ : ℕ} [hℓ : Fact ℓ.Prime] [IsCyclotomicExtension {ℓ} K L]
    (hζ : IsPrimitiveRoot ζ ℓ) (hirr : Irreducible (cyclotomic ℓ K)) :
    Algebra.norm K (ζ - 1) = (-1) ^ (ℓ - 1) * ℓ := by
  rw [← neg_sub, Algebra.norm_neg, hζ.norm_one_sub_of_prime hirr,
    IsCyclotomicExtension.finrank L hirr, Nat.totient_prime hℓ.out]

end Conductor

end IsPrimitiveRoot

variable {F K L : Type*} [Field F] [Field K] [CommRing L] [IsDomain L] [Algebra F K] [Algebra F L]
  [Algebra K L] [IsScalarTower F K L] {m ℓ : ℕ} [NeZero m]
  [IsCyclotomicExtension {m} F K] [IsCyclotomicExtension {m * ℓ} F L]

namespace IsCyclotomicExtension

/-- The degree bound `φ(mℓ) ≤ φ(m) [L : K]`, from `[L : F] = φ(mℓ)` and `[K : F] ≤ φ(m)`. -/
private theorem totient_mul_le_totient_mul_finrank [NeZero ℓ]
    (hirr : Irreducible (cyclotomic (m * ℓ) F)) :
    (m * ℓ).totient ≤ m.totient * Module.finrank K L := by
  have : IsCyclotomicExtension {m * ℓ} K L := tower_top F K L
  have := finiteDimensional {m} F K
  have := finiteDimensional {m * ℓ} K L
  rw [← finrank L hirr, ← Module.finrank_mul_finrank F K L]
  exact Nat.mul_le_mul_right _ (finrank_le_totient F K)

include F in
omit [IsScalarTower F K L] in
/-- A primitive `m * ℓ`-th root of unity of `L` whose `ℓ`-th power comes from `K`. -/
private theorem exists_isPrimitiveRoot_algebraMap_eq_pow [NeZero ℓ] :
    ∃ ζ : L, ∃ η : K, IsPrimitiveRoot ζ (m * ℓ) ∧ algebraMap K L η = ζ ^ ℓ := by
  have hζ := zeta_spec (m * ℓ) F L
  have hz := (zeta_spec m F K).map_of_injective (algebraMap K L).injective
  obtain ⟨i, -, hi⟩ := hz.eq_pow_of_pow_eq_one (ξ := zeta (m * ℓ) F L ^ ℓ)
    (by rw [← pow_mul, mul_comm ℓ, hζ.pow_eq_one])
  exact ⟨_, _, hζ, by rw [map_pow, hi]⟩

end IsCyclotomicExtension

namespace IsPrimitiveRoot

variable {ζ : L} {η : K}

/-- **The minimal polynomial of a cyclotomic step when `ℓ ∣ m`.** If `ℓ` divides `m`, then the
minimal polynomial of `ζ = ζ_{mℓ}` over `K = F(μ_m)` is `X ^ ℓ - η`, where `η = ζ ^ ℓ`. -/
theorem minpoly_eq_X_pow_sub_C_of_dvd (hirr : Irreducible (cyclotomic (m * ℓ) F))
    (hζ : IsPrimitiveRoot ζ (m * ℓ)) (hη : algebraMap K L η = ζ ^ ℓ) (hdvd : ℓ ∣ m) :
    minpoly K ζ = X ^ ℓ - C η := by
  have hℓ : 0 < ℓ := Nat.pos_of_dvd_of_pos hdvd (NeZero.pos m)
  have : NeZero ℓ := ⟨hℓ.ne'⟩
  have : IsCyclotomicExtension {m * ℓ} K L := IsCyclotomicExtension.tower_top F K L
  refine TauCeti.Algebra.minpoly_eq_X_pow_sub_C_of_pow_eq_of_natDegree_eq hℓ.ne' hη.symm
    (le_antisymm ?_ ?_)
  · -- `ζ` is a root of `X ^ ℓ - η`.
    simpa using natDegree_le_of_dvd (minpoly.dvd K ζ (by simp [hη])) (X_pow_sub_C_ne_zero hℓ η)
  · -- The degree count `φ(mℓ) = ℓ φ(m) ≤ φ(m) [L : K]` gives `ℓ ≤ [L : K] = deg (minpoly K ζ)`.
    have h := IsCyclotomicExtension.totient_mul_le_totient_mul_finrank (K := K) (L := L) hirr
    rw [mul_comm m ℓ, Nat.totient_mul_of_dvd hdvd, mul_comm ℓ,
      hζ.finrank_eq_natDegree_minpoly] at h
    exact Nat.le_of_mul_le_mul_left h (Nat.totient_pos.2 (NeZero.pos m))

section Prime

variable [hℓ : Fact ℓ.Prime]

/-- **The minimal polynomial of a cyclotomic step when `ℓ ∤ m`.** If the prime `ℓ` does not divide
`m` and `ℓ * ℓ' ≡ 1 [MOD m]`, then `η ^ ℓ'` is the `ℓ`-th root of `η = ζ ^ ℓ` of order dividing
`m`, and the minimal polynomial of `ζ = ζ_{mℓ}` over `K = F(μ_m)` is the quotient of
`X ^ ℓ - η` by `X - η ^ ℓ'`. For `m = 1` it is `Φ_ℓ = (X ^ ℓ - 1) / (X - 1)`. -/
theorem minpoly_mul_X_sub_C_of_not_dvd (hirr : Irreducible (cyclotomic (m * ℓ) F))
    (hζ : IsPrimitiveRoot ζ (m * ℓ)) (hη : algebraMap K L η = ζ ^ ℓ) (hdvd : ¬ℓ ∣ m) {ℓ' : ℕ}
    (hℓ' : ℓ * ℓ' ≡ 1 [MOD m]) :
    minpoly K ζ * (X - C (η ^ ℓ')) = X ^ ℓ - C η := by
  have : IsCyclotomicExtension {m * ℓ} K L := IsCyclotomicExtension.tower_top F K L
  have hηm := (of_algebraMap_eq_pow hζ hη).pow_eq_one
  -- `η ^ ℓ'` is a root of `X ^ ℓ - η`, which therefore factors as `(X - η ^ ℓ') * g`.
  have hroot : (X ^ ℓ - C η).IsRoot (η ^ ℓ') := by
    rw [IsRoot, eval_sub, eval_pow, eval_X, eval_C, ← pow_mul, mul_comm ℓ',
      pow_eq_pow_of_modEq hℓ' hηm, pow_one, sub_self]
  set g := (X ^ ℓ - C η) /ₘ (X - C (η ^ ℓ'))
  have hg : (X - C (η ^ ℓ')) * g = X ^ ℓ - C η := mul_divByMonic_eq_iff_isRoot.2 hroot
  have hgmon : g.Monic :=
    (monic_X_sub_C _).of_mul_monic_left (hg ▸ monic_X_pow_sub_C η hℓ.out.ne_zero)
  -- `ζ` is not `η ^ ℓ'`, whose `m`-th power is `1`, so `ζ` is a root of `g`.
  have hgζ : aeval ζ g = 0 := by
    have h0 : aeval ζ (X ^ ℓ - C η) = 0 := by simp [hη]
    rw [← hg, map_mul] at h0
    refine (mul_eq_zero.1 h0).resolve_left ?_
    rw [map_sub, aeval_X, aeval_C, sub_eq_zero]
    intro h
    refine hζ.pow_ne_one_of_pos_of_lt (NeZero.ne m)
      (lt_mul_of_one_lt_right (NeZero.pos m) hℓ.out.one_lt) ?_
    rw [h, ← map_pow, ← pow_mul, mul_comm, pow_mul, hηm, one_pow, map_one]
  -- The degree count `φ(mℓ) = φ(m) (ℓ - 1) ≤ φ(m) [L : K]` forces `minpoly K ζ = g`.
  have hdeg : g.natDegree ≤ (minpoly K ζ).natDegree := by
    have h := IsCyclotomicExtension.totient_mul_le_totient_mul_finrank (K := K) (L := L) hirr
    rw [Nat.totient_mul ((hℓ.out.coprime_iff_not_dvd.2 hdvd).symm), Nat.totient_prime hℓ.out,
      hζ.finrank_eq_natDegree_minpoly] at h
    rw [natDegree_divByMonic _ (monic_X_sub_C _), natDegree_X_pow_sub_C, natDegree_X_sub_C]
    exact Nat.le_of_mul_le_mul_left h (Nat.totient_pos.2 (NeZero.pos m))
  rw [← eq_of_monic_of_dvd_of_natDegree_le
    (minpoly.monic (hζ.isIntegral (NeZero.pos _)).tower_top) hgmon (minpoly.dvd K ζ hgζ) hdeg,
    mul_comm, hg]

end Prime

end IsPrimitiveRoot

namespace IsCyclotomicExtension

variable (K L)

/-- **The degree of a cyclotomic step when `ℓ ∣ m`**: `[F(μ_{mℓ}) : F(μ_m)] = ℓ` for every `ℓ`
dividing `m`, when `Φ_{mℓ}` is irreducible over `F`. -/
theorem finrank_eq_of_dvd (hirr : Irreducible (cyclotomic (m * ℓ) F)) (hdvd : ℓ ∣ m) :
    Module.finrank K L = ℓ := by
  have : NeZero ℓ := ⟨(Nat.pos_of_dvd_of_pos hdvd (NeZero.pos m)).ne'⟩
  have : IsCyclotomicExtension {m * ℓ} K L := tower_top F K L
  obtain ⟨ζ, η, hζ, hη⟩ :=
    exists_isPrimitiveRoot_algebraMap_eq_pow (F := F) (K := K) (L := L) (m := m) (ℓ := ℓ)
  rw [hζ.finrank_eq_natDegree_minpoly, hζ.minpoly_eq_X_pow_sub_C_of_dvd hirr hη hdvd,
    natDegree_X_pow_sub_C]

section Prime

variable [hℓ : Fact ℓ.Prime]

/-- **The degree of a cyclotomic step when `ℓ ∤ m`**: `[F(μ_{mℓ}) : F(μ_m)] = ℓ - 1` for a prime
`ℓ` not dividing `m`, when `Φ_{mℓ}` is irreducible over `F`. -/
theorem finrank_eq_of_prime_not_dvd (hirr : Irreducible (cyclotomic (m * ℓ) F))
    (hdvd : ¬ℓ ∣ m) : Module.finrank K L = ℓ - 1 := by
  have : IsCyclotomicExtension {m * ℓ} K L := tower_top F K L
  obtain ⟨ζ, η, hζ, hη⟩ :=
    exists_isPrimitiveRoot_algebraMap_eq_pow (F := F) (K := K) (L := L) (m := m) (ℓ := ℓ)
  have h := congrArg natDegree (hζ.minpoly_mul_X_sub_C_of_not_dvd hirr hη hdvd
    (ZMod.mul_val_inv_modEq_one (hℓ.out.coprime_iff_not_dvd.2 hdvd)))
  rw [natDegree_mul (minpoly.ne_zero (hζ.isIntegral (NeZero.pos _)).tower_top)
    (X_sub_C_ne_zero _), natDegree_X_sub_C, natDegree_X_pow_sub_C] at h
  rw [hζ.finrank_eq_natDegree_minpoly]
  omega

end Prime

end IsCyclotomicExtension

namespace TauCeti

/-- The prime step of `TauCeti.irreducible_cyclotomic_of_dvd`: if `Φ_{mℓ}` is irreducible over `F`
for a prime `ℓ` with `mℓ ≠ 0` in `F`, then so is `Φ_m`. -/
private theorem irreducible_cyclotomic_of_mul_prime [hℓ : Fact ℓ.Prime]
    [NeZero ((m * ℓ : ℕ) : F)] (hirr : Irreducible (cyclotomic (m * ℓ) F)) :
    Irreducible (cyclotomic m F) := by
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  -- Realise `F(μ_m) ⊆ F(μ_{mℓ})` as `F(ζ ^ ℓ) ⊆ CyclotomicField (m * ℓ) F`.
  let N := CyclotomicField (m * ℓ) F
  let ζ := IsCyclotomicExtension.zeta (m * ℓ) F N
  let M := IntermediateField.adjoin F {ζ ^ ℓ}
  have : IsCyclotomicExtension {m} F M :=
    ((IsCyclotomicExtension.zeta_spec (m * ℓ) F N).pow (NeZero.pos _)
      (mul_comm m ℓ)).intermediateField_adjoin_isCyclotomicExtension F
  have := IsCyclotomicExtension.finiteDimensional {m} F M
  have : IsCyclotomicExtension {m * ℓ} M N := IsCyclotomicExtension.tower_top F M N
  have := IsCyclotomicExtension.finiteDimensional {m * ℓ} M N
  -- The degrees `[F(μ_{mℓ}) : F] = φ(mℓ)` and `[F(μ_{mℓ}) : F(μ_m)]`, which is `ℓ` if `ℓ ∣ m`
  -- and `ℓ - 1` otherwise, force `[F(μ_m) : F] = φ(m)`.
  refine IsCyclotomicExtension.irreducible_cyclotomic_of_totient_le_finrank F M ?_
  have h := IsCyclotomicExtension.finrank N hirr
  rw [← Module.finrank_mul_finrank F M N] at h
  by_cases hdvd : ℓ ∣ m
  · have hφ : (m * ℓ).totient = m.totient * ℓ := by
      rw [mul_comm m ℓ, Nat.totient_mul_of_dvd hdvd, mul_comm]
    rw [IsCyclotomicExtension.finrank_eq_of_dvd M N hirr hdvd, hφ] at h
    exact (Nat.eq_of_mul_eq_mul_right hℓ.out.pos h).ge
  · rw [IsCyclotomicExtension.finrank_eq_of_prime_not_dvd M N hirr hdvd,
      Nat.totient_mul ((hℓ.out.coprime_iff_not_dvd.2 hdvd).symm), Nat.totient_prime hℓ.out] at h
    exact (Nat.eq_of_mul_eq_mul_right (Nat.sub_pos_of_lt hℓ.out.one_lt) h).ge

/-- **Irreducibility of `Φ_m` from that of `Φ_n`.** If `Φ_n` is irreducible over `F` with `n ≠ 0`
in `F`, then so is `Φ_m` for every `m ∣ n`. -/
theorem irreducible_cyclotomic_of_dvd {m n : ℕ} [hn : NeZero (n : F)]
    (hirr : Irreducible (cyclotomic n F)) (hmn : m ∣ n) : Irreducible (cyclotomic m F) := by
  obtain ⟨k, rfl⟩ := hmn
  -- Peel the prime factors of `k` off one at a time.
  induction k using induction_on_primes generalizing m with
  | zero => exact absurd (by simp) hn.out
  | one => simpa using hirr
  | prime_mul p a hp ih =>
    have : Fact p.Prime := ⟨hp⟩
    have : NeZero (((m * a) * p : ℕ) : F) := by rwa [mul_assoc, mul_comm a p]
    have : NeZero ((m * a : ℕ) : F) :=
      ⟨left_ne_zero_of_mul (b := (p : F)) (by exact_mod_cast NeZero.ne (((m * a) * p : ℕ) : F))⟩
    have : NeZero (m * a) := ⟨fun h ↦ NeZero.ne ((m * a : ℕ) : F) (by simp [h])⟩
    exact ih (irreducible_cyclotomic_of_mul_prime (by rwa [mul_assoc, mul_comm a p]))

end TauCeti

namespace IsPrimitiveRoot

variable {ζ : L} {η : K}

/-- **The distribution relation when `ℓ ∣ m`**: `N_{L/K}(1 - ζ_{mℓ}) = 1 - ζ_m`. -/
theorem norm_one_sub_of_dvd (hirr : Irreducible (cyclotomic (m * ℓ) F))
    (hζ : IsPrimitiveRoot ζ (m * ℓ)) (hη : algebraMap K L η = ζ ^ ℓ) (hdvd : ℓ ∣ m) :
    Algebra.norm K (1 - ζ) = 1 - η := by
  have : NeZero ℓ := ⟨(Nat.pos_of_dvd_of_pos hdvd (NeZero.pos m)).ne'⟩
  have : IsCyclotomicExtension {m * ℓ} K L := IsCyclotomicExtension.tower_top F K L
  rw [hζ.norm_one_sub_eq_eval_minpoly, hζ.minpoly_eq_X_pow_sub_C_of_dvd hirr hη hdvd]
  simp

/-- **The distribution relation for `ζ - 1` when `ℓ ∣ m`**:
`N_{L/K}(ζ_{mℓ} - 1) = (-1) ^ (ℓ + 1) * (ζ_m - 1)`. For odd `ℓ` this is `ζ_m - 1`; for even `ℓ`
the sign is `-1`. -/
theorem norm_sub_one_of_dvd (hirr : Irreducible (cyclotomic (m * ℓ) F))
    (hζ : IsPrimitiveRoot ζ (m * ℓ)) (hη : algebraMap K L η = ζ ^ ℓ) (hdvd : ℓ ∣ m) :
    Algebra.norm K (ζ - 1) = (-1) ^ (ℓ + 1) * (η - 1) := by
  have : NeZero ℓ := ⟨(Nat.pos_of_dvd_of_pos hdvd (NeZero.pos m)).ne'⟩
  have : IsCyclotomicExtension {m * ℓ} K L := IsCyclotomicExtension.tower_top F K L
  have := IsCyclotomicExtension.finiteDimensional {m * ℓ} K L
  rw [← neg_sub, Algebra.norm_neg, IsCyclotomicExtension.finrank_eq_of_dvd K L hirr hdvd,
    hζ.norm_one_sub_of_dvd hirr hη hdvd]
  ring

section Prime

variable [hℓ : Fact ℓ.Prime]

/-- **The distribution relation when `ℓ ∤ m`**: `N_{L/K}(1 - ζ_{mℓ}) * (1 - ζ_m ^ ℓ') = 1 - ζ_m`
when `ℓ * ℓ' ≡ 1 [MOD m]`. For `m = 1` both sides vanish. -/
theorem norm_one_sub_mul_one_sub_pow_of_not_dvd (hirr : Irreducible (cyclotomic (m * ℓ) F))
    (hζ : IsPrimitiveRoot ζ (m * ℓ)) (hη : algebraMap K L η = ζ ^ ℓ) (hdvd : ¬ℓ ∣ m) {ℓ' : ℕ}
    (hℓ' : ℓ * ℓ' ≡ 1 [MOD m]) :
    Algebra.norm K (1 - ζ) * (1 - η ^ ℓ') = 1 - η := by
  have : IsCyclotomicExtension {m * ℓ} K L := IsCyclotomicExtension.tower_top F K L
  have h := congrArg (eval 1) (hζ.minpoly_mul_X_sub_C_of_not_dvd hirr hη hdvd hℓ')
  rw [eval_mul, ← hζ.norm_one_sub_eq_eval_minpoly] at h
  simpa using h

/-- **The distribution relation when `ℓ ∤ m`, as a quotient**: for `m > 1`,
`N_{L/K}(1 - ζ_{mℓ}) = (1 - ζ_m) / (1 - ζ_m ^ ℓ')` when `ℓ * ℓ' ≡ 1 [MOD m]`. -/
theorem norm_one_sub_eq_div_of_not_dvd (hirr : Irreducible (cyclotomic (m * ℓ) F))
    (hζ : IsPrimitiveRoot ζ (m * ℓ)) (hη : algebraMap K L η = ζ ^ ℓ) (hdvd : ¬ℓ ∣ m) {ℓ' : ℕ}
    (hℓ' : ℓ * ℓ' ≡ 1 [MOD m]) (hm : 1 < m) :
    Algebra.norm K (1 - ζ) = (1 - η) / (1 - η ^ ℓ') := by
  have hη' := (of_algebraMap_eq_pow hζ hη).pow_of_coprime ℓ'
    (Nat.coprime_of_mul_modEq_one ℓ (by rwa [mul_comm]))
  exact eq_div_of_mul_eq (sub_ne_zero.2 (hη'.ne_one hm).symm)
    (hζ.norm_one_sub_mul_one_sub_pow_of_not_dvd hirr hη hdvd hℓ')

/-- **The distribution relation with the arithmetic Frobenius**: for a prime `ℓ` coprime to `m`,
`N_{L/K}(1 - ζ_{mℓ}) * σ_ℓ⁻¹(1 - ζ_m) = 1 - ζ_m`, where `σ_ℓ ∈ Gal(F(μ_m)/F)` is the arithmetic
Frobenius `ζ_m ↦ ζ_m ^ ℓ`, whose inverse is the image of `ℓ⁻¹ ∈ (ZMod m)ˣ` under
`(IsCyclotomicExtension.autEquivPow K h).symm`. Multiplicatively,
`N_{L/K}(1 - ζ_{mℓ}) = (1 - ζ_m) ^ (1 - σ_ℓ⁻¹)`. -/
theorem norm_one_sub_mul_autEquivPow_symm_inv_apply
    (hirr : Irreducible (cyclotomic (m * ℓ) F)) (hζ : IsPrimitiveRoot ζ (m * ℓ))
    (hη : algebraMap K L η = ζ ^ ℓ) (h : Irreducible (cyclotomic m F)) (hcop : ℓ.Coprime m) :
    Algebra.norm K (1 - ζ) *
        (IsCyclotomicExtension.autEquivPow K h).symm (ZMod.unitOfCoprime ℓ hcop)⁻¹ (1 - η) =
      1 - η := by
  simp only [map_sub, map_one]
  rw [IsCyclotomicExtension.autEquivPow_symm_inv_unitOfCoprime_apply F K h hcop
    (of_algebraMap_eq_pow hζ hη).pow_eq_one]
  exact hζ.norm_one_sub_mul_one_sub_pow_of_not_dvd hirr hη (hℓ.out.coprime_iff_not_dvd.1 hcop)
    (ZMod.mul_val_inv_modEq_one hcop)

/-- **The distribution relation for `ζ - 1` when `ℓ ∤ m`**:
`N_{L/K}(ζ_{mℓ} - 1) * (ζ_m ^ ℓ' - 1) = (-1) ^ (ℓ - 1) * (ζ_m - 1)` when `ℓ * ℓ' ≡ 1 [MOD m]`.
-/
theorem norm_sub_one_mul_pow_sub_one_of_not_dvd (hirr : Irreducible (cyclotomic (m * ℓ) F))
    (hζ : IsPrimitiveRoot ζ (m * ℓ)) (hη : algebraMap K L η = ζ ^ ℓ) (hdvd : ¬ℓ ∣ m) {ℓ' : ℕ}
    (hℓ' : ℓ * ℓ' ≡ 1 [MOD m]) :
    Algebra.norm K (ζ - 1) * (η ^ ℓ' - 1) = (-1) ^ (ℓ - 1) * (η - 1) := by
  have : IsCyclotomicExtension {m * ℓ} K L := IsCyclotomicExtension.tower_top F K L
  have := IsCyclotomicExtension.finiteDimensional {m * ℓ} K L
  rw [← neg_sub, Algebra.norm_neg,
    IsCyclotomicExtension.finrank_eq_of_prime_not_dvd K L hirr hdvd]
  linear_combination (-(-1) ^ (ℓ - 1) : K) *
    hζ.norm_one_sub_mul_one_sub_pow_of_not_dvd hirr hη hdvd hℓ'

end Prime

end IsPrimitiveRoot

/-! The case `m = ℓ = 2` over `ℚ`: the minimal polynomial of `ζ₄ = i` over `ℚ(μ₂)` is
`X ^ 2 - ζ₂ = X ^ 2 + 1`. -/
example {K L : Type*} [Field K] [Field L] [CharZero K] [CharZero L] [Algebra K L]
    [IsCyclotomicExtension {2} ℚ K] [IsCyclotomicExtension {2 * 2} ℚ L] {ζ : L}
    (hζ : IsPrimitiveRoot ζ (2 * 2)) : minpoly K ζ = X ^ 2 + 1 := by
  have hη : algebraMap K L (-1) = ζ ^ 2 := by
    rw [map_neg, map_one, (hζ.pow (by norm_num) (mul_comm 2 2)).eq_neg_one_of_two_right]
  rw [hζ.minpoly_eq_X_pow_sub_C_of_dvd (cyclotomic.irreducible_rat (by norm_num)) hη dvd_rfl,
    C_neg, C_1, sub_neg_eq_add]
