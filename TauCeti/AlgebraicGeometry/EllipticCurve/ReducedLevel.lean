/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Factorization.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Reduction.Conductor
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# The reduced level `M₀` of an elliptic curve over `ℚ`

Let `E/ℚ` be an elliptic curve of conductor `M` and minimal discriminant `Δ`, and let `ℓ ≥ 3` be
a prime. At a prime `q ∥ M` the curve has multiplicative reduction, and when `ℓ ∣ v_q(Δ)` the Tate
curve shows that `E[ℓ]` is unramified at `q` (for `q ≠ ℓ`) or finite flat at `q` (for `q = ℓ`), so
when `E[ℓ]` is irreducible, Ribet's level lowering removes `q` from the level of a weight-two
newform giving `E[ℓ]` (Bennett–Siksek, Theorem 3). Without irreducibility no such newform need
exist. These facts are not proved here. The resulting level is the **reduced level**

`M₀ = M / ∏ q`, the product over the primes `q` with `v_q(M) = 1` and `ℓ ∣ v_q(Δ)`

of Bennett–Siksek, equation (3). The prime `q = ℓ` is removed when it meets the two conditions, so
`M₀` may keep or lose `ℓ`; it is not the prime-to-`ℓ` Serre conductor of `E[ℓ]`. Only primes
occurring to exponent one in `M` are removed, so every higher conductor exponent survives.

The arithmetic part depends only on the numbers `M`, `Δ` and `ℓ`
(`Nat.reducedEllipticLevel`). The valuation `v_q(n)` is Mathlib's `multiplicity q n`, which is
`padicValNat q n` (`Nat.padicValNat_def`) and, at a prime, `n.factorization q`. The arithmetic
part asserts neither that `(M, Δ)` comes from an elliptic curve nor anything about `E[ℓ]`. For a
curve `E` over `ℚ`, `WeierstrassCurve.reducedLevel` evaluates it at the norms of the algorithmic
conductor and of the minimal discriminant ideal, so it depends only on the isomorphism class of
`E`.

## Main definitions

* `Nat.levelLoweringPrimes M Δ ℓ`: the primes `q` with `v_q(M) = 1` and `ℓ ∣ v_q(|Δ|)`.
* `Nat.reducedEllipticLevel M Δ ℓ`: the quotient of `M` by the product of these primes.
* `WeierstrassCurve.reducedLevel E ℓ`: the reduced level of an elliptic curve `E` over `ℚ`.

## Main results

* `Nat.reducedEllipticLevel_mul_prod_levelLoweringPrimes`: `M₀ · ∏ q = M`; in particular
  `M₀ ∣ M` (`Nat.reducedEllipticLevel_dvd`), and `M₀ = 0` only when `M = 0`.
* `Nat.multiplicity_reducedEllipticLevel`: at a prime `q`, the exponent of `q` in `M₀` is `0`
  if `q` is removed and the exponent of `q` in `M` otherwise.
* `Nat.multiplicity_reducedEllipticLevel_of_one_lt`: a conductor exponent above one is kept.
* `Nat.prime_dvd_reducedEllipticLevel_iff_of_multiplicity_eq_one`: a prime `q ∥ M`, including
  `q = ℓ`, divides `M₀` exactly when `ℓ ∤ v_q(|Δ|)`.
* `Nat.reducedEllipticLevel_congr`: `M₀` only sees the valuations of `Δ` at the primes `q ∥ M`,
  so in particular it is unchanged by the sign of `Δ` (`Nat.reducedEllipticLevel_neg`).
* `WeierstrassCurve.reducedLevel_smul`: the reduced level of a curve is invariant under a change
  of variables.
* `WeierstrassCurve.IsGlobalMinimal.reducedLevel_eq`: for a globally minimal integral equation,
  the reduced level is computed from its discriminant.

## References

* M. A. Bennett and S. Siksek, *A conjecture of Erdős, supersingular primes and short character
  sums*, Ann. of Math. 191 (2020), 355–392, equation (3) and Theorem 3.
* K. A. Ribet, *On modular representations of Gal(Q^alg/Q) arising from modular forms*, Invent.
  Math. 100 (1990), 431–476, Theorem 1.1.
-/

public section

namespace Nat

/-- **The level-lowering primes** of `(M, Δ)` at `ℓ`: the primes `q` occurring in `M` to exponent
exactly one, with `ℓ` dividing the exponent of `q` in `|Δ|`. For the conductor `M` and minimal
discriminant `Δ` of an elliptic curve over `ℚ`, these are the multiplicative primes at which,
when `E[ℓ]` is irreducible, level lowering removes `q` from the level of a newform giving `E[ℓ]`
(not proved here). Minimal discriminants are
nonzero; at `Δ = 0` the valuation `multiplicity q 0 = 0` is a junk value, and every `q ∥ M` is
then a level-lowering prime. -/
noncomputable def levelLoweringPrimes (M : ℕ) (Δ : ℤ) (ℓ : ℕ) : Finset ℕ :=
  M.primeFactors.filter fun q ↦ multiplicity q M = 1 ∧ ℓ ∣ multiplicity q Δ.natAbs

/-- **The reduced level** `M₀ = M / ∏ q` of `(M, Δ)` at `ℓ`, where `q` runs through the
level-lowering primes: the primes with `v_q(M) = 1` and `ℓ ∣ v_q(|Δ|)` (Bennett–Siksek,
equation (3)). For the conductor `M` and minimal discriminant `Δ` of an elliptic curve over `ℚ`
and a prime `ℓ ≥ 3` with `E[ℓ]` irreducible, Ribet's level lowering predicts a weight-two newform
of level `M₀` giving `E[ℓ]` (not proved here); without irreducibility no such newform need exist.
It may keep the prime `ℓ`. -/
noncomputable def reducedEllipticLevel (M : ℕ) (Δ : ℤ) (ℓ : ℕ) : ℕ :=
  M / ∏ q ∈ levelLoweringPrimes M Δ ℓ, q

variable {M : ℕ} {Δ Δ' : ℤ} {ℓ q : ℕ}

theorem levelLoweringPrimes_def (M : ℕ) (Δ : ℤ) (ℓ : ℕ) :
    levelLoweringPrimes M Δ ℓ =
      M.primeFactors.filter fun q ↦ multiplicity q M = 1 ∧ ℓ ∣ multiplicity q Δ.natAbs := by
  rw [levelLoweringPrimes]

theorem reducedEllipticLevel_def (M : ℕ) (Δ : ℤ) (ℓ : ℕ) :
    reducedEllipticLevel M Δ ℓ = M / ∏ q ∈ levelLoweringPrimes M Δ ℓ, q := by
  rw [reducedEllipticLevel]

/-- **Membership in the level-lowering primes**: `q` is a prime occurring in `M` to exponent
exactly one, with `ℓ` dividing its exponent in `|Δ|`. -/
@[simp]
theorem mem_levelLoweringPrimes :
    q ∈ levelLoweringPrimes M Δ ℓ ↔
      q.Prime ∧ multiplicity q M = 1 ∧ ℓ ∣ multiplicity q Δ.natAbs := by
  rw [levelLoweringPrimes_def, Finset.mem_filter, Nat.mem_primeFactors]
  refine ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun ⟨hq, h₁, h₂⟩ ↦ ⟨⟨hq, ?_, ?_⟩, h₁, h₂⟩⟩
  · exact dvd_of_one_le_multiplicity h₁.ge
  · rintro rfl
    simp at h₁

theorem prime_of_mem_levelLoweringPrimes (h : q ∈ levelLoweringPrimes M Δ ℓ) : q.Prime :=
  (mem_levelLoweringPrimes.1 h).1

theorem multiplicity_eq_one_of_mem_levelLoweringPrimes (h : q ∈ levelLoweringPrimes M Δ ℓ) :
    multiplicity q M = 1 :=
  (mem_levelLoweringPrimes.1 h).2.1

theorem levelLoweringPrimes_subset_primeFactors :
    levelLoweringPrimes M Δ ℓ ⊆ M.primeFactors :=
  Finset.filter_subset _ _

/-- **The level-lowering primes depend only on the valuations of `Δ` at the primes `q ∥ M`.** -/
theorem levelLoweringPrimes_congr
    (h : ∀ q, q.Prime → multiplicity q M = 1 →
      multiplicity q Δ.natAbs = multiplicity q Δ'.natAbs) :
    levelLoweringPrimes M Δ ℓ = levelLoweringPrimes M Δ' ℓ := by
  ext q
  simp only [mem_levelLoweringPrimes]
  exact ⟨fun ⟨hq, h₁, h₂⟩ ↦ ⟨hq, h₁, h q hq h₁ ▸ h₂⟩,
    fun ⟨hq, h₁, h₂⟩ ↦ ⟨hq, h₁, (h q hq h₁).symm ▸ h₂⟩⟩

@[simp]
theorem levelLoweringPrimes_neg : levelLoweringPrimes M (-Δ) ℓ = levelLoweringPrimes M Δ ℓ :=
  levelLoweringPrimes_congr fun _ _ _ ↦ by rw [Int.natAbs_neg]

@[simp]
theorem levelLoweringPrimes_one : levelLoweringPrimes 1 Δ ℓ = ∅ := by
  simp [levelLoweringPrimes_def]

/-- The product of the level-lowering primes divides `M`: they are distinct primes dividing `M`. -/
theorem prod_levelLoweringPrimes_dvd : ∏ q ∈ levelLoweringPrimes M Δ ℓ, q ∣ M :=
  (Finset.prod_dvd_prod_of_subset _ _ _ levelLoweringPrimes_subset_primeFactors).trans
    (Nat.prod_primeFactors_dvd M)

/-- **`M₀` times the product of the level-lowering primes is `M`.** -/
theorem reducedEllipticLevel_mul_prod_levelLoweringPrimes :
    reducedEllipticLevel M Δ ℓ * ∏ q ∈ levelLoweringPrimes M Δ ℓ, q = M := by
  rw [reducedEllipticLevel_def, Nat.div_mul_cancel prod_levelLoweringPrimes_dvd]

/-- **The reduced level divides the level.** -/
theorem reducedEllipticLevel_dvd : reducedEllipticLevel M Δ ℓ ∣ M :=
  Dvd.intro _ reducedEllipticLevel_mul_prod_levelLoweringPrimes

@[simp]
theorem reducedEllipticLevel_eq_zero_iff : reducedEllipticLevel M Δ ℓ = 0 ↔ M = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← reducedEllipticLevel_mul_prod_levelLoweringPrimes (M := M) (Δ := Δ) (ℓ := ℓ), h,
      zero_mul]
  · rw [reducedEllipticLevel_def, h, Nat.zero_div]

@[simp]
theorem reducedEllipticLevel_zero : reducedEllipticLevel 0 Δ ℓ = 0 :=
  reducedEllipticLevel_eq_zero_iff.2 rfl

theorem reducedEllipticLevel_pos (hM : 0 < M) : 0 < reducedEllipticLevel M Δ ℓ :=
  Nat.pos_of_ne_zero (reducedEllipticLevel_eq_zero_iff.not.2 hM.ne')

@[simp]
theorem reducedEllipticLevel_one : reducedEllipticLevel 1 Δ ℓ = 1 := by
  simp [reducedEllipticLevel_def]

/-- **`M₀` only depends on the valuations of `Δ` at the primes `q ∥ M`.** In particular two
discriminants with the same valuation at every such prime give the same reduced level. -/
theorem reducedEllipticLevel_congr
    (h : ∀ q, q.Prime → multiplicity q M = 1 →
      multiplicity q Δ.natAbs = multiplicity q Δ'.natAbs) :
    reducedEllipticLevel M Δ ℓ = reducedEllipticLevel M Δ' ℓ := by
  rw [reducedEllipticLevel_def, reducedEllipticLevel_def, levelLoweringPrimes_congr h]

@[simp]
theorem reducedEllipticLevel_neg : reducedEllipticLevel M (-Δ) ℓ = reducedEllipticLevel M Δ ℓ := by
  rw [reducedEllipticLevel_def, reducedEllipticLevel_def, levelLoweringPrimes_neg]

/-- The exponent of `q` in the product of the level-lowering primes is `1` or `0` according as
`q` is or is not one of them. -/
private theorem factorization_prod_levelLoweringPrimes (q : ℕ) :
    (∏ p ∈ levelLoweringPrimes M Δ ℓ, p).factorization q =
      if q ∈ levelLoweringPrimes M Δ ℓ then 1 else 0 := by
  rw [Nat.factorization_prod fun p hp ↦ (prime_of_mem_levelLoweringPrimes hp).ne_zero,
    Finset.sum_apply']
  calc ∑ p ∈ levelLoweringPrimes M Δ ℓ, p.factorization q
      = ∑ p ∈ levelLoweringPrimes M Δ ℓ, if p = q then 1 else 0 :=
        Finset.sum_congr rfl fun p hp ↦ by
          rw [(prime_of_mem_levelLoweringPrimes hp).factorization, Finsupp.single_apply]
    _ = _ := Finset.sum_ite_eq' _ _ _

/-- **The exponents of the reduced level**: at a prime `q`, the exponent of `q` in `M₀` is `0` if
`q` is a level-lowering prime and the exponent of `q` in `M` otherwise. -/
theorem multiplicity_reducedEllipticLevel (hq : q.Prime) :
    multiplicity q (reducedEllipticLevel M Δ ℓ) =
      if q ∈ levelLoweringPrimes M Δ ℓ then 0 else multiplicity q M := by
  rw [← Nat.factorization_def _ hq, ← Nat.factorization_def _ hq, reducedEllipticLevel_def,
    Nat.factorization_div prod_levelLoweringPrimes_dvd, Finsupp.tsub_apply,
    factorization_prod_levelLoweringPrimes]
  split_ifs with h
  · rw [Nat.factorization_def _ hq, multiplicity_eq_one_of_mem_levelLoweringPrimes h]
  · rw [Nat.sub_zero]

/-- **Higher conductor exponents are kept**: if a prime `q` occurs in `M` to exponent at least
two, it occurs in `M₀` to the same exponent. -/
theorem multiplicity_reducedEllipticLevel_of_one_lt (hq : q.Prime) (h : 1 < multiplicity q M) :
    multiplicity q (reducedEllipticLevel M Δ ℓ) = multiplicity q M := by
  have : q ∉ levelLoweringPrimes M Δ ℓ := fun hq' ↦
    h.ne' (multiplicity_eq_one_of_mem_levelLoweringPrimes hq')
  simp [multiplicity_reducedEllipticLevel hq, this]

/-- **The reduced level loses exactly the level-lowering primes**: a prime `q` divides `M₀`
exactly when it divides `M` and is not a level-lowering prime. -/
theorem prime_dvd_reducedEllipticLevel_iff (hq : q.Prime) :
    q ∣ reducedEllipticLevel M Δ ℓ ↔ q ∣ M ∧ q ∉ levelLoweringPrimes M Δ ℓ := by
  rcases eq_or_ne M 0 with rfl | hM
  · simp [levelLoweringPrimes_def]
  have hM₀ : reducedEllipticLevel M Δ ℓ ≠ 0 := reducedEllipticLevel_eq_zero_iff.not.2 hM
  rw [hq.dvd_iff_one_le_factorization hM₀, hq.dvd_iff_one_le_factorization hM,
    Nat.factorization_def _ hq, Nat.factorization_def _ hq, multiplicity_reducedEllipticLevel hq]
  split_ifs with h <;> simp [h]

/-- **A prime `q ∥ M` divides `M₀` exactly when `ℓ ∤ v_q(|Δ|)`.** This includes `q = ℓ`: the
reduced level can keep or remove the prime `ℓ`. -/
theorem prime_dvd_reducedEllipticLevel_iff_of_multiplicity_eq_one (hq : q.Prime)
    (h : multiplicity q M = 1) :
    q ∣ reducedEllipticLevel M Δ ℓ ↔ ¬ ℓ ∣ multiplicity q Δ.natAbs := by
  rw [prime_dvd_reducedEllipticLevel_iff hq, mem_levelLoweringPrimes]
  simp [hq, h, dvd_of_one_le_multiplicity h.ge]

/-- **The reduced level is the level exactly when no prime is removed.** -/
theorem reducedEllipticLevel_eq_self_iff :
    reducedEllipticLevel M Δ ℓ = M ↔ levelLoweringPrimes M Δ ℓ = ∅ := by
  rcases eq_or_ne M 0 with rfl | hM
  · simp [levelLoweringPrimes_def]
  refine ⟨fun h ↦ ?_, fun h ↦ by
    rw [reducedEllipticLevel_def, h, Finset.prod_empty, Nat.div_one]⟩
  have hprod := reducedEllipticLevel_mul_prod_levelLoweringPrimes (M := M) (Δ := Δ) (ℓ := ℓ)
  rw [h, Nat.mul_eq_left hM] at hprod
  exact Finset.eq_empty_of_forall_notMem fun q hq ↦
    (prime_of_mem_levelLoweringPrimes hq).one_lt.ne'
      ((Finset.prod_eq_one_iff_of_one_le fun p hp ↦
        (prime_of_mem_levelLoweringPrimes hp).one_lt.le).1 hprod q hq)

end Nat

namespace WeierstrassCurve

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (ℓ : ℕ)

/-- **The reduced level** `M₀` of an elliptic curve `E` over `ℚ` at `ℓ`: the reduced level
`Nat.reducedEllipticLevel M Δ ℓ` of its conductor `M`, the norm of the algorithmic conductor,
and its minimal discriminant `Δ`, up to sign the norm of the minimal discriminant ideal. For a
prime `ℓ ≥ 3` it divides out the primes `q ∥ M` with `ℓ ∣ v_q(Δ)`. -/
noncomputable def reducedLevel : ℕ :=
  Nat.reducedEllipticLevel (Ideal.absNorm (algorithmicConductor ℤ E))
    (Ideal.absNorm (minimalDiscriminantIdeal ℤ E)) ℓ

theorem reducedLevel_def :
    E.reducedLevel ℓ = Nat.reducedEllipticLevel (Ideal.absNorm (algorithmicConductor ℤ E))
      (Ideal.absNorm (minimalDiscriminantIdeal ℤ E)) ℓ := by
  rw [reducedLevel]

/-- **The reduced level divides the conductor.** -/
theorem reducedLevel_dvd : E.reducedLevel ℓ ∣ Ideal.absNorm (algorithmicConductor ℤ E) :=
  Nat.reducedEllipticLevel_dvd

/-- **The reduced level is positive.** -/
theorem reducedLevel_pos : 0 < E.reducedLevel ℓ :=
  Nat.reducedEllipticLevel_pos <| Nat.pos_of_ne_zero <|
    Ideal.absNorm_eq_zero_iff.not.2 (algorithmicConductor_ne_bot ℤ E)

/-- **The reduced level is invariant under a change of variables**, so it is an invariant of the
curve and not of the equation presenting it. -/
@[simp]
theorem reducedLevel_smul (C : VariableChange ℚ) : (C • E).reducedLevel ℓ = E.reducedLevel ℓ := by
  simp only [reducedLevel_def, algorithmicConductor_smul, minimalDiscriminantIdeal_smul]

variable {E} in
/-- **The reduced level of a globally minimal equation** is computed from the discriminant of its
integral model: for `W₀` over `ℤ` with `W₀.baseChange ℚ = E` globally minimal, the reduced level
is `Nat.reducedEllipticLevel M W₀.Δ ℓ` with `M` the conductor. -/
theorem IsGlobalMinimal.reducedLevel_eq (h : IsGlobalMinimal ℤ E) {W₀ : WeierstrassCurve ℤ}
    (hW₀ : W₀.baseChange ℚ = E) :
    E.reducedLevel ℓ =
      Nat.reducedEllipticLevel (Ideal.absNorm (algorithmicConductor ℤ E)) W₀.Δ ℓ := by
  rw [reducedLevel_def, minimalDiscriminantIdeal_eq_span_of_isGlobalMinimal h (d := W₀.Δ)
    (algebraMap_Δ_of_baseChange_eq hW₀), Ideal.absNorm_span_singleton]
  exact Nat.reducedEllipticLevel_congr fun q _ _ ↦ by simp [Int.natAbs_abs]

end WeierstrassCurve
