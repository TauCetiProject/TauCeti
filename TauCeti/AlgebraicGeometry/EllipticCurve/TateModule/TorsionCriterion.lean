/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.TateModule.GoodReduction
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateModule.PotentialGoodReduction
-- Proof-only: a natural number invertible in `𝒪[K]` is nonzero in `K`.
import TauCeti.Algebra.Algebra.NatCast

/-!
# Good reduction from unramified torsion at potential good reduction

Let `K` be a nonarchimedean local field with residue field `k`, and let `W` be an elliptic curve
over `K` given by a minimal equation, with potential good reduction. This file proves the
finite-level form of the criterion of Néron, Ogg and Shafarevich (Serre–Tate; compare Silverman
AEC VII.7.1 and VII.7.3): for an integer `N ≥ 3` prime to the characteristic of `k`, the curve has
good reduction exactly when the inertia subgroup `I_K` of `Gal(K^{alg}/K)` fixes every point of
`E(K^{alg})[N]`, equivalently when the division field `K(E[N])` is unramified over `K`.

Good reduction fixes the division points prime to `char k`
(`WeierstrassCurve.Affine.Point.map_eq_self_of_mem_inertiaSubgroup_algebraicClosure`). For the
converse, write `ℓ ^ k` for a divisor of `N` equal to `4` or to an odd prime, so that `ℓ ^ k ≥ 3`.

* At potential good reduction, `I_K` acts on `T_ℓ E` through a finite quotient
  (`WeierstrassCurve.HasPotentialGoodReduction.finite_image_tateModuleGaloisRepresentation`).
* An element of `I_K` fixes `E[ℓ ^ k] ⊆ E[N]`, so by Serre's lemma it acts trivially on `T_ℓ E`
  (`WeierstrassCurve.tateModuleGaloisRepresentation_eq_one_of_finite_image`).
* An unramified Tate module forces good reduction
  (`WeierstrassCurve.hasGoodReduction_of_tateModuleGaloisRepresentation_eq_one`).

The hypothesis of potential good reduction cannot be dropped, since a curve with multiplicative
reduction can have unramified `N`-torsion. For instance the curve 11a1 has split multiplicative
reduction at `11` with minimal discriminant of valuation `5`, so its Tate parameter is a fifth
power up to an unramified unit and its `5`-torsion is unramified at `11`.

## Main results

* `WeierstrassCurve.HasPotentialGoodReduction.hasGoodReduction_of_forall_mem_inertiaSubgroup`: at
  potential good reduction, if `I_K` fixes `E(K^{alg})[N]` for some `N ≥ 3` prime to `char k`,
  then `W` has good reduction.
* `WeierstrassCurve.HasPotentialGoodReduction.hasGoodReduction_iff_forall_mem_inertiaSubgroup`:
  at potential good reduction, `W` has good reduction exactly when `I_K` fixes `E(K^{alg})[N]`.
* `WeierstrassCurve.HasPotentialGoodReduction.hasGoodReduction_iff_isUnramified_divisionField`:
  at potential good reduction, `W` has good reduction exactly when `K(E[N])/K` is unramified.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.7.1 and VII.7.3.
* J.-P. Serre and J. Tate, *Good reduction of abelian varieties*, Ann. of Math. 88 (1968),
  492–517.
-/

public section

open ValuativeRel TauCeti

namespace WeierstrassCurve

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {W : WeierstrassCurve K} [W.IsElliptic] [IsMinimal 𝒪[K] W]

namespace HasPotentialGoodReduction

open scoped Classical in
/-- **Unramified torsion forces good reduction at potential good reduction** (Néron, Ogg,
Shafarevich; Serre–Tate). Let `W` be an elliptic curve over a nonarchimedean local field `K`,
given by a minimal equation, with potential good reduction. If the inertia subgroup of
`Gal(K^{alg}/K)` fixes every point of `E(K^{alg})[N]`, for an integer `N ≥ 3` that is nonzero in
the residue field of `K`, then `W` has good reduction. -/
theorem hasGoodReduction_of_forall_mem_inertiaSubgroup (h : W.HasPotentialGoodReduction 𝒪[K])
    {N : ℕ} (hN : 3 ≤ N) (hNk : (N : 𝓀[K]) ≠ 0)
    (hfix : ∀ σ ∈ inertiaSubgroup K, ∀ P : (W⁄(AlgebraicClosure K)).toAffine.Point,
      N • P = 0 → Affine.Point.map σ.toAlgHom P = P) :
    W.HasGoodReduction 𝒪[K] := by
  -- `N` has a divisor `ℓ ^ k ≥ 3` with `ℓ` prime: either `4` or an odd prime.
  obtain ⟨ℓ, k, hℓ, hdvd, hk⟩ : ∃ ℓ k : ℕ, ℓ.Prime ∧ ℓ ^ k ∣ N ∧ 3 ≤ ℓ ^ k := by
    rcases Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt hN with h4 | ⟨p, hp, hpN, hodd⟩
    · exact ⟨2, 2, Nat.prime_two, h4, by norm_num⟩
    · obtain ⟨j, rfl⟩ := hodd
      have := hp.two_le
      exact ⟨2 * j + 1, 1, hp, by rwa [pow_one], by rw [pow_one]; omega⟩
  have : Fact ℓ.Prime := ⟨hℓ⟩
  -- `ℓ` divides `N`, so it is nonzero in the residue field.
  have hℓk : (ℓ : 𝓀[K]) ≠ 0 := by
    have hk₀ : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      omega
    obtain ⟨c, hc⟩ := (dvd_pow_self ℓ hk₀).trans hdvd
    exact fun h₀ ↦ hNk (by rw [hc, Nat.cast_mul, h₀, zero_mul])
  -- Inertia fixes `E[ℓ ^ k] ⊆ E[N]` and acts on `T_ℓ E` through a finite quotient, so it acts
  -- trivially on `T_ℓ E`.
  refine W.hasGoodReduction_of_tateModuleGaloisRepresentation_eq_one hℓk fun σ hσ ↦ ?_
  refine tateModuleGaloisRepresentation_eq_one_of_finite_image
    (h.finite_image_tateModuleGaloisRepresentation ℓ hℓk) hk (fun τ hτ P hP ↦ hfix τ hτ P ?_) hσ
  obtain ⟨c, rfl⟩ := hdvd
  rw [mul_comm, mul_nsmul', hP, nsmul_zero]

open scoped Classical in
/-- **The criterion of Néron, Ogg and Shafarevich with finite coefficients** (Serre–Tate). Let
`W` be an elliptic curve over a nonarchimedean local field `K`, given by a minimal equation, with
potential good reduction, and let `N ≥ 3` be an integer that is nonzero in the residue field of
`K`. Then `W` has good reduction exactly when the inertia subgroup of `Gal(K^{alg}/K)` fixes every
point of `E(K^{alg})[N]`. -/
theorem hasGoodReduction_iff_forall_mem_inertiaSubgroup (h : W.HasPotentialGoodReduction 𝒪[K])
    {N : ℕ} (hN : 3 ≤ N) (hNk : (N : 𝓀[K]) ≠ 0) :
    W.HasGoodReduction 𝒪[K] ↔
      ∀ σ ∈ inertiaSubgroup K, ∀ P : (W⁄(AlgebraicClosure K)).toAffine.Point,
        N • P = 0 → Affine.Point.map σ.toAlgHom P = P := by
  refine ⟨fun hW σ hσ P hP ↦ ?_, h.hasGoodReduction_of_forall_mem_inertiaSubgroup hN hNk⟩
  have : (integralModel 𝒪[K] W).IsElliptic :=
    ⟨(hasGoodReduction_iff_isUnit_integralModel_Δ 𝒪[K] W).1 hW⟩
  exact Affine.Point.map_eq_self_of_mem_inertiaSubgroup_algebraicClosure hNk hσ
    (by rw [hP, map_zero])

/-- **Good reduction is an unramified `N`-division field** at potential good reduction
(Serre–Tate). Let `W` be an elliptic curve over a nonarchimedean local field `K`, given by a
minimal equation, with potential good reduction, and let `N ≥ 3` be an integer that is nonzero in
the residue field of `K`. Then `W` has good reduction exactly when the `N`-division field
`K(E[N])` is unramified over `K`, for every structure of nonarchimedean local field on it
compatible with `K`. -/
theorem hasGoodReduction_iff_isUnramified_divisionField (h : W.HasPotentialGoodReduction 𝒪[K])
    {N : ℕ} (hN : 3 ≤ N) (hNk : (N : 𝓀[K]) ≠ 0) [ValuativeRel (W.divisionField N)]
    [TopologicalSpace (W.divisionField N)] [IsNonarchimedeanLocalField (W.divisionField N)]
    [ValuativeExtension K (W.divisionField N)] :
    W.HasGoodReduction 𝒪[K] ↔ IsUnramified K (W.divisionField N) := by
  have hNK : (N : K) ≠ 0 := IsUnit.natCast_ne_zero_of_algebra (K := 𝒪[K])
    ((IsLocalRing.residue_ne_zero_iff_isUnit _).1 (by rwa [map_natCast]))
  rw [h.hasGoodReduction_iff_forall_mem_inertiaSubgroup hN hNk,
    W.isUnramified_divisionField_iff_forall_mem_inertiaSubgroup hNK]

end HasPotentialGoodReduction

end WeierstrassCurve
