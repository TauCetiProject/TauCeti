/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Diagonal.Composite
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Prime.Power

/-!
# The Fourier coefficient of `T_n F` at an index coprime to `n`

The composite element `heckeTCompositeGamma0 N n` of the `Γ₀(N)` Hecke ring is the ordered
product of the prime-power blocks `heckeTGeneratorRecGamma0 N p (v_p n)` over the primes of `n`
(`HeckeRing/GL2/Gamma0/Diagonal/Composite.lean`), and each block reads the coefficient at
`p^{v_p n} m` — at a good prime when `p ∤ m`, and at a prime dividing the level unconditionally
(`HeckeSlash/Nebentypus/Prime/Power.lean`). Peeling the blocks off one at a time therefore
gives, for `n ≠ 0` and `m` coprime to `n`,

`a_m(T_n F) = a_{m n}(F)`.

Coprimality of `m` and `n` is what makes the formula this simple: each block meets an index
prime to its own prime, so only the leading term of the prime-power formula survives. At `m = 1`
it says `a_1(T_n F) = a_n(F)`; read on a Hecke eigenvector, where `T_n F = λ_n F`, that is
`a_n(F) = λ_n a_1(F)` — the coefficient form of the eigenvalue system
(`Newforms/Coefficient.lean`).

The same peeling, run on the operators rather than on the coefficients, shows that a subspace
of `S_k(N, χ)` stable under every prime generator `T_p` is stable under every `T_n`: each block
is a polynomial in `T_p` and the scalar coset `T(p, p)`, which acts on `S_k(N, χ)` by a scalar.

## Main results

* `HeckeRing.GL2.heckeRingHomCuspCharSpace_heckeTCompositeGamma0_mem_of_forall_prime_dvd`: a
  subspace of `S_k(N, χ)` stable under `T_p` at every prime `p ∣ n` is stable under `T_n`.
* `HeckeRing.GL2.qExpansion_coeff_heckeRingHomCharSpace_heckeTCompositeGamma0_of_coprime`:
  `a_m(T_n F) = a_{m n}(F)` for `n ≠ 0` and `m` coprime to `n`, on `M_k(N, χ)`.
* `HeckeRing.GL2.qExpansion_coeff_one_heckeRingHomCharSpace_heckeTCompositeGamma0`: its `m = 1`
  case `a_1(T_n F) = a_n(F)`, the normalisation reading an arbitrary coefficient of `F` off the
  first coefficient of `T_n F`.
* `HeckeRing.GL2.qExpansion_coeff_heckeRingHomCuspCharSpace_heckeTCompositeGamma0_of_coprime`:
  its specialisation to `S_k(N, χ)`, along `cuspToModFormCharSpace`.

## Provenance

Adapted from the AINTLIB `LeanModularForms` project (Chris Birkbeck, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB> @ `2baa76f742bdb4fb8ee323fabba41203bd390e08`),
`projects/LeanModularForms/LeanModularForms/HeckeRIngs/GL2/FourierHecke.lean` —
`fourierCoeff_heckeT_n_period_one`, the divisor-sum formula at a general index for the source's
concretely-defined `heckeT_n`, which at indices coprime to `n` collapses to the single
coefficient below. Here the operator is the Hecke ring's composite element
`heckeTCompositeGamma0` acting through `heckeRingHomCharSpace`, so the proof peels its
prime-power blocks instead of summing over divisors.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §5.3.
* [T. Miyake, *Modular forms*][miyake1989], §4.5.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups HeckeCosetModule

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N] {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ}

/-- **The Fourier coefficient of `T_n F` at an index coprime to `n`.** For `n ≠ 0` and `m`
coprime to `n`, the Hecke ring's composite element reads the coefficient at `m n`:
`a_m(T_n F) = a_{m n}(F)`. No hypothesis relating `n` to the level is needed: the blocks at the
primes dividing `N` shift every coefficient. -/
theorem qExpansion_coeff_heckeRingHomCharSpace_heckeTCompositeGamma0_of_coprime {n : ℕ}
    (hn : n ≠ 0) (F : modFormCharSpace k χ) {m : ℕ} (hmn : Nat.Coprime m n) :
    (qExpansion 1 (heckeRingHomCharSpace k χ (heckeTCompositeGamma0 N n) F :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff m =
      (qExpansion 1 (F : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff (m * n) := by
  suffices key : ∀ n : ℕ, n ≠ 0 → ∀ m : ℕ, Nat.Coprime m n →
      (qExpansion 1 (heckeRingHomCharSpace k χ (heckeTCompositeGamma0 N n) F :
          ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff m =
        (qExpansion 1 (F : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff (m * n) by
    exact key n hn m hmn
  clear hmn hn m n
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn m hmn
  by_cases h1 : n = 1
  · subst h1
    rw [heckeTCompositeGamma0_one, map_one, Module.End.one_apply, mul_one]
  · -- peel the block at the least prime factor `p` of `n`, carrying its whole multiplicity
    have hlt : 1 < n := by omega
    rw [heckeTCompositeGamma0_of_one_lt N hlt, map_mul, Module.End.mul_apply]
    have hp : (n.minFac).Prime := Nat.minFac_prime h1
    have hpn : n.minFac ∣ n := Nat.minFac_dvd n
    have hv : n.factorization n.minFac ≠ 0 :=
      (hp.factorization_pos_of_dvd hn hpn).ne'
    have hnn' : n.minFac ^ n.factorization n.minFac *
        (n / n.minFac ^ n.factorization n.minFac) = n :=
      Nat.ordProj_mul_ordCompl_eq_self n n.minFac
    have hn'0 : n / n.minFac ^ n.factorization n.minFac ≠ 0 := by
      intro h
      rw [h, mul_zero] at hnn'
      exact hn hnn'.symm
    have hn'lt : n / n.minFac ^ n.factorization n.minFac < n :=
      Nat.div_lt_self (Nat.pos_of_ne_zero hn) (Nat.one_lt_pow hv hp.one_lt)
    have hpm : ¬ n.minFac ∣ m :=
      (hp.coprime_iff_not_dvd).mp (Nat.Coprime.coprime_dvd_right hpn hmn).symm
    have hcop : Nat.Coprime (n.minFac ^ n.factorization n.minFac * m)
        (n / n.minFac ^ n.factorization n.minFac) :=
      Nat.Coprime.mul_left ((Nat.coprime_ordCompl hp hn).pow_left _)
        (Nat.Coprime.coprime_dvd_right (Nat.ordCompl_dvd n n.minFac) hmn)
    -- the block at `n.minFac` shifts by `n.minFac ^ v`, whether or not that prime divides `N`
    by_cases hpN : n.minFac ∣ N
    · rw [qExpansion_coeff_heckeRingHomCharSpace_heckeTGeneratorRecGamma0_of_dvd_level hp hpN,
        ih _ hn'lt hn'0 _ hcop, mul_comm (n.minFac ^ n.factorization n.minFac) m, mul_assoc,
        hnn']
    · rw [qExpansion_coeff_heckeRingHomCharSpace_heckeTGeneratorRecGamma0_of_not_dvd hp
          (hp.coprime_iff_not_dvd.mpr hpN) _ hpm,
        ih _ hn'lt hn'0 _ hcop, mul_comm (n.minFac ^ n.factorization n.minFac) m, mul_assoc,
        hnn']

/-- **The first Fourier coefficient of `T_n F` is the `n`-th coefficient of `F`**:
`a_1(T_n F) = a_n(F)`, the `m = 1` case of
`qExpansion_coeff_heckeRingHomCharSpace_heckeTCompositeGamma0_of_coprime`. It is this
normalisation that lets an arbitrary coefficient of `F` be read off a first coefficient. -/
theorem qExpansion_coeff_one_heckeRingHomCharSpace_heckeTCompositeGamma0 {n : ℕ} (hn : n ≠ 0)
    (F : modFormCharSpace k χ) :
    (qExpansion 1 (heckeRingHomCharSpace k χ (heckeTCompositeGamma0 N n) F :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff 1 =
      (qExpansion 1 (F : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff n := by
  simpa using qExpansion_coeff_heckeRingHomCharSpace_heckeTCompositeGamma0_of_coprime hn F
    (Nat.coprime_one_left n)

/-- **The Fourier coefficient of `T_n F` at an index coprime to `n`, on `S_k(N, χ)`**: the case
of `qExpansion_coeff_heckeRingHomCharSpace_heckeTCompositeGamma0_of_coprime` at a cusp form,
transported along the inclusion of character spaces. -/
theorem qExpansion_coeff_heckeRingHomCuspCharSpace_heckeTCompositeGamma0_of_coprime {n : ℕ}
    (hn : n ≠ 0) (F : cuspFormCharSpace k χ) {m : ℕ} (hmn : Nat.Coprime m n) :
    (qExpansion 1 (heckeRingHomCuspCharSpace k χ (heckeTCompositeGamma0 N n) F :
        CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff m =
      (qExpansion 1 (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff (m * n) := by
  have h := qExpansion_coeff_heckeRingHomCharSpace_heckeTCompositeGamma0_of_coprime hn
    (cuspToModFormCharSpace k χ F) hmn
  rw [heckeRingHomCharSpace_apply, ← cuspToModFormCharSpace_twistedHeckeSlashCuspFormCharLinearMap,
    ← heckeRingHomCuspCharSpace_apply] at h
  simp only [coe_cuspToModFormCharSpace, ModularFormClass.coe_modularForm] at h
  exact h

/-- **A subspace of `S_k(N, χ)` stable under the prime generators `T_p` at every prime `p ∣ n` is
stable under `T_n`.** The composite element `heckeTCompositeGamma0 N n` is a product of the
prime-power blocks `T_{p^v}` over the primes `p ∣ n`, each a polynomial in `T_p` and the scalar
coset `T(p, p)`; the latter acts on `S_k(N, χ)` by the scalar `χ(p) p^{k-2}` when `p ∤ N` and is
`0` when `p ∣ N`, so it preserves every subspace. -/
theorem heckeRingHomCuspCharSpace_heckeTCompositeGamma0_mem_of_forall_prime_dvd
    {V : Submodule ℂ (cuspFormCharSpace k χ)} {n : ℕ}
    (hV : ∀ p : ℕ, p.Prime → p ∣ n → ∀ F ∈ V,
      heckeRingHomCuspCharSpace k χ (heckeTGeneratorGamma0 N p) F ∈ V)
    {F : cuspFormCharSpace k χ} (hF : F ∈ V) :
    heckeRingHomCuspCharSpace k χ (heckeTCompositeGamma0 N n) F ∈ V := by
  -- the elements of the Hecke ring whose action preserves `V` form a subring; membership in `S`
  -- is, by definition, its carrier predicate, which `intro` and the final `refine` unfold
  let S : Subring (𝕋 (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ℤ) :=
    { carrier := {x | ∀ F ∈ V, heckeRingHomCuspCharSpace k χ x F ∈ V}
      mul_mem' := fun ha hb F hF ↦ by
        rw [map_mul, Module.End.mul_apply]
        exact ha _ (hb F hF)
      one_mem' := fun F hF ↦ by rwa [map_one, Module.End.one_apply]
      add_mem' := fun ha hb F hF ↦ by
        rw [map_add, LinearMap.add_apply]
        exact V.add_mem (ha F hF) (hb F hF)
      zero_mem' := fun F _ ↦ by
        rw [map_zero, LinearMap.zero_apply]
        exact V.zero_mem
      neg_mem' := fun ha F hF ↦ by
        rw [map_neg, LinearMap.neg_apply]
        exact V.neg_mem (ha F hF) }
  -- it contains every prime generator, and the scalar cosets, which act by scalars; hence every
  -- composite
  refine (heckeTCompositeGamma0_mem_of_forall_prime_dvd N (S := S) (fun p hp hpn ↦ hV p hp hpn)
    fun p hp _ ↦ ?_) F hF
  by_cases hpN : Nat.Coprime p N
  · intro F hF
    rw [heckeRingHomCuspCharSpace_heckeTScalarGamma0 k χ p hp.pos hpN, LinearMap.smul_apply,
      Module.End.one_apply]
    exact V.smul_mem _ hF
  · rw [heckeTScalarGamma0_of_not_coprime N hpN]
    exact S.zero_mem

end HeckeRing.GL2
