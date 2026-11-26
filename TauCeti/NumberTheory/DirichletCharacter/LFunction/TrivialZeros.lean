/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import TauCeti.NumberTheory.DirichletCharacter.LFunction.NonpositiveIntegers
import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.FractionRing
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.DirichletCharacter.LFunction.ChangeLevel
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Completed.Basic
import TauCeti.NumberTheory.MulChar.Basic
import TauCeti.NumberTheory.MulChar.GaloisOrbit

/-!
# Trivial zeros of imprimitive Dirichlet L-functions

Mathlib's `DirichletCharacter.LFunction_eq_zero_iff_of_re_nonpos` locates the zeros of the
L-function of a *primitive* Dirichlet character in the closed left half-plane: they are the poles
of its gamma factor. This file removes the primitivity assumption in the open left half-plane.
Raising the level of a character multiplies its L-function by the Euler factors
`1 - χ(p) p⁻ˢ` at the new primes, and for `Re s < 0` each of them has a term of absolute value
`0` or `p^(-Re s) > 1`, so it does not vanish
(`DirichletCharacter.prod_one_sub_mul_prime_cpow_ne_zero`).

At the negative integers `-k`, the zero is there exactly when `χ(-1) = (-1)ᵏ`. Through
`L(χ, 1 - k) = -Bₖ,χ / k` this decides the vanishing of the generalized Bernoulli numbers
`Bₖ,χ` of every character, primitive or not, for `k ≥ 2`: `Bₖ,χ ≠ 0` exactly when
`χ(-1) = (-1)ᵏ`. For `k = 1` the imprimitive statement fails: the odd character modulo `21`
induced by the odd character `χ₀` modulo `3` has `B₁,χ = 0`, because of the Euler factor
`1 - χ₀(7)` at `7 ≡ 1` modulo `3`.

## Main results

* `DirichletCharacter.LFunction_eq_zero_iff_of_re_neg`: for every Dirichlet character `χ` and
  `Re s < 0`, `L(χ, s) = 0` exactly when `s` is a pole of the gamma factor of `χ`.
* `DirichletCharacter.LFunction_neg_natCast_eq_zero_iff`: for `k ≥ 1`, `L(χ, -k) = 0` exactly
  when `χ(-1) = (-1)ᵏ`.
* `DirichletCharacter.generalizedBernoulli_ne_zero`: for `k ≥ 2` and a character with values in a
  nonzero `ℚ`-algebra with `χ(-1) = (-1)ᵏ`, `Bₖ,χ ≠ 0`; and
  `DirichletCharacter.generalizedBernoulli_eq_zero_iff` is the resulting characterization for
  values in a domain of characteristic zero.

## References

* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I*, Corollaries 10.3 and
  10.8.
* L. C. Washington, *Introduction to Cyclotomic Fields*, 2nd ed., Theorem 4.2 and §4.1.

## Provenance

The reduction to the primitive character through the Euler factors at the new primes is adapted
from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC),
file `src/Lib/Analytic/ZeroSymmetry.lean`, declarations `New.prod_euler_factor_ne_zero` and
`New.gammaFactor_eq_zero_or_LFunction_one_sub_eq_zero`, and file
`src/Lib/Cyclotomic/Voronoi.lean`, declarations `New.OddPart.LFunction_neg_nat_eq_zero_iff` and
`New.OddPart.sum_mul_bernoulli_ne_zero`. Here the statements are made for the gamma factor in the
whole open left half-plane and for Tau Ceti's `DirichletCharacter.generalizedBernoulli`.
-/

public section

open Complex

namespace DirichletCharacter

/-- **Trivial zeros of imprimitive L-functions.** For every Dirichlet character `χ` and every `s`
with `Re s < 0`, `L(χ, s) = 0` exactly when `s` is a pole of the gamma factor of `χ` (where
Mathlib's `gammaFactor` takes the value `0`). Primitivity is not needed, in contrast with
`DirichletCharacter.LFunction_eq_zero_iff_of_re_nonpos`. -/
theorem LFunction_eq_zero_iff_of_re_neg {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : s.re < 0) :
    χ.LFunction s = 0 ↔ χ.gammaFactor s = 0 := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hs1 : s ≠ 1 := fun h ↦ by simp [h] at hs; linarith
  have hs0 : s ≠ 0 := fun h ↦ by simp [h] at hs
  conv_lhs => rw [← χ.changeLevel_primitiveCharacter]
  rw [LFunction_changeLevel _ _ (.inr hs1),
    mul_eq_zero_iff_right (prod_one_sub_mul_prime_cpow_ne_zero _ hs.ne),
    LFunction_eq_zero_iff_of_re_nonpos χ.primitiveCharacter_isPrimitive hs.le,
    gammaFactor_primitiveCharacter]
  simp [hs0]

/-- **Trivial zeros at the negative integers.** For every Dirichlet character `χ`, primitive or
not, and `k ≥ 1`, `L(χ, -k) = 0` exactly when `χ(-1) = (-1)ᵏ`. -/
theorem LFunction_neg_natCast_eq_zero_iff {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {k : ℕ} (hk : k ≠ 0) :
    χ.LFunction (-k) = 0 ↔ χ (-1) = (-1) ^ k := by
  rw [LFunction_eq_zero_iff_of_re_neg χ (by simpa using Nat.pos_of_ne_zero hk)]
  rcases χ.even_or_odd with hχ | hχ
  · have hχ1 : χ (-1) = 1 := by simpa using DirichletCharacter.Even.eval_neg χ 1 hχ
    rw [gammaFactor_eq_zero_iff_of_even hχ, hχ1, eq_comm,
      neg_one_pow_eq_one_iff_even (by norm_num)]
    refine ⟨fun ⟨n, hn⟩ ↦ ⟨n, ?_⟩, fun ⟨n, hn⟩ ↦ ⟨n, ?_⟩⟩
    · have hkn : (k : ℂ) = n + n := by linear_combination -hn
      exact_mod_cast hkn
    · rw [hn]; push_cast; ring
  · have hχ1 : χ (-1) = -1 := by simpa using DirichletCharacter.Odd.eval_neg χ 1 hχ
    rw [gammaFactor_eq_zero_iff_of_odd hχ, hχ1, eq_comm,
      neg_one_pow_eq_neg_one_iff_odd (by norm_num)]
    refine ⟨fun ⟨n, hn⟩ ↦ ⟨n, ?_⟩, fun ⟨n, hn⟩ ↦ ⟨n, ?_⟩⟩
    · have hkn : (k : ℂ) = 2 * n + 1 := by linear_combination -hn
      exact_mod_cast hkn
    · rw [hn]; push_cast; ring

/-- For `k ≥ 2` and a complex character with `χ(-1) = (-1)ᵏ`, the generalized Bernoulli number
`Bₖ,χ` is nonzero: `-Bₖ,χ / k = L(χ, 1 - k)` is not a trivial zero. -/
private theorem generalizedBernoulli_ne_zero_complex {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {k : ℕ} (hk : 2 ≤ k) (hχ : χ (-1) = (-1) ^ k) :
    χ.generalizedBernoulli k ≠ 0 := by
  intro h
  have hL := LFunction_one_sub_natCast χ (k := k) (by omega)
  have hk' : (1 : ℂ) - k = -((k - 1 : ℕ) : ℂ) := by
    rw [Nat.cast_sub (by omega)]
    ring
  rw [h, neg_zero, zero_div, hk', LFunction_neg_natCast_eq_zero_iff χ (by omega), hχ] at hL
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
  have hj : j + 2 - 1 = j + 1 := by omega
  rw [hj, pow_succ, pow_succ] at hL
  exact pow_ne_zero j (neg_ne_zero.2 one_ne_zero : (-1 : ℂ) ≠ 0) (by linear_combination hL / 2)

/-- `generalizedBernoulli_ne_zero` for a character with values in a domain: pass to the fraction
field, then to the subfield generated by the values, which embeds into `ℂ`. -/
private theorem generalizedBernoulli_ne_zero_of_isDomain {N : ℕ} [NeZero N] {R : Type*} [CommRing R]
    [IsDomain R] [Algebra ℚ R] {χ : DirichletCharacter R N} {k : ℕ} (hk : 2 ≤ k)
    (hχ : χ (-1) = (-1) ^ k) :
    χ.generalizedBernoulli k ≠ 0 := by
  let F := FractionRing R
  let f : R →ₐ[ℚ] F := (algebraMap R F).toRatAlgHom
  have hf : Function.Injective f := IsFractionRing.injective R F
  set χF : DirichletCharacter F N := χ.ringHomComp (f : R →+* F)
  have hχF : χF (-1) = (-1) ^ k := by simp [χF, hχ]
  suffices hF : χF.generalizedBernoulli k ≠ 0 by
    rwa [← map_generalizedBernoulli, ← map_zero f, Ne, hf.eq_iff] at hF
  set K := IntermediateField.adjoin ℚ (Set.range χF)
  let χK : DirichletCharacter K N := χF.restrictValues
  let j : K →ₐ[ℚ] F := (K.val : K →+* F).toRatAlgHom
  have hχK : χK.ringHomComp (j : K →+* F) = χF := by
    rw [RingHom.toRatAlgHom_toRingHom]
    exact χF.ringHomComp_restrictValues
  let ι : K →ₐ[ℚ] ℂ := IsAlgClosed.lift
  have hK : χK (-1) = (-1) ^ k := j.injective <| by
    simpa [← hχK, MulChar.ringHomComp_apply] using hχF
  have hι : (χK.ringHomComp (ι : K →+* ℂ)) (-1) = (-1) ^ k := by
    simp [MulChar.ringHomComp_apply, hK]
  have hC := generalizedBernoulli_ne_zero_complex hk hι
  rw [← hχK, ← map_generalizedBernoulli]
  rw [← map_generalizedBernoulli] at hC
  exact fun h ↦ hC (by rw [j.injective (h.trans (map_zero j).symm), map_zero])

/-- **Non-vanishing of generalized Bernoulli numbers.** Let `χ` be a Dirichlet character, not
necessarily primitive, with values in a nonzero `ℚ`-algebra, and let `k ≥ 2` with
`χ(-1) = (-1)ᵏ`. Then `Bₖ,χ ≠ 0`. For an imprimitive character this needs the deleted Euler
factors `1 - χ₀(p) pᵏ⁻¹` to be nonzero, which fails for `k = 1`. -/
theorem generalizedBernoulli_ne_zero {N : ℕ} [NeZero N] {R : Type*} [CommRing R] [Nontrivial R]
    [Algebra ℚ R] {χ : DirichletCharacter R N} {k : ℕ} (hk : 2 ≤ k) (hχ : χ (-1) = (-1) ^ k) :
    χ.generalizedBernoulli k ≠ 0 := by
  -- map to the field `R ⧸ m` for a maximal ideal `m`
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  have := hm.isPrime
  let f : R →ₐ[ℚ] R ⧸ m := Ideal.Quotient.mkₐ ℚ m
  have h := generalizedBernoulli_ne_zero_of_isDomain (χ := χ.ringHomComp (f : R →+* R ⧸ m)) hk
    (by simp [MulChar.ringHomComp_apply, hχ])
  rw [← map_generalizedBernoulli] at h
  exact fun h0 ↦ h (by rw [h0, map_zero])

/-- **Vanishing of generalized Bernoulli numbers.** For `k ≥ 2` and a Dirichlet character `χ`, not
necessarily primitive, with values in a domain of characteristic zero, `Bₖ,χ = 0` exactly when the
parities of `χ` and `k` differ. -/
theorem generalizedBernoulli_eq_zero_iff {N : ℕ} [NeZero N] {R : Type*} [CommRing R] [IsDomain R]
    [Algebra ℚ R] {χ : DirichletCharacter R N} {k : ℕ} (hk : 2 ≤ k) :
    χ.generalizedBernoulli k = 0 ↔ χ (-1) = -(-1) ^ k := by
  refine ⟨fun h ↦ ?_, generalizedBernoulli_eq_zero_of_apply_neg_one_eq_neg (.inl (by omega))⟩
  exact (χ.apply_neg_one_eq_neg_one_pow_or k).resolve_left (generalizedBernoulli_ne_zero hk · h)

end DirichletCharacter
