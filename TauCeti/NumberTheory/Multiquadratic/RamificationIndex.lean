/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.ResidueDegree
import TauCeti.FieldTheory.IntermediateField.Adjoin.EqTop
import TauCeti.NumberTheory.Multiquadratic.RamifiedPrimes
import TauCeti.NumberTheory.RamificationInertia.Galois

/-!
# The inertia group at an odd ramified prime of a multiquadratic field

Let `K = ℚ(√d₁, …, √dₙ)` be a number field generated over `ℚ` by square roots `r i` of integers
`d i`, and let `Q` be a prime of `𝓞 K` above an odd prime `p`. When `p` divides none of the `d i`
the inertia group of `Q` is trivial (`TauCeti.Multiquadratic.inertia_eq_bot_of_forall_not_dvd`).
This file treats the remaining odd primes, those dividing some radicand, assuming `p² ∤ dᵢ` (for
instance, squarefree radicands). The answer is that ramification at `p` is as small as it can be,
however many radicands `p` divides:

* the inertia group of `Q` has at most two elements, and its only possible nontrivial element is
  the sign change negating exactly the roots `r i` with `p ∣ dᵢ`;
* if `p` divides some `dᵢ`, that sign change does lie in the inertia group, which therefore has
  order `2`, and the ramification index of `Q` over `p` is `2`.

The upper bound is a direct computation in the style of the unramified case. An inertia element
`τ` fixes every root of a radicand prime to `p`
(`TauCeti.Multiquadratic.apply_eq_self_of_mem_inertia`). If `p` divides both `dᵢ = p a` and
`dⱼ = p b`, then `rᵢ rⱼ / p` squares to `a b`, which is prime to `p`, so `τ` fixes `rᵢ rⱼ / p`
too: `τ` acts by the same sign on all the roots of radicands divisible by `p`. Hence `τ` is
determined by that one sign. The lower bound is the ramification of `p` in `K`
(`TauCeti.Multiquadratic.isUnramifiedIn_iff_forall_not_dvd_of_ne_two`), which forces the
ramification index, common to all primes above `p` because `K / ℚ` is Galois, to exceed `1`.

As a consequence, the number `g` of primes above an odd ramified `p` and their common residue
degree `f` satisfy `g · f · 2 = [K : ℚ]`.

## Main results

* `TauCeti.Multiquadratic.apply_mul_apply_eq_mul_of_mem_inertia`: an inertia element acts by the
  same sign on the roots of any two radicands divisible by `p`.
* `TauCeti.Multiquadratic.eq_of_mem_inertia_of_ne_one` and
  `TauCeti.Multiquadratic.card_inertia_le_two`: the inertia group has at most one nontrivial
  element, so at most two elements.
* `TauCeti.Multiquadratic.mem_inertia_iff`: when `p` divides some radicand, the inertia group
  consists of the identity and the sign change negating exactly the roots of the radicands
  divisible by `p`.
* `TauCeti.Multiquadratic.card_inertia_eq_two` and
  `TauCeti.Multiquadratic.ramificationIdx_eq_two`: the inertia group has order `2`, and the
  ramification index is `2`, at an odd prime dividing some squarefree radicand.
* `TauCeti.Multiquadratic.ramificationIdx_eq_two_iff`: for squarefree radicands, the ramification
  index over an odd prime is `2` exactly when the prime divides some radicand (and it is `1`
  otherwise).
* `TauCeti.Multiquadratic.ncard_primesOver_mul_inertiaDeg_mul_two_eq_finrank`: the prime-count
  formula `g · f · 2 = [K : ℚ]` at an odd ramified prime.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §5.B.
* J. Neukirch, *Algebraic Number Theory*, Chapter I, §9.
-/

public section

open NumberField Ideal Module
open scoped NumberField

namespace TauCeti.Multiquadratic

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} {d : ι → ℤ} {r : ι → K}
  {p : ℕ} [Fact p.Prime]

/-! ### The action of inertia on the roots -/

/-- **Inertia acts by one sign on the roots of the radicands divisible by `p`.** Let `Q` be a
prime of `𝓞 K` above an odd prime `p`, and let `r i`, `r j` be square roots of integers `d i`,
`d j` that are divisible by `p` but not by `p²`. Then every element `τ` of the inertia group of
`Q` satisfies `τ (r i) * τ (r j) = r i * r j`: the root `r i * r j / p` of the integer
`(d i / p) * (d j / p)`, which is prime to `p`, is fixed by `τ`. -/
theorem apply_mul_apply_eq_mul_of_mem_inertia (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (hodd : p ≠ 2) {i j : ι} (hi : (p : ℤ) ∣ d i) (hi2 : ¬ (p : ℤ) ^ 2 ∣ d i)
    (hj : (p : ℤ) ∣ d j) (hj2 : ¬ (p : ℤ) ^ 2 ∣ d j) (Q : Ideal (𝓞 K)) [Q.IsPrime]
    [Q.LiesOver (span {(p : ℤ)})] {τ : K ≃ₐ[ℚ] K} (hτ : τ ∈ Q.inertia (K ≃ₐ[ℚ] K)) :
    τ (r i) * τ (r j) = r i * r j := by
  obtain ⟨a, ha⟩ := hi
  obtain ⟨b, hb⟩ := hj
  have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpa : ¬ (p : ℤ) ∣ a := fun h => hi2 (by rw [ha, pow_two]; exact mul_dvd_mul_left _ h)
  have hpb : ¬ (p : ℤ) ∣ b := fun h => hj2 (by rw [hb, pow_two]; exact mul_dvd_mul_left _ h)
  have hpab : ¬ (p : ℤ) ∣ a * b := fun h => (hp.dvd_or_dvd h).elim hpa hpb
  have hx : (r i * r j / p) ^ 2 = algebraMap ℤ K (a * b) := by
    rw [div_pow, mul_pow, hr i, hr j, ha, hb]
    field_simp
    simp
    ring
  have h := apply_eq_self_of_mem_inertia hx hodd hpab Q hτ
  rw [map_div₀, map_mul, map_natCast] at h
  exact (div_left_inj' hp0).mp h

variable (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
  (htop : IntermediateField.adjoin ℚ (Set.range r) = ⊤) (hodd : p ≠ 2)
  (hd : ∀ i, ¬ (p : ℤ) ^ 2 ∣ d i) (Q : Ideal (𝓞 K)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})]
include hr htop hodd hd

/-- **A nontrivial inertia element negates the roots of the radicands divisible by `p`.** Let `K`
be generated over `ℚ` by square roots `r i` of integers `d i` with `p² ∤ d i`, and let `Q` lie over
the odd prime `p`. A nontrivial element `τ` of the inertia group of `Q` sends `r i` to `-r i`
whenever `p ∣ d i`. (It fixes `r i` whenever `p ∤ d i`, by
`TauCeti.Multiquadratic.apply_eq_self_of_mem_inertia`.) -/
theorem apply_eq_neg_of_mem_inertia_of_ne_one {τ : K ≃ₐ[ℚ] K}
    (hτ : τ ∈ Q.inertia (K ≃ₐ[ℚ] K)) (hτ1 : τ ≠ 1) {i : ι} (hi : (p : ℤ) ∣ d i) :
    τ (r i) = -r i := by
  have hr' (j : ι) : r j ^ 2 = algebraMap ℚ K (d j : ℚ) := by rw [hr j]; simp
  have hri : r i ≠ 0 := by
    intro h0
    have h := hr i
    rw [h0, zero_pow two_ne_zero, eq_comm,
      map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective ℤ K)] at h
    exact hd i (h ▸ dvd_zero _)
  have hsq : τ (r i) ^ 2 = r i ^ 2 := by rw [← map_pow, hr' i, AlgEquiv.commutes]
  refine (eq_or_eq_neg_of_sq_eq_sq _ _ hsq).resolve_left fun hfix => hτ1 ?_
  -- If `τ` fixes `r i`, it fixes every generator, so it is the identity.
  refine TauCeti.IntermediateField.algEquiv_eq_one_of_adjoin_eq_top htop ?_
  rintro _ ⟨j, rfl⟩
  by_cases hj : (p : ℤ) ∣ d j
  · have h := apply_mul_apply_eq_mul_of_mem_inertia hr hodd hi (hd i) hj (hd j) Q hτ
    rw [hfix] at h
    exact mul_left_cancel₀ hri h
  · exact apply_eq_self_of_mem_inertia (hr j) hodd hj Q hτ

/-- **The inertia group has at most one nontrivial element.** Let `K` be generated over `ℚ` by
square roots of integers `d i` with `p² ∤ d i`, and let `Q` lie over the odd prime `p`. Any two
nontrivial elements of the inertia group of `Q` are equal: both negate exactly the roots of the
radicands divisible by `p`. -/
theorem eq_of_mem_inertia_of_ne_one {σ τ : K ≃ₐ[ℚ] K}
    (hσ : σ ∈ Q.inertia (K ≃ₐ[ℚ] K)) (hτ : τ ∈ Q.inertia (K ≃ₐ[ℚ] K)) (hσ1 : σ ≠ 1)
    (hτ1 : τ ≠ 1) : σ = τ := by
  refine TauCeti.IntermediateField.algEquiv_ext_of_adjoin_eq_top htop ?_
  rintro _ ⟨j, rfl⟩
  by_cases hj : (p : ℤ) ∣ d j
  · rw [apply_eq_neg_of_mem_inertia_of_ne_one hr htop hodd hd Q hσ hσ1 hj,
      apply_eq_neg_of_mem_inertia_of_ne_one hr htop hodd hd Q hτ hτ1 hj]
  · rw [apply_eq_self_of_mem_inertia (hr j) hodd hj Q hσ,
      apply_eq_self_of_mem_inertia (hr j) hodd hj Q hτ]

/-- **The inertia group at an odd prime has order at most `2`.** Let `K` be generated over `ℚ` by
square roots of integers `d i` with `p² ∤ d i`, and let `Q` lie over the odd prime `p`. Then the
inertia group of `Q` in `Gal(K/ℚ)` has at most two elements, however many of the `d i` are
divisible by `p`. -/
theorem card_inertia_le_two : Nat.card (Q.inertia (K ≃ₐ[ℚ] K)) ≤ 2 := by
  classical
  -- Recording whether an inertia element is the identity is injective.
  have hinj :
      Function.Injective fun τ : Q.inertia (K ≃ₐ[ℚ] K) => decide ((τ : K ≃ₐ[ℚ] K) = 1) := by
    intro σ τ h
    by_cases hσ1 : (σ : K ≃ₐ[ℚ] K) = 1
    · have hτ1 : (τ : K ≃ₐ[ℚ] K) = 1 := by simpa [hσ1] using h
      exact Subtype.ext (hσ1.trans hτ1.symm)
    · have hτ1 : (τ : K ≃ₐ[ℚ] K) ≠ 1 := by simpa [hσ1] using h
      exact Subtype.ext (eq_of_mem_inertia_of_ne_one hr htop hodd hd Q σ.2 τ.2 hσ1 hτ1)
  simpa using Nat.card_le_card_of_injective _ hinj

/-- The ramification index of a prime above an odd prime `p` is at most `2`, when no radicand is
divisible by `p²`. -/
theorem ramificationIdx_le_two [Finite ι] : Q.ramificationIdx ℤ ≤ 2 := by
  have := isGalois_rat hr htop
  rw [← Ideal.card_inertia_eq_ramificationIdx ℤ (K ≃ₐ[ℚ] K) Q]
  exact card_inertia_le_two hr htop hodd hd Q

omit hd in
/-- An odd prime dividing a squarefree radicand has ramification index greater than `1` at every
prime above it: it ramifies in `K`, and in the Galois extension `K / ℚ` unramifiedness at one prime
above `p` would spread to all of them. -/
private theorem one_lt_ramificationIdx [Finite ι] (hsf : ∀ i, Squarefree (d i)) {i : ι}
    (hi : (p : ℤ) ∣ d i) : 1 < Q.ramificationIdx ℤ := by
  have := isGalois_rat hr htop
  refine lt_of_le_of_ne (Q.ramificationIdx_pos ℤ) fun h1 => ?_
  have hunr : Algebra.IsUnramifiedAt ℤ Q := Ideal.ramificationIdx_eq_one_iff.mp h1.symm
  have hin : Algebra.IsUnramifiedIn (𝓞 K) (span {(p : ℤ)}) := fun P _ _ =>
    Ideal.isUnramifiedAt_of_isUnramifiedAt_of_isGaloisGroup (span {(p : ℤ)}) Q P (K ≃ₐ[ℚ] K)
  exact (isUnramifiedIn_iff_forall_not_dvd_of_ne_two hsf hr htop Fact.out hodd).mp hin i hi

omit hd in
/-- **The ramification index at an odd ramified prime is `2`.** Let `K` be generated over `ℚ` by
square roots `r i` of squarefree integers `d i`, and let `Q` be a prime of `𝓞 K` above an odd
prime `p` dividing some `d i`. Then the ramification index of `Q` over `p` is exactly `2`, however
many of the `d i` are divisible by `p`. -/
theorem ramificationIdx_eq_two [Finite ι] (hsf : ∀ i, Squarefree (d i)) {i : ι}
    (hi : (p : ℤ) ∣ d i) : Q.ramificationIdx ℤ = 2 := by
  have hd (j : ι) : ¬ (p : ℤ) ^ 2 ∣ d j := fun h =>
    (Nat.prime_iff_prime_int.mp Fact.out).not_isUnit (hsf j _ (by rwa [← pow_two]))
  have hle := ramificationIdx_le_two hr htop hodd hd Q
  have hlt := one_lt_ramificationIdx hr htop hodd Q hsf hi
  omega

omit hd in
/-- **Ramification at an odd prime.** Let `K` be generated over `ℚ` by square roots `r i` of
squarefree integers `d i`, and let `Q` be a prime of `𝓞 K` above an odd prime `p`. Then the
ramification index of `Q` over `p` is `2` if `p` divides some `d i`; otherwise it is `1`
(`TauCeti.Multiquadratic.isUnramifiedAt_of_forall_not_dvd`). -/
theorem ramificationIdx_eq_two_iff [Finite ι] (hsf : ∀ i, Squarefree (d i)) :
    Q.ramificationIdx ℤ = 2 ↔ ∃ i, (p : ℤ) ∣ d i := by
  refine ⟨fun h2 => ?_, fun ⟨i, hi⟩ => ramificationIdx_eq_two hr htop hodd Q hsf hi⟩
  by_contra hcon
  have : Algebra.IsUnramifiedAt ℤ Q := by
    have := isGalois_rat hr htop
    exact (isUnramifiedIn_iff_forall_not_dvd_of_ne_two hsf hr htop Fact.out hodd).mpr
      (not_exists.mp hcon) Q inferInstance inferInstance
  rw [Ideal.ramificationIdx_eq_one Q ℤ] at h2
  exact absurd h2 (by decide)

omit hd in
/-- **The inertia group at an odd ramified prime has order `2`.** Let `K` be generated over `ℚ` by
square roots of squarefree integers `d i`, and let `Q` be a prime of `𝓞 K` above an odd prime `p`
dividing some `d i`. Then the inertia group of `Q` in `Gal(K/ℚ)` has exactly two elements. -/
theorem card_inertia_eq_two [Finite ι] (hsf : ∀ i, Squarefree (d i)) {i : ι}
    (hi : (p : ℤ) ∣ d i) : Nat.card (Q.inertia (K ≃ₐ[ℚ] K)) = 2 := by
  have := isGalois_rat hr htop
  rw [Ideal.card_inertia_eq_ramificationIdx ℤ (K ≃ₐ[ℚ] K) Q]
  exact ramificationIdx_eq_two hr htop hodd Q hsf hi

omit hd in
/-- **The inertia group at an odd ramified prime.** Let `K` be generated over `ℚ` by square roots
`r i` of squarefree integers `d i`, and let `Q` be a prime of `𝓞 K` above an odd prime `p` dividing
some `d i`. An automorphism of `K` lies in the inertia group of `Q` exactly when it is the identity
or the sign change negating `r j` for the `j` with `p ∣ d j` and fixing the other `r j`. -/
theorem mem_inertia_iff [Finite ι] (hsf : ∀ i, Squarefree (d i)) {i : ι} (hi : (p : ℤ) ∣ d i)
    {τ : K ≃ₐ[ℚ] K} :
    τ ∈ Q.inertia (K ≃ₐ[ℚ] K) ↔
      τ = 1 ∨ ∀ j, τ (r j) = if (p : ℤ) ∣ d j then -r j else r j := by
  have hd (j : ι) : ¬ (p : ℤ) ^ 2 ∣ d j := fun h =>
    (Nat.prime_iff_prime_int.mp Fact.out).not_isUnit (hsf j _ (by rwa [← pow_two]))
  -- A nontrivial inertia element acts on the roots by the stated signs.
  have hsign {σ : K ≃ₐ[ℚ] K} (hσ : σ ∈ Q.inertia (K ≃ₐ[ℚ] K)) (hσ1 : σ ≠ 1) (j : ι) :
      σ (r j) = if (p : ℤ) ∣ d j then -r j else r j := by
    split_ifs with hj
    · exact apply_eq_neg_of_mem_inertia_of_ne_one hr htop hodd hd Q hσ hσ1 hj
    · exact apply_eq_self_of_mem_inertia (hr j) hodd hj Q hσ
  refine ⟨fun hτ => or_iff_not_imp_left.mpr (hsign hτ), ?_⟩
  rintro (rfl | hτ)
  · exact one_mem _
  -- The inertia group has a nontrivial element, which agrees with `τ` on the generators.
  have hne : Q.inertia (K ≃ₐ[ℚ] K) ≠ ⊥ := by
    intro hbot
    have h := card_inertia_eq_two hr htop hodd Q hsf hi
    rw [hbot, Subgroup.card_bot] at h
    exact absurd h (by decide)
  obtain ⟨⟨σ, hσ⟩, hσ1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  replace hσ1 : σ ≠ 1 := fun h => hσ1 (Subtype.ext h)
  have hστ : σ = τ := TauCeti.IntermediateField.algEquiv_ext_of_adjoin_eq_top htop <| by
    rintro _ ⟨j, rfl⟩
    rw [hsign hσ hσ1 j, hτ j]
  exact hστ ▸ hσ

omit hd in
/-- **The prime-count formula at an odd ramified prime.** Let `K` be generated over `ℚ` by square
roots of squarefree integers `d i`, and let `Q` be a prime of `𝓞 K` above an odd prime `p` dividing
some `d i`. Then the number `g` of primes above `p` and their common residue degree `f` satisfy
`g · f · 2 = [K : ℚ]`. -/
theorem ncard_primesOver_mul_inertiaDeg_mul_two_eq_finrank [Finite ι]
    (hsf : ∀ i, Squarefree (d i)) {i : ι} (hi : (p : ℤ) ∣ d i) :
    (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard * Q.inertiaDeg ℤ * 2 = finrank ℚ K := by
  have := isGalois_rat hr htop
  have h := Ideal.ncard_primesOver_mul_card_inertia_mul_finrank (G := K ≃ₐ[ℚ] K)
    (span {(p : ℤ)}) Q
  rw [card_inertia_eq_two hr htop hodd Q hsf hi, IsGalois.card_aut_eq_finrank] at h
  rw [← h]
  ring

end TauCeti.Multiquadratic
