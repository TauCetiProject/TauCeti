/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.ResidueDegree
import TauCeti.Algebra.Field.SqrtIntDiv
import TauCeti.FieldTheory.Galois.SquareRoot
import TauCeti.FieldTheory.IntermediateField.Adjoin.EqTop
import TauCeti.NumberTheory.Multiquadratic.RamifiedPrimes
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat
import TauCeti.NumberTheory.RamificationInertia.Galois

/-!
# Inertia and residue degree at an odd ramified prime of a multiquadratic field

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

The residue degree is read off from a Frobenius `σ` at `Q`, which is determined only up to the
inertia group: `f = 1` exactly when `σ` lies in the inertia group
(`Ideal.inertiaDeg_eq_one_iff_mem_inertia`), and otherwise `f = 2`, since `f` divides the order
of `σ`, which is at most `2` (`TauCeti.Multiquadratic.inertiaDeg_dvd_two`). The Frobenius acts on
a root `r i` of a radicand prime to `p` by the Legendre symbol `(dᵢ/p)`, and on `rᵢ rⱼ / p` by
the Legendre symbol of `(dᵢ / p) (dⱼ / p)` when `p` divides `dᵢ` and `dⱼ`. So for squarefree
radicands, `f = 1` exactly when every radicand prime to `p` is a quadratic residue mod `p` and the
`p`-free parts `dᵢ / p` of the radicands divisible by `p` all have the same Legendre
symbol. Without ramification this is the criterion
`TauCeti.Multiquadratic.inertiaDeg_eq_one_iff_forall_legendreSym_eq_one`.

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
* `TauCeti.Multiquadratic.isArithFrobAt_apply_mul_apply_eq_mul_iff`: a Frobenius changes the signs
  of the roots of two radicands divisible by `p` together exactly when their `p`-free parts have
  the same Legendre symbol.
* `TauCeti.Multiquadratic.isArithFrobAt_mem_inertia_iff`: at an odd ramified prime, a Frobenius
  lies in the inertia group exactly when every radicand prime to `p` is a quadratic residue mod `p`
  and the `p`-free parts of the radicands divisible by `p` have equal Legendre symbols.
* `TauCeti.Multiquadratic.inertiaDeg_eq_one_iff_of_squarefree` and
  `TauCeti.Multiquadratic.inertiaDeg_eq_two_iff_of_squarefree`: the residue degree at any odd
  prime, ramified or not, in terms of Legendre symbols.
* `TauCeti.Multiquadratic.ncard_primesOver_mul_two_eq_finrank_iff_of_dvd`: an odd ramified prime
  has `[K : ℚ] / 2` primes above it exactly when that Legendre-symbol criterion holds.
* `TauCeti.Multiquadratic.ncard_primesOver_eq_two_pow_sub_one_of_dvd` and
  `TauCeti.Multiquadratic.ncard_primesOver_eq_two_pow_sub_two`: under square-class independence
  of `n` radicands, an odd prime dividing some radicand has `2ⁿ⁻¹` primes above it when that
  criterion holds, and `2ⁿ⁻²` when it fails, so its decomposition type is `(2, 1, 2ⁿ⁻¹)` or
  `(2, 2, 2ⁿ⁻²)`.

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
  have hp0 : ((p : ℤ) : K) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have h := apply_eq_self_of_mem_inertia (mul_div_intCast_sq_eq (hr i) (hr j) hi hj hp0) hodd
    ((Nat.prime_iff_prime_int.mp Fact.out).not_dvd_mul
      (by rwa [Int.dvd_ediv_iff_mul_dvd hi, ← pow_two])
      (by rwa [Int.dvd_ediv_iff_mul_dvd hj, ← pow_two])) Q hτ
  rw [map_div₀, map_mul, map_intCast] at h
  exact (div_left_inj' hp0).mp h

/-- **A Frobenius acts by one sign on two ramified roots exactly when their `p`-free parts have
the same Legendre symbol.** Let `p` be an odd prime, let `r i`, `r j` be square roots of
integers `d i`, `d j` that are divisible by `p` but not by `p²`, and let `σ` be an arithmetic
Frobenius at a prime `Q` above `p`. Then `σ (r i) * σ (r j) = r i * r j`, that is, `σ` changes
the signs of `r i` and `r j` together, exactly when `(d i / p | p) = (d j / p | p)`. Indeed
`σ` acts on the square root `r i * r j / p` of the `p`-unit `(d i / p) * (d j / p)` by its
Legendre symbol. -/
theorem isArithFrobAt_apply_mul_apply_eq_mul_iff (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (hodd : p ≠ 2) {i j : ι} (hi : (p : ℤ) ∣ d i) (hi2 : ¬ (p : ℤ) ^ 2 ∣ d i)
    (hj : (p : ℤ) ∣ d j) (hj2 : ¬ (p : ℤ) ^ 2 ∣ d j) (Q : Ideal (𝓞 K))
    [Q.LiesOver (span {(p : ℤ)})] {σ : K ≃ₐ[ℚ] K} (hσ : IsArithFrobAt ℤ σ Q) :
    σ (r i) * σ (r j) = r i * r j ↔ legendreSym p (d i / p) = legendreSym p (d j / p) := by
  have hp0 : ((p : ℤ) : K) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have h := isArithFrobAt_apply_sqrt_eq_self_iff hodd
    ((Nat.prime_iff_prime_int.mp Fact.out).not_dvd_mul
      (by rwa [Int.dvd_ediv_iff_mul_dvd hi, ← pow_two])
      (by rwa [Int.dvd_ediv_iff_mul_dvd hj, ← pow_two]))
      (mul_div_intCast_sq_eq (hr i) (hr j) hi hj hp0) Q hσ
  rw [map_div₀, map_mul, map_intCast, div_left_inj' hp0, legendreSym.mul] at h
  rw [h]
  -- Both symbols are `±1`, since the `p`-free parts are prime to `p`.
  have hunit {c : ℤ} (hc : (p : ℤ) ∣ c) (hc2 : ¬ (p : ℤ) ^ 2 ∣ c) :
      legendreSym p (c / p) = 1 ∨ legendreSym p (c / p) = -1 := by
    refine legendreSym.eq_one_or_neg_one p ?_
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact fun h => hc2 (pow_two (p : ℤ) ▸ Int.mul_dvd_of_dvd_ediv hc h)
  rcases hunit hi hi2 with h1 | h1 <;> rcases hunit hj hj2 with h2 | h2 <;> simp [h1, h2]

section Inertia

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
  have hri : r i ≠ 0 := ne_zero_of_sq_eq_intCast (hr i) fun h0 => hd i (h0 ▸ dvd_zero _)
  refine (AlgEquiv.apply_eq_or_eq_neg_of_sq_eq τ (hr i)).resolve_left fun hfix => hτ1 ?_
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

end Inertia

/-! ### The residue degree at an odd prime -/

/-- **A Frobenius at an odd ramified prime lies in the inertia group exactly at the residues.**
Let `K` be generated over `ℚ` by square roots `r i` of squarefree integers `d i`, let `Q` be a
prime of `𝓞 K` above an odd prime `p` dividing some `d i`, and let `σ` be an arithmetic Frobenius
at `Q`. Then `σ` lies in the inertia group of `Q` exactly when every radicand prime to `p` is a
quadratic residue mod `p`, and the `p`-free parts `d j / p` of the radicands divisible by `p` all
have the same Legendre symbol. -/
theorem isArithFrobAt_mem_inertia_iff [Finite ι] (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (htop : IntermediateField.adjoin ℚ (Set.range r) = ⊤) (hodd : p ≠ 2)
    (hsf : ∀ i, Squarefree (d i)) (Q : Ideal (𝓞 K)) [Q.IsPrime]
    [Q.LiesOver (span {(p : ℤ)})] {i : ι} (hi : (p : ℤ) ∣ d i) {σ : K ≃ₐ[ℚ] K}
    (hσ : IsArithFrobAt ℤ σ Q) :
    σ ∈ Q.inertia (K ≃ₐ[ℚ] K) ↔ (∀ j, ¬ (p : ℤ) ∣ d j → legendreSym p (d j) = 1) ∧
      ∀ j k, (p : ℤ) ∣ d j → (p : ℤ) ∣ d k → legendreSym p (d j / p) = legendreSym p (d k / p) := by
  have hd (j : ι) : ¬ (p : ℤ) ^ 2 ∣ d j := fun h =>
    (Nat.prime_iff_prime_int.mp Fact.out).not_isUnit (hsf j _ (by rwa [← pow_two]))
  have hcop {j : ι} (hj : ¬ (p : ℤ) ∣ d j) :=
    isArithFrobAt_apply_sqrt_eq_self_iff hodd hj (hr j) Q hσ
  have hpair {j k : ι} (hj : (p : ℤ) ∣ d j) (hk : (p : ℤ) ∣ d k) :=
    isArithFrobAt_apply_mul_apply_eq_mul_iff hr hodd hj (hd j) hk (hd k) Q hσ
  constructor
  · intro hI
    exact ⟨fun j hj => (hcop hj).mp (apply_eq_self_of_mem_inertia (hr j) hodd hj Q hI),
      fun j k hj hk => (hpair hj hk).mp
        (apply_mul_apply_eq_mul_of_mem_inertia hr hodd hj (hd j) hk (hd k) Q hI)⟩
  · rintro ⟨hres, hsym⟩
    -- `σ` fixes the roots prime to `p` and acts by the sign `σ (r i) = ± r i` on the others.
    rw [mem_inertia_iff hr htop hodd Q hsf hi]
    have hri : r i ≠ 0 := ne_zero_of_sq_eq_intCast (hr i) (hsf i).ne_zero
    have hsame {k : ι} (hk : (p : ℤ) ∣ d k) : σ (r i) * σ (r k) = r i * r k :=
      (hpair hi hk).mpr (hsym i k hi hk)
    have hsq : σ (r i) ^ 2 = r i ^ 2 := by
      rw [← map_pow, hr i]
      simp
    rcases eq_or_eq_neg_of_sq_eq_sq _ _ hsq with h | h
    · left
      refine TauCeti.IntermediateField.algEquiv_eq_one_of_adjoin_eq_top htop ?_
      rintro _ ⟨k, rfl⟩
      by_cases hk : (p : ℤ) ∣ d k
      · have h' := hsame hk
        rw [h] at h'
        exact mul_left_cancel₀ hri h'
      · exact (hcop hk).mpr (hres k hk)
    · right
      intro k
      split_ifs with hk
      · have h' := hsame hk
        rw [h, neg_mul, neg_eq_iff_eq_neg, ← mul_neg] at h'
        exact mul_left_cancel₀ hri h'
      · exact (hcop hk).mpr (hres k hk)

/-- **The residue degree at an odd prime.** Let `K` be generated over `ℚ` by square roots `r i` of
squarefree integers `d i`, and let `Q` be a prime of `𝓞 K` above an odd prime `p`. Then `Q` has
residue degree `1` exactly when every radicand prime to `p` is a quadratic residue mod `p`, and
the `p`-free parts `d i / p` of the radicands divisible by `p` all have the same Legendre symbol.
When `p` divides no radicand the second condition is vacuous, and this is
`TauCeti.Multiquadratic.inertiaDeg_eq_one_iff_forall_legendreSym_eq_one`. -/
theorem inertiaDeg_eq_one_iff_of_squarefree [Finite ι] (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (htop : IntermediateField.adjoin ℚ (Set.range r) = ⊤) (hodd : p ≠ 2)
    (hsf : ∀ i, Squarefree (d i)) (Q : Ideal (𝓞 K)) [Q.IsPrime]
    [Q.LiesOver (span {(p : ℤ)})] :
    Q.inertiaDeg ℤ = 1 ↔ (∀ j, ¬ (p : ℤ) ∣ d j → legendreSym p (d j) = 1) ∧
      ∀ j k, (p : ℤ) ∣ d j → (p : ℤ) ∣ d k → legendreSym p (d j / p) = legendreSym p (d k / p) := by
  have := isGalois_rat hr htop
  by_cases hram : ∃ i, (p : ℤ) ∣ d i
  · obtain ⟨i, hi⟩ := hram
    obtain ⟨σ, hσ⟩ := exists_isArithFrobAt_int_of_liesOver (p := p) Q
    rw [Ideal.inertiaDeg_eq_one_iff_mem_inertia Q hσ,
      isArithFrobAt_mem_inertia_iff hr htop hodd hsf Q hi hσ]
  · -- At an unramified prime only the first condition remains.
    push Not at hram
    rw [inertiaDeg_eq_one_iff_forall_legendreSym_eq_one hr htop hodd hram Q]
    exact ⟨fun h => ⟨fun j _ => h j, fun j _ hj => absurd hj (hram j)⟩,
      fun h j => h.1 j (hram j)⟩

/-- **Residue degree two at an odd prime.** Let `K` be generated over `ℚ` by square roots of
squarefree integers `d i`, and let `Q` be a prime of `𝓞 K` above an odd prime `p`. Then `Q` has
residue degree `2` exactly when the criterion of
`TauCeti.Multiquadratic.inertiaDeg_eq_one_iff_of_squarefree` fails: some radicand prime to `p` is
a quadratic non-residue mod `p`, or two radicands divisible by `p` have `p`-free parts with
different Legendre symbols. -/
theorem inertiaDeg_eq_two_iff_of_squarefree [Finite ι] (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (htop : IntermediateField.adjoin ℚ (Set.range r) = ⊤) (hodd : p ≠ 2)
    (hsf : ∀ i, Squarefree (d i)) (Q : Ideal (𝓞 K)) [Q.IsPrime]
    [Q.LiesOver (span {(p : ℤ)})] :
    Q.inertiaDeg ℤ = 2 ↔ ¬ ((∀ j, ¬ (p : ℤ) ∣ d j → legendreSym p (d j) = 1) ∧
      ∀ j k, (p : ℤ) ∣ d j → (p : ℤ) ∣ d k →
        legendreSym p (d j / p) = legendreSym p (d k / p)) := by
  rw [← inertiaDeg_eq_one_iff_of_squarefree hr htop hodd hsf Q]
  rcases (Nat.dvd_prime Nat.prime_two).mp (inertiaDeg_dvd_two (p := p) hr htop Q) with h | h <;>
    simp [h]

/-- **The number of primes above an odd ramified prime.** Let `K` be generated over `ℚ` by square
roots of squarefree integers `d i`, and let `p` be an odd prime dividing some `d i`. Then there are
exactly `[K : ℚ] / 2` primes of `𝓞 K` above `p`, the most possible given that `p` ramifies,
exactly when the criterion of `TauCeti.Multiquadratic.inertiaDeg_eq_one_iff_of_squarefree`
holds. -/
theorem ncard_primesOver_mul_two_eq_finrank_iff_of_dvd [Finite ι]
    (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (htop : IntermediateField.adjoin ℚ (Set.range r) = ⊤) (hodd : p ≠ 2)
    (hsf : ∀ i, Squarefree (d i)) {i : ι} (hi : (p : ℤ) ∣ d i) :
    (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard * 2 = finrank ℚ K ↔
      (∀ j, ¬ (p : ℤ) ∣ d j → legendreSym p (d j) = 1) ∧
        ∀ j k, (p : ℤ) ∣ d j → (p : ℤ) ∣ d k →
          legendreSym p (d j / p) = legendreSym p (d k / p) := by
  obtain ⟨Q, hQ, _⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 K) (span {(p : ℤ)})
  rw [← inertiaDeg_eq_one_iff_of_squarefree hr htop hodd hsf Q]
  have h := ncard_primesOver_mul_inertiaDeg_mul_two_eq_finrank hr htop hodd Q hsf hi
  have hpos : 0 < finrank ℚ K := finrank_pos
  constructor
  · intro hg
    exact Nat.eq_of_mul_eq_mul_left (hg ▸ hpos) (by linarith)
  · intro h1
    rwa [h1, mul_one] at h

/-- **The number of primes above an odd ramified prime of residue degree one.** Let `K` be
generated over `ℚ` by square roots of `n` square-class independent squarefree integers `d i` (no
nonempty subset product is a square), and let `p` be an odd prime dividing some `d i` for which the
criterion of `TauCeti.Multiquadratic.inertiaDeg_eq_one_iff_of_squarefree` holds. Then there are
exactly `2 ^ (n - 1)` primes of `𝓞 K` above `p`: the decomposition type is `e = 2`, `f = 1`,
`g = 2 ^ (n - 1)`. -/
theorem ncard_primesOver_eq_two_pow_sub_one_of_dvd [Finite ι]
    (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (htop : IntermediateField.adjoin ℚ (Set.range r) = ⊤) (hodd : p ≠ 2)
    (hsf : ∀ i, Squarefree (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, (d i : ℚ)))
    {i : ι} (hi : (p : ℤ) ∣ d i)
    (hres : (∀ j, ¬ (p : ℤ) ∣ d j → legendreSym p (d j) = 1) ∧
      ∀ j k, (p : ℤ) ∣ d j → (p : ℤ) ∣ d k → legendreSym p (d j / p) = legendreSym p (d k / p)) :
    (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = 2 ^ (Nat.card ι - 1) :=
  eq_two_pow_sub_of_mul_two_pow_eq_finrank hr htop hindep (k := 1) (by
    rw [pow_one]
    exact (ncard_primesOver_mul_two_eq_finrank_iff_of_dvd hr htop hodd hsf hi).mpr hres)

/-- **The number of primes above an odd ramified prime of residue degree two.** Let `K` be
generated over `ℚ` by square roots of `n` square-class independent squarefree integers `d i` (no
nonempty subset product is a square), and let `p` be an odd prime dividing some `d i` for which the
criterion of `TauCeti.Multiquadratic.inertiaDeg_eq_one_iff_of_squarefree` fails. Then there are
exactly `2 ^ (n - 2)` primes of `𝓞 K` above `p`: the decomposition type is `e = 2`, `f = 2`,
`g = 2 ^ (n - 2)`. -/
theorem ncard_primesOver_eq_two_pow_sub_two [Finite ι]
    (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (htop : IntermediateField.adjoin ℚ (Set.range r) = ⊤) (hodd : p ≠ 2)
    (hsf : ∀ i, Squarefree (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, (d i : ℚ)))
    {i : ι} (hi : (p : ℤ) ∣ d i)
    (hnr : ¬ ((∀ j, ¬ (p : ℤ) ∣ d j → legendreSym p (d j) = 1) ∧
      ∀ j k, (p : ℤ) ∣ d j → (p : ℤ) ∣ d k →
        legendreSym p (d j / p) = legendreSym p (d k / p))) :
    (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = 2 ^ (Nat.card ι - 2) := by
  obtain ⟨Q, _, _⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 K) (span {(p : ℤ)})
  refine eq_two_pow_sub_of_mul_two_pow_eq_finrank hr htop hindep (k := 2) ?_
  have h := ncard_primesOver_mul_inertiaDeg_mul_two_eq_finrank hr htop hodd Q hsf hi
  rwa [(inertiaDeg_eq_two_iff_of_squarefree hr htop hodd hsf Q).mpr hnr, mul_assoc, ← pow_two] at h

end TauCeti.Multiquadratic
