/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Frobenius
import TauCeti.NumberTheory.Multiquadratic.Galois.Basic
import TauCeti.FieldTheory.Galois.SquareRoot
import TauCeti.FieldTheory.IntermediateField.Adjoin.EqTop
import TauCeti.NumberTheory.Multiquadratic.Degree
import TauCeti.NumberTheory.NumberField.Frobenius.DecompositionGroup
import TauCeti.NumberTheory.NumberField.AutomorphismAction
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat
import TauCeti.RingTheory.Ideal.LiesOver

/-!
# The decomposition law at an unramified prime of a multiquadratic field

Let `K = ℚ(√d₁, …, √dₙ)` be a number field generated over `ℚ` by square roots `r i` of integers
`d i`, and let `p` be an odd prime dividing none of the `d i`. The Frobenius at a prime `Q` of
`𝓞 K` above `p` acts on the generators by the Legendre symbols, `σ (r i) = (dᵢ/p) · r i`
(`NumberField.exists_isArithFrobAt_multiquadratic`). This file reads off from that action the
complete decomposition type of `p` in `K`:

* `p` is unramified in `K`: the inertia group of `Q` is trivial, because an element of it that
  negated some `r i` would force `2 r i ∈ Q`, hence `p ∣ 2 dᵢ`;
* the residue degree `f` of every prime above `p` is `1` if every `dᵢ` is a quadratic residue
  mod `p` and `2` otherwise, since `f` is the order of the Frobenius, an involution that is
  trivial exactly when every symbol is `1`;
* the number `g` of primes above `p` satisfies `g · f = [K : ℚ]`. When every `dᵢ` is a residue
  this is the splitting law `NumberField.ncard_primesOver_multiquadratic_iff` (`g = [K : ℚ]`);
  otherwise `g = [K : ℚ] / 2`, which is `2ⁿ⁻¹` under square-class independence of the radicands.

The same holds at `p = 2` when every `dᵢ` is `1` modulo `4`, with the congruence class of `dᵢ`
modulo `8` in place of the Legendre symbol. There the integral half-generator `(1 + r i) / 2`
replaces `r i`: an inertia element negating `r i` sends it to `1 - (1 + r i) / 2`, and the
difference `-r i` would then lie in `Q`, forcing `2 ∣ dᵢ`. The Frobenius above `2` is trivial
exactly when every `dᵢ` is `1` modulo `8` (`isArithFrobAt_eq_one_iff_mod_eight`), so `2` splits
completely exactly then, and otherwise has residue degree `2` and `[K : ℚ] / 2` primes above it.

No squarefreeness of the radicands is assumed: unramifiedness is proved directly from
`p ∤ 2 dᵢ`, or from `dᵢ ≡ 1 (mod 4)` at `2`, rather than through the discriminant.

## Main results

* `TauCeti.Multiquadratic.apply_eq_self_of_mem_inertia`: inertia at an odd prime `p` fixes every
  square root of an integer prime to `p`.
* `TauCeti.Multiquadratic.inertia_eq_bot_of_forall_not_dvd` and
  `TauCeti.Multiquadratic.isUnramifiedAt_of_forall_not_dvd`: an odd prime dividing no radicand
  has trivial inertia and is unramified.
* `TauCeti.Multiquadratic.inertiaDeg_eq_one_iff_forall_legendreSym_eq_one` and
  `TauCeti.Multiquadratic.inertiaDeg_eq_two_iff_exists_legendreSym_eq_neg_one`: the residue
  degree of a prime above such a `p` is `1` if every `dᵢ` is a quadratic residue mod `p`, and
  `2` if some `dᵢ` is not.
* `TauCeti.Multiquadratic.ncard_primesOver_mul_inertiaDeg_eq_finrank`: the number of primes
  above `p` times their residue degree is `[K : ℚ]`.
* `TauCeti.Multiquadratic.ncard_primesOver_mul_two_eq_finrank`: when some `dᵢ` is a non-residue,
  there are `[K : ℚ] / 2` primes above `p`.
* `TauCeti.Multiquadratic.eq_two_pow_sub_of_mul_two_pow_eq_finrank`: under square-class
  independence of `n` radicands, `g · 2ᵏ = [K : ℚ]` forces `g = 2ⁿ⁻ᵏ`.
* `TauCeti.Multiquadratic.ncard_primesOver_eq_two_pow_sub_one`: under square-class
  independence of `n` radicands, that number is `2ⁿ⁻¹`.
* `TauCeti.Multiquadratic.apply_eq_self_of_mem_inertia_of_mod_four_eq_one`: inertia above `2`
  fixes every square root of an integer that is `1` modulo `4`.
* `TauCeti.Multiquadratic.inertia_eq_bot_of_forall_mod_four_eq_one` and
  `TauCeti.Multiquadratic.isUnramifiedAt_of_forall_mod_four_eq_one`: `2` has trivial inertia and
  is unramified when every radicand is `1` modulo `4`.
* `TauCeti.Multiquadratic.inertiaDeg_eq_one_iff_forall_mod_eight_eq_one` and
  `TauCeti.Multiquadratic.inertiaDeg_eq_two_iff_exists_mod_eight_eq_five`: the residue degree of
  a prime above `2` is `1` if every `dᵢ` is `1` modulo `8`, and `2` if some `dᵢ` is `5`
  modulo `8`.
* `TauCeti.Multiquadratic.ncard_primesOver_two_mul_inertiaDeg_eq_finrank` and
  `TauCeti.Multiquadratic.ncard_primesOver_two_eq_finrank_iff`: the prime-count formula at `2`,
  and the splitting law: `2` splits completely iff every `dᵢ` is `1` modulo `8`.
* `TauCeti.Multiquadratic.ncard_primesOver_two_mul_two_eq_finrank` and
  `TauCeti.Multiquadratic.ncard_primesOver_two_eq_two_pow_sub_one`: when some `dᵢ` is `5`
  modulo `8`, there are `[K : ℚ] / 2` primes above `2`, which is `2ⁿ⁻¹` under square-class
  independence.
* `TauCeti.Multiquadratic.inertiaDeg_dvd_two`: at every rational prime, ramified or not, the
  residue degree divides `2`.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §5.B.
* J. Neukirch, *Algebraic Number Theory*, Chapter I, §9.
-/

public section

open NumberField Ideal Module MulAction
open scoped NumberField Pointwise

namespace TauCeti.Multiquadratic

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} {d : ι → ℤ} {r : ι → K}
  {p : ℕ} [Fact p.Prime]

/-! ### Shared unramified-prime facts -/

/-- A number field generated over `ℚ` by square roots of integers is Galois over `ℚ`. -/
theorem isGalois_rat [Finite ι] (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (htop : IntermediateField.adjoin ℚ (Set.range r) = ⊤) : IsGalois ℚ K :=
  isGalois_of_adjoin_eq_top (d := fun i => (d i : ℚ)) (fun i => by rw [hr i]; simp) htop

/-- **Reading a prime count off the degree.** Under square-class independence of `n` radicands,
`[K : ℚ] = 2 ^ n`, so a number `g` with `g * 2 ^ k = [K : ℚ]` is `2 ^ (n - k)`; the equation itself
forces `k ≤ n`. This is how the decomposition formulas `g · f · e = [K : ℚ]` are solved for the
number `g` of primes above a rational prime. -/
theorem eq_two_pow_sub_of_mul_two_pow_eq_finrank [Finite ι]
    (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (htop : IntermediateField.adjoin ℚ (Set.range r) = ⊤)
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, (d i : ℚ)))
    {g k : ℕ} (h : g * 2 ^ k = finrank ℚ K) : g = 2 ^ (Nat.card ι - k) := by
  have hr' (i : ι) : r i ^ 2 = algebraMap ℚ K (d i : ℚ) := by rw [hr i]; simp
  have hdeg := finrank_adjoin_range (K := ℚ) (L := K) (d := fun i => (d i : ℚ)) hr' hindep
  rw [htop, IntermediateField.finrank_top'] at hdeg
  rw [hdeg] at h
  -- `g ≠ 0`, so `2 ^ k ≤ 2 ^ n` and `k ≤ n`; then cancel `2 ^ k`.
  have hg : g ≠ 0 := by rintro rfl; exact (pow_pos two_pos _).ne (by simpa using h)
  have hk : k ≤ Nat.card ι := by
    by_contra hlt
    have h1 : 2 ^ Nat.card ι < 2 ^ k := Nat.pow_lt_pow_right one_lt_two (not_le.mp hlt)
    have h2 : 2 ^ k ≤ g * 2 ^ k := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hg)
    omega
  rw [← Nat.sub_add_cancel hk, pow_add] at h
  exact Nat.eq_of_mul_eq_mul_right (pow_pos two_pos k) h

/-! ### The decomposition law at an odd prime -/

/-- **Inertia at an odd prime fixes the square roots of integers prime to it.** Let `Q` be a
prime of `𝓞 K` above an odd prime `p`, and let `x ∈ K` square to an integer `c` with `p ∤ c`. Then
every element of the inertia group of `Q` in `Gal(K/ℚ)` fixes `x`. Indeed `τ x = ± x`, and
`τ x = -x` would put `2 x` in `Q`, hence `p ∣ 2 c`. -/
theorem apply_eq_self_of_mem_inertia {x : K} {c : ℤ} (hx : x ^ 2 = algebraMap ℤ K c)
    (hodd : p ≠ 2) (hc : ¬ (p : ℤ) ∣ c) (Q : Ideal (𝓞 K)) [Q.IsPrime]
    [Q.LiesOver (span {(p : ℤ)})] {τ : K ≃ₐ[ℚ] K} (hτ : τ ∈ Q.inertia (K ≃ₐ[ℚ] K)) :
    τ x = x := by
  -- `τ x` is a square root of `c`, hence `± x`; rule out the minus sign.
  have hx' : x ^ 2 = algebraMap ℚ K (c : ℚ) := by rw [hx]; simp
  have hsq : τ x ^ 2 = x ^ 2 := by rw [← map_pow, hx', AlgEquiv.commutes]
  refine (eq_or_eq_neg_of_sq_eq_sq _ _ hsq).resolve_right fun hneg => ?_
  let R : 𝓞 K := integralSqrt hx
  have hR : τ • R = -R := by
    apply FaithfulSMul.algebraMap_injective (𝓞 K) K
    rw [algebraMap_smul_eq_apply τ R, map_neg, algebraMap_integralSqrt, hneg]
  -- `τ` acts trivially modulo `Q`, so `τ • R - R = -(2 * R)` lies in `Q`.
  have h2R : (2 : 𝓞 K) * R ∈ Q := by
    have h := (Ideal.mem_inertia.mp hτ) R
    rw [hR, show -R - R = -((2 : 𝓞 K) * R) by ring] at h
    exact Q.neg_mem_iff.mp h
  rcases (‹Q.IsPrime›).mem_or_mem h2R with h2 | hRQ
  · -- `2 ∈ Q` would force the odd prime `p` to divide `2`.
    have h2' : algebraMap ℤ (𝓞 K) 2 ∈ Q := by simpa using h2
    have hdvd : (p : ℤ) ∣ 2 := (Ideal.algebraMap_int_mem_iff_dvd_of_liesOver Q _).mp h2'
    exact hodd ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp (by exact_mod_cast hdvd))
  · -- `R ∈ Q` would put `c = R ^ 2` in `Q`, so `p ∣ c`.
    have hc' : algebraMap ℤ (𝓞 K) c ∈ Q := by
      rw [← integralSqrt_sq hx, pow_two]
      exact Q.mul_mem_left _ hRQ
    exact hc ((Ideal.algebraMap_int_mem_iff_dvd_of_liesOver Q _).mp hc')

/-- **An odd prime dividing no radicand has trivial inertia.** Let `K` be generated over `ℚ` by
square roots `r i` of integers `d i`, and let `Q` be a prime of `𝓞 K` above an odd prime `p` with
`p ∤ d i` for all `i`. Then the inertia group of `Q` in `Gal(K/ℚ)` is trivial, so `p` is
unramified in `K`. No squarefreeness of the `d i` is needed. -/
theorem inertia_eq_bot_of_forall_not_dvd (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (htop : IntermediateField.adjoin ℚ (Set.range r) = ⊤) (hodd : p ≠ 2)
    (hcop : ∀ i, ¬ (p : ℤ) ∣ d i) (Q : Ideal (𝓞 K)) [Q.IsPrime]
    [Q.LiesOver (span {(p : ℤ)})] :
    Q.inertia (K ≃ₐ[ℚ] K) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun τ hτ => ?_
  refine TauCeti.IntermediateField.algEquiv_eq_one_of_adjoin_eq_top htop ?_
  rintro _ ⟨i, rfl⟩
  exact apply_eq_self_of_mem_inertia (hr i) hodd (hcop i) Q hτ

/-- An odd prime dividing no radicand is unramified in the multiquadratic field. -/
theorem isUnramifiedAt_of_forall_not_dvd [Finite ι]
    (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (htop : IntermediateField.adjoin ℚ (Set.range r) = ⊤) (hodd : p ≠ 2)
    (hcop : ∀ i, ¬ (p : ℤ) ∣ d i) (Q : Ideal (𝓞 K)) [Q.IsPrime]
    [Q.LiesOver (span {(p : ℤ)})] : Algebra.IsUnramifiedAt (𝓞 ℚ) Q := by
  have := isGalois_rat hr htop
  exact (Ideal.isUnramifiedAt_iff_inertia_eq_bot (K := ℚ) Q).mpr
    (inertia_eq_bot_of_forall_not_dvd hr htop hodd hcop Q)

/-- **Residue degree one exactly at the residues.** Let `K` be generated over `ℚ` by square roots
`r i` of integers `d i`, and let `Q` be a prime of `𝓞 K` above an odd prime `p` dividing none of
the `d i`. Then `Q` has residue degree `1` iff every `d i` is a quadratic residue mod `p`. -/
theorem inertiaDeg_eq_one_iff_forall_legendreSym_eq_one [Finite ι]
    (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (htop : IntermediateField.adjoin ℚ (Set.range r) = ⊤) (hodd : p ≠ 2)
    (hcop : ∀ i, ¬ (p : ℤ) ∣ d i) (Q : Ideal (𝓞 K)) [Q.IsPrime]
    [Q.LiesOver (span {(p : ℤ)})] :
    Q.inertiaDeg ℤ = 1 ↔ ∀ i, legendreSym p (d i) = 1 := by
  have := isGalois_rat hr htop
  have := isUnramifiedAt_of_forall_not_dvd hr htop hodd hcop Q
  obtain ⟨σ, hσ⟩ := exists_isArithFrobAt_int_of_liesOver (p := p) Q
  rw [Ideal.inertiaDeg_eq_orderOf (p := p) Q hσ, orderOf_eq_one_iff]
  exact isArithFrobAt_multiquadratic_eq_one_iff d r hr htop hodd hcop Q hσ

/-- **Residue degree two exactly at a non-residue.** Let `K` be generated over `ℚ` by square roots
`r i` of integers `d i`, and let `Q` be a prime of `𝓞 K` above an odd prime `p` dividing none of
the `d i`. Then `Q` has residue degree `2` iff some `d i` is a quadratic non-residue mod `p`.
Together with `inertiaDeg_eq_one_iff_forall_legendreSym_eq_one`, the residue degree is always
`1` or `2`. -/
theorem inertiaDeg_eq_two_iff_exists_legendreSym_eq_neg_one [Finite ι]
    (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (htop : IntermediateField.adjoin ℚ (Set.range r) = ⊤) (hodd : p ≠ 2)
    (hcop : ∀ i, ¬ (p : ℤ) ∣ d i) (Q : Ideal (𝓞 K)) [Q.IsPrime]
    [Q.LiesOver (span {(p : ℤ)})] :
    Q.inertiaDeg ℤ = 2 ↔ ∃ i, legendreSym p (d i) = -1 := by
  have := isGalois_rat hr htop
  have := isUnramifiedAt_of_forall_not_dvd hr htop hodd hcop Q
  obtain ⟨σ, hσ⟩ := exists_isArithFrobAt_int_of_liesOver (p := p) Q
  have hiff := isArithFrobAt_multiquadratic_eq_one_iff d r hr htop hodd hcop Q hσ
  -- Away from `p ∣ d i`, a Legendre symbol that is not `1` is `-1`.
  have hsym : (∃ i, legendreSym p (d i) = -1) ↔ ¬ ∀ i, legendreSym p (d i) = 1 := by
    simp only [not_forall]
    refine exists_congr fun i => ⟨fun h => by rw [h]; decide, fun h => ?_⟩
    refine (legendreSym.eq_one_or_neg_one p ?_).resolve_left h
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hcop i
  rw [Ideal.inertiaDeg_eq_orderOf (p := p) Q hσ, hsym, ← hiff]
  refine ⟨fun h h1 => by simp [h1] at h, fun h => ?_⟩
  exact orderOf_eq_prime
    (aut_pow_two_eq_one_of_adjoin_eq_top (d := fun i => (d i : ℚ))
      (fun i => by rw [hr i]; simp) htop σ) h

/-- **The unramified prime-count formula.** If `K` is generated by square roots of integers
`d i`, and the odd prime `p` divides none of them, then the number of primes above `p` times
their common residue degree is `[K : ℚ]`. -/
theorem ncard_primesOver_mul_inertiaDeg_eq_finrank [Finite ι]
    (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (htop : IntermediateField.adjoin ℚ (Set.range r) = ⊤) (hodd : p ≠ 2)
    (hcop : ∀ i, ¬ (p : ℤ) ∣ d i) (Q : Ideal (𝓞 K)) [Q.IsPrime]
    [Q.LiesOver (span {(p : ℤ)})] :
    (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard * Q.inertiaDeg ℤ = finrank ℚ K := by
  have := isGalois_rat hr htop
  have := isUnramifiedAt_of_forall_not_dvd hr htop hodd hcop Q
  exact Ideal.ncard_primesOver_mul_inertiaDeg_eq_finrank_of_isUnramifiedAt Q

/-- **The number of primes above an odd prime with a non-residue radicand.** Let `K` be
generated over `ℚ` by square roots of integers `d i`, and let `p` be an odd prime dividing none of
them such that some `d i` is a quadratic non-residue mod `p`. Then there are exactly `[K : ℚ] / 2`
primes of `𝓞 K` above `p`. (When every `d i` is a residue, `p` splits completely instead:
`NumberField.ncard_primesOver_multiquadratic_iff`.) -/
theorem ncard_primesOver_mul_two_eq_finrank [Finite ι]
    (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (htop : IntermediateField.adjoin ℚ (Set.range r) = ⊤) (hodd : p ≠ 2)
    (hcop : ∀ i, ¬ (p : ℤ) ∣ d i) (hnr : ∃ i, legendreSym p (d i) = -1) :
    (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard * 2 = finrank ℚ K := by
  obtain ⟨Q, hQ, _⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 K) (span {(p : ℤ)})
  rw [← (inertiaDeg_eq_two_iff_exists_legendreSym_eq_neg_one hr htop hodd hcop Q).mpr hnr]
  exact ncard_primesOver_mul_inertiaDeg_eq_finrank hr htop hodd hcop Q

/-- **The number of primes above an odd prime with a non-residue radicand, explicitly.** Let `K`
be generated over `ℚ` by square roots of `n` square-class independent integers `d i` (no nonempty
subset product is a square), and let `p` be an odd prime dividing none of them such that some
`d i` is a quadratic non-residue mod `p`. Then there are exactly `2 ^ (n - 1)` primes of `𝓞 K`
above `p`. -/
theorem ncard_primesOver_eq_two_pow_sub_one [Finite ι]
    (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (htop : IntermediateField.adjoin ℚ (Set.range r) = ⊤)
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, (d i : ℚ)))
    (hodd : p ≠ 2) (hcop : ∀ i, ¬ (p : ℤ) ∣ d i) (hnr : ∃ i, legendreSym p (d i) = -1) :
    (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = 2 ^ (Nat.card ι - 1) := by
  exact eq_two_pow_sub_of_mul_two_pow_eq_finrank hr htop hindep (k := 1)
    (by rw [pow_one]; exact ncard_primesOver_mul_two_eq_finrank hr htop hodd hcop hnr)

/-! ### The decomposition law at `2`

When every radicand is `1` modulo `4`, the prime `2` is unramified as well, and the dyadic
Frobenius calculation `isArithFrobAt_eq_one_iff_mod_eight` plays the role of the Legendre symbols:
the residue degree above `2` is `1` if every `dᵢ` is `1` modulo `8` and `2` otherwise. -/

/-- **Inertia above `2` fixes the square roots of integers that are `1` modulo `4`.** Let `Q` be a
prime of `𝓞 K` above `2`, and let `x ∈ K` square to an integer `c ≡ 1 (mod 4)`. Then every element
of the inertia group of `Q` in `Gal(K/ℚ)` fixes `x`. Indeed `τ x = ± x`, and `τ x = -x` would move
the integral half-generator `(1 + x) / 2` by `-x`, putting `c = x ^ 2` in `Q`, hence `2 ∣ c`. -/
theorem apply_eq_self_of_mem_inertia_of_mod_four_eq_one {x : K} {c : ℤ}
    (hx : x ^ 2 = algebraMap ℤ K c) (hc : c % 4 = 1) (Q : Ideal (𝓞 K))
    [Q.LiesOver (span {(2 : ℤ)})] {τ : K ≃ₐ[ℚ] K} (hτ : τ ∈ Q.inertia (K ≃ₐ[ℚ] K)) :
    τ x = x := by
  refine (AlgEquiv.apply_eq_or_eq_neg_of_sq_eq τ hx).resolve_right fun hneg => ?_
  -- The half-generator `w = (1 + x) / 2` is integral, and `τ • w - w = -x`.
  let w : 𝓞 K := ⟨(1 + x) / 2, isIntegral_one_add_div_two_of_sq_eq hx hc⟩
  have hw : algebraMap (𝓞 K) K w = (1 + x) / 2 := RingOfIntegers.map_mk _ _
  have hwsq : (τ • w - w) ^ 2 = algebraMap ℤ (𝓞 K) c := by
    apply FaithfulSMul.algebraMap_injective (𝓞 K) K
    rw [map_pow, map_sub, algebraMap_smul_eq_apply, hw,
      ← IsScalarTower.algebraMap_apply ℤ (𝓞 K) K, ← hx]
    simp only [map_div₀, map_add, map_one, map_ofNat, hneg]
    ring
  -- `τ` acts trivially modulo `Q`, so `c = (τ • w - w) ^ 2` lies in `Q`, and `2 ∣ c`.
  have hmem : algebraMap ℤ (𝓞 K) c ∈ Q :=
    hwsq ▸ Q.pow_mem_of_mem ((Ideal.mem_inertia.mp hτ) w) 2 two_pos
  have h2 : (2 : ℤ) ∣ c := (Ideal.algebraMap_int_mem_iff_dvd_of_liesOver Q _).mp hmem
  omega

/-- **`2` has trivial inertia when every radicand is `1` modulo `4`.** Let `K` be generated over
`ℚ` by square roots `r i` of integers `d i ≡ 1 (mod 4)`, and let `Q` be a prime of `𝓞 K` above
`2`. Then the inertia group of `Q` in `Gal(K/ℚ)` is trivial. No squarefreeness of the `d i` is
needed. -/
theorem inertia_eq_bot_of_forall_mod_four_eq_one (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (htop : IntermediateField.adjoin ℚ (Set.range r) = ⊤) (hd : ∀ i, d i % 4 = 1)
    (Q : Ideal (𝓞 K)) [Q.LiesOver (span {(2 : ℤ)})] :
    Q.inertia (K ≃ₐ[ℚ] K) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun τ hτ => ?_
  refine TauCeti.IntermediateField.algEquiv_eq_one_of_adjoin_eq_top htop ?_
  rintro _ ⟨i, rfl⟩
  exact apply_eq_self_of_mem_inertia_of_mod_four_eq_one (hr i) (hd i) Q hτ

/-- `2` is unramified in the multiquadratic field when every radicand is `1` modulo `4`. -/
theorem isUnramifiedAt_of_forall_mod_four_eq_one [Finite ι]
    (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (htop : IntermediateField.adjoin ℚ (Set.range r) = ⊤) (hd : ∀ i, d i % 4 = 1)
    (Q : Ideal (𝓞 K)) [Q.IsPrime] [Q.LiesOver (span {(2 : ℤ)})] :
    Algebra.IsUnramifiedAt (𝓞 ℚ) Q := by
  have := isGalois_rat hr htop
  exact (Ideal.isUnramifiedAt_iff_inertia_eq_bot (K := ℚ) Q).mpr
    (inertia_eq_bot_of_forall_mod_four_eq_one hr htop hd Q)

/-- **Residue degree one above `2` exactly when every radicand is `1` modulo `8`.** Let `K` be
generated over `ℚ` by square roots `r i` of integers `d i ≡ 1 (mod 4)`, and let `Q` be a prime of
`𝓞 K` above `2`. Then `Q` has residue degree `1` iff every `d i` is `1` modulo `8`. -/
theorem inertiaDeg_eq_one_iff_forall_mod_eight_eq_one [Finite ι]
    (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (htop : IntermediateField.adjoin ℚ (Set.range r) = ⊤) (hd : ∀ i, d i % 4 = 1)
    (Q : Ideal (𝓞 K)) [Q.IsPrime] [Q.LiesOver (span {(2 : ℤ)})] :
    Q.inertiaDeg ℤ = 1 ↔ ∀ i, d i % 8 = 1 := by
  have := isGalois_rat hr htop
  have := isUnramifiedAt_of_forall_mod_four_eq_one hr htop hd Q
  obtain ⟨σ, hσ⟩ := exists_isArithFrobAt_int_of_liesOver (p := 2) Q
  rw [Ideal.inertiaDeg_eq_orderOf (p := 2) Q hσ, orderOf_eq_one_iff]
  exact isArithFrobAt_eq_one_iff_mod_eight d r hr htop hd Q hσ

/-- **Residue degree two above `2` exactly when some radicand is `5` modulo `8`.** Let `K` be
generated over `ℚ` by square roots `r i` of integers `d i ≡ 1 (mod 4)`, and let `Q` be a prime of
`𝓞 K` above `2`. Then `Q` has residue degree `2` iff some `d i` is `5` modulo `8`. Together with
`inertiaDeg_eq_one_iff_forall_mod_eight_eq_one`, the residue degree is always `1` or `2`. -/
theorem inertiaDeg_eq_two_iff_exists_mod_eight_eq_five [Finite ι]
    (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (htop : IntermediateField.adjoin ℚ (Set.range r) = ⊤) (hd : ∀ i, d i % 4 = 1)
    (Q : Ideal (𝓞 K)) [Q.IsPrime] [Q.LiesOver (span {(2 : ℤ)})] :
    Q.inertiaDeg ℤ = 2 ↔ ∃ i, d i % 8 = 5 := by
  have := isGalois_rat hr htop
  have := isUnramifiedAt_of_forall_mod_four_eq_one hr htop hd Q
  obtain ⟨σ, hσ⟩ := exists_isArithFrobAt_int_of_liesOver (p := 2) Q
  -- A radicand `1` modulo `4` that is not `1` modulo `8` is `5` modulo `8`.
  have hmod : (∃ i, d i % 8 = 5) ↔ ¬ ∀ i, d i % 8 = 1 := by
    simp only [not_forall]
    exact exists_congr fun i => by have := hd i; omega
  rw [Ideal.inertiaDeg_eq_orderOf (p := 2) Q hσ, hmod,
    ← isArithFrobAt_eq_one_iff_mod_eight d r hr htop hd Q hσ]
  refine ⟨fun h h1 => by simp [h1] at h, fun h => ?_⟩
  exact orderOf_eq_prime
    (aut_pow_two_eq_one_of_adjoin_eq_top (d := fun i => (d i : ℚ))
      (fun i => by rw [hr i]; simp) htop σ) h

/-- **The prime-count formula at `2`.** If `K` is generated by square roots of integers
`d i ≡ 1 (mod 4)`, then the number of primes above `2` times their common residue degree is
`[K : ℚ]`. -/
theorem ncard_primesOver_two_mul_inertiaDeg_eq_finrank [Finite ι]
    (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (htop : IntermediateField.adjoin ℚ (Set.range r) = ⊤) (hd : ∀ i, d i % 4 = 1)
    (Q : Ideal (𝓞 K)) [Q.IsPrime] [Q.LiesOver (span {(2 : ℤ)})] :
    (primesOver (span {(2 : ℤ)}) (𝓞 K)).ncard * Q.inertiaDeg ℤ = finrank ℚ K := by
  have := isGalois_rat hr htop
  have := isUnramifiedAt_of_forall_mod_four_eq_one hr htop hd Q
  exact Ideal.ncard_primesOver_mul_inertiaDeg_eq_finrank_of_isUnramifiedAt (p := 2) Q

/-- **The splitting law at `2`.** Let `K` be generated over `ℚ` by square roots of integers
`d i ≡ 1 (mod 4)`. Then `2` splits completely in `K` (there are `[K : ℚ]` primes of `𝓞 K`
above `2`) iff every `d i` is `1` modulo `8`. -/
theorem ncard_primesOver_two_eq_finrank_iff [Finite ι]
    (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (htop : IntermediateField.adjoin ℚ (Set.range r) = ⊤) (hd : ∀ i, d i % 4 = 1) :
    (primesOver (span {(2 : ℤ)}) (𝓞 K)).ncard = finrank ℚ K ↔ ∀ i, d i % 8 = 1 := by
  obtain ⟨Q, hQ, hQ2⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 K) (span {((2 : ℕ) : ℤ)})
  rw [Nat.cast_ofNat] at hQ2
  rw [← inertiaDeg_eq_one_iff_forall_mod_eight_eq_one hr htop hd Q]
  have h := ncard_primesOver_two_mul_inertiaDeg_eq_finrank hr htop hd Q
  have hpos : 0 < finrank ℚ K := finrank_pos
  constructor
  · intro hsplit
    rw [hsplit] at h
    exact (Nat.mul_eq_left hpos.ne').mp h
  · intro h1
    rwa [h1, mul_one] at h

/-- **The number of primes above `2` when some radicand is `5` modulo `8`.** Let `K` be generated
over `ℚ` by square roots of integers `d i ≡ 1 (mod 4)`, some `d i` being `5` modulo `8`. Then there
are exactly `[K : ℚ] / 2` primes of `𝓞 K` above `2`. -/
theorem ncard_primesOver_two_mul_two_eq_finrank [Finite ι]
    (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (htop : IntermediateField.adjoin ℚ (Set.range r) = ⊤) (hd : ∀ i, d i % 4 = 1)
    (h5 : ∃ i, d i % 8 = 5) :
    (primesOver (span {(2 : ℤ)}) (𝓞 K)).ncard * 2 = finrank ℚ K := by
  obtain ⟨Q, hQ, hQ2⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 K) (span {((2 : ℕ) : ℤ)})
  rw [Nat.cast_ofNat] at hQ2
  rw [← (inertiaDeg_eq_two_iff_exists_mod_eight_eq_five hr htop hd Q).mpr h5]
  exact ncard_primesOver_two_mul_inertiaDeg_eq_finrank hr htop hd Q

/-- **The number of primes above `2` when some radicand is `5` modulo `8`, explicitly.** Let `K`
be generated over `ℚ` by square roots of `n` square-class independent integers `d i ≡ 1 (mod 4)`
(no nonempty subset product is a square), some `d i` being `5` modulo `8`. Then there are exactly
`2 ^ (n - 1)` primes of `𝓞 K` above `2`. -/
theorem ncard_primesOver_two_eq_two_pow_sub_one [Finite ι]
    (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (htop : IntermediateField.adjoin ℚ (Set.range r) = ⊤)
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, (d i : ℚ)))
    (hd : ∀ i, d i % 4 = 1) (h5 : ∃ i, d i % 8 = 5) :
    (primesOver (span {(2 : ℤ)}) (𝓞 K)).ncard = 2 ^ (Nat.card ι - 1) := by
  exact eq_two_pow_sub_of_mul_two_pow_eq_finrank hr htop hindep (k := 1)
    (by rw [pow_one]; exact ncard_primesOver_two_mul_two_eq_finrank hr htop hd h5)

/-! ### Residue degrees divide two

At any rational prime, ramified or not, the residue degree divides the order of a Frobenius, which
is an involution. -/

/-- **Residue degrees in a multiquadratic field divide `2`.** Let `K` be generated over `ℚ` by
square roots of integers. Then every prime of `𝓞 K`, ramified or not and above any rational prime
`p`, including `p = 2`, has residue degree `1` or `2` over `p`. -/
theorem inertiaDeg_dvd_two [Finite ι] (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (htop : IntermediateField.adjoin ℚ (Set.range r) = ⊤) (Q : Ideal (𝓞 K)) [Q.IsPrime]
    [Q.LiesOver (span {(p : ℤ)})] : Q.inertiaDeg ℤ ∣ 2 := by
  have := isGalois_rat hr htop
  obtain ⟨σ, hσ⟩ := exists_isArithFrobAt_int_of_liesOver (p := p) Q
  exact (Ideal.inertiaDeg_dvd_orderOf Q hσ).trans (orderOf_dvd_of_pow_eq_one
    (aut_pow_two_eq_one_of_adjoin_eq_top (d := fun i => (d i : ℚ))
      (fun i => by rw [hr i]; simp) htop σ))

end TauCeti.Multiquadratic
