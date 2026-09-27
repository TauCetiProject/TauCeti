/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Frobenius
import TauCeti.NumberTheory.Multiquadratic.Galois.Basic
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
* `TauCeti.Multiquadratic.ncard_primesOver_eq_two_pow_sub_one`: under square-class
  independence of `n` radicands, that number is `2ⁿ⁻¹`.
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
private theorem isGalois_rat [Finite ι] (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (htop : IntermediateField.adjoin ℚ (Set.range r) = ⊤) : IsGalois ℚ K :=
  isGalois_of_adjoin_eq_top (d := fun i => (d i : ℚ)) (fun i => by rw [hr i]; simp) htop

/-- Under square-class independence of the radicands, a number `g` with `g * 2 = [K : ℚ]` is
`2 ^ (n - 1)`, since `[K : ℚ] = 2 ^ n`. -/
private theorem eq_two_pow_sub_one_of_mul_two_eq_finrank [Finite ι] [Nonempty ι]
    (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (htop : IntermediateField.adjoin ℚ (Set.range r) = ⊤)
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, (d i : ℚ)))
    {g : ℕ} (h : g * 2 = finrank ℚ K) : g = 2 ^ (Nat.card ι - 1) := by
  have hr' (i : ι) : r i ^ 2 = algebraMap ℚ K (d i : ℚ) := by rw [hr i]; simp
  have hdeg := finrank_adjoin_range (K := ℚ) (L := K) (d := fun i => (d i : ℚ)) hr' hindep
  rw [htop, IntermediateField.finrank_top'] at hdeg
  rw [hdeg, ← Nat.sub_add_cancel Nat.card_pos, pow_succ] at h
  exact Nat.eq_of_mul_eq_mul_right two_pos h

/-! ### The decomposition law at an odd prime -/

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
  -- `τ (r i)` is a square root of `d i`, hence `± r i`; rule out the minus sign.
  have hr' : r i ^ 2 = algebraMap ℚ K (d i : ℚ) := by rw [hr i]; simp
  have hsq : τ (r i) ^ 2 = r i ^ 2 := by rw [← map_pow, hr', AlgEquiv.commutes]
  refine (eq_or_eq_neg_of_sq_eq_sq _ _ hsq).resolve_right fun hneg => ?_
  let R : 𝓞 K := integralSqrt (hr i)
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
  · -- `R ∈ Q` would put `d i = R ^ 2` in `Q`, so `p ∣ d i`.
    have hd : algebraMap ℤ (𝓞 K) (d i) ∈ Q := by
      rw [← integralSqrt_sq (hr i), pow_two]
      exact Q.mul_mem_left _ hRQ
    exact hcop i ((Ideal.algebraMap_int_mem_iff_dvd_of_liesOver Q _).mp hd)

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
  have : Nonempty ι := let ⟨i, _⟩ := hnr; ⟨i⟩
  exact eq_two_pow_sub_one_of_mul_two_eq_finrank hr htop hindep
    (ncard_primesOver_mul_two_eq_finrank hr htop hodd hcop hnr)

/-! ### The decomposition law at `2`

When every radicand is `1` modulo `4`, the prime `2` is unramified as well, and the dyadic
Frobenius calculation `isArithFrobAt_eq_one_iff_mod_eight` plays the role of the Legendre symbols:
the residue degree above `2` is `1` if every `dᵢ` is `1` modulo `8` and `2` otherwise. -/

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
  -- `τ (r i)` is a square root of `d i`, hence `± r i`; rule out the minus sign.
  have hsq : τ (r i) ^ 2 = r i ^ 2 := by rw [← map_pow, hr i]; simp
  refine (eq_or_eq_neg_of_sq_eq_sq _ _ hsq).resolve_right fun hneg => ?_
  -- The half-generator `w = (1 + r i) / 2` is integral, and `τ • w - w = -r i`.
  let w : 𝓞 K := ⟨(1 + r i) / 2, isIntegral_one_add_div_two_of_sq_eq (hr i) (hd i)⟩
  have hw : algebraMap (𝓞 K) K w = (1 + r i) / 2 := RingOfIntegers.map_mk _ _
  have hwsq : (τ • w - w) ^ 2 = algebraMap ℤ (𝓞 K) (d i) := by
    apply FaithfulSMul.algebraMap_injective (𝓞 K) K
    rw [map_pow, map_sub, algebraMap_smul_eq_apply, hw,
      ← IsScalarTower.algebraMap_apply ℤ (𝓞 K) K, ← hr i]
    simp only [map_div₀, map_add, map_one, map_ofNat, hneg]
    ring
  -- `τ` acts trivially modulo `Q`, so `d i = (τ • w - w) ^ 2` lies in `Q`, and `2 ∣ d i`.
  have hmem : algebraMap ℤ (𝓞 K) (d i) ∈ Q :=
    hwsq ▸ Q.pow_mem_of_mem ((Ideal.mem_inertia.mp hτ) w) 2 two_pos
  have h2 : (2 : ℤ) ∣ d i := (Ideal.algebraMap_int_mem_iff_dvd_of_liesOver Q _).mp hmem
  have := hd i
  omega

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
  have : Nonempty ι := let ⟨i, _⟩ := h5; ⟨i⟩
  exact eq_two_pow_sub_one_of_mul_two_eq_finrank hr htop hindep
    (ncard_primesOver_two_mul_two_eq_finrank hr htop hd h5)

end TauCeti.Multiquadratic
