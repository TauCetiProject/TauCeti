/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Frobenius
import TauCeti.FieldTheory.IntermediateField.Adjoin.EqTop
import TauCeti.NumberTheory.Multiquadratic.Degree
import TauCeti.NumberTheory.NumberField.Frobenius.DecompositionGroup
import TauCeti.NumberTheory.NumberField.AutomorphismAction
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat
import TauCeti.RingTheory.Ideal.LiesOver

/-!
# The decomposition law at an unramified odd prime of a multiquadratic field

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

No squarefreeness of the radicands is assumed: unramifiedness is proved directly from
`p ∤ 2 dᵢ` rather than through the discriminant.

## Main results

* `TauCeti.Multiquadratic.inertia_eq_bot_of_forall_not_dvd`: the inertia group of a prime above
  an odd `p` dividing no radicand is trivial.
* `TauCeti.Multiquadratic.inertiaDeg_eq_one_iff_forall_legendreSym_eq_one` and
  `TauCeti.Multiquadratic.inertiaDeg_eq_two_iff_exists_legendreSym_eq_neg_one`: the residue
  degree of a prime above such a `p` is `1` if every `dᵢ` is a quadratic residue mod `p`, and
  `2` if some `dᵢ` is not.
* `TauCeti.Multiquadratic.ncard_primesOver_mul_two_eq_finrank`: when some `dᵢ` is a non-residue,
  there are `[K : ℚ] / 2` primes above `p`.
* `TauCeti.Multiquadratic.ncard_primesOver_eq_two_pow_sub_one`: under square-class
  independence of `n` radicands, that number is `2ⁿ⁻¹`.

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

/-- A number field generated over `ℚ` by square roots of integers is Galois over `ℚ`. -/
private theorem isGalois_rat_of_adjoin_eq_top [Finite ι] (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (htop : IntermediateField.adjoin ℚ (Set.range r) = ⊤) : IsGalois ℚ K := by
  have hr' (i : ι) : r i ^ 2 = algebraMap ℚ K (d i : ℚ) := by rw [hr i]; simp
  have hg := isGalois (K := ℚ) (L := K) (d := fun i => (d i : ℚ)) hr'
  rw [htop] at hg
  exact isGalois_iff_isGalois_top.mp hg

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

/-- The Frobenius at an odd prime dividing no radicand is an involution. -/
private theorem isArithFrobAt_pow_two_eq_one (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (htop : IntermediateField.adjoin ℚ (Set.range r) = ⊤) (hodd : p ≠ 2)
    (hcop : ∀ i, ¬ (p : ℤ) ∣ d i) (Q : Ideal (𝓞 K)) [Q.LiesOver (span {(p : ℤ)})]
    {σ : K ≃ₐ[ℚ] K} (hσ : IsArithFrobAt ℤ σ Q) : σ ^ 2 = 1 := by
  refine TauCeti.IntermediateField.algEquiv_eq_one_of_adjoin_eq_top htop ?_
  rintro _ ⟨i, rfl⟩
  have happ := isArithFrobAt_apply_sqrt hodd (hcop i) (hr i) Q hσ
  have hne : ((d i : ℤ) : ZMod p) ≠ 0 := by rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hcop i
  rw [pow_two, AlgEquiv.mul_apply, happ, map_zsmul, happ, smul_smul, ← pow_two,
    legendreSym.sq_one p hne, one_smul]

/-- At a prime above an odd prime dividing no radicand, the residue degree over `ℤ` is the order
of a Frobenius. The decomposition-group API computes it over `𝓞 ℚ`; the comparison lemmas of
`TauCeti.NumberTheory.NumberField.Ideal.IntegersRat` transport it to `ℤ`. -/
private theorem inertiaDeg_eq_orderOf [Finite ι] (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (htop : IntermediateField.adjoin ℚ (Set.range r) = ⊤) (hodd : p ≠ 2)
    (hcop : ∀ i, ¬ (p : ℤ) ∣ d i) (Q : Ideal (𝓞 K)) [Q.IsPrime]
    [Q.LiesOver (span {(p : ℤ)})] {σ : K ≃ₐ[ℚ] K} (hσ : IsArithFrobAt ℤ σ Q) :
    Q.inertiaDeg ℤ = orderOf σ := by
  have := isGalois_rat_of_adjoin_eq_top hr htop
  have hp0 : (span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hQ : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp0 Q
  have : Algebra.IsUnramifiedAt (𝓞 ℚ) Q :=
    (Ideal.isUnramifiedAt_iff_inertia_eq_bot (K := ℚ) Q).mpr
      (inertia_eq_bot_of_forall_not_dvd hr htop hodd hcop Q)
  rw [← Ideal.inertiaDeg_ringOfIntegers_rat_eq_int Q hQ,
    Ideal.orderOf_eq_inertiaDeg_of_isArithFrobAt Q hQ
      ((Ideal.isArithFrobAt_ringOfIntegers_rat_iff σ Q).mpr hσ)]

/-- **Residue degree one exactly at the residues.** Let `K` be generated over `ℚ` by square roots
`r i` of integers `d i`, and let `Q` be a prime of `𝓞 K` above an odd prime `p` dividing none of
the `d i`. Then `Q` has residue degree `1` iff every `d i` is a quadratic residue mod `p`. -/
theorem inertiaDeg_eq_one_iff_forall_legendreSym_eq_one [Finite ι]
    (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (htop : IntermediateField.adjoin ℚ (Set.range r) = ⊤) (hodd : p ≠ 2)
    (hcop : ∀ i, ¬ (p : ℤ) ∣ d i) (Q : Ideal (𝓞 K)) [Q.IsPrime]
    [Q.LiesOver (span {(p : ℤ)})] :
    Q.inertiaDeg ℤ = 1 ↔ ∀ i, legendreSym p (d i) = 1 := by
  have := isGalois_rat_of_adjoin_eq_top hr htop
  obtain ⟨σ, hσ⟩ := exists_isArithFrobAt_int_of_liesOver (p := p) Q
  rw [inertiaDeg_eq_orderOf hr htop hodd hcop Q hσ, orderOf_eq_one_iff]
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
  have := isGalois_rat_of_adjoin_eq_top hr htop
  obtain ⟨σ, hσ⟩ := exists_isArithFrobAt_int_of_liesOver (p := p) Q
  have hiff := isArithFrobAt_multiquadratic_eq_one_iff d r hr htop hodd hcop Q hσ
  -- Away from `p ∣ d i`, a Legendre symbol that is not `1` is `-1`.
  have hsym : (∃ i, legendreSym p (d i) = -1) ↔ ¬ ∀ i, legendreSym p (d i) = 1 := by
    simp only [not_forall]
    refine exists_congr fun i => ⟨fun h => by rw [h]; decide, fun h => ?_⟩
    refine (legendreSym.eq_one_or_neg_one p ?_).resolve_left h
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hcop i
  rw [inertiaDeg_eq_orderOf hr htop hodd hcop Q hσ, hsym, ← hiff]
  refine ⟨fun h h1 => by simp [h1] at h, fun h => ?_⟩
  exact orderOf_eq_prime (isArithFrobAt_pow_two_eq_one hr htop hodd hcop Q hσ) h

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
  have := isGalois_rat_of_adjoin_eq_top hr htop
  have hpne : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hp0 : (span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hpne
  have : (span {(p : ℤ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hpne).mpr (Nat.prime_iff_prime_int.mp Fact.out)).isMaximal hp0
  obtain ⟨⟨Q, hQp, hQo⟩⟩ := (inferInstance : Nonempty (primesOver (span {(p : ℤ)}) (𝓞 K)))
  have hQ : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp0 Q
  have : Algebra.IsUnramifiedAt (𝓞 ℚ) Q :=
    (Ideal.isUnramifiedAt_iff_inertia_eq_bot (K := ℚ) Q).mpr
      (inertia_eq_bot_of_forall_not_dvd hr htop hodd hcop Q)
  -- Orbit–stabilizer: the primes above `p` form one orbit, and the stabilizer of the unramified
  -- prime `Q` has order its residue degree, which is `2`.
  have horbit : orbit (K ≃ₐ[ℚ] K) Q = (span {(p : ℤ)}).primesOver (𝓞 K) :=
    Algebra.IsInvariant.orbit_eq_primesOver ℤ (𝓞 K) (K ≃ₐ[ℚ] K) (span {(p : ℤ)}) Q
  rw [← (inertiaDeg_eq_two_iff_exists_legendreSym_eq_neg_one hr htop hodd hcop Q).mpr hnr,
    ← Ideal.inertiaDeg_ringOfIntegers_rat_eq_int Q hQ,
    ← Ideal.card_stabilizer_eq_inertiaDeg_of_isUnramifiedAt Q hQ, ← Nat.card_coe_set_eq,
    ← horbit, ← Nat.card_prod, Nat.card_congr (orbitProdStabilizerEquivGroup (K ≃ₐ[ℚ] K) Q),
    IsGalois.card_aut_eq_finrank]

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
  have hr' (i : ι) : r i ^ 2 = algebraMap ℚ K (d i : ℚ) := by rw [hr i]; simp
  have hdeg := finrank_adjoin_range (K := ℚ) (L := K) (d := fun i => (d i : ℚ)) hr' hindep
  rw [htop, IntermediateField.finrank_top'] at hdeg
  have h := ncard_primesOver_mul_two_eq_finrank hr htop hodd hcop hnr
  -- A non-residue exists, so there is a radicand and `2 ^ n = 2 ^ (n - 1) * 2`.
  obtain ⟨i, -⟩ := hnr
  have hn : 0 < Nat.card ι := Nat.card_pos_iff.mpr ⟨⟨i⟩, inferInstance⟩
  rw [hdeg, ← Nat.sub_add_cancel hn, pow_succ] at h
  exact Nat.eq_of_mul_eq_mul_right two_pos h

end TauCeti.Multiquadratic
