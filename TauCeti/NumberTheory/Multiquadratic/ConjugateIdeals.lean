/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.MultiquadraticSplitting
public import TauCeti.NumberTheory.Multiquadratic.ResidueDegree
public import TauCeti.RingTheory.DedekindDomain.ConjugateFactorization
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.DedekindDomain.Factorization
import TauCeti.FieldTheory.IntermediateField.Adjoin.EqTop
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat

/-!
# Conjugate-product factorizations in a multiquadratic field

Let `K = ℚ(√d₁, …, √dₙ)` be generated over `ℚ` by square roots `r i` of integers `d i`, let `σ`
be an automorphism of `K`, and let `m` be a product of odd primes dividing none of the `d i`. This
file counts the ideals `𝔄` of `𝓞 K` whose product with its `σ`-conjugate is the prescribed ideal
`(m)`:

`#{𝔄 : 𝔄 · σ𝔄 = (m)} = 2 ^ (g / 2)`,

where `g` is the number of primes of `𝓞 K` above `m`. The count is exact, and the hypothesis that
makes it nonzero is arithmetic: some radicand `d i` is a quadratic residue modulo every prime
dividing `m` while `σ` moves its square root `r i`.

Two inputs combine. The unramifiedness of such an `m` makes `(m)` the squarefree product of the
primes above it, so the combinatorial count
`TauCeti.ncard_setOf_mul_map_eq_prod` applies once `σ` is known to act on that set of primes as a
fixed-point-free involution. Fixed-point-freeness is where the arithmetic enters: an automorphism
that fixes a prime `Q` above `p` lies in the decomposition group of `Q`, and the decomposition
group fixes the square root of every quadratic residue mod `p`
(`NumberField.map_eq_self_of_legendreSym_eq_one`). Involutivity is automatic, since a
multiquadratic Galois group has exponent two. Only the count is recorded here; which ideals they
are — the products over the transversals of the conjugate pairs — is `TauCeti.mul_map_eq_prod_iff`,
applied to the same set of primes.

The intended reading is the imaginary one: with `d i = -1`, so that `r i` is a square root of `-1`
and `σ` is the sign change on it, the residue condition becomes the congruence `p ≡ 1 (mod 4)`.
That is the CM-field source of many ideals with a prescribed conjugate product, and for a
realization inside `ℂ` with the remaining square roots real the sign change is complex
conjugation.

## Provenance

The statement being generalised is `exists_transversal_family` together with
`exists_ideal_family` in
[kim-em/erdos-unit-distance](https://github.com/kim-em/erdos-unit-distance), the formalization of
L. Alpöge's disproof of the uniform-constant Erdős unit-distance conjecture, which produce at
least `2 ^ (t · 2 ^ (g-1))` ideals `𝔄` with `𝔄 · 𝔄* = (m)` in one concrete CM field
`ℚ(i, √q₀, …, √q_{g-1})`. The combinatorial half of that argument is
`TauCeti.ncard_setOf_mul_map_eq_prod`; this file supplies the arithmetic half for an arbitrary
multiquadratic field and turns the lower bound into an exact count.

## Main results

* `TauCeti.Multiquadratic.span_natCast_eq_prod_primesOverFinset`: an odd prime dividing no
  radicand generates the squarefree product of the primes above it.
* `TauCeti.Multiquadratic.ncard_setOf_mul_smul_eq_span_prod`: the conjugate-product count at a
  squarefree product of rational primes, and
  `TauCeti.Multiquadratic.ncard_setOf_mul_smul_eq_span_natCast` at a single prime.
* `TauCeti.Multiquadratic.exists_two_pow_le_ncard_setOf_mul_smul_eq_span_prod`: for a radicand
  `-1` and primes `q ≡ 1 (mod 4)`, the sign change on its square root realizes the count.
-/

public section

open IntermediateField Module NumberField Ideal
open scoped NumberField Pointwise

namespace TauCeti.Multiquadratic

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} {d : ι → ℤ} {r : ι → K}
  {p : ℕ} [Fact p.Prime]

private theorem span_intCast_ne_bot : (span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
  have hpne : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  simpa [Ideal.span_singleton_eq_bot] using hpne

private theorem isMaximal_span_intCast : (span {(p : ℤ)} : Ideal ℤ).IsMaximal := by
  have hpne : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  exact ((Ideal.span_singleton_prime hpne).mpr
    (Nat.prime_iff_prime_int.mp Fact.out)).isMaximal span_intCast_ne_bot

/-- An automorphism of a multiquadratic field is an involution: it fixes or negates each
generator. -/
private theorem aut_mul_self_eq_one_of_adjoin_eq_top
    (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i)) (htop : adjoin ℚ (Set.range r) = ⊤)
    (σ : K ≃ₐ[ℚ] K) : σ * σ = 1 := by
  refine TauCeti.IntermediateField.algEquiv_eq_one_of_adjoin_eq_top htop ?_
  rintro _ ⟨j, rfl⟩
  have hfix : σ (algebraMap ℤ K (d j)) = algebraMap ℤ K (d j) := by
    rw [IsScalarTower.algebraMap_apply ℤ ℚ K, AlgEquiv.commutes]
  have hsq : σ (r j) ^ 2 = r j ^ 2 := by rw [← map_pow, hr j, hfix]
  rcases eq_or_eq_neg_of_sq_eq_sq (σ (r j)) (r j) hsq with h | h
  · rw [AlgEquiv.mul_apply, h, h]
  · rw [AlgEquiv.mul_apply, h, map_neg, h, neg_neg]

/-- **An unramified rational prime is the product of the primes above it.** If `K` is generated
over `ℚ` by square roots of the integers `d i` and the odd prime `p` divides none of them, then
`p` generates the squarefree product of the primes of `𝓞 K` above `p`. -/
theorem span_natCast_eq_prod_primesOverFinset [Finite ι]
    (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i)) (htop : adjoin ℚ (Set.range r) = ⊤)
    (hodd : p ≠ 2) (hcop : ∀ i, ¬ (p : ℤ) ∣ d i) :
    span {(p : 𝓞 K)}
      = ∏ P ∈ IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 K), P := by
  have hp0 : (span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := span_intCast_ne_bot
  have : (span {(p : ℤ)} : Ideal ℤ).IsMaximal := isMaximal_span_intCast
  have hfinset : IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 K)
      = ((span {(p : ℤ)}).primesOver (𝓞 K)).toFinset :=
    Finset.coe_injective (by
      rw [IsDedekindDomain.coe_primesOverFinset hp0, Set.coe_toFinset])
  have hmap : Ideal.map (algebraMap ℤ (𝓞 K)) (span {(p : ℤ)}) = span {(p : 𝓞 K)} := by
    rw [Ideal.map_span]
    simp
  rw [← hmap, Ideal.map_algebraMap_eq_finsetProd_pow hp0, hfinset]
  refine Finset.prod_congr rfl fun P hP => ?_
  -- Membership in `primesOver` carries the two instances the ramification index needs.
  obtain ⟨hPprime, hPover⟩ := Set.mem_toFinset.mp hP
  have := hPprime
  have := hPover
  have hPbot : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp0 P
  have : Algebra.IsUnramifiedAt (𝓞 ℚ) P :=
    isUnramifiedAt_of_forall_not_dvd hr htop hodd hcop P
  rw [← Ideal.ramificationIdx_ringOfIntegers_rat_eq_int P hPbot,
    Ideal.ramificationIdx_eq_one_of_isUnramifiedAt, pow_one]

/-- **The conjugate-product count at a squarefree product of rational primes.** Let `K` be
generated over `ℚ` by square roots `r i` of integers `d i`, let `T` be a finite set of odd primes
dividing none of them, and let `σ` be an automorphism of `K` moving the square root `r i` of a
radicand `d i` which is a quadratic residue modulo every member of `T`. Then the ideals `𝔄` of
`𝓞 K` with `𝔄 · σ𝔄 = (∏ q ∈ T, q)` number exactly `2 ^ (g / 2)`, where `g` is the total number of
primes of `𝓞 K` above the members of `T`. -/
theorem ncard_setOf_mul_smul_eq_span_prod [Finite ι]
    (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i)) (htop : adjoin ℚ (Set.range r) = ⊤)
    {T : Finset ℕ} (hT : ∀ q ∈ T, q.Prime) (hodd : ∀ q ∈ T, q ≠ 2)
    (hcop : ∀ q ∈ T, ∀ i, ¬ (q : ℤ) ∣ d i) {i : ι}
    (hres : ∀ q ∈ T, IsSquare ((d i : ZMod q)))
    {σ : K ≃ₐ[ℚ] K} (hσ : σ (r i) ≠ r i) :
    {A : Ideal (𝓞 K) | A * σ • A = span {((∏ q ∈ T, q : ℕ) : 𝓞 K)}}.ncard
      = 2 ^ ((∑ q ∈ T, (primesOver (span {(q : ℤ)}) (𝓞 K)).ncard) / 2) := by
  classical
  -- The `Fact` instance, nonvanishing and maximality of `(q)`, and the Legendre reading of the
  -- residue hypothesis, all at a single member of `T`.
  have hfact : ∀ q ∈ T, Fact q.Prime := fun q hq => ⟨hT q hq⟩
  have hq0 : ∀ q ∈ T, (span {(q : ℤ)} : Ideal ℤ) ≠ ⊥ := fun q hq => by
    have := hfact q hq
    exact span_intCast_ne_bot
  have hqmax : ∀ q ∈ T, (span {(q : ℤ)} : Ideal ℤ).IsMaximal := fun q hq => by
    have := hfact q hq
    exact isMaximal_span_intCast
  have hlegendre : ∀ q ∈ T, ∀ _ : Fact q.Prime, legendreSym q (d i) = 1 := by
    intro q hq _
    refine (legendreSym.eq_one_iff q ?_).2 (hres q hq)
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hcop q hq i
  set S := T.biUnion (fun q => IsDedekindDomain.primesOverFinset (span {(q : ℤ)}) (𝓞 K)) with hSdef
  have hmemS : ∀ {P : Ideal (𝓞 K)}, P ∈ S ↔
      ∃ q ∈ T, P.IsPrime ∧ P.LiesOver (span {(q : ℤ)}) := by
    intro P
    rw [hSdef, Finset.mem_biUnion]
    refine ⟨fun ⟨q, hq, hP⟩ => ⟨q, hq, ?_⟩, fun ⟨q, hq, hP⟩ => ⟨q, hq, ?_⟩⟩
    · have := hqmax q hq
      exact IsDedekindDomain.mem_primesOverFinset_iff (hq0 q hq) (𝓞 K) |>.mp hP
    · have := hqmax q hq
      exact IsDedekindDomain.mem_primesOverFinset_iff (hq0 q hq) (𝓞 K) |>.mpr hP
  -- The primes above distinct rational primes are distinct, since a prime lies over exactly one.
  have hdisj : ∀ q₁ ∈ T, ∀ q₂ ∈ T, q₁ ≠ q₂ →
      Disjoint (IsDedekindDomain.primesOverFinset (span {(q₁ : ℤ)}) (𝓞 K))
        (IsDedekindDomain.primesOverFinset (span {(q₂ : ℤ)}) (𝓞 K)) := by
    intro q₁ hq₁ q₂ hq₂ hne
    have := hqmax q₁ hq₁
    have := hqmax q₂ hq₂
    refine Finset.disjoint_left.2 fun P hP₁ hP₂ => ?_
    have hunder₁ :=
      ((IsDedekindDomain.mem_primesOverFinset_iff (hq0 q₁ hq₁) (𝓞 K)).mp hP₁).2.over
    have hunder₂ :=
      ((IsDedekindDomain.mem_primesOverFinset_iff (hq0 q₂ hq₂) (𝓞 K)).mp hP₂).2.over
    have hassoc : Associated (q₁ : ℤ) (q₂ : ℤ) :=
      Ideal.span_singleton_eq_span_singleton.1 (hunder₁.trans hunder₂.symm)
    exact hne (by simpa using Int.associated_iff_natAbs.1 hassoc)
  -- The prescribed ideal is the product over `S`.
  have hprod : ∏ P ∈ S, P = span {((∏ q ∈ T, q : ℕ) : 𝓞 K)} := by
    rw [hSdef, Finset.prod_biUnion (fun q₁ hq₁ q₂ hq₂ h => hdisj q₁ hq₁ q₂ hq₂ h)]
    have hfactor : ∀ q ∈ T, ∏ P ∈ IsDedekindDomain.primesOverFinset (span {(q : ℤ)}) (𝓞 K), P
        = span {(q : 𝓞 K)} := by
      intro q hq
      have := hfact q hq
      exact (span_natCast_eq_prod_primesOverFinset hr htop (hodd q hq) (hcop q hq)).symm
    rw [Finset.prod_congr rfl hfactor, Ideal.prod_span_singleton]
    push_cast
    rfl
  -- The hypotheses of the conjugate-factorization count, member by member.
  have hsq := aut_mul_self_eq_one_of_adjoin_eq_top hr htop σ
  have hkey := TauCeti.ncard_setOf_mul_map_eq_prod
    (σ := MulSemiringAction.toRingHom (K ≃ₐ[ℚ] K) (𝓞 K) σ) (S := S)
    (fun P hP => by obtain ⟨q, -, hPp, -⟩ := hmemS.mp hP; exact hPp)
    (fun P hP => by
      obtain ⟨q, hq, -, hPo⟩ := hmemS.mp hP
      have := hPo
      exact Ideal.ne_bot_of_liesOver_of_ne_bot (hq0 q hq) P)
    (fun P hP => by
      obtain ⟨q, hq, hPp, hPo⟩ := hmemS.mp hP
      have := hPp
      have := hPo
      rw [← Ideal.pointwise_smul_def]
      exact hmemS.mpr ⟨q, hq, Ideal.IsPrime.smul σ, Ideal.LiesOver.smul σ⟩)
    (fun P _ => by rw [← Ideal.pointwise_smul_def, ← Ideal.pointwise_smul_def, smul_smul, hsq,
      one_smul])
    (fun P hP => by
      obtain ⟨q, hq, hPp, hPo⟩ := hmemS.mp hP
      have hfq := hfact q hq
      have := hPp
      have := hPo
      rw [← Ideal.pointwise_smul_def]
      intro hfix
      exact hσ (NumberField.map_eq_self_of_legendreSym_eq_one (d i) (r i) (hr i) (hodd q hq)
        (hlegendre q hq hfq) P (MulAction.mem_stabilizer_iff.mpr hfix)))
  -- Rewrite the two sides into the stated shape.
  have hcard : ∑ q ∈ T, (primesOver (span {(q : ℤ)}) (𝓞 K)).ncard = S.card := by
    rw [hSdef, Finset.card_biUnion (fun q₁ hq₁ q₂ hq₂ h => hdisj q₁ hq₁ q₂ hq₂ h)]
    refine Finset.sum_congr rfl fun q hq => ?_
    have := hqmax q hq
    rw [← IsDedekindDomain.coe_primesOverFinset (hq0 q hq) (𝓞 K), Set.ncard_coe_finset]
  rw [hcard, ← hprod]
  simpa only [Ideal.pointwise_smul_def] using hkey

/-- **The conjugate-product count at one rational prime.** The case of a single prime of
`ncard_setOf_mul_smul_eq_span_prod`: for an odd prime `p` dividing no radicand and an automorphism
`σ` moving the square root `r i` of a radicand which is a quadratic residue mod `p`, the ideals
`𝔄` of `𝓞 K` with `𝔄 · σ𝔄 = (p)` number exactly `2 ^ (g / 2)`, where `g` is the number of primes
above `p`: one for each choice of a prime from each `σ`-conjugate pair. -/
theorem ncard_setOf_mul_smul_eq_span_natCast [Finite ι]
    (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i)) (htop : adjoin ℚ (Set.range r) = ⊤)
    (hodd : p ≠ 2) (hcop : ∀ i, ¬ (p : ℤ) ∣ d i) {i : ι} (hres : legendreSym p (d i) = 1)
    {σ : K ≃ₐ[ℚ] K} (hσ : σ (r i) ≠ r i) :
    {A : Ideal (𝓞 K) | A * σ • A = span {(p : 𝓞 K)}}.ncard
      = 2 ^ ((primesOver (span {(p : ℤ)}) (𝓞 K)).ncard / 2) := by
  have hne : ((d i : ℤ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hcop i
  have hkey := ncard_setOf_mul_smul_eq_span_prod hr htop (T := {p})
    (fun q hq => by rw [Finset.mem_singleton.mp hq]; exact Fact.out)
    (fun q hq => by rw [Finset.mem_singleton.mp hq]; exact hodd)
    (fun q hq => by rw [Finset.mem_singleton.mp hq]; exact hcop)
    (fun q hq => by
      rw [Finset.mem_singleton.mp hq]
      exact (legendreSym.eq_one_iff p hne).1 hres)
    hσ
  rwa [Finset.prod_singleton, Finset.sum_singleton] at hkey

/-! ### Imaginary multiquadratic fields

A radicand `-1` makes the residue condition the congruence `q ≡ 1 (mod 4)`, and the sign change on
its square root is the conjugation to use. This is the shape in which the count supplies many
ideals with a prescribed conjugate product in a CM field `ℚ(i, √p₁, …, √pₙ)`. -/

section NegOne

variable {L : Type*} [Field L] [NumberField L] [Finite ι] {root : ι → L}

/-- **Many ideals with a prescribed conjugate product in an imaginary multiquadratic field.** Let
`M = ℚ(√d₁, …, √dₙ₊₁)` be generated by the square roots of square-class independent integers, one
of which is `-1`, and let `T` be a finite set of primes `q ≡ 1 (mod 4)` dividing none of the
radicands. Then the sign change `σ` on the square root of `-1` admits at least
`2 ^ (#T · 2 ^ (n - 1))` ideals `𝔄` of `𝓞 M` with `𝔄 · σ𝔄 = (∏ q ∈ T, q)`.

For the CM field `ℚ(i, √p₁, …, √pₙ)` this is the supply of ideals with a prescribed conjugate
product above a set of split primes; there `σ` is complex conjugation. -/
theorem exists_two_pow_le_ncard_setOf_mul_smul_eq_span_prod
    (hroot : ∀ i, root i ^ 2 = algebraMap ℚ L (d i : ℚ))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, (d i : ℚ)))
    {i₀ : ι} (hd : d i₀ = -1) (hcard : 2 ≤ Nat.card ι)
    {T : Finset ℕ} (hT : ∀ q ∈ T, q.Prime) (hmod : ∀ q ∈ T, q % 4 = 1)
    (hcop : ∀ q ∈ T, ∀ i, ¬ (q : ℤ) ∣ d i) :
    ∃ σ : adjoin ℚ (Set.range root) ≃ₐ[ℚ] adjoin ℚ (Set.range root),
      σ (gen root i₀) = -gen root i₀ ∧
        2 ^ (T.card * 2 ^ (Nat.card ι - 2)) ≤
          {A : Ideal (𝓞 (adjoin ℚ (Set.range root))) |
            A * σ • A = span {((∏ q ∈ T, q : ℕ) : 𝓞 (adjoin ℚ (Set.range root)))}}.ncard := by
  classical
  have hfact : ∀ q ∈ T, Fact q.Prime := fun q hq => ⟨hT q hq⟩
  have hodd : ∀ q ∈ T, q ≠ 2 := fun q hq hq2 => by
    have := hmod q hq
    omega
  -- The generators of `M` and their integral defining equations.
  have hgen : ∀ i, gen root i ^ 2 = algebraMap ℤ (adjoin ℚ (Set.range root)) (d i) := fun i => by
    rw [gen_sq hroot i, IsScalarTower.algebraMap_apply ℤ ℚ (adjoin ℚ (Set.range root))]
    simp
  -- `-1` is a quadratic residue modulo a prime `q ≡ 1 (mod 4)`.
  have hres : ∀ q ∈ T, IsSquare ((d i₀ : ZMod q)) := fun q hq => by
    have := hfact q hq
    have hval : ((d i₀ : ℤ) : ZMod q) = -1 := by rw [hd]; push_cast; ring
    rw [hval]
    exact ZMod.exists_sq_eq_neg_one_iff.mpr (by have := hmod q hq; omega)
  -- The sign change on the square root of `-1`.
  set σ := (galoisGroupEquiv hroot hindep).symm
    (Multiplicative.ofAdd (Pi.single i₀ (1 : ZMod 2))) with hσdef
  have hneg : σ (gen root i₀) = -gen root i₀ := by
    rw [hσdef, galoisGroupEquiv_symm_apply_gen, Pi.single_eq_same, ZMod.val_one, pow_one,
      neg_one_mul]
  have hσ : σ (gen root i₀) ≠ gen root i₀ := fun h =>
    gen_ne_neg hroot i₀ (by rw [hd]; norm_num) (h.symm.trans hneg)
  refine ⟨σ, hneg, ?_⟩
  rw [ncard_setOf_mul_smul_eq_span_prod hgen adjoin_gen_eq_top hT hodd hcop hres hσ]
  refine Nat.pow_le_pow_right (by norm_num) ?_
  -- Every `q ∈ T` has at least `2 ^ (#ι - 1)` primes above it, since the residue degree is at
  -- most two and the degree of `M` is `2 ^ #ι`.
  have hfinrank : finrank ℚ (adjoin ℚ (Set.range root)) = 2 ^ Nat.card ι :=
    finrank_adjoin_range hroot hindep
  have hg : ∀ q ∈ T, 2 ^ (Nat.card ι - 1) ≤
      (primesOver (span {(q : ℤ)}) (𝓞 (adjoin ℚ (Set.range root)))).ncard := by
    intro q hq
    have := hfact q hq
    by_cases hall : ∀ i, legendreSym q (d i) = 1
    · rw [(NumberField.ncard_primesOver_multiquadratic_iff d (gen root) hgen adjoin_gen_eq_top
        (hodd q hq) (hcop q hq)).mpr hall, hfinrank]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    · obtain ⟨i, hi⟩ : ∃ i, legendreSym q (d i) = -1 := by
        obtain ⟨i, hi⟩ := not_forall.mp hall
        have hne : ((d i : ℤ) : ZMod q) ≠ 0 := by
          rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
          exact hcop q hq i
        exact ⟨i, (legendreSym.eq_one_or_neg_one q hne).resolve_left hi⟩
      have h2 := ncard_primesOver_mul_two_eq_finrank hgen adjoin_gen_eq_top (hodd q hq)
        (hcop q hq) ⟨i, hi⟩
      rw [hfinrank, show Nat.card ι = (Nat.card ι - 1) + 1 by omega, pow_succ] at h2
      omega
  have hsum : T.card * 2 ^ (Nat.card ι - 2) * 2 ≤
      ∑ q ∈ T, (primesOver (span {(q : ℤ)}) (𝓞 (adjoin ℚ (Set.range root)))).ncard :=
    calc T.card * 2 ^ (Nat.card ι - 2) * 2 = ∑ _q ∈ T, 2 ^ (Nat.card ι - 1) := by
          rw [Finset.sum_const, smul_eq_mul, mul_assoc, ← pow_succ,
            show Nat.card ι - 2 + 1 = Nat.card ι - 1 from by omega]
      _ ≤ _ := Finset.sum_le_sum hg
  exact (Nat.le_div_iff_mul_le two_pos).mpr hsum

end NegOne

end TauCeti.Multiquadratic
