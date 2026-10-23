/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.MultiquadraticSplitting
public import TauCeti.NumberTheory.Multiquadratic.ResidueDegree
public import TauCeti.RingTheory.DedekindDomain.ConjugateFactorization
import TauCeti.NumberTheory.NumberField.PrimeIdeal

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
primes above it (`TauCeti.NumberField.span_natCast_eq_prod_primesOverFinset`, fed by
`isUnramifiedAt_of_forall_not_dvd`), so the combinatorial count
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

* `TauCeti.Multiquadratic.ncard_setOf_mul_smul_eq_span_prod`: the conjugate-product count at a
  squarefree product of rational primes, and
  `TauCeti.Multiquadratic.ncard_setOf_mul_smul_eq_span_natCast` at a single prime.
* `TauCeti.Multiquadratic.exists_two_pow_le_ncard_setOf_mul_smul_eq_span_prod`: the sign change on
  the square root of a radicand that is a residue modulo every prime of `T` realizes the count,
  and `TauCeti.Multiquadratic.exists_two_pow_le_ncard_setOf_mul_smul_eq_span_prod_of_eq_neg_one`
  reads that off for the radicand `-1` and primes `q ≡ 1 (mod 4)`.
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
  -- The `Fact` instance, nonvanishing of `(q)`, and the Legendre reading of the residue
  -- hypothesis, all at a single member of `T`.
  have hfact : ∀ q ∈ T, Fact q.Prime := fun q hq => ⟨hT q hq⟩
  have hq0 : ∀ q ∈ T, (span {(q : ℤ)} : Ideal ℤ) ≠ ⊥ := fun q hq => by
    have := hfact q hq
    exact span_intCast_ne_bot
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
    · have := hfact q hq
      exact IsDedekindDomain.mem_primesOverFinset_iff (hq0 q hq) (𝓞 K) |>.mp hP
    · have := hfact q hq
      exact IsDedekindDomain.mem_primesOverFinset_iff (hq0 q hq) (𝓞 K) |>.mpr hP
  -- The primes above distinct rational primes are distinct, since a prime lies over exactly one.
  have hdisj : ∀ q₁ ∈ T, ∀ q₂ ∈ T, q₁ ≠ q₂ →
      Disjoint (IsDedekindDomain.primesOverFinset (span {(q₁ : ℤ)}) (𝓞 K))
        (IsDedekindDomain.primesOverFinset (span {(q₂ : ℤ)}) (𝓞 K)) := by
    intro q₁ hq₁ q₂ hq₂ hne
    have := hfact q₁ hq₁
    have := hfact q₂ hq₂
    refine Finset.disjoint_left.2 fun P hP₁ hP₂ => ?_
    have hunder₁ :=
      ((IsDedekindDomain.mem_primesOverFinset_iff (hq0 q₁ hq₁) (𝓞 K)).mp hP₁).2.over
    have hunder₂ :=
      ((IsDedekindDomain.mem_primesOverFinset_iff (hq0 q₂ hq₂) (𝓞 K)).mp hP₂).2.over
    have hassoc : Associated (q₁ : ℤ) (q₂ : ℤ) :=
      Ideal.span_singleton_eq_span_singleton.1 (hunder₁.trans hunder₂.symm)
    exact hne (by simpa using Int.associated_iff_natAbs.1 hassoc)
  -- The prescribed ideal is the product over `S`: each `(q)` is unramified, hence the squarefree
  -- product of the primes above it.
  have hprod : ∏ P ∈ S, P = span {((∏ q ∈ T, q : ℕ) : 𝓞 K)} := by
    rw [hSdef, Finset.prod_biUnion (fun q₁ hq₁ q₂ hq₂ h => hdisj q₁ hq₁ q₂ hq₂ h)]
    have hfactor : ∀ q ∈ T, ∏ P ∈ IsDedekindDomain.primesOverFinset (span {(q : ℤ)}) (𝓞 K), P
        = span {(q : 𝓞 K)} := by
      intro q hq
      have := hfact q hq
      exact (TauCeti.NumberField.span_natCast_eq_prod_primesOverFinset
        (fun P _ _ => isUnramifiedAt_of_forall_not_dvd hr htop (hodd q hq) (hcop q hq) P)).symm
    rw [Finset.prod_congr rfl hfactor, Ideal.prod_span_singleton]
    push_cast
    rfl
  -- Involutivity of `σ`: the multiquadratic Galois group has exponent two, transported along the
  -- presentation `htop` of `K` as an adjoin of the square roots.
  have hsq : σ * σ = 1 := by
    have hr' : ∀ i, r i ^ 2 = algebraMap ℚ K (d i : ℚ) := fun i => by rw [hr i]; simp
    let e : adjoin ℚ (Set.range r) ≃ₐ[ℚ] K := (equivOfEq htop).trans topEquiv
    have h := aut_mul_self_eq_one hr' ((AlgEquiv.autCongr e).symm σ)
    rw [← map_mul] at h
    exact (MulEquiv.map_eq_one_iff _).mp h
  -- The hypotheses of the conjugate-factorization count, member by member.
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
    have := hfact q hq
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

/-! ### Realizing the count by a sign change

A radicand that is a quadratic residue modulo every member of `T` supplies the automorphism the
count needs: the sign change on its square root. For the radicand `-1` the residue condition is
the congruence `q ≡ 1 (mod 4)`, which is the shape in which the count supplies many ideals with a
prescribed conjugate product in a CM field `ℚ(i, √p₁, …, √pₙ)`. -/

section SignChange

variable {L : Type*} [Field L] [NumberField L] [Finite ι] {root : ι → L}

/-- **Many ideals with a prescribed conjugate product in a multiquadratic field.** Let
`M = ℚ(√d₁, …, √dₙ)` be generated by the square roots of square-class independent integers, let
`T` be a finite set of odd primes dividing none of the radicands, and let `d i₀` be a radicand
that is a quadratic residue modulo every member of `T`. Then the sign change `σ` on the square
root of `d i₀` admits at least `2 ^ (#T · 2 ^ (n - 2))` ideals `𝔄` of `𝓞 M` with
`𝔄 · σ𝔄 = (∏ q ∈ T, q)`: each member of `T` has at least `2 ^ (n - 1)` primes above it, since the
residue degree is at most two and `[M : ℚ] = 2 ^ n`. -/
theorem exists_two_pow_le_ncard_setOf_mul_smul_eq_span_prod
    (hroot : ∀ i, root i ^ 2 = algebraMap ℚ L (d i : ℚ))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, (d i : ℚ)))
    {i₀ : ι} {T : Finset ℕ} (hT : ∀ q ∈ T, q.Prime) (hodd : ∀ q ∈ T, q ≠ 2)
    (hcop : ∀ q ∈ T, ∀ i, ¬ (q : ℤ) ∣ d i) (hres : ∀ q ∈ T, IsSquare ((d i₀ : ZMod q))) :
    ∃ σ : adjoin ℚ (Set.range root) ≃ₐ[ℚ] adjoin ℚ (Set.range root),
      σ (gen root i₀) = -gen root i₀ ∧
        2 ^ (T.card * 2 ^ (Nat.card ι - 2)) ≤
          {A : Ideal (𝓞 (adjoin ℚ (Set.range root))) |
            A * σ • A = span {((∏ q ∈ T, q : ℕ) : 𝓞 (adjoin ℚ (Set.range root)))}}.ncard := by
  classical
  have hfact : ∀ q ∈ T, Fact q.Prime := fun q hq => ⟨hT q hq⟩
  -- The generators of `M` and their integral defining equations.
  have hgen : ∀ i, gen root i ^ 2 = algebraMap ℤ (adjoin ℚ (Set.range root)) (d i) := fun i => by
    rw [gen_sq hroot i, IsScalarTower.algebraMap_apply ℤ ℚ (adjoin ℚ (Set.range root))]
    simp
  -- The sign change on the square root of `d i₀`. It moves that square root because the radicand
  -- is not a square, in particular nonzero.
  set σ := (galoisGroupEquiv hroot hindep).symm
    (Multiplicative.ofAdd (Pi.single i₀ (1 : ZMod 2))) with hσdef
  have hneg : σ (gen root i₀) = -gen root i₀ := by
    rw [hσdef, galoisGroupEquiv_symm_apply_gen, Pi.single_eq_same, ZMod.val_one, pow_one,
      neg_one_mul]
  have hd₀ : (d i₀ : ℚ) ≠ 0 := fun h =>
    hindep {i₀} (Finset.singleton_nonempty i₀) (by simp [h])
  have hσ : σ (gen root i₀) ≠ gen root i₀ := fun h =>
    gen_ne_neg hroot i₀ hd₀ (h.symm.trans hneg)
  refine ⟨σ, hneg, ?_⟩
  rw [ncard_setOf_mul_smul_eq_span_prod hgen adjoin_gen_eq_top hT hodd hcop hres hσ]
  refine Nat.pow_le_pow_right (by norm_num) ?_
  have hfinrank : finrank ℚ (adjoin ℚ (Set.range root)) = 2 ^ Nat.card ι :=
    finrank_adjoin_range hroot hindep
  have : Nonempty ι := ⟨i₀⟩
  have hpos : 0 < Nat.card ι := Nat.card_pos
  -- Every `q ∈ T` has at least `2 · 2 ^ (n - 2)` primes above it: when every radicand is a
  -- residue mod `q` there are `2 ^ n`, and otherwise the residue degree is two, leaving `2 ^ n /
  -- 2`, where a non-residue radicand is not `d i₀` and hence forces `n ≥ 2`.
  have hg : ∀ q ∈ T, 2 * 2 ^ (Nat.card ι - 2) ≤
      (primesOver (span {(q : ℤ)}) (𝓞 (adjoin ℚ (Set.range root)))).ncard := by
    intro q hq
    have := hfact q hq
    have hres₀ : legendreSym q (d i₀) = 1 := by
      refine (legendreSym.eq_one_iff q ?_).2 (hres q hq)
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact hcop q hq i₀
    by_cases hall : ∀ i, legendreSym q (d i) = 1
    · rw [(NumberField.ncard_primesOver_multiquadratic_iff d (gen root) hgen adjoin_gen_eq_top
        (hodd q hq) (hcop q hq)).mpr hall, hfinrank]
      have hstep : (2 : ℕ) ^ (Nat.card ι - 2) ≤ 2 ^ (Nat.card ι - 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have hsucc : 2 * (2 : ℕ) ^ (Nat.card ι - 1) = 2 ^ Nat.card ι := by
        have harith : Nat.card ι - 1 + 1 = Nat.card ι := by omega
        rw [mul_comm, ← pow_succ, harith]
      omega
    · obtain ⟨i, hi⟩ : ∃ i, legendreSym q (d i) = -1 := by
        obtain ⟨i, hi⟩ := not_forall.mp hall
        have hne : ((d i : ℤ) : ZMod q) ≠ 0 := by
          rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
          exact hcop q hq i
        exact ⟨i, (legendreSym.eq_one_or_neg_one q hne).resolve_left hi⟩
      -- A non-residue radicand differs from `d i₀`, so there are at least two of them.
      have hne : i ≠ i₀ := fun h => by
        rw [h, hres₀] at hi
        norm_num at hi
      have hcard : 2 ≤ Nat.card ι := Finite.one_lt_card_iff_nontrivial.mpr ⟨i, i₀, hne⟩
      have h2 := ncard_primesOver_mul_two_eq_finrank hgen adjoin_gen_eq_top (hodd q hq)
        (hcop q hq) ⟨i, hi⟩
      have hsplit : 2 * (2 : ℕ) ^ (Nat.card ι - 2) * 2 = 2 ^ Nat.card ι := by
        have harith : Nat.card ι - 2 + 1 + 1 = Nat.card ι := by omega
        rw [mul_comm 2 ((2 : ℕ) ^ (Nat.card ι - 2)), ← pow_succ, ← pow_succ, harith]
      rw [hfinrank, ← hsplit] at h2
      omega
  have hsum : T.card * 2 ^ (Nat.card ι - 2) * 2 ≤
      ∑ q ∈ T, (primesOver (span {(q : ℤ)}) (𝓞 (adjoin ℚ (Set.range root)))).ncard :=
    calc T.card * 2 ^ (Nat.card ι - 2) * 2 = ∑ _q ∈ T, 2 * 2 ^ (Nat.card ι - 2) := by
          rw [Finset.sum_const, smul_eq_mul]
          ring
      _ ≤ _ := Finset.sum_le_sum hg
  exact (Nat.le_div_iff_mul_le two_pos).mpr hsum

/-- **Many ideals with a prescribed conjugate product in an imaginary multiquadratic field.** The
case of the radicand `-1` of `exists_two_pow_le_ncard_setOf_mul_smul_eq_span_prod`, where the
residue condition on the primes of `T` is the congruence `q ≡ 1 (mod 4)`: for the CM field
`ℚ(i, √p₁, …, √pₙ)` this is the supply of ideals with a prescribed conjugate product above a set
of split primes, and there the sign change `σ` on the square root of `-1` is complex
conjugation. -/
theorem exists_two_pow_le_ncard_setOf_mul_smul_eq_span_prod_of_eq_neg_one
    (hroot : ∀ i, root i ^ 2 = algebraMap ℚ L (d i : ℚ))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, (d i : ℚ)))
    {i₀ : ι} (hd : d i₀ = -1) {T : Finset ℕ} (hT : ∀ q ∈ T, q.Prime)
    (hmod : ∀ q ∈ T, q % 4 = 1) (hcop : ∀ q ∈ T, ∀ i, ¬ (q : ℤ) ∣ d i) :
    ∃ σ : adjoin ℚ (Set.range root) ≃ₐ[ℚ] adjoin ℚ (Set.range root),
      σ (gen root i₀) = -gen root i₀ ∧
        2 ^ (T.card * 2 ^ (Nat.card ι - 2)) ≤
          {A : Ideal (𝓞 (adjoin ℚ (Set.range root))) |
            A * σ • A = span {((∏ q ∈ T, q : ℕ) : 𝓞 (adjoin ℚ (Set.range root)))}}.ncard := by
  refine exists_two_pow_le_ncard_setOf_mul_smul_eq_span_prod hroot hindep hT
    (fun q hq hq2 => by have := hmod q hq; omega) hcop fun q hq => ?_
  -- `-1` is a quadratic residue modulo a prime `q ≡ 1 (mod 4)`.
  have := Fact.mk (hT q hq)
  have hval : ((d i₀ : ℤ) : ZMod q) = -1 := by rw [hd]; push_cast; ring
  rw [hval]
  exact ZMod.exists_sq_eq_neg_one_iff.mpr (by have := hmod q hq; omega)

end SignChange

end TauCeti.Multiquadratic
