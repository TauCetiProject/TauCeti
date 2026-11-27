/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.ComplexConjugation.AlgebraicClosure
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings
public import TauCeti.NumberTheory.NumberField.Cyclotomic.Splitting

/-!
# Tests of place-constant functions with the conjugation relation

`K = ℚ(i)`, here any `4`-th cyclotomic extension of `ℚ`, and a prime `p ≡ 3 mod 4`. The prime
`p` is inert in `K`: it is unramified with inertia degree `2`, so by the cyclotomic splitting law
(`TauCeti.NumberField.ncard_primesOver_mul_orderOf_eq_totient`) a single place of `K` lies above
`p`. A function `m` on the embeddings `K →+* Ω` with `m(c ∘ τ) + m(τ) = w` for every complex
conjugation `c`, whose value at `τ` depends only on the place above `p` induced by `τ`, is
therefore constant, and `2 m(τ) = w` on both embeddings: the half-weight conclusion of
Lawrence–Venkatesh (§2.4, proof of Lemma 2.8) at an inert prime.

At a prime `p ≡ 1 mod 4` the conclusion fails, so the hypothesis on the place cannot be dropped:
`p` splits into two places of `K`, and with `Ω = K`, the embedding `id` sent to one place and the
complex conjugation to the other, the exponents `m(id) = 1`, `m(conj) = 0` (those of the CM
elliptic curve with multiplication by `ℤ[i]`) satisfy `m(c ∘ τ) + m(τ) = 1` and are constant on
places, while `2 m(τ) ≠ 1`.

## References

* B. Lawrence and A. Venkatesh, *Diophantine problems and p-adic period mappings*, §2.4, proof of
  Lemma 2.8.
-/

public section

open NumberField TauCeti.NumberField IsDedekindDomain

namespace TauCeti.Examples.HalfWeight

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]
  {Ω : Type*} [Field Ω] [CharZero Ω] [Normal ℚ Ω]
  {A : Type*} [AddRightCancelMonoid A] {m : (K →+* Ω) → A} {w : A}

/-- **`ℚ(i)` at `p ≡ 3 mod 4`: `2 m = w` on both embeddings.** Let `m` be a function on the
embeddings `K →+* Ω` with `m(c ∘ τ) + m(τ) = w` for every complex conjugation `c`, constant on
the fibres of a map `v` sending each embedding to a place of `K` above `p`. Then `2 m(τ) = w` for
every `τ`. -/
theorem two_nsmul_eq_of_mod_four_eq_three (p : ℕ) [Fact p.Prime] (h : p % 4 = 3)
    (hm : ∀ c ∈ complexConjugations Ω, ∀ τ, m ((c : Ω →+* Ω).comp τ) + m τ = w)
    (v : (K →+* Ω) → HeightOneSpectrum (𝓞 K))
    (hvp : ∀ τ, (v τ).asIdeal.LiesOver (Ideal.span {(p : ℤ)}))
    (hv : ∀ τ τ', v τ = v τ' → m τ = m τ') (τ : K →+* Ω) : 2 • m τ = w := by
  have h4 : ¬p ∣ 4 := fun h' ↦ by
    have := Nat.le_of_dvd (by norm_num) h'
    interval_cases p <;> simp_all
  -- `p` has order `2 = φ(4)` modulo `4`, so a single place of `K` lies above `p`.
  have hf : orderOf (p : ZMod 4) = 2 := by
    rw [← ZMod.natCast_mod, h]
    exact orderOf_eq_prime (by decide) (by decide)
  have key := ncard_primesOver_mul_orderOf_eq_totient (K := K) p h4
  rw [hf, show Nat.totient 4 = 2 by decide] at key
  have hone : ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K)).ncard = 1 := by omega
  obtain ⟨P, hP⟩ := Set.ncard_eq_one.mp hone
  obtain ⟨c, hc⟩ := complexConjugations_nonempty Ω
  have hvP (τ' : K →+* Ω) : (v τ').asIdeal = P := by
    have : (v τ').asIdeal ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) :=
      ⟨(v τ').isPrime, hvp τ'⟩
    rwa [hP] at this
  have hcτ : m ((c : Ω →+* Ω).comp τ) = m τ :=
    hv _ _ (HeightOneSpectrum.ext ((hvP _).trans (hvP τ).symm))
  rw [two_nsmul]
  nth_rewrite 1 [← hcτ]
  exact hm c hc τ

/-! ### `ℚ(i)` at `p ≡ 1 mod 4` -/

section Split

/-- A complex conjugation of `K = ℚ(i)` is not the identity: `K` has no real embedding. -/
theorem ne_one_of_mem_complexConjugations {c : Gal(K/ℚ)} (hc : c ∈ complexConjugations K) :
    c ≠ 1 := by
  intro h1
  obtain ⟨ι, hι⟩ := mem_complexConjugations_iff.mp hc
  rw [h1] at hι
  have := IsCyclotomicExtension.Rat.isTotallyComplex (n := 4) K (by norm_num)
  exact IsTotallyComplex.complexEmbedding_not_isReal ι
    (ComplexEmbedding.isConj_one_iff.mp hι)

/-- The automorphisms of `K = ℚ(i)` are `1` and any complex conjugation. -/
theorem eq_one_or_eq_of_mem_complexConjugations {c : Gal(K/ℚ)}
    (hc : c ∈ complexConjugations K) (σ : Gal(K/ℚ)) : σ = 1 ∨ σ = c := by
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {4} ℚ K
  have hcard : Nat.card Gal(K/ℚ) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, IsCyclotomicExtension.finrank (n := 4) K
      (Polynomial.cyclotomic.irreducible_rat (by norm_num))]
    decide
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : Gal(K/ℚ))).mp hcard
  by_cases hσ : σ = 1
  · exact Or.inl hσ
  · exact Or.inr ((hy σ hσ).trans (hy c (ne_one_of_mem_complexConjugations hc)).symm)

/-- **The `p ≡ 3 mod 4` hypothesis of `two_nsmul_eq_of_mod_four_eq_three` is needed.** For
`K = ℚ(i)`, `Ω = K` and a prime `p ≡ 1 mod 4`, there are `m` with `m(id) = 1` and `m = 0` at the
complex conjugation, and `v` sending the two embeddings to the two places above `p`, such that
`m(c ∘ τ) + m(τ) = 1` for every complex conjugation `c` and `m` is constant on the fibres of `v`;
yet `2 m(τ) ≠ 1` for every `τ`. -/
theorem exists_not_two_nsmul_eq_of_mod_four_eq_one (p : ℕ) [Fact p.Prime] (h : p % 4 = 1) :
    ∃ (m : (K →+* K) → ℤ) (v : (K →+* K) → HeightOneSpectrum (𝓞 K)),
      (∀ c ∈ complexConjugations K, ∀ τ, m ((c : K →+* K).comp τ) + m τ = 1) ∧
      (∀ τ, (v τ).asIdeal.LiesOver (Ideal.span {(p : ℤ)})) ∧
      (∀ τ τ', v τ = v τ' → m τ = m τ') ∧ m (RingHom.id K) = 1 ∧ ∀ τ, 2 • m τ ≠ 1 := by
  classical
  have h4 : ¬p ∣ 4 := fun h' ↦ by
    have := Nat.le_of_dvd (by norm_num) h'
    have := (Fact.out : p.Prime).two_le
    interval_cases p <;> simp_all
  -- `p` has order `1` modulo `4`, so two places of `K` lie above `p`.
  have hf : orderOf (p : ZMod 4) = 1 := by
    rw [← ZMod.natCast_mod, h, Nat.cast_one, orderOf_one]
  have key := ncard_primesOver_mul_orderOf_eq_totient (K := K) p h4
  rw [hf, show Nat.totient 4 = 2 by decide, mul_one] at key
  obtain ⟨P₁, P₂, hne, hP⟩ := Set.ncard_eq_two.mp key
  have hmem (P : Ideal (𝓞 K)) (hP' : P ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K)) :
      P.IsPrime ∧ P ≠ ⊥ ∧ P.LiesOver (Ideal.span {(p : ℤ)}) := by
    obtain ⟨hprime, hlies⟩ := hP'
    refine ⟨hprime, Ideal.ne_bot_of_liesOver_of_ne_bot (p := Ideal.span {(p : ℤ)}) ?_ P, hlies⟩
    simpa using (Fact.out : p.Prime).ne_zero
  obtain ⟨h₁, h₁', h₁''⟩ := hmem P₁ (hP ▸ Set.mem_insert _ _)
  obtain ⟨h₂, h₂', h₂''⟩ := hmem P₂ (hP ▸ Set.mem_insert_of_mem _ rfl)
  let Q₁ : HeightOneSpectrum (𝓞 K) := ⟨P₁, h₁, h₁'⟩
  let Q₂ : HeightOneSpectrum (𝓞 K) := ⟨P₂, h₂, h₂'⟩
  have hQ : Q₁ ≠ Q₂ := fun hQ ↦ hne (congrArg HeightOneSpectrum.asIdeal hQ)
  refine ⟨fun τ ↦ if τ = RingHom.id K then 1 else 0, fun τ ↦ if τ = RingHom.id K then Q₁ else Q₂,
    fun c hc τ ↦ ?_, fun τ ↦ ?_, fun τ τ' hττ' ↦ ?_, by simp, fun τ ↦ ?_⟩
  · have hc1 : (c : K →+* K) ≠ RingHom.id K := fun h1 ↦ ne_one_of_mem_complexConjugations hc
      (AlgEquiv.ext fun x ↦ RingHom.congr_fun h1 x)
    by_cases hτ : τ = RingHom.id K
    · subst hτ
      simp [hc1]
    · -- `τ` is an automorphism other than `1`, hence the complex conjugation `c`, and `c² = 1`.
      let σ : Gal(K/ℚ) := AlgEquiv.ofBijective τ.toRatAlgHom
        (Algebra.IsAlgebraic.algHom_bijective _)
      have hσ : σ = c := (eq_one_or_eq_of_mem_complexConjugations hc σ).resolve_left fun h1 ↦
        hτ (RingHom.ext fun x ↦ by simpa [σ] using AlgEquiv.ext_iff.mp h1 x)
      have hcτ : (c : K →+* K).comp τ = RingHom.id K := RingHom.ext fun x ↦ by
        have hx : τ x = c x := by simpa [σ] using AlgEquiv.ext_iff.mp hσ x
        simp only [RingHom.comp_apply, RingHom.coe_coe, RingHom.id_apply, hx]
        exact apply_apply_of_mem_complexConjugations hc x
      simp [hcτ, hτ]
  · dsimp only
    split_ifs
    exacts [h₁'', h₂'']
  · dsimp only at hττ' ⊢
    split_ifs at hττ' ⊢ <;> simp_all
  · dsimp only
    split_ifs <;> decide

end Split

end TauCeti.Examples.HalfWeight
