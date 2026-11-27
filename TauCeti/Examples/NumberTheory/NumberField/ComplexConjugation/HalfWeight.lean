/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.ComplexConjugation.AlgebraicClosure
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings
public import TauCeti.NumberTheory.NumberField.Cyclotomic.Splitting
import TauCeti.NumberTheory.NumberField.Cyclotomic.Four.Basic

/-!
# Tests of place-constant functions with the conjugation relation

`K = ℚ(i)`, here any `4`-th cyclotomic extension of `ℚ`, and a prime `p ≡ 3 mod 4`. The prime
`p` is inert in `K`: it is unramified with inertia degree `2`, so by the splitting law of `ℚ(i)`
(`TauCeti.NumberField.ncard_primesOver_eq_one_of_mod_four_eq_three`) a single place of `K` lies
above `p`. A function `m` on the embeddings `K →+* Ω` with `m(c ∘ τ) + m(τ) = w` for every complex
conjugation `c`, whose value at `τ` depends only on the place above `p` induced by `τ`, is
therefore constant, and `2 m(τ) = w` on both embeddings: the half-weight conclusion of
Lawrence–Venkatesh (§2.4, proof of Lemma 2.8) at an inert prime.

At a prime `p ≡ 1 mod 4` the conclusion fails, so the hypothesis on the place cannot be dropped:
`p` splits into two places of `K`, and with `Ω = K`, the embedding `id` sent to one place and the
complex conjugation to the other, the exponents `m(id) = 1`, `m(conj) = 0` (those of the CM
elliptic curve with multiplication by `ℤ[i]`) satisfy `m(c ∘ τ) + m(τ) = 1` and are constant on
places. The conclusion `2 m(τ) = 1` has no solution in `ℤ`, so the content is that exponents
satisfying every other hypothesis with `w = 1` exist at such a prime.

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
  -- `p` is inert: a single place of `K` lies above `p`.
  obtain ⟨P, hP⟩ := Set.ncard_eq_one.mp (ncard_primesOver_eq_one_of_mod_four_eq_three (K := K) p h)
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

/-- **The `p ≡ 3 mod 4` hypothesis of `two_nsmul_eq_of_mod_four_eq_three` is needed.** For
`K = ℚ(i)`, `Ω = K`, `w = 1` and a prime `p ≡ 1 mod 4`, there are `m : (K →+* K) → ℤ` with
`m(id) = 1` and `v` sending each embedding to a place above `p`, such that `m(c ∘ τ) + m(τ) = 1`
for every complex conjugation `c` and `m` is constant on the fibres of `v`: every other hypothesis
of `two_nsmul_eq_of_mod_four_eq_three` holds. Its conclusion `2 m(τ) = 1` fails for every `τ`,
since `2 n = 1` has no solution `n : ℤ`; the content is the existence of `m` and `v`. -/
theorem exists_not_two_nsmul_eq_of_mod_four_eq_one (p : ℕ) [Fact p.Prime] (h : p % 4 = 1) :
    ∃ (m : (K →+* K) → ℤ) (v : (K →+* K) → HeightOneSpectrum (𝓞 K)),
      (∀ c ∈ complexConjugations K, ∀ τ, m ((c : K →+* K).comp τ) + m τ = 1) ∧
      (∀ τ, (v τ).asIdeal.LiesOver (Ideal.span {(p : ℤ)})) ∧
      (∀ τ τ', v τ = v τ' → m τ = m τ') ∧ m (RingHom.id K) = 1 ∧ ∀ τ, 2 • m τ ≠ 1 := by
  classical
  -- `p` splits: two places of `K` lie above `p`.
  obtain ⟨P₁, P₂, hne, hP⟩ :=
    Set.ncard_eq_two.mp (ncard_primesOver_eq_two_of_mod_four_eq_one (K := K) p h)
  have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by simpa using (Fact.out : p.Prime).ne_zero
  have hP₁ : P₁ ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) := hP ▸ Set.mem_insert _ _
  have hP₂ : P₂ ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) := hP ▸ Set.mem_insert_of_mem _ rfl
  let Q₁ : HeightOneSpectrum (𝓞 K) := ⟨P₁, hP₁.1, Ideal.ne_bot_of_mem_primesOver hp0 hP₁⟩
  let Q₂ : HeightOneSpectrum (𝓞 K) := ⟨P₂, hP₂.1, Ideal.ne_bot_of_mem_primesOver hp0 hP₂⟩
  have hQ : Q₁ ≠ Q₂ := fun hQ ↦ hne (congrArg HeightOneSpectrum.asIdeal hQ)
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {4} ℚ K
  have := IsCyclotomicExtension.Rat.isTotallyComplex (n := 4) K (by norm_num)
  have hcard : Nat.card Gal(K/ℚ) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, TauCeti.finrank_eq_two_of_isCyclotomicExtension_four]
  refine ⟨fun τ ↦ if τ = RingHom.id K then 1 else 0, fun τ ↦ if τ = RingHom.id K then Q₁ else Q₂,
    fun c hc τ ↦ ?_, fun τ ↦ ?_, fun τ τ' hττ' ↦ ?_, by simp, fun τ ↦ ?_⟩
  · have hc1 : (c : K →+* K) ≠ RingHom.id K := fun h1 ↦ ne_one_of_mem_complexConjugations hc
      (AlgEquiv.ext fun x ↦ by simpa using DFunLike.congr_fun h1 x)
    -- `τ` is `1` or the complex conjugation `c`, and `c² = 1`.
    rcases ringHom_eq_id_or_eq_of_mem_complexConjugations hcard hc τ with rfl | rfl
    · simp [hc1]
    · have hcc : (c : K →+* K).comp c = RingHom.id K := by ext x; simp [hc]
      simp [hcc, hc1]
  · dsimp only
    split_ifs
    exacts [hP₁.2, hP₂.2]
  · dsimp only at hττ' ⊢
    split_ifs at hττ' ⊢ <;> simp_all
  · dsimp only
    split_ifs <;> decide

end Split

end TauCeti.Examples.HalfWeight
