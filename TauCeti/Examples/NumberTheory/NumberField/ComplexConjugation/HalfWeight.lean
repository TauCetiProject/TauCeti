/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.ComplexConjugation.AlgebraicClosure
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

end TauCeti.Examples.HalfWeight
