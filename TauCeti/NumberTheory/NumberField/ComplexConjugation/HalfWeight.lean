/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.ComplexConjugation.MaximalRealOrCMSubfield

/-!
# `2 m(τ) = w` at places where some `δ` acts as complex conjugation on `E_K`

Let `K` be a number field, `Ω` a normal extension of `ℚ`, and `m` a function on the embeddings
`τ : K →+* Ω` with `m(c ∘ τ) + m(τ) = w` for every complex conjugation `c`. Suppose that `m(τ)`
depends only on `v(τ)` for some function `v` on embeddings, in the application the place of `K`
induced by `ι_p ∘ τ` for a `p`-adic embedding `ι_p` of `Ω`. If an element `δ` of `Gal(Ω/ℚ)` fixes
`v(τ₀)` (it lies in the decomposition group) and acts on the image of the largest totally real or
CM subfield `E_K` through its complex conjugation `s`, that is `δ ∘ τ₀ = τ₀ ∘ s` on `E_K`, then
`2 m(τ₀) = w` (Lawrence–Venkatesh, §2.4, proof of Lemma 2.8).

The proof: every complex conjugation `c` also satisfies `c ∘ τ₀ = τ₀ ∘ s` on `E_K`, so `δ ∘ τ₀`
and `c ∘ τ₀` agree on `E_K` and `m(δ τ₀) = m(c τ₀)` by the Artin–Weil factorization
(`TauCeti.NumberField.apply_eq_apply_of_eqOn_maximalRealOrCMSubfield`). Place-constancy gives
`m(δ τ₀) = m(τ₀)`, so `m(τ₀) + m(τ₀) = m(c τ₀) + m(τ₀) = w`. When `K` has no CM subfield,
`2 m = w` holds everywhere (`TauCeti.NumberField.two_nsmul_eq_of_forall_not_isCMField`).

The hypothesis on `δ` is the decomposition-group form of friendliness: a friendly place `v` is one
unramified over `ℚ` at which, when `E_K` is CM, such a `δ` exists.

## Main results

* `TauCeti.NumberField.two_nsmul_eq_of_apply_comp_eq`: `2 m(τ₀) = w` from one `δ` with
  `m(δ τ₀) = m(τ₀)` acting on `E_K` as its complex conjugation.
* `TauCeti.NumberField.two_nsmul_eq_of_isCMField_imp_exists_comp_eq_complexConj`: for `m`
  constant on the fibres of `v`, if (when `E_K` is CM) some `δ` fixing `v(τ₀)` acts on `E_K` as
  its complex conjugation, then `2 m(τ) = w` for every `τ` with `v(τ) = v(τ₀)`.

## References

* B. Lawrence and A. Venkatesh, *Diophantine problems and p-adic period mappings*, §2.4, proof of
  Lemma 2.8.
-/

public section

open NumberField

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] {Ω : Type*} [Field Ω] [CharZero Ω] [Normal ℚ Ω]
  {A : Type*} [AddRightCancelMonoid A] {m : (K →+* Ω) → A} {w : A}

/-- **An element acting as complex conjugation on `E_K` forces `2 m = w`.** Let `m` be a function
on embeddings `K →+* Ω` with `m(c ∘ τ) + m(τ) = w` for every complex conjugation `c`, and suppose
that `E_K` is CM. If `δ ∈ Gal(Ω/ℚ)` satisfies `m(δ ∘ τ) = m(τ)` and `δ ∘ τ = τ ∘ s` on `E_K`, for
the complex conjugation `s` of `E_K`, then `2 m(τ) = w`. -/
theorem two_nsmul_eq_of_apply_comp_eq
    (hm : ∀ c ∈ complexConjugations Ω, ∀ τ, m ((c : Ω →+* Ω).comp τ) + m τ = w)
    [IsCMField (maximalRealOrCMSubfield K)] {τ : K →+* Ω} {δ : Gal(Ω/ℚ)}
    (hδm : m ((δ : Ω →+* Ω).comp τ) = m τ)
    (hδ : ∀ x : maximalRealOrCMSubfield K,
      δ (τ x) = τ (IsCMField.complexConj (maximalRealOrCMSubfield K) x : K)) :
    2 • m τ = w := by
  obtain ⟨c, hc⟩ := complexConjugations_nonempty Ω
  have hδc : m ((δ : Ω →+* Ω).comp τ) = m ((c : Ω →+* Ω).comp τ) :=
    apply_eq_apply_of_eqOn_maximalRealOrCMSubfield hm fun x hx ↦ by
      simp only [RingHom.comp_apply, RingHom.coe_coe]
      rw [hδ ⟨x, hx⟩]
      exact (apply_eq_complexConj_of_isCMField hc
        (τ.comp (maximalRealOrCMSubfield K).subtype) ⟨x, hx⟩).symm
  rw [two_nsmul, ← hm c hc τ, ← hδc, hδm]

/-- **`2 m(τ) = w` on the fibre of `v(τ₀)` when some `δ` fixing `v(τ₀)` acts on `E_K` as its
complex conjugation.** Let `m` be a function on embeddings `K →+* Ω` with
`m(c ∘ τ) + m(τ) = w` for every complex conjugation `c`, constant on the fibres of a function `v`
on embeddings. Suppose that, if `E_K` is CM, some `δ ∈ Gal(Ω/ℚ)` with `v(δ ∘ τ₀) = v(τ₀)`
satisfies `δ ∘ τ₀ = τ₀ ∘ s` on `E_K`, for the complex conjugation `s` of `E_K`. Then `2 m(τ) = w`
for every `τ` with `v(τ) = v(τ₀)` (Lawrence–Venkatesh, §2.4, proof of Lemma 2.8). -/
theorem two_nsmul_eq_of_isCMField_imp_exists_comp_eq_complexConj {P : Type*}
    {v : (K →+* Ω) → P}
    (hm : ∀ c ∈ complexConjugations Ω, ∀ τ, m ((c : Ω →+* Ω).comp τ) + m τ = w)
    (hv : ∀ τ τ', v τ = v τ' → m τ = m τ') {τ₀ : K →+* Ω}
    (hδ : ∀ _ : IsCMField (maximalRealOrCMSubfield K), ∃ δ : Gal(Ω/ℚ),
      v ((δ : Ω →+* Ω).comp τ₀) = v τ₀ ∧ ∀ x : maximalRealOrCMSubfield K,
        δ (τ₀ x) = τ₀ (IsCMField.complexConj (maximalRealOrCMSubfield K) x : K))
    {τ : K →+* Ω} (hτ : v τ = v τ₀) : 2 • m τ = w := by
  rw [hv τ τ₀ hτ]
  by_cases hK : IsCMField (maximalRealOrCMSubfield K)
  · obtain ⟨δ, hδv, hδ⟩ := hδ hK
    exact two_nsmul_eq_of_apply_comp_eq hm (hv _ _ hδv) hδ
  · exact two_nsmul_eq_of_forall_not_isCMField
      (fun F hF ↦ hK (isCMField_maximalRealOrCMSubfield_iff_exists.mpr ⟨F, hF⟩)) hm τ₀

end TauCeti.NumberField
