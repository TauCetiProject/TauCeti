/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.PowerResidueSymbol.StickelbergerPhi.Relation
import TauCeti.NumberTheory.NumberField.Cyclotomic.MaximalRealSubfield
import TauCeti.NumberTheory.NumberField.AutomorphismAction
import TauCeti.NumberTheory.NumberField.Ideal.Norm

/-!
# The root-of-unity factor in Stickelberger's relation

For `m ≥ 2` and an integer `α` in the `m`-th cyclotomic field, the Stickelberger product is
`α ^ γ = ∏ σ, (σ⁻¹ α) ^ c(σ)`, where `c(σ)` is the representative of the cyclotomic
character in `[1, m)`. Its squared absolute value at every complex embedding is
`|N α| ^ m`. When the norm of `α` is prime to `m`, the unit relating it to the
Gauss sum power `Φ((α))` is therefore a root of unity. This separates the
ideal-theoretic relation from the primary-element normalization of the unit.

The argument uses `Ideal.span_stickelbergerPhi_span_singleton` and
`Ideal.stickelbergerPhi_norm_sq`, followed by Mathlib's torsion criterion
`NumberField.Units.mem_torsion`. The final theorem expresses
the unit as `±ζ ^ i`, with `i < m`, using Mathlib's cyclotomic roots-of-unity API.

## References

* S. D. Adhikari, *The early reciprocity laws: from Gauss to Eisenstein*, §4,
  Propositions 4.4(iv) and 4.5.
* N. Xu, *Reciprocity Laws*, §6, Lemmas 6.14–6.16 and Proposition 6.17.
-/

public section

open NumberField IsCyclotomicExtension.Rat

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K] (m : ℕ) [NeZero m]
  [IsCyclotomicExtension {m} ℚ K]

/-- At each complex embedding the squared absolute value of `α ^ γ` is `|N α| ^ m`. -/
theorem norm_stickelbergerProduct_sq (hm : 2 ≤ m) (α : 𝓞 K) (φ : K →+* ℂ) :
    ‖φ (stickelbergerProduct m α)‖ ^ 2 = (Ideal.absNorm (Ideal.span {α}) : ℝ) ^ m := by
  classical
  have : Fact (1 < m) := ⟨hm⟩
  let τ : Gal(K/ℚ) := (galEquivZMod m K).symm (-1)
  let f : Gal(K/ℚ) → ℝ := fun σ ↦ ‖φ (σ⁻¹ (α : K))‖
  let c : Gal(K/ℚ) → ℕ := fun σ ↦ (galEquivZMod m K σ : ZMod m).val
  have hf (σ : Gal(K/ℚ)) : f (σ * τ) = f σ := by
    simp only [f, mul_inv_rev, AlgEquiv.mul_apply]
    have ht : τ⁻¹ = τ := by
      apply (galEquivZMod m K).injective
      simp [τ]
    rw [ht, IsCyclotomicExtension.Rat.complexEmbedding_galEquivZMod_symm_neg_one_apply,
      Complex.norm_conj]
  have hc (σ : Gal(K/ℚ)) : c (σ * τ) + c σ = m := by
    have : NeZero (galEquivZMod m K σ : ZMod m) := ⟨Units.ne_zero _⟩
    simp only [c, map_mul, τ, MulEquiv.apply_symm_apply, mul_neg,
      mul_one, Units.val_neg]
    rw [ZMod.val_neg_of_ne_zero]
    have := ZMod.val_lt (galEquivZMod m K σ : ZMod m)
    omega
  have hp : ‖φ (stickelbergerProduct m α)‖ = ∏ σ, f σ ^ c σ := by
    simp [stickelbergerProduct_def, map_prod, map_pow, norm_prod, norm_pow, f, c]
  have hreindex : (∏ σ, f σ ^ c σ) = ∏ σ, f σ ^ c (σ * τ) := by
    calc
      _ = ∏ σ, f (σ * τ) ^ c (σ * τ) :=
        (Equiv.prod_comp (Equiv.mulRight τ) (fun σ ↦ f σ ^ c σ)).symm
      _ = _ := by simp only [hf]
  have hnorm : (∏ σ, f σ) = (Ideal.absNorm (Ideal.span {α}) : ℝ) := by
    have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {m} ℚ K
    exact (Equiv.prod_comp (Equiv.inv Gal(K/ℚ))
      (fun σ ↦ ‖φ (σ (α : K))‖)).trans (φ.prod_norm_automorphisms_eq_absNorm α)
  rw [hp, pow_two]
  calc
    _ = (∏ σ, f σ ^ c (σ * τ)) * (∏ σ, f σ ^ c σ) := congrArg (· * _) hreindex
    _ = (Ideal.absNorm (Ideal.span {α}) : ℝ) ^ m := by
      rw [← Finset.prod_mul_distrib]
      simp_rw [← pow_add, hc]
      rw [Finset.prod_pow, hnorm]

variable [HasEnoughRootsOfUnity (𝓞 K) m]

/-- The unit in the principal-ideal form of Stickelberger's relation has finite order. -/
theorem exists_torsion_mul_stickelbergerProduct_eq (hm : 2 ≤ m) {α : 𝓞 K}
    (hα : (Ideal.absNorm (Ideal.span {α})).Coprime m) :
    ∃ u : (𝓞 K)ˣ, u ∈ NumberField.Units.torsion K ∧
      (u : 𝓞 K) * stickelbergerProduct m α = Ideal.stickelbergerPhi (Ideal.span {α}) m := by
  obtain ⟨u, hu⟩ := (Ideal.span_singleton_eq_span_singleton.mp
    (Ideal.span_stickelbergerPhi_span_singleton hm hα)).symm
  have hu' : (u : 𝓞 K) * stickelbergerProduct m α =
      Ideal.stickelbergerPhi (Ideal.span {α}) m := by
    simpa only [mul_comm] using hu
  refine ⟨u, (NumberField.Units.mem_torsion K).mpr fun w ↦ ?_, hu'⟩
  have hN : Ideal.absNorm (Ideal.span {α}) ≠ 0 := by
    intro h
    rw [h, Nat.coprime_zero_left] at hα
    omega
  have hnorm (φ : K →+* ℂ) : ‖φ ((u : 𝓞 K) : K)‖ = 1 := by
    have hP := norm_stickelbergerProduct_sq m hm α φ
    have hΦ := Ideal.stickelbergerPhi_norm_sq hα hm φ
    rw [← hu'] at hΦ
    simp only [map_mul, norm_mul, mul_pow] at hΦ
    rw [hP] at hΦ
    have hN' : (Ideal.absNorm (Ideal.span {α}) : ℝ) ^ m ≠ 0 :=
      pow_ne_zero _ (Nat.cast_ne_zero.mpr hN)
    have hsq : ‖φ ((u : 𝓞 K) : K)‖ ^ 2 = 1 :=
      mul_right_cancel₀ hN' (hΦ.trans (one_mul _).symm)
    nlinarith [norm_nonneg (φ ((u : 𝓞 K) : K))]
  rw [← InfinitePlace.norm_embedding_eq]
  exact hnorm w.embedding

end TauCeti

namespace IsPrimitiveRoot

variable {K : Type*} [Field K] [NumberField K] {m : ℕ} [NeZero m]
  [IsCyclotomicExtension {m} ℚ K] [HasEnoughRootsOfUnity (𝓞 K) m] {ζ : K}

/-- **The root-of-unity factor in Stickelberger's relation.** For a cyclotomic integer
`α` of norm prime to `m`, the Gauss sum power `Φ((α))` is `α ^ γ` times a root of unity
`±ζ ^ i`, with `0 ≤ i < m`. -/
theorem exists_stickelbergerPhi_eq_pow_mul_or_neg_pow_mul (hζ : IsPrimitiveRoot ζ m)
    (hm : 2 ≤ m) {α : 𝓞 K} (hα : (Ideal.absNorm (Ideal.span {α})).Coprime m) :
    ∃ i : ℕ, i < m ∧
      ((Ideal.stickelbergerPhi (Ideal.span {α}) m : K) =
          ζ ^ i * (TauCeti.stickelbergerProduct m α : K) ∨
        (Ideal.stickelbergerPhi (Ideal.span {α}) m : K) =
          -ζ ^ i * (TauCeti.stickelbergerProduct m α : K)) := by
  obtain ⟨u, hu, heq⟩ := TauCeti.exists_torsion_mul_stickelbergerProduct_eq m hm hα
  have huorder : IsOfFinOrder ((u : 𝓞 K) : K) :=
    ((algebraMap (𝓞 K) K).toMonoidHom.comp (Units.coeHom _)).isOfFinOrder
      ((CommGroup.mem_torsion u).mp hu)
  have hroot : ∃ i : ℕ, i < m ∧
      (((u : 𝓞 K) : K) = ζ ^ i ∨ ((u : 𝓞 K) : K) = -ζ ^ i) := by
    obtain hm' | hm' := Nat.even_or_odd m
    · have hpow := congrArg (fun v : (𝓞 K)ˣ ↦ ((v : 𝓞 K) : K))
        (NumberField.Units.pow_torsionOrder_eq_one K hu)
      have hpow' : (((u : 𝓞 K) : K)) ^ m = 1 := by
        simpa [IsCyclotomicExtension.Rat.torsionOrder_eq (n := m) (K := K), hm'] using hpow
      obtain ⟨i, hi, he⟩ := hζ.eq_pow_of_pow_eq_one hpow'
      exact ⟨i, hi, Or.inl he.symm⟩
    · exact hζ.exists_pow_or_neg_mul_pow_of_isOfFinOrder hm' huorder
  obtain ⟨i, hi, h | h⟩ := hroot
  · refine ⟨i, hi, Or.inl ?_⟩
    simpa [← h] using congrArg (algebraMap (𝓞 K) K) heq.symm
  · refine ⟨i, hi, Or.inr ?_⟩
    simpa [← h] using congrArg (algebraMap (𝓞 K) K) heq.symm

end IsPrimitiveRoot
