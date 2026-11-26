/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.Analysis.Normed.Ring.Finite

/-!
# Families of algebraic integers of squared norm one

In an abelian number field (in particular a cyclotomic field), if the squared absolute
values of a finite family of algebraic integers sum to `1` under one complex embedding,
they do so under every embedding. Thus all conjugates of each entry lie in the closed
unit disk. By Kronecker's theorem, the nonzero entries are roots of unity, and there must
be exactly one of them. This is the arithmetic step that singles out one coefficient in
an orthonormal expansion of a norm-one virtual character on a coset.
-/

public section

open Complex NumberField

namespace Finset

open ComplexEmbedding

/-- A rational sum of squared absolute values in an abelian extension of `ℚ` is independent of
the complex embedding. No integrality of the summands is required. -/
theorem sum_normSq_eq_ratCast_iff_of_isAbelianGalois {K ι : Type*} [Field K] [Algebra ℚ K]
    [IsAbelianGalois ℚ K] (s : Finset ι) (b : ι → K) (φ ψ : K →+* ℂ) (q : ℚ) :
    (∑ i ∈ s, normSq (φ (b i))) = (q : ℝ) ↔ (∑ i ∈ s, normSq (ψ (b i))) = (q : ℝ) := by
  obtain ⟨c, hc⟩ := exists_comp_symm_eq_of_comp_eq (k := ℚ) φ (conjugate φ) (Subsingleton.elim _ _)
  have hcφ : IsConj φ c.symm := hc.symm
  -- Abelianity makes the automorphism inducing complex conjugation independent of the embedding.
  obtain ⟨g, rfl⟩ := exists_comp_symm_eq_of_comp_eq (k := ℚ) φ ψ (Subsingleton.elim _ _)
  have hcomm : g.symm⁻¹ * c.symm * g.symm = c.symm := by
    rw [mul_comm' _ c.symm, mul_assoc, inv_mul_cancel, mul_one]
  have hcψ : IsConj (φ.comp g.symm) c.symm := hcomm ▸ hcφ.comp g.symm
  have h (σ : K →+* ℂ) (hcσ : IsConj σ c.symm) :
      (∑ i ∈ s, normSq (σ (b i))) = (q : ℝ) ↔
        (∑ i ∈ s, b i * c.symm (b i)) = algebraMap ℚ K q := by
    rw [← ofReal_inj, ← σ.injective.eq_iff]
    simp [hcσ.eq, mul_conj, ofReal_ratCast]
  exact (h φ hcφ).trans (h _ hcψ).symm

/-- In an abelian number field, squared absolute values of algebraic integers sum to `1`
precisely when one entry is a root of unity and all other entries in the sum are zero. -/
theorem sum_normSq_eq_one_iff_of_isAbelianGalois {K ι : Type*} [Field K] [NumberField K]
    [IsAbelianGalois ℚ K] (s : Finset ι) (b : ι → 𝓞 K) (φ : K →+* ℂ) :
    (∑ i ∈ s, normSq (φ (b i))) = 1 ↔
      ∃ i ∈ s, IsOfFinOrder (b i : K) ∧ ∀ j ∈ s, j ≠ i → b j = 0 := by
  classical
  have normSq_eq_one {i : ι} (hi : IsOfFinOrder (b i : K)) : normSq (φ (b i)) = 1 := by
    have hn : ‖φ (b i)‖ = 1 := (φ.toMonoidHom.isOfFinOrder hi).norm_eq_one
    rw [normSq_eq_norm_sq, hn, one_pow]
  constructor
  · intro h
    obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (h.trans_ne one_ne_zero)
    have hbi : (b i : K) ≠ 0 := fun hb ↦ hne (by simp [hb])
    have hbound (ψ : K →+* ℂ) : ‖ψ (b i)‖ ≤ 1 := by
      have hψ : (∑ j ∈ s, normSq (ψ (b j))) = 1 := by
        simpa using (sum_normSq_eq_ratCast_iff_of_isAbelianGalois s (fun j ↦ ↑(b j)) φ ψ 1).mp
          (by simpa using h)
      have hle := Finset.single_le_sum (f := fun j ↦ normSq (ψ (b j)))
        (fun j _ ↦ normSq_nonneg _) hi
      rw [hψ, normSq_eq_norm_sq] at hle
      exact le_of_pow_le_pow_left₀ two_ne_zero zero_le_one (by simpa only [one_pow] using hle)
    obtain ⟨m, hm, hpow⟩ := Embeddings.pow_eq_one_of_norm_le_one K ℂ hbi (b i).isIntegral_coe hbound
    have hroot := isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm, hpow⟩
    refine ⟨i, hi, hroot, fun j hj hji ↦ ?_⟩
    have hz : (∑ k ∈ s.erase i, normSq (φ (b k))) = 0 := by
      simpa [normSq_eq_one hroot] using (Finset.sum_erase_add _ _ hi).trans h
    have hjz := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ ↦ normSq_nonneg (φ (b k)))).mp hz
      j (Finset.mem_erase.mpr ⟨hji, hj⟩)
    exact RingOfIntegers.coe_injective (φ.injective (by simpa using hjz))
  · rintro ⟨i, hi, hroot, hzero⟩
    rw [Finset.sum_eq_single_of_mem i hi (fun j hj hji ↦ by simp [hzero j hj hji]),
      normSq_eq_one hroot]

end Finset
