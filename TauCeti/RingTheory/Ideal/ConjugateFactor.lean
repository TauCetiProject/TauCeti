/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Maps

/-!
# Splitting an ideal into conjugate factors

If `b` and its conjugate are comaximal and their product lies in the radical of a
conjugation-invariant ideal `J`, then the primes of `J` split into those containing `b`
and those containing its conjugate. The corresponding factor supported on the first set
can be computed as `J + (b^n)` for any sufficiently large `n`. This construction does
not require prime factorization of ideals.
-/

public section

namespace Ideal

variable {R : Type*} [CommSemiring R]

/-- An invariant ideal is the product of a unique factor supported at its primes
containing `b` and that factor's image under `e`, provided `b` and `e b` are coprime
and their product lies in the ideal's radical. -/
theorem existsUnique_conjugate_factor (J : Ideal R) (e : R →+* R)
    (hJ : J.map e = J) {b : R} (hb : IsCoprime b (e b)) (hm : b * e b ∈ J.radical) :
    ∃! I : Ideal R, I * I.map e = J ∧
      ∀ (P : Ideal R), P.IsPrime → (I ≤ P ↔ J ≤ P ∧ b ∈ P) := by
  obtain ⟨n, hn⟩ := mem_radical_iff.mp hm
  have hn' : (b * e b) ^ (n + 1) ∈ J := by
    rw [pow_succ']
    exact J.mul_mem_left _ hn
  let B : Ideal R := span {b ^ (n + 1)}
  let C : Ideal R := span {(e b) ^ (n + 1)}
  have hBC : B ⊔ C = ⊤ := by
    simpa only [B, C, ← span_singleton_pow] using
      pow_sup_pow_eq_top (sup_eq_top_iff_isCoprime b (e b) |>.mpr hb)
        (m := n + 1) (n := n + 1)
  have hprod : B * C ≤ J := by
    simpa only [B, C, span_singleton_mul_span_singleton, ← mul_pow, span_singleton_le_iff_mem]
      using hn'
  have hconj : (J ⊔ B).map e = J ⊔ C := by
    rw [map_sup, hJ]
    simp [B, C, map_span]
  have hcop : (J ⊔ B) ⊔ (J ⊔ C) = ⊤ := top_unique <| hBC ▸
    sup_le (le_sup_right.trans le_sup_left) (le_sup_right.trans le_sup_right)
  refine ⟨J ⊔ B, ⟨?_, fun P hP ↦ ?_⟩, ?_⟩
  · rw [hconj]
    apply le_antisymm
    · rw [mul_sup, sup_mul, sup_mul]
      exact sup_le (sup_le mul_le_right mul_le_right) (sup_le mul_le_left hprod)
    · rw [mul_eq_inf_of_isCoprime (isCoprime_iff_sup_eq.mpr hcop)]
      exact le_inf le_sup_left le_sup_left
  · simp only [sup_le_iff, B, span_singleton_le_iff_mem]
    exact and_congr_right fun _ ↦
      ⟨fun h ↦ hP.mem_of_pow_mem _ h, fun h ↦ P.pow_mem_of_mem h _ n.succ_pos⟩
  · intro I hI
    -- The image is supported on primes containing `e b`, by pulling a prime back along `e`.
    have hIB : I.map e ⊔ B = ⊤ := (coprime_of_no_prime_ge fun P hmap hBP hP ↦ by
      have heb : e b ∈ P :=
        ((hI.2 (P.comap e) (hP.comap e)).mp (map_le_iff_le_comap.mp hmap)).2
      exact hP.ne_top (top_unique <| hBC ▸ sup_le hBP ((span_singleton_le_iff_mem P).2
        (P.pow_mem_of_mem heb _ n.succ_pos)))).sup_eq
    have hIC : I ⊔ C = ⊤ := (coprime_of_no_prime_ge fun P hIP hCP hP ↦ by
      have hbP := ((hI.2 P hP).mp hIP).2
      exact hP.ne_top (top_unique <| hBC ▸ sup_le ((span_singleton_le_iff_mem P).2
        (P.pow_mem_of_mem hbP _ n.succ_pos)) hCP)).sup_eq
    have hBI : B ≤ I := by
      have h : I ⊔ C * B = I := sup_eq_left.mpr <|
        (mul_comm C B).le.trans (hprod.trans (hI.1 ▸ mul_le_left))
      rw [sup_mul_eq_of_coprime_left hIC] at h
      exact sup_eq_left.mp h
    rw [← hI.1, mul_comm I, mul_sup_eq_of_coprime_left hIB, sup_eq_left.mpr hBI]

end Ideal
