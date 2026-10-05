/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Coprime integral multiples of invertible fractional ideals

Let `R` be a commutative ring with fraction field `K`, and let `𝔞` be an ideal of `R` contained in
only finitely many maximal ideals, for instance an ideal with finite quotient ring
(`Ideal.finite_setOfPred_isMaximal_and_le`). Every invertible fractional ideal `J` of `R` then has
a nonzero multiple `a J` which is an integral ideal of `R` coprime to `𝔞`.

No Dedekind hypothesis is made: `R` need not be integrally closed, and its non-invertible ideals
play no role. The motivating case is a non-maximal order `O` in a number field and the conductor
of `O`.

The element `a` is built by the Chinese remainder theorem. At each maximal ideal `P ⊇ 𝔞`, the
equation `J⁻¹ J = R` provides `y_P ∈ J⁻¹` and `x_P ∈ J` with `y_P x_P ∉ P`. Choosing `e_P ∈ R`
congruent to `1` modulo `P` and to `0` modulo the other maximal ideals containing `𝔞`, the element
`a = ∑ e_P y_P` of `J⁻¹` satisfies `a x_P ≡ y_P x_P` modulo `P`, so `a J` lies in none of them.

## Main results

* `FractionalIdeal.exists_mem_inv_exists_mem_mul_notMem`: for an invertible fractional ideal `J`
  and a proper ideal `P`, some product `y * x` with `y ∈ J⁻¹`, `x ∈ J` is an element of `R`
  outside `P`.
* `FractionalIdeal.exists_coeIdeal_eq_spanSingleton_mul_and_sup_eq_top`: an invertible fractional
  ideal has a nonzero multiple which is an integral ideal coprime to `𝔞`.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §7, Corollary 7.17 (orders in quadratic fields).
* G. S. Kopp and J. C. Lagarias, *Class Field Theory for Orders of Number Fields*, §2.
-/

open scoped nonZeroDivisors

public section

namespace FractionalIdeal

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]

/-- Since `J⁻¹ * J = 1`, some product `y * x` with `y ∈ J⁻¹` and `x ∈ J` is an element of `R`
outside a given proper ideal `P`. -/
theorem exists_mem_inv_exists_mem_mul_notMem (J : (FractionalIdeal R⁰ K)ˣ)
    {P : Ideal R} (hP : P ≠ ⊤) :
    ∃ y ∈ (↑J⁻¹ : FractionalIdeal R⁰ K), ∃ x ∈ (J : FractionalIdeal R⁰ K),
      ∃ r : R, algebraMap R K r = y * x ∧ r ∉ P := by
  by_contra! h
  have hle : (↑J⁻¹ : FractionalIdeal R⁰ K) * J ≤ (P : FractionalIdeal R⁰ K) := by
    refine mul_le.mpr fun y hy x hx => ?_
    obtain ⟨r, hr⟩ := (mem_one_iff R⁰).mp (J.inv_mul ▸ mul_mem_mul hy hx)
    exact (mem_coeIdeal R⁰).mpr ⟨r, h y hy x hx r hr, hr⟩
  obtain ⟨r, hr, hr1⟩ := (mem_coeIdeal R⁰).mp ((J.inv_mul ▸ hle) (one_mem_one R⁰))
  rw [← map_one (algebraMap R K), (IsFractionRing.injective R K).eq_iff] at hr1
  exact hP ((Ideal.eq_top_iff_one P).mpr (hr1 ▸ hr))

/-- **Coprime representatives.** Let `J` be an invertible fractional ideal of `R`, and let `𝔞` be
an ideal of `R` contained in only finitely many maximal ideals. Then `J` has a nonzero multiple
`a J` which is an integral ideal of `R` coprime to `𝔞`. -/
theorem exists_coeIdeal_eq_spanSingleton_mul_and_sup_eq_top (J : (FractionalIdeal R⁰ K)ˣ)
    {𝔞 : Ideal R} (h𝔞 : {P : Ideal R | P.IsMaximal ∧ 𝔞 ≤ P}.Finite) :
    ∃ a : K, a ≠ 0 ∧ ∃ I : Ideal R,
      (I : FractionalIdeal R⁰ K) = spanSingleton R⁰ a * J ∧ I ⊔ 𝔞 = ⊤ := by
  classical
  -- Every `a ∈ J⁻¹` makes `a J` integral.
  have hint {a : K} (ha : a ∈ (↑J⁻¹ : FractionalIdeal R⁰ K)) :
      ∃ I : Ideal R, (I : FractionalIdeal R⁰ K) = spanSingleton R⁰ a * J :=
    le_one_iff_exists_coeIdeal.mp <| J.inv_mul ▸ mul_le_mul_left
      (spanSingleton_le_iff_mem.mpr ha) _
  by_cases htop : 𝔞 = ⊤
  · obtain ⟨a, ha, ha0⟩ : ∃ a ∈ (↑J⁻¹ : FractionalIdeal R⁰ K), a ≠ 0 := by
      by_contra! h
      exact (J⁻¹).ne_zero (eq_zero_iff.mpr h)
    obtain ⟨I, hI⟩ := hint ha
    exact ⟨a, ha0, I, hI, by rw [htop, sup_top_eq]⟩
  -- Index by the finitely many maximal ideals `P ⊇ 𝔞`, and choose `y P ∈ J⁻¹`, `x P ∈ J` with
  -- `y P * x P = r P ∉ P`.
  let ι := {P : Ideal R // P.IsMaximal ∧ 𝔞 ≤ P}
  have : Fintype ι := @Fintype.ofFinite _ h𝔞.to_subtype
  choose y hy x hx r hr hrP using fun P : ι => exists_mem_inv_exists_mem_mul_notMem J P.2.1.ne_top
  -- Chinese remainder theorem: `e P ≡ 1` modulo `P` and `e P ≡ 0` modulo every other `Q`.
  have hcop : Pairwise (Function.onFun IsCoprime fun P : ι => (P : Ideal R)) := fun P Q hPQ =>
    Ideal.isCoprime_iff_sup_eq.mpr (P.2.1.coprime_of_ne Q.2.1 (Subtype.coe_injective.ne hPQ))
  choose e he using fun P : ι => Ideal.exists_forall_sub_mem_ideal hcop (Pi.single P 1)
  -- The element `a = ∑ e P * y P` of `J⁻¹` satisfies `a * x P ∉ P` for every `P`.
  set a : K := ∑ Q, algebraMap R K (e Q) * y Q
  have ha : a ∈ (↑J⁻¹ : FractionalIdeal R⁰ K) := Submodule.sum_mem _ fun Q _ => by
    rw [← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (hy Q)
  have hax (P : ι) : ∃ s : R, algebraMap R K s = a * x P ∧ s ∉ (P : Ideal R) := by
    choose t ht using fun Q : ι =>
      (mem_one_iff R⁰).mp (J.inv_mul ▸ mul_mem_mul (hy Q) (hx P))
    have htP : t P = r P := IsFractionRing.injective R K (by rw [ht, hr])
    -- `algebraMap (∑ e Q * t Q) = ∑ e Q * (y Q * x P) = a * x P`.
    have hs : algebraMap R K (∑ Q, e Q * t Q) = a * x P := by
      simp only [map_sum, map_mul, ht, a, Finset.sum_mul, mul_assoc]
    refine ⟨∑ Q, e Q * t Q, hs, fun hs => hrP P ?_⟩
    -- `∑ e Q * t Q - t P = (e P - 1) * t P + ∑_{Q ≠ P} e Q * t Q` lies in `P`.
    have hsub : ∑ Q, e Q * t Q - t P ∈ (P : Ideal R) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ P), add_sub_right_comm, ← sub_one_mul]
      refine add_mem (Ideal.mul_mem_right _ _ (by simpa using he P P)) (sum_mem fun Q hQ => ?_)
      exact Ideal.mul_mem_right _ _
        (by simpa [Pi.single_eq_of_ne (Finset.ne_of_mem_erase hQ).symm] using he Q P)
    simpa [htP] using Ideal.sub_mem _ hs hsub
  obtain ⟨I, hI⟩ := hint ha
  obtain ⟨P, hP, h𝔞P⟩ := Ideal.exists_le_maximal 𝔞 htop
  refine ⟨a, fun ha0 => ?_, I, hI, ?_⟩
  · obtain ⟨s, hs, hsP⟩ := hax ⟨P, hP, h𝔞P⟩
    rw [ha0, zero_mul, ← map_zero (algebraMap R K)] at hs
    exact hsP (IsFractionRing.injective R K hs ▸ P.zero_mem)
  · -- A maximal ideal `Q ⊇ I ⊔ 𝔞` would contain the element `a * x Q` of `I`.
    by_contra hne
    obtain ⟨Q, hQ, hIQ⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨s, hs, hsQ⟩ := hax ⟨Q, hQ, le_sup_right.trans hIQ⟩
    obtain ⟨s', hs', hs's⟩ := (mem_coeIdeal R⁰).mp
      (hI ▸ mul_mem_mul (mem_spanSingleton_self R⁰ a) (hx ⟨Q, hQ, le_sup_right.trans hIQ⟩))
    rw [← hs] at hs's
    exact hsQ (IsFractionRing.injective R K hs's ▸ le_sup_left.trans hIQ hs')

end FractionalIdeal
