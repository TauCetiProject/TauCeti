/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Presentation.PowerConjugate.Basic

/-!
# Bounded normal forms from power-conjugate relations

For generators `x₀, …, xₙ₋₁` with triangular power-conjugate relations and positive power
bounds `mᵢ`, every element of the generated subgroup has an expression
`xₙ₋₁ ^ eₙ₋₁ * … * x₀ ^ e₀`, with `eᵢ < mᵢ`. The descending order agrees with the cyclic
extension convention `h * x ^ k` of `Subgroup.mem_sup_zpowers_iff_exists_mul_pow`.

`powerConjugateNormalForm` evaluates these bounded exponent tuples in the actual generated
subgroup, with existence proved in `PowerConjugate.Basic`. This module gives the ambient
membership characterization, uniqueness criterion, and homomorphism comparison.
Surjectivity turns universal checks on that subgroup into finite checks on
tuples, for example when certifying conjugacy coverage in a Sylow subgroup. No consistency
or uniqueness of the expressions is assumed. The tuples give unique normal forms exactly
when the subgroup order attains the product of the power bounds.

The ambient group need not be finite. In a presented group, the relations must be proved
in that presented group; their validity in a finite permutation image alone does not suffice.

## References

* D. F. Holt, B. Eick and E. A. O'Brien, *Handbook of Computational Group Theory*,
  Chapter 8, for power-conjugate presentations and collection.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G]

/-- A bounded normal form belongs to a suffix subgroup when every exponent before that
suffix is zero. -/
theorem powerConjugateNormalForm_mem_generatorSuffix {n : ℕ} (x : Fin n → G)
    (m : Fin n → ℕ) (e : ∀ i, Fin (m i)) (k : ℕ)
    (he : ∀ i : Fin n, (i : ℕ) < k → (e i : ℕ) = 0) :
    (powerConjugateNormalForm x m e : G) ∈ generatorSuffix x k := by
  rw [coe_powerConjugateNormalForm]
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp hg)
  by_cases hi : k ≤ (i : ℕ)
  · exact Subgroup.pow_mem _ (apply_mem_generatorSuffix x i hi) _
  · simp [he i (by omega)]

/-- Membership in the generated subgroup is equivalent to the existence of a bounded
descending power expression. This form supports proofs about elements given in the ambient
group, without constructing a subgroup element first. -/
theorem mem_closure_iff_exists_powerConjugateNormalForm {n : ℕ} (x : Fin n → G)
    (m : Fin n → ℕ) (hm : ∀ i, 0 < m i)
    (hpow : ∀ i : Fin n, x i ^ m i ∈ generatorSuffix x ((i : ℕ) + 1))
    (hconj : ∀ i j : Fin n, i < j →
      x i * x j * (x i)⁻¹ ∈ generatorSuffix x ((i : ℕ) + 1)) {g : G} :
    g ∈ Subgroup.closure (Set.range x) ↔
      ∃ e : ∀ i, Fin (m i), (powerConjugateNormalForm x m e : G) = g := by
  constructor
  · intro hg
    obtain ⟨e, he⟩ := powerConjugateNormalForm_surjective x m hm hpow hconj ⟨g, hg⟩
    exact ⟨e, congrArg Subtype.val he⟩
  · rintro ⟨e, rfl⟩
    exact (powerConjugateNormalForm x m e).property

/-- **Uniqueness of bounded normal forms is equivalent to attaining the order bound.**
Under the triangular power-conjugate relations, distinct exponent tuples represent distinct
elements exactly when the generated subgroup has order equal to the product of the bounds. -/
theorem powerConjugateNormalForm_injective_iff {n : ℕ} (x : Fin n → G)
    (m : Fin n → ℕ) (hm : ∀ i, 0 < m i)
    (hpow : ∀ i : Fin n, x i ^ m i ∈ generatorSuffix x ((i : ℕ) + 1))
    (hconj : ∀ i j : Fin n, i < j →
      x i * x j * (x i)⁻¹ ∈ generatorSuffix x ((i : ℕ) + 1)) :
    Function.Injective (powerConjugateNormalForm x m) ↔
      Nat.card (Subgroup.closure (Set.range x)) = ∏ i, m i := by
  have hsurj := powerConjugateNormalForm_surjective x m hm hpow hconj
  have hc : Nat.card (∀ i, Fin (m i)) = ∏ i, m i := by simp
  constructor
  · intro hinj
    exact (Nat.card_eq_of_bijective _ ⟨hinj, hsurj⟩).symm.trans hc
  · intro hcard
    exact (hsurj.bijective_of_nat_card_le (by rw [hc, hcard])).1

end TauCeti

namespace MonoidHom

open TauCeti

variable {G H : Type*} [Group G] [Group H]

/-- Evaluation of normal forms commutes with a group homomorphism. In particular, a normal-form
identity checked in a presented group remains valid in each of its images. -/
theorem map_powerConjugateNormalForm {n : ℕ} (f : G →* H) (x : Fin n → G)
    (m : Fin n → ℕ) (e : ∀ i, Fin (m i)) :
    f (powerConjugateNormalForm x m e : G) =
      (powerConjugateNormalForm (f ∘ x) m e : H) := by
  simp only [coe_powerConjugateNormalForm, ← List.prod_hom, List.map_reverse, List.map_ofFn,
    Function.comp_def, map_pow]

end MonoidHom
