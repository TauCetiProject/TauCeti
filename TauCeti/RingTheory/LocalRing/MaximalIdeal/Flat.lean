/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.SpanRankOperations
public import Mathlib.RingTheory.Flat.EquationalCriterion

/-!
# Generators of the maximal ideal along flat local homomorphisms

Let `R → S` be a flat homomorphism of Noetherian local rings under which the maximal ideal `𝔪_R`
of `R` generates the maximal ideal `𝔪_S` of `S`. Then `𝔪_R` and `𝔪_S` need the same number of
generators. One inequality holds without flatness, since the images of generators of `𝔪_R`
generate `𝔪_S`. For the other, the images of elements of `𝔪_R` that are linearly independent in
`𝔪_R / 𝔪_R²` remain linearly independent in `𝔪_S / 𝔪_S²`: by the equational criterion for
flatness, a relation modulo `𝔪_S² = 𝔪_R² S` among them comes from relations modulo `𝔪_R²` in `R`,
whose coefficients all lie in `𝔪_R`.

The basic example is the completion of a Noetherian local ring at its maximal ideal, where Mathlib
proves the same equality as `AdicCompletion.spanFinrank_maximalIdeal_eq`.

## Main results

* `TauCeti.IsLocalRing.spanFinrank_maximalIdeal_eq_of_flat_of_map_maximalIdeal_eq`: the maximal
  ideals of `R` and `S` have the same minimal number of generators.

## References

* H. Matsumura, *Commutative Ring Theory*, Theorem 23.7.
-/

public section

namespace TauCeti.IsLocalRing

open _root_.IsLocalRing

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Let `x₁, …, xₙ ∈ R` be such that `∑ rᵢ xᵢ ∈ J` forces every `rᵢ ∈ I`. After a flat base change
`R → S`, the same holds for `∑ sᵢ xᵢ ∈ J S`: every `sᵢ ∈ I S`. -/
private theorem mem_map_of_sum_mul_mem_map [Module.Flat R S] {n : ℕ} {x : Fin n → R}
    {I J : Ideal R} (hJ : J.FG) (hx : ∀ r : Fin n → R, ∑ i, r i * x i ∈ J → ∀ i, r i ∈ I)
    {s : Fin n → S} (hs : ∑ i, s i * algebraMap R S (x i) ∈ J.map (algebraMap R S)) (i : Fin n) :
    s i ∈ I.map (algebraMap R S) := by
  obtain ⟨m, y, rfl⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hJ
  rw [Ideal.map_span, ← Set.range_comp, Ideal.mem_span_range_iff_exists_fun] at hs
  obtain ⟨t, ht⟩ := hs
  -- The relation `∑ xᵢ sᵢ - ∑ yⱼ tⱼ = 0` in the flat `R`-module `S` is trivial.
  have hrel : ∑ k, Sum.elim x (fun j ↦ -y j) k • Sum.elim s t k = 0 := by
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Algebra.smul_def, map_neg,
      neg_mul, Finset.sum_neg_distrib]
    simp only [Function.comp_apply, mul_comm (algebraMap R S _)] at ht ⊢
    rw [ht, add_neg_cancel]
  obtain ⟨k, a, w, hsw, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
  have hI : ∀ j, a (.inl i) j ∈ I := by
    intro j
    refine hx (fun i ↦ a (.inl i) j) ?_ i
    have := ha j
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, neg_mul,
      Finset.sum_neg_distrib, add_neg_eq_zero] at this
    simp only [mul_comm (a _ j), this]
    exact Ideal.sum_mem _ fun l _ ↦ Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨l, rfl⟩)
  have hsi := hsw (.inl i)
  rw [Sum.elim_inl] at hsi
  rw [hsi]
  exact Ideal.sum_mem _ fun j _ ↦ by
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hI j))

variable [IsLocalRing R] [IsLocalRing S]

/-- Along a flat homomorphism of Noetherian local rings under which the maximal ideal of `R`
generates the maximal ideal of `S`, the two maximal ideals have the same minimal number of
generators. -/
theorem spanFinrank_maximalIdeal_eq_of_flat_of_map_maximalIdeal_eq [IsNoetherianRing R]
    [IsNoetherianRing S] [Module.Flat R S]
    (h : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S) :
    (maximalIdeal S).spanFinrank = (maximalIdeal R).spanFinrank := by
  refine le_antisymm (h ▸ Ideal.spanFinrank_map_le_of_fg _ (maximalIdeal R).fg_of_isNoetherianRing)
    ?_
  rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace,
    spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  -- Lift a basis of `𝔪_R / 𝔪_R²` to elements `xᵢ ∈ 𝔪_R`.
  let b := Module.finBasis (ResidueField R) (CotangentSpace R)
  choose x hx using fun i ↦ (maximalIdeal R).toCotangent_surjective (b i)
  have hxS (i) : algebraMap R S (x i) ∈ maximalIdeal S := h ▸ Ideal.mem_map_of_mem _ (x i).2
  -- A relation `∑ rᵢ xᵢ ∈ 𝔪_R²` has all coefficients in `𝔪_R`.
  have key (r : Fin _ → R) (hr : ∑ i, r i * x i ∈ maximalIdeal R ^ 2) (i) :
      r i ∈ maximalIdeal R := by
    rw [← residue_eq_zero_iff]
    refine Fintype.linearIndependent_iff.mp b.linearIndependent (fun i ↦ residue R (r i)) ?_ i
    have hmem : ((∑ i, r i • x i : maximalIdeal R) : R) ∈ maximalIdeal R ^ 2 := by simpa using hr
    rw [← (maximalIdeal R).toCotangent_eq_zero, map_sum] at hmem
    simpa [← hx, ← algebraMap_smul (ResidueField R), ResidueField.algebraMap_eq] using hmem
  -- The images of the `xᵢ` in `𝔪_S / 𝔪_S²` are linearly independent.
  suffices LinearIndependent (ResidueField S)
      fun i ↦ (maximalIdeal S).toCotangent ⟨_, hxS i⟩ by
    simpa using this.fintype_card_le_finrank
  refine Fintype.linearIndependent_iff.mpr fun g hg i ↦ ?_
  choose s hs using fun i ↦ residue_surjective (g i)
  have hsum : ∑ i, s i * algebraMap R S (x i) ∈ (maximalIdeal R ^ 2).map (algebraMap R S) := by
    rw [Ideal.map_pow, h]
    simp only [← hs, ← ResidueField.algebraMap_eq, algebraMap_smul, ← map_smul, ← map_sum,
      Ideal.toCotangent_eq_zero] at hg
    simpa using hg
  rw [← hs, residue_eq_zero_iff, ← h]
  exact mem_map_of_sum_mul_mem_map ((maximalIdeal R).fg_of_isNoetherianRing.pow (n := 2)) key
    hsum i

end TauCeti.IsLocalRing
