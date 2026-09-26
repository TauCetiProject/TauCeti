/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Square
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import TauCeti.LinearAlgebra.Span.Basic

/-!
# Elements of `𝔪 \ 𝔪²` in a local ring

For a local ring `R` with maximal ideal `𝔪`, elements of `𝔪 \ 𝔪²` are the ones that can be part
of a minimal system of generators of `𝔪`.

## Main declarations

* `TauCeti.IsLocalRing.spanFinrank_map_maximalIdeal_quotient_add_one_le`: for `x ∈ 𝔪 \ 𝔪²`, the
  maximal ideal of `R ⧸ (x)` needs at least one generator fewer than `𝔪`;
* `TauCeti.IsLocalRing.spanFinrank_map_maximalIdeal_quotient_of_le_sq`: dividing out an ideal
  contained in `𝔪²` does not change the number of generators of the maximal ideal;
* `TauCeti.IsLocalRing.exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes`: in a Noetherian
  local ring of positive dimension there is `x ∈ 𝔪 \ 𝔪²` outside every minimal prime.
-/

public section

namespace TauCeti.IsLocalRing

open _root_.IsLocalRing Ideal

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- If `x ∈ 𝔪 \ 𝔪²`, then the image of `𝔪` in `R ⧸ (x)`, which is the maximal ideal of `R ⧸ (x)`,
needs at least one generator fewer than `𝔪`. -/
theorem spanFinrank_map_maximalIdeal_quotient_add_one_le (hfg : (maximalIdeal R).FG) {x : R}
    (hxm : x ∈ maximalIdeal R) (hx : x ∉ maximalIdeal R ^ 2) :
    ((maximalIdeal R).map (Ideal.Quotient.mk (span {x}))).spanFinrank + 1 ≤
      (maximalIdeal R).spanFinrank := by
  classical
  -- `x` replaces a generator with a unit coefficient in a minimal system of generators of `𝔪`
  obtain ⟨s, hcard, hspan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank hfg
  obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.mp (hspan ▸ hxm)
  -- some coefficient of `x` is a unit, since otherwise `x ∈ 𝔪²`
  obtain ⟨i, hi, hfi⟩ : ∃ i ∈ s, IsUnit (f i) := by
    by_contra! h
    refine hx (hf ▸ Ideal.sum_mem _ fun i hi ↦ ?_)
    rw [pow_two, smul_eq_mul]
    exact mul_mem_mul (not_not.mp (mt notMem_maximalIdeal.mp (h i hi)))
      (hspan ▸ Submodule.subset_span hi)
  set q := Ideal.Quotient.mk (span {x})
  have hqx : q x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (mem_span_singleton_self x)
  have hmap : (maximalIdeal R).map q = span ((s.erase i).image q : Set (R ⧸ span {x})) := by
    rw [← hspan]
    rw [← TauCeti.Submodule.span_insert_erase_eq_span_of_isUnit hi hf hfi,
      Ideal.submodule_span_eq, Ideal.map_span,
      Set.image_insert_eq]
    rw [hqx, Ideal.span_insert_zero, Finset.coe_image]
  rw [hmap, ← hcard, ← Finset.card_erase_add_one hi, add_le_add_iff_right]
  refine (Submodule.spanFinrank_span_le_ncard_of_finite (Finset.finite_toSet _)).trans ?_
  rw [Set.ncard_coe_finset]
  exact Finset.card_image_le

/-- Dividing out an ideal contained in `𝔪²` does not change the number of generators needed for
the maximal ideal: the image of `𝔪` in `R ⧸ I` needs exactly as many generators as `𝔪`. -/
theorem spanFinrank_map_maximalIdeal_quotient_of_le_sq (hfg : (maximalIdeal R).FG) {I : Ideal R}
    (hI : I ≤ maximalIdeal R ^ 2) :
    ((maximalIdeal R).map (Ideal.Quotient.mk I)).spanFinrank = (maximalIdeal R).spanFinrank := by
  classical
  refine le_antisymm (Ideal.spanFinrank_map_le_of_fg _ hfg) ?_
  set q := Ideal.Quotient.mk I
  obtain ⟨s, hcard, hspan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank (hfg.map q)
  -- lift a minimal system of generators of the image of `𝔪` to elements of `𝔪`
  have hlift (y : R ⧸ I) (hy : y ∈ s) : ∃ x ∈ maximalIdeal R, q x = y :=
    (mem_map_iff_of_surjective q Ideal.Quotient.mk_surjective).mp
      (hspan ▸ Submodule.subset_span hy)
  choose! g hgm hgq using hlift
  -- by Nakayama's lemma the lifts generate `𝔪`, since they generate it modulo `I ≤ 𝔪²`
  have hmap : (span (s.image g : Set R)).map q = span (s : Set (R ⧸ I)) := by
    rw [Ideal.map_span, Finset.coe_image, ← Set.image_comp]
    exact congrArg span ((Set.image_congr hgq).trans (Set.image_id _))
  have hle : maximalIdeal R ≤ span (s.image g : Set R) := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot hfg
      (jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge fun x hx ↦ ?_
    have hx' : x ∈ ((span (s.image g : Set R)).map q).comap q := by
      rw [mem_comap, hmap, ← Ideal.submodule_span_eq, hspan]
      exact mem_map_of_mem q hx
    rw [comap_map_of_surjective' q Ideal.Quotient.mk_surjective, Ideal.mk_ker] at hx'
    rw [smul_eq_mul, ← pow_two]
    exact sup_le_sup_left hI _ hx'
  have heq : maximalIdeal R = span (s.image g : Set R) :=
    le_antisymm hle (span_le.mpr fun x hx ↦ by
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact hgm y hy)
  rw [← hcard]
  conv_lhs => rw [heq]
  refine (Submodule.spanFinrank_span_le_ncard_of_finite (Finset.finite_toSet _)).trans ?_
  rw [Set.ncard_coe_finset]
  exact Finset.card_image_le

/-- In a Noetherian local ring of positive dimension there is an element of the maximal ideal
which lies neither in its square nor in any minimal prime. -/
theorem exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes [IsNoetherianRing R]
    (h : 0 < ringKrullDim R) :
    ∃ x ∈ maximalIdeal R, x ∉ maximalIdeal R ^ 2 ∧ ∀ p ∈ minimalPrimes R, x ∉ p := by
  -- prime avoidance for `𝔪²` and the finitely many minimal primes
  by_contra! H
  have hsub : (maximalIdeal R : Set R) ⊆ ⋃ i ∈ insert (maximalIdeal R ^ 2) (minimalPrimes R),
      (i : Set R) := by
    intro x hx
    by_cases hx2 : x ∈ maximalIdeal R ^ 2
    · exact Set.mem_biUnion (Set.mem_insert _ _) hx2
    · obtain ⟨p, hp, hxp⟩ := H x hx hx2
      exact Set.mem_biUnion (Set.mem_insert_of_mem _ hp) hxp
  obtain ⟨i, hi, hmi⟩ := (subset_union_prime_finite
    ((minimalPrimes.finite_of_isNoetherianRing R).insert _) (f := id)
    (maximalIdeal R ^ 2) (maximalIdeal R ^ 2)
    fun (i : Ideal R) hi hi₁ _ ↦
      IsMinimalPrime.isPrime ((Set.mem_insert_iff.mp hi).resolve_left hi₁)).mp hsub
  rcases Set.mem_insert_iff.mp hi with rfl | hi
  · exact (maximalIdeal_sq_lt_of_ringKrullDim_ne_zero h.ne').not_ge hmi
  · -- `𝔪` would be a minimal prime, hence of height zero
    obtain rfl : i = maximalIdeal R :=
      le_antisymm (le_maximalIdeal (IsMinimalPrime.isPrime hi).ne_top) hmi
    rw [← maximalIdeal_height_eq_ringKrullDim, height_eq_zero_iff.mpr hi] at h
    exact h.false

end TauCeti.IsLocalRing
