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
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Nakayama

/-!
# Elements of `𝔪 \ 𝔪²` in a local ring

For a local ring `R` with maximal ideal `𝔪`, elements of `𝔪 \ 𝔪²` are the ones that can be part
of a minimal system of generators of `𝔪`.

## Main declarations

* `TauCeti.IsLocalRing.spanFinrank_map_maximalIdeal_quotient_add_one_le`: for `x ∈ 𝔪 \ 𝔪²`, the
  maximal ideal of `R ⧸ (x)` needs at least one generator fewer than `𝔪`;
* `TauCeti.IsLocalRing.spanFinrank_map_maximalIdeal_quotient_of_le_sq`: dividing out an ideal
  contained in `𝔪²` does not change the number of generators of the maximal ideal;
* `TauCeti.IsLocalRing.spanFinrank_maximalIdeal_le_spanFinrank_map_quotient_add_one`: for
  `x ∈ 𝔪`, the maximal ideal of `R ⧸ (x)` needs at most one generator fewer than `𝔪`;
* `TauCeti.IsLocalRing.exists_mem_maximalIdeal_notMem_sq_forall_notMem`: prime avoidance for
  `𝔪 \ 𝔪²` and finitely many primes other than `𝔪`;
* `TauCeti.IsLocalRing.exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes`: in a Noetherian
  local ring of positive dimension there is `x ∈ 𝔪 \ 𝔪²` outside every minimal prime;
* `TauCeti.IsLocalRing.exists_mem_maximalIdeal_notMem_sq_mem_nonZeroDivisors`: in a Noetherian
  local ring whose maximal ideal is not an associated prime there is a nonzerodivisor in
  `𝔪 \ 𝔪²`;
* `TauCeti.IsLocalRing.exists_comp_eq_id_of_notMem_sq`: for `x ∈ 𝔪 \ 𝔪²`, the residue field of
  `R ⧸ (x)` is a direct summand of `𝔪 ⧸ x 𝔪` as an `R ⧸ (x)`-module.

## References

* H. Matsumura, *Commutative Ring Theory*, Section 19, the proof of Theorem 19.2, for the direct
  summand `𝔪 ⧸ x 𝔪 ≅ κ ⊕ 𝔪 ⧸ (x)`.
-/

public section

namespace TauCeti.IsLocalRing

open _root_.IsLocalRing Ideal Pointwise

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

/-- **Prime avoidance for `𝔪 \ 𝔪²`.** If the maximal ideal is neither contained in its square
nor one of finitely many primes `S`, then some element of `𝔪 \ 𝔪²` lies in no prime of `S`. -/
theorem exists_mem_maximalIdeal_notMem_sq_forall_notMem {S : Set (Ideal R)} (hS : S.Finite)
    (hprime : ∀ p ∈ S, p.IsPrime) (hsq : ¬maximalIdeal R ≤ maximalIdeal R ^ 2)
    (hm : maximalIdeal R ∉ S) :
    ∃ x ∈ maximalIdeal R, x ∉ maximalIdeal R ^ 2 ∧ ∀ p ∈ S, x ∉ p := by
  by_contra! H
  have hsub : (maximalIdeal R : Set R) ⊆ ⋃ i ∈ insert (maximalIdeal R ^ 2) S, (i : Set R) := by
    intro x hx
    by_cases hx2 : x ∈ maximalIdeal R ^ 2
    · exact Set.mem_biUnion (Set.mem_insert _ _) hx2
    · obtain ⟨p, hp, hxp⟩ := H x hx hx2
      exact Set.mem_biUnion (Set.mem_insert_of_mem _ hp) hxp
  obtain ⟨i, hi, hmi⟩ := (subset_union_prime_finite (hS.insert _) (f := id)
    (maximalIdeal R ^ 2) (maximalIdeal R ^ 2)
    fun (i : Ideal R) hi hi₁ _ ↦ hprime i ((Set.mem_insert_iff.mp hi).resolve_left hi₁)).mp hsub
  rcases Set.mem_insert_iff.mp hi with rfl | hi
  · exact hsq hmi
  · -- a prime containing `𝔪` is `𝔪`
    exact hm (le_antisymm (le_maximalIdeal (hprime i hi).ne_top) hmi ▸ hi)

/-- In a Noetherian local ring of positive dimension there is an element of the maximal ideal
which lies neither in its square nor in any minimal prime. -/
theorem exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes [IsNoetherianRing R]
    (h : 0 < ringKrullDim R) :
    ∃ x ∈ maximalIdeal R, x ∉ maximalIdeal R ^ 2 ∧ ∀ p ∈ minimalPrimes R, x ∉ p := by
  refine exists_mem_maximalIdeal_notMem_sq_forall_notMem
    (minimalPrimes.finite_of_isNoetherianRing R) (fun p hp ↦ hp.isPrime)
    (maximalIdeal_sq_lt_of_ringKrullDim_ne_zero h.ne').not_ge fun hm ↦ ?_
  -- `𝔪` would be a minimal prime, hence of height zero
  rw [← maximalIdeal_height_eq_ringKrullDim, height_eq_zero_iff.mpr hm] at h
  exact h.false

/-- Dividing out an element `x ∈ 𝔪` saves at most one generator of the maximal ideal: `𝔪` is
generated by `x` together with lifts of generators of its image in `R ⧸ (x)`. -/
theorem spanFinrank_maximalIdeal_le_spanFinrank_map_quotient_add_one
    (hfg : (maximalIdeal R).FG) {x : R} (hxm : x ∈ maximalIdeal R) :
    (maximalIdeal R).spanFinrank ≤
      ((maximalIdeal R).map (Ideal.Quotient.mk (span {x}))).spanFinrank + 1 := by
  classical
  set q := Ideal.Quotient.mk (span {x})
  obtain ⟨s, hcard, hspan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank (hfg.map q)
  -- lift the generators of the image of `𝔪` to elements of `𝔪`
  have hlift (y : R ⧸ span {x}) (hy : y ∈ s) : ∃ z ∈ maximalIdeal R, q z = y :=
    (mem_map_iff_of_surjective q Ideal.Quotient.mk_surjective).mp
      (hspan ▸ Submodule.subset_span hy)
  choose! g hgm hgq using hlift
  have hmap : (span (s.image g : Set R)).map q = (maximalIdeal R).map q := by
    rw [Ideal.map_span, Finset.coe_image, ← Set.image_comp, ← hspan]
    exact congrArg span ((Set.image_congr hgq).trans (Set.image_id _))
  -- `𝔪` is generated by `x` and the lifts, since its image is generated by the lifts
  have heq : maximalIdeal R = span (insert x (s.image g : Set R)) := by
    refine le_antisymm (fun z hz ↦ ?_) (span_le.mpr ?_)
    · have hz' : z ∈ ((span (s.image g : Set R)).map q).comap q := by
        rw [mem_comap, hmap]
        exact mem_map_of_mem q hz
      rw [comap_map_of_surjective' q Ideal.Quotient.mk_surjective, Ideal.mk_ker] at hz'
      rw [Set.insert_eq, span_union, sup_comm]
      exact hz'
    · rintro z (rfl | hz)
      · exact hxm
      · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
        exact hgm y hy
  rw [← hcard, heq]
  refine (Submodule.spanFinrank_span_le_ncard_of_finite
    ((Finset.finite_toSet _).insert x)).trans ?_
  refine (Set.ncard_insert_le _ _).trans ?_
  rw [Set.ncard_coe_finset]
  exact Nat.add_le_add_right Finset.card_image_le 1

/-- In a Noetherian local ring whose maximal ideal is not an associated prime, that is, of
positive depth, there is a nonzerodivisor in `𝔪 \ 𝔪²`. -/
theorem exists_mem_maximalIdeal_notMem_sq_mem_nonZeroDivisors [IsNoetherianRing R]
    (h : maximalIdeal R ∉ associatedPrimes R R) :
    ∃ x ∈ maximalIdeal R, x ∉ maximalIdeal R ^ 2 ∧ x ∈ nonZeroDivisors R := by
  have hsq : ¬maximalIdeal R ≤ maximalIdeal R ^ 2 := fun hle ↦ by
    -- `𝔪 = 𝔪²` forces `𝔪 = 0` by Nakayama's lemma; then every associated prime of `R` is `𝔪`
    have hm : maximalIdeal R = ⊥ :=
      Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) (maximalIdeal R)
        (maximalIdeal R).fg_of_isNoetherianRing (by rwa [smul_eq_mul, ← pow_two])
        (jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    obtain ⟨p, hp⟩ := associatedPrimes.nonempty R R
    obtain rfl : p = maximalIdeal R := le_antisymm (le_maximalIdeal hp.isPrime.ne_top) (hm ▸ bot_le)
    exact h hp
  -- the zero divisors are the union of the finitely many associated primes
  obtain ⟨x, hxm, hx2, hx⟩ := exists_mem_maximalIdeal_notMem_sq_forall_notMem
    (associatedPrimes.finite R R) (fun p hp ↦ hp.isPrime) hsq h
  have : x ∉ ⋃ p ∈ associatedPrimes R R, (p : Set R) := by simpa using hx
  rw [biUnion_associatedPrimes_eq_compl_nonZeroDivisors, Set.notMem_compl_iff] at this
  exact ⟨x, hxm, hx2, this⟩

/-- **The residue field is a direct summand of `𝔪 ⧸ x 𝔪`.** For `x ∈ 𝔪 \ 𝔪²`, the residue field
`(R ⧸ (x)) ⧸ 𝔪 (R ⧸ (x))` of `R ⧸ (x)` is a retract of the `R ⧸ (x)`-module `𝔪 ⧸ x 𝔪`: the
section sends `1` to the class of `x`, and the retraction is a linear form on the cotangent space
`𝔪 ⧸ 𝔪²` taking the value `1` at `x`. -/
theorem exists_comp_eq_id_of_notMem_sq {x : R} (hxm : x ∈ maximalIdeal R)
    (hx : x ∉ maximalIdeal R ^ 2) :
    ∃ (i : (R ⧸ span {x}) ⧸ (maximalIdeal R).map (Ideal.Quotient.mk (span {x})) →ₗ[R ⧸ span {x}]
        maximalIdeal R ⧸ span {x} • (⊤ : Submodule R (maximalIdeal R)))
      (r : maximalIdeal R ⧸ span {x} • (⊤ : Submodule R (maximalIdeal R)) →ₗ[R ⧸ span {x}]
        (R ⧸ span {x}) ⧸ (maximalIdeal R).map (Ideal.Quotient.mk (span {x}))),
      r ∘ₗ i = LinearMap.id := by
  set I := span {x}
  set q := Ideal.Quotient.mk I
  have hN : I • (⊤ : Submodule R (maximalIdeal R)) = x • ⊤ :=
    Submodule.ideal_span_singleton_smul x ⊤
  -- `i` sends `1` to the class of `x`, which `𝔪` kills modulo `x 𝔪`.
  let x' : maximalIdeal R := ⟨x, hxm⟩
  have hi : (maximalIdeal R).map q ≤ LinearMap.ker (LinearMap.toSpanSingleton (R ⧸ I) _
      (Submodule.Quotient.mk (p := I • (⊤ : Submodule R (maximalIdeal R))) x')) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [mem_comap, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply,
      Module.Quotient.mk_smul_mk, Submodule.Quotient.mk_eq_zero, hN]
    convert Submodule.smul_mem_pointwise_smul (⟨a, ha⟩ : maximalIdeal R) x ⊤ trivial using 1
    ext
    simp [x', mul_comm]
  let i := ((maximalIdeal R).map q).liftQ _ hi
  -- `r` is a linear form on the cotangent space `𝔪 ⧸ 𝔪²` taking the value `1` at `x`.
  have hx0 : (maximalIdeal R).toCotangent x' ≠ 0 := by
    rwa [Ne, Ideal.toCotangent_eq_zero]
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one (ResidueField R) hx0
  let ψ : maximalIdeal R →ₗ[R] ResidueField R :=
    φ.restrictScalars R ∘ₗ (maximalIdeal R).toCotangent
  have hψ : I • (⊤ : Submodule R (maximalIdeal R)) ≤ LinearMap.ker ψ := by
    rw [hN]
    rintro _ ⟨m, -, rfl⟩
    rw [LinearMap.mem_ker, DistribSMul.toLinearMap_apply, map_smul, Algebra.smul_def,
      IsLocalRing.ResidueField.algebraMap_eq, (IsLocalRing.residue_eq_zero_iff x).mpr hxm,
      zero_mul]
  let θ : ResidueField R →ₗ[R] (R ⧸ I) ⧸ (maximalIdeal R).map q :=
    (Ideal.quotientMapₐ ((maximalIdeal R).map q) (Ideal.Quotient.mkₐ R I)
      Ideal.le_comap_map).toLinearMap
  let r := (θ ∘ₗ Submodule.liftQ _ ψ hψ).extendScalarsOfSurjective
    (Ideal.Quotient.mk_surjective (I := I))
  refine ⟨i, r, Submodule.linearMap_qext _ (LinearMap.ext_ring ?_)⟩
  have hi1 : i (Submodule.Quotient.mk 1) = Submodule.Quotient.mk x' := by
    rw [Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, one_smul]
  have hr : r (Submodule.Quotient.mk x') = 1 := by
    rw [LinearMap.extendScalarsOfSurjective_apply, LinearMap.comp_apply, Submodule.liftQ_apply,
      LinearMap.comp_apply, LinearMap.restrictScalars_apply, hφ]
    exact map_one (Ideal.quotientMapₐ ((maximalIdeal R).map q) (Ideal.Quotient.mkₐ R I)
      Ideal.le_comap_map)
  rw [LinearMap.comp_apply, LinearMap.comp_apply, Submodule.mkQ_apply, hi1, hr,
    LinearMap.comp_apply, LinearMap.id_apply, Submodule.mkQ_apply, Ideal.Quotient.mk_eq_mk,
    map_one]

end TauCeti.IsLocalRing
