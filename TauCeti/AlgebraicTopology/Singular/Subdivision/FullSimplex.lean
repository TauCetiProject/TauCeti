/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Subdivision.Basic
public import TauCeti.Geometry.Convex.FullSimplex
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Measure-theoretic tiling of the full-dimensional simplex by barycentric subdivision

For each permutation `π` of `Fin (p + 1)`, the `π`-th barycentric subdivision simplex of the
standard `p`-simplex has vertices `BarycentricSubdivision.vertex π`, and on the full-dimensional
simplex `Δᵖ ⊆ ℝᵖ` it is parametrized by the continuous affine map
`affineMapAmbient (BarycentricSubdivision.vertex π) : ℝᵖ →ᴬ[ℝ] ℝᵖ`.

This file establishes the Euclidean and measure-theoretic properties of these subdivision maps:

* Each map factors as the vertex permutation `simplexMapAmbient π` composed with the identity
  chamber map `affineMapAmbient (vertex 1)`, and its linear part has exact determinant
  `(π.sign : ℝ) / ((p + 1).factorial : ℝ)` (`det_contLinear_affineMapAmbient_vertex`). In
  particular, each subdivision map is injective and preserves or reverses orientation according to
  `π.sign`.
* Distinct permutations give distinct vertex tuples (`vertex_injective`).
* The image of `Δᵖ` under `affineMapAmbient (vertex π)` is the order chamber where the barycentric
  weights satisfy `w (π 0) ≤ w (π 1) ≤ … ≤ w (π p)` (`mem_image_affineMapAmbient_vertex_iff`).
* These `(p + 1)!` chambers cover `Δᵖ` (`iUnion_image_affineMapAmbient_vertex`) and overlap in sets
  of Lebesgue measure zero (`volume_image_affineMapAmbient_vertex_inter_eq_zero`), since any two
  distinct chambers intersect inside a proper affine hyperplane where two barycentric weights agree.
* Consequently, Bochner integrals over `Δᵖ` decompose over the barycentric subdivision, both in
  unsigned change-of-variables form (`sum_setIntegral_affineMapAmbient_vertex`) and in signed
  orientation-weighted form (`sum_sign_setIntegral_affineMapAmbient_vertex`).

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1, barycentric subdivision of simplices.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18, smooth singular chains.
-/

public section

noncomputable section

open Convexity Equiv MeasureTheory Set
open scoped BigOperators

namespace TauCeti

namespace BarycentricSubdivision

variable {p : ℕ}

/-- The `k`-th vertex of the `π`-th subdivision simplex is the image under `π` of the `k`-th vertex
of the identity subdivision simplex. -/
theorem vertex_eq_map_one (π : Perm (Fin (p + 1))) (k : Fin (p + 1)) :
    vertex π k = (vertex 1 k).map π := by
  rw [vertex_def, vertex_def, ← Equiv.coe_toEmbedding, StdSimplex.map_subBarycenter]
  congr 1
  rw [Finset.map_map]
  congr 1

/-- The barycentric weight of `vertex π k` at vertex `π j` is `(p + 1 - k)⁻¹` when `k ≤ j` and `0`
otherwise. -/
theorem weights_vertex_apply (π : Perm (Fin (p + 1))) (k j : Fin (p + 1)) :
    (vertex π k).weights (π j) = if k ≤ j then ((p + 1 - (k : ℕ) : ℝ)⁻¹) else 0 := by
  rw [vertex_def, StdSimplex.weights_subBarycenter]
  have hcard : (((Finset.Ici k).map π.toEmbedding).card : ℝ) = (p + 1 - (k : ℕ) : ℝ) := by
    rw [Finset.card_map, Fin.card_Ici, Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
  rw [hcard]
  by_cases h : k ≤ j
  · simp [h, Finsupp.single_apply, Finset.sum_ite_eq']
  · simp [h, Finsupp.single_apply]

/-- Distinct permutations determine distinct barycentric subdivision vertex tuples. -/
theorem vertex_injective : Function.Injective (vertex (n := p)) := by
  intro π₁ π₂ h
  have hsymm : π₁.symm = π₂.symm := by
    ext m
    have hset (π : Perm (Fin (p + 1))) :
        Finset.univ.filter (fun k : Fin (p + 1) ↦ (vertex π k).weights m ≠ 0) =
          Finset.Iic (π.symm m) := by
      ext k
      have hpos : ((p + 1 - (k : ℕ) : ℝ)⁻¹) ≠ 0 := by
        refine inv_ne_zero ?_
        have hk : (k : ℕ) < p + 1 := k.isLt
        have : (0 : ℝ) < (p + 1 - (k : ℕ) : ℝ) := by
          have : (k : ℝ) < (p : ℝ) + 1 := by exact_mod_cast hk
          linarith
        exact this.ne'
      have hw := weights_vertex_apply π k (π.symm m)
      rw [Equiv.apply_symm_apply] at hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic, hw]
      split_ifs with hk
      · exact ⟨fun _ ↦ hk, fun _ ↦ hpos⟩
      · exact ⟨fun h0 ↦ (h0 rfl).elim, fun hk' ↦ (hk hk').elim⟩
    have hcard : (Finset.Iic (π₁.symm m)).card = (Finset.Iic (π₂.symm m)).card := by
      rw [← hset π₁, ← hset π₂, h]
    simpa [Fin.card_Iic] using hcard
  exact Equiv.symm_bijective.injective hsymm

/-- The ambient affine map of the `π`-th barycentric subdivision simplex is the vertex permutation
`simplexMapAmbient π` composed with the identity chamber map. -/
theorem affineMapAmbient_vertex_eq_comp (π : Perm (Fin (p + 1))) :
    affineMapAmbient (vertex π) = (simplexMapAmbient π).comp (affineMapAmbient (vertex 1)) := by
  refine continuousAffineMap_eq_of_eqOn_fullSimplex fun x hx ↦ ?_
  rw [ContinuousAffineMap.comp_apply, affineMapAmbient_coe _ ⟨x, hx⟩,
    affineMapAmbient_coe _ ⟨x, hx⟩,
    simplexMapAmbient_coe π ((fullSimplexEquivStdSimplex p).symm
      (StdSimplex.affineMapMk (vertex 1) (fullSimplexEquivStdSimplex p ⟨x, hx⟩))),
    Homeomorph.apply_symm_apply]
  congr 2
  ext m
  obtain ⟨j, rfl⟩ := π.surjective m
  rw [StdSimplex.weights_map, Finsupp.mapDomain_apply_of_injective π.injective,
    StdSimplex.affineMapMk_apply, StdSimplex.affineMapMk_apply, StdSimplex.weights_iConvexComb,
    StdSimplex.weights_iConvexComb, Finsupp.sum_apply, Finsupp.sum_apply,
    Finsupp.sum_fintype _ _ (by simp), Finsupp.sum_fintype _ _ (by simp)]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul, vertex_eq_map_one π k,
    StdSimplex.weights_map, Finsupp.mapDomain_apply_of_injective π.injective]

/-- The linear part of the identity barycentric subdivision map has determinant `((p + 1)!)⁻¹`. -/
theorem det_contLinear_affineMapAmbient_vertex_one (p : ℕ) :
    LinearMap.det (affineMapAmbient (vertex (n := p) 1)).contLinear.toLinearMap =
      ((p + 1).factorial : ℝ)⁻¹ := by
  rw [det_contLinear_affineMapAmbient]
  set M : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ := Matrix.of fun j i ↦ (vertex 1 i).weights j
  have hlower : M.IsLowerTriangular := by
    intro j k hjk
    have hlt : j < k := hjk
    have hw := weights_vertex_apply (1 : Perm (Fin (p + 1))) k j
    simpa [M, not_le.mpr hlt] using hw
  rw [Matrix.det_of_isLowerTriangular M hlower]
  have hdiag : ∀ k : Fin (p + 1), M k k = ((p + 1 - (k : ℕ) : ℝ)⁻¹) := fun k ↦ by
    have hw := weights_vertex_apply (1 : Perm (Fin (p + 1))) k k
    simpa [M] using hw
  simp_rw [hdiag]
  rw [← Equiv.prod_comp (Fin.revPerm : Perm (Fin (p + 1)))]
  have hrev : ∀ k : Fin (p + 1), ((p + 1 - ((Fin.revPerm k : Fin (p + 1)) : ℕ) : ℝ)⁻¹) =
      (((k : ℕ) + 1 : ℕ) : ℝ)⁻¹ := fun k ↦ by
    congr 1
    simp only [Fin.revPerm_apply, Fin.val_rev]
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  simp_rw [hrev, Finset.prod_inv_distrib]
  congr 1
  rw [Fin.prod_univ_eq_prod_range (fun k ↦ ((k + 1 : ℕ) : ℝ))]
  exact_mod_cast Finset.prod_range_add_one_eq_factorial (p + 1)

/-- The linear part of the `π`-th barycentric subdivision map has determinant
`π.sign / (p + 1)!`. -/
theorem det_contLinear_affineMapAmbient_vertex (π : Perm (Fin (p + 1))) :
    LinearMap.det (affineMapAmbient (vertex π)).contLinear.toLinearMap =
      (π.sign : ℝ) / ((p + 1).factorial : ℝ) := by
  rw [affineMapAmbient_vertex_eq_comp, ContinuousAffineMap.comp_contLinear]
  have hcomp :
      ((simplexMapAmbient π).contLinear.comp
        (affineMapAmbient (vertex 1)).contLinear).toLinearMap =
      (simplexMapAmbient π).contLinear.toLinearMap ∘ₗ
        (affineMapAmbient (vertex 1)).contLinear.toLinearMap := rfl
  rw [hcomp, LinearMap.det_comp, det_contLinear_simplexMapAmbient_perm,
    det_contLinear_affineMapAmbient_vertex_one, div_eq_mul_inv]

/-- The absolute determinant of every barycentric subdivision map on `Δᵖ` is `((p + 1)!)⁻¹`. -/
theorem abs_det_contLinear_affineMapAmbient_vertex (π : Perm (Fin (p + 1))) :
    |LinearMap.det (affineMapAmbient (vertex π)).contLinear.toLinearMap| =
      ((p + 1).factorial : ℝ)⁻¹ := by
  rw [det_contLinear_affineMapAmbient_vertex, abs_div,
    abs_of_pos (Nat.cast_pos (α := ℝ).mpr (Nat.factorial_pos _))]
  have hsign : |(π.sign : ℝ)| = 1 := by
    rcases Int.units_eq_one_or π.sign with h | h <;> simp [h]
  rw [hsign, one_div]

/-- Every barycentric subdivision map on `ℝᵖ` is injective. -/
theorem affineMapAmbient_vertex_injective (π : Perm (Fin (p + 1))) :
    Function.Injective (affineMapAmbient (vertex π)) := by
  have hdet : LinearMap.det (affineMapAmbient (vertex π)).contLinear.toLinearMap ≠ 0 := by
    intro h0
    have habs := abs_det_contLinear_affineMapAmbient_vertex π
    rw [h0, abs_zero] at habs
    exact (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))) habs.symm
  have hunit : IsUnit (affineMapAmbient (vertex π)).contLinear.toLinearMap :=
    (LinearMap.isUnit_iff_isUnit_det _).mpr hdet.isUnit
  obtain ⟨g, hg⟩ := hunit.exists_left_inv
  have hlin : Function.Injective (affineMapAmbient (vertex π)).contLinear :=
    Function.LeftInverse.injective (g := g) fun x ↦ by
      simpa using LinearMap.congr_fun hg x
  intro x y hxy
  have hsub : (affineMapAmbient (vertex π)).contLinear (x - y) = 0 := by
    have hv := (affineMapAmbient (vertex π)).contLinear_apply_vsub x y
    rw [vsub_eq_sub, vsub_eq_sub, hxy, sub_self] at hv
    exact hv
  exact sub_eq_zero.mp (hlin (hsub.trans (map_zero _).symm))

/-- The image of `Δᵖ` under the `π`-th barycentric subdivision map is the order chamber of points
whose barycentric weights are nondecreasing along `π`. -/
theorem mem_image_affineMapAmbient_vertex_iff (π : Perm (Fin (p + 1)))
    {y : EuclideanSpace ℝ (Fin p)} (hy : y ∈ fullSimplex p) :
    y ∈ affineMapAmbient (vertex π) '' fullSimplex p ↔
      Monotone fun i ↦ (fullSimplexEquivStdSimplex p ⟨y, hy⟩).weights (π i) := by
  set wy := fullSimplexEquivStdSimplex p ⟨y, hy⟩
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hwy : wy = StdSimplex.affineMapMk (vertex π) (fullSimplexEquivStdSimplex p ⟨x, hx⟩) := by
      have hcoe := affineMapAmbient_coe (vertex π) ⟨x, hx⟩
      have hsub : (⟨affineMapAmbient (vertex π) x, hy⟩ : fullSimplex p) =
          (fullSimplexEquivStdSimplex p).symm
            (StdSimplex.affineMapMk (vertex π) (fullSimplexEquivStdSimplex p ⟨x, hx⟩)) :=
        Subtype.ext hcoe
      dsimp only [wy]
      rw [hsub, Homeomorph.apply_symm_apply]
    intro j₁ j₂ hj
    have hformula (j : Fin (p + 1)) : wy.weights (π j) =
        ∑ k ∈ Finset.Iic j,
          (fullSimplexEquivStdSimplex p ⟨x, hx⟩).weights k * ((p + 1 - (k : ℕ) : ℝ)⁻¹) := by
      rw [hwy, StdSimplex.affineMapMk_apply, StdSimplex.weights_iConvexComb, Finsupp.sum_apply,
        Finsupp.sum_fintype _ _ (by simp)]
      simp only [Finsupp.smul_apply, smul_eq_mul, weights_vertex_apply, mul_ite, mul_zero,
        ← Finset.sum_filter]
      congr 1
      ext k
      simp
    dsimp only
    rw [hformula j₁, hformula j₂]
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.Iic_subset_Iic.mpr hj) fun k _ _ ↦ ?_
    refine mul_nonneg (StdSimplex.weights_nonneg _) (inv_nonneg.mpr ?_)
    have hk : (k : ℕ) ≤ p + 1 := k.isLt.le
    have : (k : ℝ) ≤ (p : ℝ) + 1 := by exact_mod_cast hk
    linarith
  · intro hmono
    let t : Fin (p + 1) → ℝ := Fin.cases
      ((p + 1 : ℝ) * wy.weights (π 0))
      (fun k ↦ (p + 1 - (k.succ : ℕ) : ℝ) * (wy.weights (π k.succ) - wy.weights (π k.castSucc)))
    have hpos (k : Fin (p + 1)) : (0 : ℝ) < (p + 1 - (k : ℕ) : ℝ) := by
      have hk : (k : ℕ) < p + 1 := k.isLt
      have : (k : ℝ) < (p : ℝ) + 1 := by exact_mod_cast hk
      linarith
    have ht_nonneg : ∀ k, 0 ≤ t k := fun k ↦ by
      cases k using Fin.cases with
      | zero =>
        exact mul_nonneg (by positivity) (StdSimplex.weights_nonneg _)
      | succ k =>
        exact mul_nonneg (hpos k.succ).le (sub_nonneg.mpr (hmono k.castSucc_le_succ))
    have hpart : ∀ j : Fin (p + 1),
        ∑ k ∈ Finset.Iic j, t k * ((p + 1 - (k : ℕ) : ℝ)⁻¹) = wy.weights (π j) := by
      intro j
      induction j using Fin.induction with
      | zero =>
        have hIic : Finset.Iic (0 : Fin (p + 1)) = {0} := by
          ext k
          simp
        rw [hIic, Finset.sum_singleton]
        simp only [t, Fin.cases_zero, Fin.val_zero, Nat.cast_zero, sub_zero]
        field_simp
      | succ k ih =>
        have hIic : Finset.Iic k.succ = insert k.succ (Finset.Iic k.castSucc) := by
          ext m
          simp only [Finset.mem_Iic, Finset.mem_insert, Fin.le_iff_val_le_val, Fin.val_succ,
            Fin.val_castSucc, Fin.ext_iff]
          omega
        have hnotmem : k.succ ∉ Finset.Iic k.castSucc := by
          simp only [Finset.mem_Iic, Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc]
          omega
        rw [hIic, Finset.sum_insert hnotmem, ih]
        simp only [t, Fin.cases_succ]
        have hne : (p + 1 - (k.succ : ℕ) : ℝ) ≠ 0 := (hpos k.succ).ne'
        field_simp [hne]
        ring
    have ht_sum : ∑ k : Fin (p + 1), t k = 1 := by
      have h1 : ∑ j : Fin (p + 1), wy.weights (π j) = 1 := by
        rw [Equiv.sum_comp π (fun i ↦ wy.weights i), StdSimplex.total_of_fintype]
      rw [← h1]
      simp_rw [← hpart]
      have hIic_eq (j : Fin (p + 1)) : Finset.Iic j = Finset.univ.filter (· ≤ j) := by
        ext k; simp
      have hIci_eq (k : Fin (p + 1)) : Finset.Ici k = Finset.univ.filter (k ≤ ·) := by
        ext j; simp
      have hswap :
          (∑ j : Fin (p + 1), ∑ k ∈ Finset.Iic j, t k * ((p + 1 - (k : ℕ) : ℝ)⁻¹)) =
            ∑ k : Fin (p + 1), ∑ _ ∈ Finset.Ici k, t k * ((p + 1 - (k : ℕ) : ℝ)⁻¹) := by
        simp_rw [hIic_eq, hIci_eq, Finset.sum_filter]
        exact Finset.sum_comm
      rw [hswap]
      symm
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [Finset.sum_const, nsmul_eq_mul, Fin.card_Ici, Nat.cast_sub k.isLt.le, Nat.cast_add,
        Nat.cast_one]
      have hne : (p + 1 - (k : ℕ) : ℝ) ≠ 0 := (hpos k).ne'
      field_simp [hne]
    let w : StdSimplex ℝ (Fin (p + 1)) :=
      { weights := Finsupp.equivFunOnFinite.symm t
        nonneg := fun k ↦ ht_nonneg k
        total := by
          rw [Finsupp.sum_fintype _ _ (by simp)]
          exact ht_sum }
    refine ⟨((fullSimplexEquivStdSimplex p).symm w).val, Subtype.prop _, ?_⟩
    rw [affineMapAmbient_coe, Homeomorph.apply_symm_apply]
    have heq : StdSimplex.affineMapMk (vertex π) w = wy := by
      ext m
      obtain ⟨j, rfl⟩ := π.surjective m
      rw [StdSimplex.affineMapMk_apply, StdSimplex.weights_iConvexComb, Finsupp.sum_apply,
        Finsupp.sum_fintype _ _ (by simp)]
      simp only [Finsupp.smul_apply, smul_eq_mul, weights_vertex_apply, mul_ite, mul_zero,
        ← Finset.sum_filter]
      have hfilt : Finset.univ.filter (fun k : Fin (p + 1) ↦ k ≤ j) = Finset.Iic j := by
        ext k; simp
      rw [hfilt]
      exact hpart j
    rw [heq]
    exact congrArg Subtype.val ((fullSimplexEquivStdSimplex p).symm_apply_apply ⟨y, hy⟩)

/-- The images of `Δᵖ` under the `(p + 1)!` barycentric subdivision maps cover `Δᵖ`. -/
theorem iUnion_image_affineMapAmbient_vertex (p : ℕ) :
    (⋃ π : Perm (Fin (p + 1)), affineMapAmbient (vertex π) '' fullSimplex p) = fullSimplex p := by
  refine Subset.antisymm (iUnion_subset fun π ↦ (mapsTo_affineMapAmbient _).image_subset) ?_
  intro y hy
  let f : Fin (p + 1) → ℝ := fun i ↦ (fullSimplexEquivStdSimplex p ⟨y, hy⟩).weights i
  refine mem_iUnion.mpr ⟨Tuple.sort f, ?_⟩
  rw [mem_image_affineMapAmbient_vertex_iff (Tuple.sort f) hy]
  exact Tuple.monotone_sort f

/-- Distinct barycentric subdivision chambers of `Δᵖ` overlap in a set of Lebesgue measure zero. -/
theorem volume_image_affineMapAmbient_vertex_inter_eq_zero {π₁ π₂ : Perm (Fin (p + 1))}
    (hne : π₁ ≠ π₂) :
    volume ((affineMapAmbient (vertex π₁) '' fullSimplex p) ∩
      (affineMapAmbient (vertex π₂) '' fullSimplex p)) = 0 := by
  have hnotmono : ¬ Monotone (π₁.symm * π₂) := by
    intro hmono
    set τ : Perm (Fin (p + 1)) := π₁.symm * π₂
    have hstrict : StrictMono τ := hmono.strictMono_of_injective τ.injective
    have hstrict_symm : StrictMono τ.symm := fun a b hab ↦ by
      by_contra hle
      have h := hmono (not_lt.mp hle)
      rw [τ.apply_symm_apply, τ.apply_symm_apply] at h
      exact hab.not_ge h
    have heq : τ = 1 := by
      ext i
      have h1 : τ i ≤ τ (τ.symm i) := hmono (hstrict_symm.id_le i)
      rw [τ.apply_symm_apply] at h1
      exact le_antisymm h1 (hstrict.id_le i)
    exact hne (inv_mul_eq_one.mp heq)
  simp only [Monotone, not_forall, not_le] at hnotmono
  obtain ⟨j₁, j₂, hj, hlt⟩ := hnotmono
  let a : Fin (p + 1) := π₂ j₁
  let b : Fin (p + 1) := π₂ j₂
  have hab : a ≠ b := by
    intro h
    have := π₂.injective h
    exact (lt_irrefl _ (this ▸ hlt))
  let W : Fin (p + 1) → EuclideanSpace ℝ (Fin p) →ᵃ[ℝ] ℝ :=
    Fin.cases
      (AffineMap.const ℝ _ 1 -
        (∑ k : Fin p,
          (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ).toLinearMap).toAffineMap)
      (fun k ↦ (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ).toLinearMap.toAffineMap)
  have hW_coe (k : Fin (p + 1)) (y : fullSimplex p) :
      W k y.val = (fullSimplexEquivStdSimplex p y).weights k := by
    cases k using Fin.cases with
    | zero => simp [W]
    | succ k => simp [W]
  let S : AffineSubspace ℝ (EuclideanSpace ℝ (Fin p)) :=
    { carrier := {x | W a x = W b x}
      smul_vsub_vadd_mem' := fun c x₁ x₂ x₃ hx₁ hx₂ hx₃ ↦ by
        -- Membership in `S` is equality of the affine functionals `W a` and `W b`.
        change W a x₁ = W b x₁ at hx₁
        change W a x₂ = W b x₂ at hx₂
        change W a x₃ = W b x₃ at hx₃
        change W a (c • (x₁ -ᵥ x₂) +ᵥ x₃) = W b (c • (x₁ -ᵥ x₂) +ᵥ x₃)
        simp only [AffineMap.map_vadd, LinearMap.map_smul, AffineMap.linear_apply_vsub,
          hx₁, hx₂, hx₃] }
  have hS_ne_top : S ≠ ⊤ := by
    intro htop
    let x₀ : fullSimplex p := (fullSimplexEquivStdSimplex p).symm (StdSimplex.single a)
    have hx₀ : x₀.val ∈ S := htop.symm ▸ trivial
    -- Membership of `x₀` in `S` is `W a x₀ = W b x₀`.
    change W a x₀.val = W b x₀.val at hx₀
    rw [hW_coe, hW_coe, Homeomorph.apply_symm_apply] at hx₀
    simp [hab] at hx₀
  have hsub : (affineMapAmbient (vertex π₁) '' fullSimplex p) ∩
      (affineMapAmbient (vertex π₂) '' fullSimplex p) ⊆ (S : Set (EuclideanSpace ℝ (Fin p))) := by
    rintro y ⟨hy₁, hy₂⟩
    have hy : y ∈ fullSimplex p := (mapsTo_affineMapAmbient _).image_subset hy₁
    have hm₁ := (mem_image_affineMapAmbient_vertex_iff π₁ hy).mp hy₁
    have hm₂ := (mem_image_affineMapAmbient_vertex_iff π₂ hy).mp hy₂
    have hle₁ : (fullSimplexEquivStdSimplex p ⟨y, hy⟩).weights a ≤
        (fullSimplexEquivStdSimplex p ⟨y, hy⟩).weights b := hm₂ hj
    have hle₂ : (fullSimplexEquivStdSimplex p ⟨y, hy⟩).weights b ≤
        (fullSimplexEquivStdSimplex p ⟨y, hy⟩).weights a := by
      have h := hm₁ hlt.le
      simpa [a, b] using h
    -- Membership of `y` in `S` is `W a y = W b y`.
    change W a y = W b y
    rw [hW_coe a ⟨y, hy⟩, hW_coe b ⟨y, hy⟩]
    exact le_antisymm hle₁ hle₂
  exact measure_mono_null hsub (Measure.addHaar_affineSubspace volume S hS_ne_top)

/-- Change of variables on a single barycentric subdivision chamber of `Δᵖ`. -/
theorem setIntegral_comp_affineMapAmbient_vertex {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (π : Perm (Fin (p + 1))) (f : EuclideanSpace ℝ (Fin p) → F) :
    ∫ x in fullSimplex p,
        |LinearMap.det (affineMapAmbient (vertex π)).contLinear.toLinearMap| •
          f (affineMapAmbient (vertex π) x) =
      ∫ y in affineMapAmbient (vertex π) '' fullSimplex p, f y := by
  symm
  exact MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul volume
    (isClosed_fullSimplex p).measurableSet
    (fun x _ ↦ (affineMapAmbient (vertex π)).hasFDerivAt.hasFDerivWithinAt)
    (affineMapAmbient_vertex_injective π).injOn f

/-- **Unsigned subdivision decomposition of Bochner integrals on `Δᵖ`.** For any integrable function
`f` on `Δᵖ`, summing its pulled-back integrals over the `(p + 1)!` barycentric subdivision chambers
with their Jacobian factors `|det|` recovers the integral of `f` over `Δᵖ`. -/
theorem sum_setIntegral_affineMapAmbient_vertex {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : EuclideanSpace ℝ (Fin p) → F}
    (hf : IntegrableOn f (fullSimplex p)) :
    ∑ π : Perm (Fin (p + 1)),
        ∫ x in fullSimplex p,
          |LinearMap.det (affineMapAmbient (vertex π)).contLinear.toLinearMap| •
            f (affineMapAmbient (vertex π) x) =
      ∫ y in fullSimplex p, f y := by
  simp_rw [setIntegral_comp_affineMapAmbient_vertex]
  let s (π : Perm (Fin (p + 1))) : Set (EuclideanSpace ℝ (Fin p)) :=
    affineMapAmbient (vertex π) '' fullSimplex p
  have hmeas (π : Perm (Fin (p + 1))) : MeasurableSet (s π) :=
    ((isCompact_fullSimplex p).image
      (affineMapAmbient (vertex π)).continuous).isClosed.measurableSet
  have hint (π : Perm (Fin (p + 1))) : IntegrableOn f (s π) :=
    hf.mono_set (mapsTo_affineMapAmbient _).image_subset
  have hfin : ∀ t : Finset (Perm (Fin (p + 1))),
      ∫ y in ⋃ π ∈ t, s π, f y = ∑ π ∈ t, ∫ y in s π, f y := by
    intro t
    classical
    induction t using Finset.induction_on with
    | empty => simp
    | insert π t hπ ih =>
      rw [Finset.set_biUnion_insert, Finset.sum_insert hπ, ← ih]
      refine setIntegral_union₀ ?_
        (Finset.measurableSet_biUnion t fun τ _ ↦ hmeas τ).nullMeasurableSet
        (hint π) (integrableOn_finset_iUnion.mpr fun τ _ ↦ hint τ)
      rw [AEDisjoint, Set.inter_iUnion₂]
      refine (measure_biUnion_null_iff (Finset.countable_toSet t)).mpr fun τ hτ ↦ ?_
      exact volume_image_affineMapAmbient_vertex_inter_eq_zero (fun h ↦ hπ (h ▸ hτ))
  rw [← hfin Finset.univ,
    show (⋃ π ∈ (Finset.univ : Finset (Perm (Fin (p + 1)))), s π) = fullSimplex p by
      simpa [s] using iUnion_image_affineMapAmbient_vertex p]

/-- **Signed subdivision decomposition of Bochner integrals on `Δᵖ`.** Weighting each barycentric
subdivision chamber by `π.sign` and its signed linear determinant `det` gives the same
decomposition as the unsigned formula, because `π.sign * det = |det|`. -/
theorem sum_sign_setIntegral_affineMapAmbient_vertex {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : EuclideanSpace ℝ (Fin p) → F}
    (hf : IntegrableOn f (fullSimplex p)) :
    ∑ π : Perm (Fin (p + 1)),
        π.sign • ∫ x in fullSimplex p,
          LinearMap.det (affineMapAmbient (vertex π)).contLinear.toLinearMap •
            f (affineMapAmbient (vertex π) x) =
      ∫ y in fullSimplex p, f y := by
  rw [← sum_setIntegral_affineMapAmbient_vertex hf]
  refine Finset.sum_congr rfl fun π _ ↦ ?_
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul ℝ, ← integral_smul]
  refine setIntegral_congr_fun (isClosed_fullSimplex p).measurableSet fun x _ ↦ ?_
  rw [smul_smul, abs_det_contLinear_affineMapAmbient_vertex,
    det_contLinear_affineMapAmbient_vertex]
  have hsq : (π.sign : ℝ) * ((π.sign : ℝ) / ((p + 1).factorial : ℝ)) =
      ((p + 1).factorial : ℝ)⁻¹ := by
    rcases Int.units_eq_one_or π.sign with h | h <;> simp [h, div_eq_mul_inv]
  rw [hsq]

end BarycentricSubdivision

end TauCeti
