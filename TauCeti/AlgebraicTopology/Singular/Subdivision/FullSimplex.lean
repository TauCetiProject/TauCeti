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

For each `π : Equiv.Perm (Fin (p + 1))`, the `π`-th barycentric subdivision simplex of `Δᵖ ⊆ ℝᵖ` is
parametrized by `affineMapAmbient (BarycentricSubdivision.vertex π) : ℝᵖ →ᴬ[ℝ] ℝᵖ`. We compute its
weights, determinant `π.sign / (p + 1)!`, injectivity, order-chamber image characterization,
full covering of `Δᵖ`, measure-zero pairwise overlaps, and unsigned/signed Bochner integral
decompositions (`sum_setIntegral_affineMapAmbient_vertex`,
`sum_sign_setIntegral_affineMapAmbient_vertex`).

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

private theorem sub_cast_pos (k : Fin (p + 1)) : (0 : ℝ) < (p + 1 - (k : ℕ) : ℝ) := by
  have : (k : ℝ) < (p : ℝ) + 1 := by exact_mod_cast k.isLt
  linarith

/-- The `k`-th vertex of the `π`-th subdivision simplex is the image under `π` of the `k`-th vertex
of the identity subdivision simplex. -/
theorem vertex_eq_map_one (π : Perm (Fin (p + 1))) (k : Fin (p + 1)) :
    vertex π k = (vertex 1 k).map π := by
  rw [vertex_def, vertex_def, ← Equiv.coe_toEmbedding, StdSimplex.map_subBarycenter]
  congr 1; rw [Finset.map_map]; congr 1

/-- The barycentric weight of `vertex π k` at vertex `π j` is `(p + 1 - k)⁻¹` when `k ≤ j` and `0`
otherwise. -/
theorem weights_vertex_apply (π : Perm (Fin (p + 1))) (k j : Fin (p + 1)) :
    (vertex π k).weights (π j) = if k ≤ j then ((p + 1 - (k : ℕ) : ℝ)⁻¹) else 0 := by
  rw [vertex_def, StdSimplex.weights_subBarycenter]
  have hcard : (((Finset.Ici k).map π.toEmbedding).card : ℝ) = (p + 1 - (k : ℕ) : ℝ) := by
    rw [Finset.card_map, Fin.card_Ici, Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
  rw [hcard]; by_cases h : k ≤ j <;> simp [h, Finsupp.single_apply, Finset.sum_ite_eq']

private theorem weights_affineMapMk_vertex (π : Perm (Fin (p + 1)))
    (w : StdSimplex ℝ (Fin (p + 1))) (j : Fin (p + 1)) :
    (StdSimplex.affineMapMk (vertex π) w).weights (π j) =
      ∑ k ∈ Finset.Iic j, w.weights k * (p + 1 - (k : ℕ) : ℝ)⁻¹ := by
  rw [StdSimplex.affineMapMk_apply, StdSimplex.weights_iConvexComb, Finsupp.sum_apply,
    Finsupp.sum_fintype _ _ (by simp)]
  simp only [Finsupp.smul_apply, smul_eq_mul, weights_vertex_apply, mul_ite, mul_zero,
    ← Finset.sum_filter]
  congr 1; ext k; simp

/-- Distinct permutations determine distinct barycentric subdivision vertex tuples. -/
theorem vertex_injective : Function.Injective (vertex (n := p)) := fun π₁ π₂ h ↦
  Equiv.symm_bijective.injective <| Equiv.ext fun m ↦ by
    have hset (π : Perm (Fin (p + 1))) :
        Finset.univ.filter (fun k : Fin (p + 1) ↦ (vertex π k).weights m ≠ 0) =
          Finset.Iic (π.symm m) := by
      ext k
      have hw := weights_vertex_apply π k (π.symm m); rw [Equiv.apply_symm_apply] at hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic, hw]
      split_ifs with hk
      · exact ⟨fun _ ↦ hk, fun _ ↦ inv_ne_zero (sub_cast_pos k).ne'⟩
      · exact ⟨fun h0 ↦ (h0 rfl).elim, fun hk' ↦ (hk hk').elim⟩
    have hcard : (Finset.Iic (π₁.symm m)).card = (Finset.Iic (π₂.symm m)).card := by
      rw [← hset π₁, ← hset π₂, h]
    exact Fin.ext (by simpa [Fin.card_Iic] using hcard)

/-- The ambient affine map of the `π`-th barycentric subdivision simplex is the vertex permutation
`simplexMapAmbient π` composed with the identity chamber map. -/
theorem affineMapAmbient_vertex_eq_comp (π : Perm (Fin (p + 1))) :
    affineMapAmbient (vertex π) = (simplexMapAmbient π).comp (affineMapAmbient (vertex 1)) :=
  continuousAffineMap_eq_of_eqOn_fullSimplex fun x hx ↦ by
    rw [ContinuousAffineMap.comp_apply, affineMapAmbient_coe _ ⟨x, hx⟩,
      affineMapAmbient_coe _ ⟨x, hx⟩, simplexMapAmbient_coe, Homeomorph.apply_symm_apply]
    congr 2; ext m; obtain ⟨j, rfl⟩ := π.surjective m
    rw [StdSimplex.weights_map, Finsupp.mapDomain_apply_of_injective π.injective,
      weights_affineMapMk_vertex]
    simpa using (weights_affineMapMk_vertex (1 : Perm (Fin (p + 1))) _ j).symm

/-- The linear part of the identity barycentric subdivision map has determinant `((p + 1)!)⁻¹`. -/
theorem det_contLinear_affineMapAmbient_vertex_one (p : ℕ) :
    LinearMap.det (affineMapAmbient (vertex (n := p) 1)).contLinear.toLinearMap =
      ((p + 1).factorial : ℝ)⁻¹ := by
  rw [det_contLinear_affineMapAmbient]
  set M : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ := Matrix.of fun j i ↦ (vertex 1 i).weights j
  have hlower : M.IsLowerTriangular := fun j k hjk ↦ by
    have hlt : j < k := hjk
    simpa [M, not_le.mpr hlt] using weights_vertex_apply (1 : Perm (Fin (p + 1))) k j
  rw [Matrix.det_of_isLowerTriangular M hlower]
  have hdiag (k : Fin (p + 1)) : M k k = ((p + 1 - (k : ℕ) : ℝ)⁻¹) := by
    simpa [M] using weights_vertex_apply (1 : Perm (Fin (p + 1))) k k
  simp_rw [hdiag]; rw [← Equiv.prod_comp (Fin.revPerm : Perm (Fin (p + 1)))]
  have hrev (k : Fin (p + 1)) : ((p + 1 - ((Fin.revPerm k : Fin (p + 1)) : ℕ) : ℝ)⁻¹) =
      (((k : ℕ) + 1 : ℕ) : ℝ)⁻¹ := by
    congr 1; simp only [Fin.revPerm_apply, Fin.val_rev]
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  simp_rw [hrev, Finset.prod_inv_distrib]; congr 1
  rw [Fin.prod_univ_eq_prod_range (fun k ↦ ((k + 1 : ℕ) : ℝ))]
  exact_mod_cast Finset.prod_range_add_one_eq_factorial (p + 1)

/-- The linear part of the `π`-th barycentric subdivision map has determinant
`π.sign / (p + 1)!`. -/
theorem det_contLinear_affineMapAmbient_vertex (π : Perm (Fin (p + 1))) :
    LinearMap.det (affineMapAmbient (vertex π)).contLinear.toLinearMap =
      (π.sign : ℝ) / ((p + 1).factorial : ℝ) := by
  rw [affineMapAmbient_vertex_eq_comp, ContinuousAffineMap.comp_contLinear]
  exact (LinearMap.det_comp _ _).trans <| by
    rw [det_contLinear_simplexMapAmbient_perm, det_contLinear_affineMapAmbient_vertex_one,
      div_eq_mul_inv]

/-- The absolute determinant of every barycentric subdivision map on `Δᵖ` is `((p + 1)!)⁻¹`. -/
theorem abs_det_contLinear_affineMapAmbient_vertex (π : Perm (Fin (p + 1))) :
    |LinearMap.det (affineMapAmbient (vertex π)).contLinear.toLinearMap| =
      ((p + 1).factorial : ℝ)⁻¹ := by
  rw [det_contLinear_affineMapAmbient_vertex, abs_div,
    abs_of_pos (Nat.cast_pos (α := ℝ).mpr (Nat.factorial_pos _))]
  rcases Int.units_eq_one_or π.sign with h | h <;> simp [h, one_div]

/-- Every barycentric subdivision map on `ℝᵖ` is injective. -/
theorem affineMapAmbient_vertex_injective (π : Perm (Fin (p + 1))) :
    Function.Injective (affineMapAmbient (vertex π)) := by
  have hdet : LinearMap.det (affineMapAmbient (vertex π)).contLinear.toLinearMap ≠ 0 := by
    rw [det_contLinear_affineMapAmbient_vertex]
    exact div_ne_zero (by rcases Int.units_eq_one_or π.sign with h | h <;> simp [h])
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  exact (AffineMap.linear_injective_iff (affineMapAmbient (vertex π)).toAffineMap).mp
    (LinearMap.equivOfDetNeZero _ hdet).injective

private def chamberInvWeights (π : Perm (Fin (p + 1))) (wy : StdSimplex ℝ (Fin (p + 1))) :
    Fin (p + 1) → ℝ :=
  Fin.cases ((p + 1 : ℝ) * wy.weights (π 0)) fun k ↦
    (p + 1 - (k.succ : ℕ) : ℝ) * (wy.weights (π k.succ) - wy.weights (π k.castSucc))

private theorem chamberInvWeights_nonneg {π : Perm (Fin (p + 1))}
    {wy : StdSimplex ℝ (Fin (p + 1))} (hmono : Monotone fun i ↦ wy.weights (π i))
    (k : Fin (p + 1)) :
    0 ≤ chamberInvWeights π wy k := by
  cases k using Fin.cases with
  | zero => exact mul_nonneg (by positivity) (StdSimplex.weights_nonneg _)
  | succ k =>
    exact mul_nonneg (sub_cast_pos k.succ).le (sub_nonneg.mpr (hmono k.castSucc_le_succ))

private theorem sum_Iic_chamberInvWeights_mul_inv (π : Perm (Fin (p + 1)))
    (wy : StdSimplex ℝ (Fin (p + 1))) (j : Fin (p + 1)) :
    ∑ k ∈ Finset.Iic j, chamberInvWeights π wy k * (p + 1 - (k : ℕ) : ℝ)⁻¹ =
      wy.weights (π j) := by
  induction j using Fin.induction with
  | zero =>
    have hIic : Finset.Iic (0 : Fin (p + 1)) = {0} := by ext; simp
    rw [hIic, Finset.sum_singleton]
    simp only [chamberInvWeights, Fin.cases_zero, Fin.val_zero, Nat.cast_zero, sub_zero]
    field_simp
  | succ k ih =>
    have hIic : Finset.Iic k.succ = insert k.succ (Finset.Iic k.castSucc) := by
      ext m; simp [Fin.le_iff_val_le_val, Fin.ext_iff]; omega
    rw [hIic, Finset.sum_insert (by simp [Fin.le_iff_val_le_val]), ih]
    simp only [chamberInvWeights, Fin.cases_succ]
    rw [mul_right_comm, mul_inv_cancel₀ (sub_cast_pos k.succ).ne', one_mul, sub_add_cancel]

private theorem sum_chamberInvWeights_eq_one (π : Perm (Fin (p + 1)))
    (wy : StdSimplex ℝ (Fin (p + 1))) :
    ∑ k : Fin (p + 1), chamberInvWeights π wy k = 1 := by
  have hsum : ∑ j : Fin (p + 1), wy.weights (π j) = 1 := by
    rw [Equiv.sum_comp π (fun i ↦ wy.weights i), StdSimplex.total_of_fintype]
  rw [← hsum]
  simp_rw [← sum_Iic_chamberInvWeights_mul_inv π wy]
  have hswap : (∑ j : Fin (p + 1),
        ∑ k ∈ Finset.Iic j, chamberInvWeights π wy k * (p + 1 - (k : ℕ) : ℝ)⁻¹) =
      ∑ k : Fin (p + 1),
        ∑ _ ∈ Finset.Ici k, chamberInvWeights π wy k * (p + 1 - (k : ℕ) : ℝ)⁻¹ := by
    have hIic (j : Fin (p + 1)) : Finset.Iic j = Finset.univ.filter (· ≤ j) := by ext; simp
    have hIci (k : Fin (p + 1)) : Finset.Ici k = Finset.univ.filter (k ≤ ·) := by ext; simp
    simp_rw [hIic, hIci, Finset.sum_filter]
    exact Finset.sum_comm
  rw [hswap]; symm; refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Finset.sum_const, nsmul_eq_mul, Fin.card_Ici, Nat.cast_sub k.isLt.le, Nat.cast_add,
    Nat.cast_one, mul_left_comm, mul_inv_cancel₀ (sub_cast_pos k).ne', mul_one]

/-- The image of `Δᵖ` under the `π`-th barycentric subdivision map is the order chamber of points
whose barycentric weights are nondecreasing along `π`. -/
theorem mem_image_affineMapAmbient_vertex_iff (π : Perm (Fin (p + 1)))
    {y : EuclideanSpace ℝ (Fin p)} (hy : y ∈ fullSimplex p) :
    y ∈ affineMapAmbient (vertex π) '' fullSimplex p ↔
      Monotone fun i ↦ (fullSimplexEquivStdSimplex p ⟨y, hy⟩).weights (π i) := by
  set wy := fullSimplexEquivStdSimplex p ⟨y, hy⟩
  constructor
  · rintro ⟨x, hx, rfl⟩ j₁ j₂ hj
    have hwy : wy = StdSimplex.affineMapMk (vertex π) (fullSimplexEquivStdSimplex p ⟨x, hx⟩) := by
      simpa [wy] using congrArg (fullSimplexEquivStdSimplex p)
        (Subtype.ext (affineMapAmbient_coe (vertex π) ⟨x, hx⟩) :
          (⟨affineMapAmbient (vertex π) x, hy⟩ : fullSimplex p) = _)
    dsimp only; rw [hwy, weights_affineMapMk_vertex, weights_affineMapMk_vertex]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Iic_subset_Iic.mpr hj) fun k _ _ ↦
      mul_nonneg (StdSimplex.weights_nonneg _) (inv_nonneg.mpr (sub_cast_pos k).le)
  · intro hmono
    let w : StdSimplex ℝ (Fin (p + 1)) :=
      ⟨Finsupp.equivFunOnFinite.symm (chamberInvWeights π wy), chamberInvWeights_nonneg hmono,
        by rw [Finsupp.sum_fintype _ _ (by simp)]; exact sum_chamberInvWeights_eq_one π wy⟩
    have hw : StdSimplex.affineMapMk (vertex π) w = wy := by
      ext m; obtain ⟨j, rfl⟩ := π.surjective m
      rw [weights_affineMapMk_vertex]; exact sum_Iic_chamberInvWeights_mul_inv π wy j
    refine ⟨((fullSimplexEquivStdSimplex p).symm w).val, Subtype.prop _, ?_⟩
    rw [affineMapAmbient_coe, Homeomorph.apply_symm_apply, hw]
    exact congrArg Subtype.val ((fullSimplexEquivStdSimplex p).symm_apply_apply ⟨y, hy⟩)

/-- The images of `Δᵖ` under the `(p + 1)!` barycentric subdivision maps cover `Δᵖ`. -/
theorem iUnion_image_affineMapAmbient_vertex (p : ℕ) :
    (⋃ π : Perm (Fin (p + 1)), affineMapAmbient (vertex π) '' fullSimplex p) = fullSimplex p := by
  refine Subset.antisymm (iUnion_subset fun π ↦ (mapsTo_affineMapAmbient _).image_subset) fun y hy ↦
    mem_iUnion.mpr ⟨Tuple.sort fun i ↦ (fullSimplexEquivStdSimplex p ⟨y, hy⟩).weights i, ?_⟩
  rw [mem_image_affineMapAmbient_vertex_iff _ hy]
  exact Tuple.monotone_sort _

private theorem perm_eq_one_of_monotone {α : Type*} [LinearOrder α] [Finite α] {τ : Perm α}
    (h : Monotone τ) : τ = 1 :=
  Equiv.ext fun _ ↦ (h.strictMono_of_injective τ.injective).apply_eq

/-- Distinct barycentric subdivision chambers of `Δᵖ` overlap in a set of Lebesgue measure zero. -/
theorem volume_image_affineMapAmbient_vertex_inter_eq_zero {π₁ π₂ : Perm (Fin (p + 1))}
    (hne : π₁ ≠ π₂) :
    volume ((affineMapAmbient (vertex π₁) '' fullSimplex p) ∩
      (affineMapAmbient (vertex π₂) '' fullSimplex p)) = 0 := by
  have hnotmono : ¬ Monotone (π₁.symm * π₂) := fun hmono ↦
    hne (inv_mul_eq_one.mp (perm_eq_one_of_monotone hmono))
  simp only [Monotone, not_forall, not_le] at hnotmono
  obtain ⟨j₁, j₂, hj, hlt⟩ := hnotmono
  let a := π₂ j₁; let b := π₂ j₂
  have hab : a ≠ b := fun h ↦ lt_irrefl _ (π₂.injective h ▸ hlt)
  let W : Fin (p + 1) → EuclideanSpace ℝ (Fin p) →ᵃ[ℝ] ℝ :=
    Fin.cases (AffineMap.const ℝ _ 1 -
      (∑ k : Fin p, (EuclideanSpace.proj (𝕜 := ℝ) k).toLinearMap).toAffineMap)
      fun k ↦ (EuclideanSpace.proj (𝕜 := ℝ) k).toLinearMap.toAffineMap
  have hW_coe (k : Fin (p + 1)) (y : fullSimplex p) :
      W k y.val = (fullSimplexEquivStdSimplex p y).weights k := by
    cases k using Fin.cases <;> simp [W]
  let S : AffineSubspace ℝ (EuclideanSpace ℝ (Fin p)) :=
    { carrier := {x | W a x = W b x}
      smul_vsub_vadd_mem' := fun c x₁ x₂ x₃ hx₁ hx₂ hx₃ ↦ by
        simp only [mem_ofPred_eq] at hx₁ hx₂ hx₃ ⊢
        simp only [AffineMap.map_vadd, LinearMap.map_smul, AffineMap.linear_apply_vsub,
          hx₁, hx₂, hx₃] }
  have hS_ne_top : S ≠ ⊤ := fun htop ↦ by
    let x₀ : fullSimplex p := (fullSimplexEquivStdSimplex p).symm (StdSimplex.single a)
    have hx₀ : x₀.val ∈ S := htop.symm ▸ trivial
    have hW : W a x₀.val = W b x₀.val := hx₀
    rw [hW_coe, hW_coe, Homeomorph.apply_symm_apply] at hW; simp [hab] at hW
  refine measure_mono_null ?_ (Measure.addHaar_affineSubspace volume S hS_ne_top)
  rintro y ⟨hy₁, hy₂⟩
  have hy : y ∈ fullSimplex p := (mapsTo_affineMapAmbient _).image_subset hy₁
  have hm₁ := (mem_image_affineMapAmbient_vertex_iff π₁ hy).mp hy₁
  have hm₂ := (mem_image_affineMapAmbient_vertex_iff π₂ hy).mp hy₂
  have heq : W a y = W b y := by
    rw [hW_coe a ⟨y, hy⟩, hW_coe b ⟨y, hy⟩]
    exact le_antisymm (hm₂ hj) (by simpa [a, b] using hm₁ hlt.le)
  exact heq

section Integral

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Change of variables on a single barycentric subdivision chamber of `Δᵖ`. -/
theorem setIntegral_comp_affineMapAmbient_vertex (π : Perm (Fin (p + 1)))
    (f : EuclideanSpace ℝ (Fin p) → F) :
    ∫ x in fullSimplex p,
        |LinearMap.det (affineMapAmbient (vertex π)).contLinear.toLinearMap| •
          f (affineMapAmbient (vertex π) x) =
      ∫ y in affineMapAmbient (vertex π) '' fullSimplex p, f y :=
  (MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul volume
    (isClosed_fullSimplex p).measurableSet
    (fun _ _ ↦ (affineMapAmbient (vertex π)).hasFDerivAt.hasFDerivWithinAt)
    (affineMapAmbient_vertex_injective π).injOn f).symm

/-- **Unsigned subdivision decomposition of Bochner integrals on `Δᵖ`.** For any integrable function
`f` on `Δᵖ`, summing its pulled-back integrals over the `(p + 1)!` barycentric subdivision chambers
with their Jacobian factors `|det|` recovers the integral of `f` over `Δᵖ`. -/
theorem sum_setIntegral_affineMapAmbient_vertex {f : EuclideanSpace ℝ (Fin p) → F}
    (hf : IntegrableOn f (fullSimplex p)) :
    ∑ π : Perm (Fin (p + 1)),
        ∫ x in fullSimplex p,
          |LinearMap.det (affineMapAmbient (vertex π)).contLinear.toLinearMap| •
            f (affineMapAmbient (vertex π) x) =
      ∫ y in fullSimplex p, f y := by
  simp_rw [setIntegral_comp_affineMapAmbient_vertex]
  let s (π : Perm (Fin (p + 1))) := affineMapAmbient (vertex π) '' fullSimplex p
  have hU : (⋃ π, s π) = fullSimplex p := iUnion_image_affineMapAmbient_vertex p
  conv_rhs => rw [← hU]
  rw [MeasureTheory.integral_iUnion_ae
    (fun π ↦ ((isCompact_fullSimplex p).image
      (affineMapAmbient (vertex π)).continuous).isClosed.measurableSet.nullMeasurableSet)
    (fun _ _ hne ↦ volume_image_affineMapAmbient_vertex_inter_eq_zero hne)
    (hU.symm ▸ hf), tsum_fintype]

/-- **Signed subdivision decomposition of Bochner integrals on `Δᵖ`.** Weighting each barycentric
subdivision chamber by `π.sign` and its signed linear determinant `det` gives the same
decomposition as the unsigned formula, because `π.sign * det = |det|`. -/
theorem sum_sign_setIntegral_affineMapAmbient_vertex {f : EuclideanSpace ℝ (Fin p) → F}
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
  rw [smul_smul, abs_det_contLinear_affineMapAmbient_vertex, det_contLinear_affineMapAmbient_vertex]
  rcases Int.units_eq_one_or π.sign with h | h <;> simp [h, div_eq_mul_inv]

end Integral

end BarycentricSubdivision

end TauCeti
