/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

/-!
# Reindexing restricted products

An equivalence of index types reindexes a restricted product by precomposition.  The two
orientations below give the coordinate equations needed to transport maps and decompositions.

The algebraic equivalence follows the construction in FLT,
`FLT/Mathlib/Topology/Algebra/RestrictedProduct/Equiv.lean`, at commit
`a9efe585de92be60be84ac1d14ced5a1b0944333` (Apache 2.0), specialized to the cofinite filter.
The continuity proofs use Mathlib's `RestrictedProduct.mapAlong_continuous`.
-/

public section

namespace TauCeti

open Filter
open scoped RestrictedProduct

universe u v

variable {ι ι' : Type u} {G : ι → Type v} {U : ∀ i, Set (G i)}

/-- Reindex a restricted product along an equivalence, in the orientation from `ι'` to `ι`.
At the index `e i`, the output has the same coordinate as the input at `i`. -/
def restrictedProductCongrLeft (e : ι' ≃ ι) :
    (Πʳ i, [G (e i), U (e i)]) ≃ (Πʳ i, [G i, U i]) where
  toFun x := ⟨e.piCongrLeft G x, by
    have hx : ∀ᶠ i in cofinite, x i ∈ U (e i) := x.2
    have hx' := e.symm.injective.tendsto_cofinite hx
    filter_upwards [hx'] with i hi
    have hi : x (e.symm i) ∈ U (e (e.symm i)) := by
      simpa only [Set.mem_preimage, Set.mem_ofPred_eq] using hi
    rw [← e.apply_symm_apply i, Equiv.piCongrLeft_apply_apply]
    exact hi⟩
  invFun x := ⟨(e.piCongrLeft G).symm x, by
    have hx : ∀ᶠ i in cofinite, x i ∈ U i := x.2
    have hx' := e.injective.tendsto_cofinite hx
    filter_upwards [hx'] with i hi
    have hi : x (e i) ∈ U (e i) := by
      simpa only [Set.mem_preimage, Set.mem_ofPred_eq] using hi
    simpa only [Equiv.piCongrLeft_symm_apply] using hi⟩
  left_inv x := by
    apply RestrictedProduct.ext
    intro i
    exact congrFun ((e.piCongrLeft G).left_inv x) i
  right_inv x := by
    apply RestrictedProduct.ext
    intro i
    exact congrFun ((e.piCongrLeft G).right_inv x) i

/-- The reindexing equivalence preserves coordinates when evaluated at `e i`. -/
@[simp]
theorem restrictedProductCongrLeft_apply_apply (e : ι' ≃ ι)
    (x : Πʳ i, [G (e i), U (e i)]) (i : ι') :
    restrictedProductCongrLeft e x (e i) = x i := by
  -- Unfolding the restricted-product equivalence exposes the underlying dependent Pi reindexing.
  change (e.piCongrLeft G x) (e i) = x i
  exact Equiv.piCongrLeft_apply_apply G e x i

/-- The inverse reindexing equivalence evaluates at the corresponding original index. -/
@[simp]
theorem restrictedProductCongrLeft_symm_apply (e : ι' ≃ ι)
    (x : Πʳ i, [G i, U i]) (i : ι') :
    (restrictedProductCongrLeft e).symm x i = x (e i) := by
  -- As above, the subtype equivalence uses the inverse Pi reindexing pointwise.
  change ((e.piCongrLeft G).symm x) i = x (e i)
  exact Equiv.piCongrLeft_symm_apply G e x i

/-- Reindex in the consumer orientation: `x` is sent to the function `i ↦ x (e i)`. -/
def restrictedProductReindex (e : ι' ≃ ι) :
    (Πʳ i, [G i, U i]) ≃ (Πʳ i, [G (e i), U (e i)]) :=
  (restrictedProductCongrLeft e).symm

/-- Evaluation of `restrictedProductReindex` at a new index. -/
@[simp]
theorem restrictedProductReindex_apply (e : ι' ≃ ι)
    (x : Πʳ i, [G i, U i]) (i : ι') :
    restrictedProductReindex e x i = x (e i) := by
  simp [restrictedProductReindex]

/-- Evaluation of the inverse of `restrictedProductReindex` at an original index. -/
@[simp]
theorem restrictedProductReindex_symm_apply (e : ι' ≃ ι)
    (x : Πʳ i, [G (e i), U (e i)]) (i : ι') :
    (restrictedProductReindex e).symm x (e i) = x i := by
  simp [restrictedProductReindex]

variable [∀ i, TopologicalSpace (G i)]

/-- Reindexing a restricted product is continuous. -/
theorem continuous_restrictedProductCongrLeft (e : ι' ≃ ι) :
    Continuous (@restrictedProductCongrLeft ι ι' G U e) := by
  rw [RestrictedProduct.continuous_dom]
  intro S hS
  let T : Set ι := e '' S
  have hT : cofinite ≤ 𝓟 T := by
    rw [le_principal_iff] at hS ⊢
    rw [mem_cofinite] at hS ⊢
    rw [← Set.image_compl_eq e.bijective]
    exact hS.image e
  let f : (Πʳ i, [G (e i), U (e i)]_[𝓟 S]) →
      (Πʳ i, [G i, U i]_[𝓟 T]) := fun x ↦ ⟨e.piCongrLeft G x, by
        intro i hi
        -- Unpack the principal-filter condition to its coordinate membership statement.
        change (e.piCongrLeft G x) i ∈ U i
        obtain ⟨j, hj, rfl⟩ := hi
        have hcoord : (e.piCongrLeft G x) (e j) = x.1 j :=
          Equiv.piCongrLeft_apply_apply G e x.1 j
        rw [hcoord]
        exact (Filter.eventually_principal.mp x.2) j hj⟩
  have hf : Continuous f := by
    apply (RestrictedProduct.continuous_rng_of_principal
      (R := G) (A := U)).mpr
    exact (Homeomorph.piCongrLeft (Y := G) e).continuous_toFun.comp
      (RestrictedProduct.continuous_coe (R := fun i : ι' ↦ G (e i))
        (A := fun i ↦ U (e i)))
  have hfac : restrictedProductCongrLeft e ∘ RestrictedProduct.inclusion _ _ hS =
      RestrictedProduct.inclusion _ _ hT ∘ f := by
    funext x
    apply RestrictedProduct.ext
    intro i
    rfl
  rw [hfac]
  exact (RestrictedProduct.continuous_inclusion hT).comp hf

/-- The inverse of restricted-product reindexing is continuous. -/
theorem continuous_restrictedProductCongrLeft_symm (e : ι' ≃ ι) :
    Continuous (@restrictedProductCongrLeft ι ι' G U e).symm := by
  rw [RestrictedProduct.continuous_dom]
  intro S hS
  let T : Set ι' := e ⁻¹' S
  have hT : cofinite ≤ 𝓟 T := by
    rw [le_principal_iff] at hS ⊢
    rw [mem_cofinite] at hS ⊢
    have hcompl : Tᶜ = e.symm '' Sᶜ := by
      ext i
      simp [T]
    rw [hcompl]
    exact hS.image e.symm
  let f : (Πʳ i, [G i, U i]_[𝓟 S]) →
      (Πʳ i, [G (e i), U (e i)]_[𝓟 T]) := fun x ↦ ⟨(e.piCongrLeft G).symm x, by
        intro i hi
        -- Unpack the principal-filter condition to its coordinate membership statement.
        change (e.piCongrLeft G).symm x i ∈ U (e i)
        have hi' : e i ∈ S := by simpa [T] using hi
        change x (e i) ∈ U (e i)
        exact (Filter.eventually_principal.mp x.2) (e i) hi'⟩
  have hf : Continuous f := by
    apply (RestrictedProduct.continuous_rng_of_principal
      (R := fun i : ι' ↦ G (e i)) (A := fun i ↦ U (e i))).mpr
    exact (Homeomorph.piCongrLeft (Y := G) e).symm.continuous_toFun.comp
      (RestrictedProduct.continuous_coe (R := G) (A := U))
  have hfac : (restrictedProductCongrLeft e).symm ∘ RestrictedProduct.inclusion _ _ hS =
      RestrictedProduct.inclusion _ _ hT ∘ f := by
    funext x
    apply RestrictedProduct.ext
    intro i
    rfl
  rw [hfac]
  exact (RestrictedProduct.continuous_inclusion hT).comp hf

/-- The consumer-oriented reindexing map is continuous. -/
theorem continuous_restrictedProductReindex (e : ι' ≃ ι) :
    Continuous (@restrictedProductReindex ι ι' G U e) := by
  exact continuous_restrictedProductCongrLeft_symm e

/-- The inverse of the consumer-oriented reindexing map is continuous. -/
theorem continuous_restrictedProductReindex_symm (e : ι' ≃ ι) :
    Continuous (@restrictedProductReindex ι ι' G U e).symm := by
  exact continuous_restrictedProductCongrLeft e

end TauCeti
