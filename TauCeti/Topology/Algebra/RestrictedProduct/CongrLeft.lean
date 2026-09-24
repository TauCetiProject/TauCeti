/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

/-!
# Reindexing restricted products

An equivalence of index types transports restricted products between reindexed families.  The
coordinate equations make the correspondence available for transporting maps and decompositions.

The algebraic equivalence follows the construction in FLT,
`FLT/Mathlib/Topology/Algebra/RestrictedProduct/Equiv.lean`, at commit
`a9efe585de92be60be84ac1d14ced5a1b0944333` (Apache 2.0), specialized to the cofinite filter.
-/

public section

namespace TauCeti

open Filter
open scoped RestrictedProduct

universe u v w

section Equiv

variable {ι : Type u} {ι' : Type v} {G : ι → Type w} {U : ∀ i, Set (G i)}

private theorem cast_apply {i j : ι} (h : i = j) (x : ∀ k, G k) :
    cast (congrArg G h) (x i) = x j := by
  subst j
  rfl

private theorem cast_mapsTo {i j : ι} (h : i = j) :
    Set.MapsTo (cast (congrArg G h)) (U i) (U j) := by
  subst j
  exact Set.mapsTo_id _

private theorem continuous_cast [∀ i, TopologicalSpace (G i)] {i j : ι} (h : i = j) :
    Continuous (cast (congrArg G h) : G i → G j) := by
  subst j
  exact continuous_id

private def restrictedProductCongrLeftMap (e : ι' ≃ ι) :
    (Πʳ i, [G (e i), U (e i)]) → (Πʳ i, [G i, U i]) :=
  RestrictedProduct.mapAlong (fun i : ι' ↦ G (e i)) G e.symm
    e.symm.injective.tendsto_cofinite
    (fun i ↦ cast (congrArg G (e.apply_symm_apply i)))
    (.of_forall fun i ↦ cast_mapsTo (G := G) (U := U) (e.apply_symm_apply i))

private def restrictedProductReindexMap (e : ι' ≃ ι) :
    (Πʳ i, [G i, U i]) → (Πʳ i, [G (e i), U (e i)]) :=
  RestrictedProduct.mapAlong G (fun i : ι' ↦ G (e i)) e
    e.injective.tendsto_cofinite (fun _ x ↦ x)
    (.of_forall fun _ ↦ Set.mapsTo_id _)

/-- Reindex a restricted product of arbitrary sets along an equivalence, from `ι'` to `ι`. -/
def restrictedProductCongrLeftEquiv (e : ι' ≃ ι) :
    (Πʳ i, [G (e i), U (e i)]) ≃ (Πʳ i, [G i, U i]) where
  toFun := restrictedProductCongrLeftMap e
  invFun := restrictedProductReindexMap e
  left_inv x := by
    apply RestrictedProduct.ext
    intro i
    simp only [restrictedProductCongrLeftMap, restrictedProductReindexMap,
      RestrictedProduct.mapAlong_apply]
    rw [← Equiv.piCongrLeft_apply_eq_cast x (e i)]
    exact Equiv.piCongrLeft_apply_apply G e x i
  right_inv x := by
    apply RestrictedProduct.ext
    intro i
    simp only [restrictedProductCongrLeftMap, restrictedProductReindexMap,
      RestrictedProduct.mapAlong_apply]
    exact cast_apply (e.apply_symm_apply i) x

/-- The set-level reindexing equivalence preserves the coordinate at `e i`. -/
@[simp]
theorem restrictedProductCongrLeftEquiv_apply_apply (e : ι' ≃ ι)
    (x : Πʳ i, [G (e i), U (e i)]) (i : ι') :
    restrictedProductCongrLeftEquiv e x (e i) = x i := by
  -- Expose the private mapAlong implementation to use its coordinate equation.
  change restrictedProductCongrLeftMap e x (e i) = x i
  simp only [restrictedProductCongrLeftMap, RestrictedProduct.mapAlong_apply]
  rw [← Equiv.piCongrLeft_apply_eq_cast x (e i)]
  exact Equiv.piCongrLeft_apply_apply G e x i

/-- Evaluation of set-level reindexing at any target coordinate. -/
@[simp]
theorem restrictedProductCongrLeftEquiv_apply (e : ι' ≃ ι)
    (x : Πʳ i, [G (e i), U (e i)]) (j : ι) :
    restrictedProductCongrLeftEquiv e x j =
      cast (congrArg G (e.apply_symm_apply j)) (x (e.symm j)) := by
  -- Expose the private mapAlong implementation to use its coordinate equation.
  change restrictedProductCongrLeftMap e x j = _
  simp only [restrictedProductCongrLeftMap, RestrictedProduct.mapAlong_apply]

/-- The inverse set-level reindexing equivalence evaluates by precomposition with `e`. -/
@[simp]
theorem restrictedProductCongrLeftEquiv_symm_apply (e : ι' ≃ ι)
    (x : Πʳ i, [G i, U i]) (i : ι') :
    (restrictedProductCongrLeftEquiv e).symm x i = x (e i) := by
  -- The inverse equivalence is the private inverse map by construction.
  change restrictedProductReindexMap e x i = _
  simp only [restrictedProductReindexMap, RestrictedProduct.mapAlong_apply]

/-- Reindex a restricted product of arbitrary sets in the consumer orientation. -/
def restrictedProductReindexEquiv (e : ι' ≃ ι) :
    (Πʳ i, [G i, U i]) ≃ (Πʳ i, [G (e i), U (e i)]) :=
  (restrictedProductCongrLeftEquiv e).symm

/-- Evaluation of consumer-oriented set-level reindexing at a new index. -/
@[simp]
theorem restrictedProductReindexEquiv_apply (e : ι' ≃ ι)
    (x : Πʳ i, [G i, U i]) (i : ι') :
    restrictedProductReindexEquiv e x i = x (e i) := by
  exact restrictedProductCongrLeftEquiv_symm_apply e x i

/-- Evaluation of the inverse consumer-oriented set-level reindexing at a corresponding index. -/
@[simp]
theorem restrictedProductReindexEquiv_symm_apply (e : ι' ≃ ι)
    (x : Πʳ i, [G (e i), U (e i)]) (i : ι') :
    (restrictedProductReindexEquiv e).symm x (e i) = x i := by
  simpa [restrictedProductReindexEquiv] using restrictedProductCongrLeftEquiv_apply_apply e x i

/-- Evaluation of inverse consumer-oriented set-level reindexing at any original index. -/
@[simp]
theorem restrictedProductReindexEquiv_symm_apply_eq_cast (e : ι' ≃ ι)
    (x : Πʳ i, [G (e i), U (e i)]) (j : ι) :
    (restrictedProductReindexEquiv e).symm x j =
      cast (congrArg G (e.apply_symm_apply j)) (x (e.symm j)) := by
  exact restrictedProductCongrLeftEquiv_apply e x j

variable [∀ i, TopologicalSpace (G i)]

/-- Set-level reindexing from `ι'` to `ι` is continuous. -/
theorem continuous_restrictedProductCongrLeftEquiv (e : ι' ≃ ι) :
    Continuous (@restrictedProductCongrLeftEquiv ι ι' G U e) := by
  -- The equivalence coerces to the private mapAlong implementation.
  change Continuous (restrictedProductCongrLeftMap e)
  exact RestrictedProduct.mapAlong_continuous (fun i : ι' ↦ G (e i)) G e.symm
    e.symm.injective.tendsto_cofinite
    (fun i ↦ cast (congrArg G (e.apply_symm_apply i)))
    (.of_forall fun i ↦ cast_mapsTo (G := G) (U := U) (e.apply_symm_apply i))
    (fun i ↦ continuous_cast (G := G) (e.apply_symm_apply i))

/-- The inverse of set-level reindexing from `ι'` to `ι` is continuous. -/
theorem continuous_restrictedProductCongrLeftEquiv_symm (e : ι' ≃ ι) :
    Continuous (@restrictedProductCongrLeftEquiv ι ι' G U e).symm := by
  -- The inverse equivalence coerces to the private inverse mapAlong implementation.
  change Continuous (restrictedProductReindexMap e)
  exact RestrictedProduct.mapAlong_continuous G (fun i : ι' ↦ G (e i)) e
    e.injective.tendsto_cofinite (fun _ x ↦ x)
    (.of_forall fun _ ↦ Set.mapsTo_id _) (fun _ ↦ continuous_id)

/-- Consumer-oriented set-level reindexing is continuous. -/
theorem continuous_restrictedProductReindexEquiv (e : ι' ≃ ι) :
    Continuous (@restrictedProductReindexEquiv ι ι' G U e) := by
  exact continuous_restrictedProductCongrLeftEquiv_symm e

/-- The inverse of consumer-oriented set-level reindexing is continuous. -/
theorem continuous_restrictedProductReindexEquiv_symm (e : ι' ≃ ι) :
    Continuous (@restrictedProductReindexEquiv ι ι' G U e).symm := by
  exact continuous_restrictedProductCongrLeftEquiv e

end Equiv

variable {ι : Type u} {ι' : Type v} {G : ι → Type w} [∀ i, Mul (G i)]
  {U : ∀ i, Subsemigroup (G i)}

/-- Reindex a restricted product along an equivalence, in the orientation from `ι'` to `ι`.
At the index `e i`, the output has the same coordinate as the input at `i`. -/
def restrictedProductCongrLeft (e : ι' ≃ ι) :
    (Πʳ i, [G (e i), U (e i)]) ≃* (Πʳ i, [G i, U i]) where
  toEquiv := restrictedProductCongrLeftEquiv (G := G)
    (U := fun i ↦ (U i : Set (G i))) e
  map_mul' x y := by
    apply RestrictedProduct.ext
    intro i
    -- Unpack the MulEquiv's underlying Equiv to apply its existing coordinate theorem.
    change restrictedProductCongrLeftEquiv (G := G)
      (U := fun i ↦ (U i : Set (G i))) e (x * y) i =
      restrictedProductCongrLeftEquiv (G := G)
        (U := fun i ↦ (U i : Set (G i))) e x i *
      restrictedProductCongrLeftEquiv (G := G)
        (U := fun i ↦ (U i : Set (G i))) e y i
    rw [restrictedProductCongrLeftEquiv_apply (G := G)
      (U := fun i ↦ (U i : Set (G i))) (e := e)]
    rw [restrictedProductCongrLeftEquiv_apply (G := G)
      (U := fun i ↦ (U i : Set (G i))) (e := e)]
    rw [restrictedProductCongrLeftEquiv_apply (G := G)
      (U := fun i ↦ (U i : Set (G i))) (e := e)]
    simp only [RestrictedProduct.mul_apply]
    exact (MulEquiv.cast (e.apply_symm_apply i)).map_mul _ _

/-- The reindexing equivalence preserves coordinates when evaluated at `e i`. -/
@[simp]
theorem restrictedProductCongrLeft_apply_apply (e : ι' ≃ ι)
    (x : Πʳ i, [G (e i), U (e i)]) (i : ι') :
    restrictedProductCongrLeft e x (e i) = x i := by
  exact restrictedProductCongrLeftEquiv_apply_apply (G := G)
    (U := fun i ↦ (U i : Set (G i))) e x i

/-- Evaluation at any target index, with the dependent coordinate transported along
`e (e.symm j) = j`. This also describes the inverse of `restrictedProductReindex`. -/
@[simp]
theorem restrictedProductCongrLeft_apply (e : ι' ≃ ι)
    (x : Πʳ i, [G (e i), U (e i)]) (j : ι) :
    restrictedProductCongrLeft e x j =
      cast (congrArg G (e.apply_symm_apply j)) (x (e.symm j)) := by
  exact restrictedProductCongrLeftEquiv_apply (G := G)
    (U := fun i ↦ (U i : Set (G i))) e x j

/-- The inverse reindexing equivalence evaluates at the corresponding original index. -/
@[simp]
theorem restrictedProductCongrLeft_symm_apply (e : ι' ≃ ι)
    (x : Πʳ i, [G i, U i]) (i : ι') :
    (restrictedProductCongrLeft e).symm x i = x (e i) := by
  -- The MulEquiv's toEquiv field is the set-level equivalence above.
  change (restrictedProductCongrLeftEquiv (G := G)
    (U := fun i ↦ (U i : Set (G i))) e).symm x i = x (e i)
  exact restrictedProductCongrLeftEquiv_symm_apply (G := G)
    (U := fun i ↦ (U i : Set (G i))) e x i

/-- Reindex in the consumer orientation: `x` is sent to the function `i ↦ x (e i)`. -/
def restrictedProductReindex (e : ι' ≃ ι) :
    (Πʳ i, [G i, U i]) ≃* (Πʳ i, [G (e i), U (e i)]) :=
  (restrictedProductCongrLeft e).symm

/-- Evaluation of `restrictedProductReindex` at a new index. -/
@[simp]
theorem restrictedProductReindex_apply (e : ι' ≃ ι)
    (x : Πʳ i, [G i, U i]) (i : ι') :
    restrictedProductReindex e x i = x (e i) := by
  exact restrictedProductCongrLeft_symm_apply e x i

/-- Evaluation of the inverse of `restrictedProductReindex` at an original index. -/
@[simp]
theorem restrictedProductReindex_symm_apply (e : ι' ≃ ι)
    (x : Πʳ i, [G (e i), U (e i)]) (i : ι') :
    (restrictedProductReindex e).symm x (e i) = x i := by
  simpa [restrictedProductReindex] using restrictedProductCongrLeft_apply_apply e x i

/-- Evaluation of the inverse reindexing equivalence at any original index, with its dependent
coordinate transported along `e (e.symm j) = j`. -/
@[simp]
theorem restrictedProductReindex_symm_apply_eq_cast (e : ι' ≃ ι)
    (x : Πʳ i, [G (e i), U (e i)]) (j : ι) :
    (restrictedProductReindex e).symm x j =
      cast (congrArg G (e.apply_symm_apply j)) (x (e.symm j)) := by
  exact restrictedProductCongrLeft_apply e x j

variable [∀ i, TopologicalSpace (G i)]

/-- Reindexing a restricted product is continuous. -/
theorem continuous_restrictedProductCongrLeft (e : ι' ≃ ι) :
    Continuous (@restrictedProductCongrLeft ι ι' G _ U e) := by
  -- The MulEquiv's underlying function is the set-level equivalence's function.
  change Continuous (@restrictedProductCongrLeftEquiv ι ι' G
    (fun i ↦ (U i : Set (G i))) e)
  exact continuous_restrictedProductCongrLeftEquiv (G := G)
    (U := fun i ↦ (U i : Set (G i))) e

/-- The inverse of the left-oriented restricted-product reindexing is continuous. -/
theorem continuous_restrictedProductCongrLeft_symm (e : ι' ≃ ι) :
    Continuous (@restrictedProductCongrLeft ι ι' G _ U e).symm := by
  -- The inverse MulEquiv function is the inverse set-level equivalence function.
  change Continuous (@restrictedProductCongrLeftEquiv ι ι' G
    (fun i ↦ (U i : Set (G i))) e).symm
  exact continuous_restrictedProductCongrLeftEquiv_symm (G := G)
    (U := fun i ↦ (U i : Set (G i))) e

/-- The consumer-oriented reindexing map is continuous. -/
theorem continuous_restrictedProductReindex (e : ι' ≃ ι) :
    Continuous (@restrictedProductReindex ι ι' G _ U e) := by
  exact continuous_restrictedProductCongrLeft_symm e

/-- The inverse of the consumer-oriented reindexing map is continuous. -/
theorem continuous_restrictedProductReindex_symm (e : ι' ≃ ι) :
    Continuous (@restrictedProductReindex ι ι' G _ U e).symm := by
  exact continuous_restrictedProductCongrLeft e

end TauCeti
