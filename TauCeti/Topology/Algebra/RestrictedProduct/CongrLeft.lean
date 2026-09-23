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

variable {ι : Type u} {ι' : Type v} {G : ι → Type w} {U : ∀ i, Set (G i)}

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
theorem restrictedProductCongrLeft_apply_apply (e : ι' ≃ ι)
    (x : Πʳ i, [G (e i), U (e i)]) (i : ι') :
    restrictedProductCongrLeft e x (e i) = x i := by
  -- The Mathlib coordinate theorem is stated for functions, so expose the restricted-product
  -- subtype coercion before applying it.
  change (e.piCongrLeft G x) (e i) = x i
  exact Equiv.piCongrLeft_apply_apply G e x i

/-- Evaluation at any target index, with the dependent coordinate transported along
`e (e.symm j) = j`. This also describes the inverse of `restrictedProductReindex`. -/
@[simp]
theorem restrictedProductCongrLeft_apply (e : ι' ≃ ι)
    (x : Πʳ i, [G (e i), U (e i)]) (j : ι) :
    restrictedProductCongrLeft e x j =
      cast (congrArg G (e.apply_symm_apply j)) (x (e.symm j)) := by
  exact Equiv.piCongrLeft_apply_eq_cast x j

/-- The inverse reindexing equivalence evaluates at the corresponding original index. -/
@[simp]
theorem restrictedProductCongrLeft_symm_apply (e : ι' ≃ ι)
    (x : Πʳ i, [G i, U i]) (i : ι') :
    (restrictedProductCongrLeft e).symm x i = x (e i) := by
  -- The inverse equivalence's subtype coercion must be exposed to match Mathlib's function lemma.
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
  simp [restrictedProductReindex, restrictedProductCongrLeft_apply]

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
  have mapsToCast (i j : ι) (h : i = j) :
      Set.MapsTo (cast (congrArg G h)) (U i) (U j) := by
    cases h
    exact Set.mapsTo_id _
  have continuousCast (i j : ι) (h : i = j) :
      Continuous (cast (congrArg G h) : G i → G j) := by
    cases h
    exact continuous_id
  let φ : ∀ i, G (e (e.symm i)) → G i := fun i ↦
    cast (congrArg G (e.apply_symm_apply i))
  have hφ : ∀ i, Set.MapsTo (φ i) (U (e (e.symm i))) (U i) := by
    intro i
    exact mapsToCast _ _ (e.apply_symm_apply i)
  have hφcont : ∀ i, Continuous (φ i) := by
    intro i
    exact continuousCast _ _ (e.apply_symm_apply i)
  have hfS : Tendsto e.symm (𝓟 T) (𝓟 S) := by
    apply tendsto_principal.2
    rintro i ⟨j, hj, rfl⟩
    simpa using hj
  have hφS : ∀ᶠ i in 𝓟 T, Set.MapsTo (φ i) (U (e (e.symm i))) (U i) :=
    .of_forall hφ
  let f : (Πʳ i, [G (e i), U (e i)]_[𝓟 S]) →
      (Πʳ i, [G i, U i]_[𝓟 T]) :=
    RestrictedProduct.mapAlong (fun i : ι' ↦ G (e i)) G e.symm hfS φ hφS
  have hf : Continuous f := by
    exact RestrictedProduct.mapAlong_continuous (fun i : ι' ↦ G (e i)) G e.symm
      hfS φ hφS hφcont
  have hfac : restrictedProductCongrLeft e ∘ RestrictedProduct.inclusion _ _ hS =
      RestrictedProduct.inclusion _ _ hT ∘ f := by
    funext x
    apply RestrictedProduct.ext
    intro i
    rw [Function.comp_apply, Function.comp_apply]
    rw [restrictedProductCongrLeft_apply, RestrictedProduct.inclusion_apply]
    simp [f, RestrictedProduct.mapAlong_apply, φ]
  rw [hfac]
  exact (RestrictedProduct.continuous_inclusion hT).comp hf

/-- The inverse of the left-oriented restricted-product reindexing is continuous. -/
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
  have hfS : Tendsto e (𝓟 T) (𝓟 S) := by
    apply tendsto_principal.2
    intro i hi
    simpa [T] using hi
  have hφS : ∀ᶠ i in 𝓟 T,
      Set.MapsTo (fun x : G (e i) ↦ x) (U (e i)) (U (e i)) :=
    .of_forall fun _ _ hx ↦ hx
  let f : (Πʳ i, [G i, U i]_[𝓟 S]) →
      (Πʳ i, [G (e i), U (e i)]_[𝓟 T]) :=
    RestrictedProduct.mapAlong G (fun i : ι' ↦ G (e i)) e hfS (fun _ x ↦ x) hφS
  have hf : Continuous f := by
    exact RestrictedProduct.mapAlong_continuous G (fun i : ι' ↦ G (e i)) e
      hfS (fun _ x ↦ x) hφS (fun _ ↦ continuous_id)
  have hfac : (restrictedProductCongrLeft e).symm ∘ RestrictedProduct.inclusion _ _ hS =
      RestrictedProduct.inclusion _ _ hT ∘ f := by
    funext x
    apply RestrictedProduct.ext
    intro i
    rw [Function.comp_apply, Function.comp_apply]
    simp [f, RestrictedProduct.mapAlong_apply]
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
