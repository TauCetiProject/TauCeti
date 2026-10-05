/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps

/-!
# The irrelevant ideal under a surjective graded ring homomorphism

For a surjective graded ring homomorphism `f : 𝒜 →+*ᵍ ℬ`, the irrelevant ideal `ℬ₊` is contained
in the image `𝒜₊.map f` of the irrelevant ideal `𝒜₊`. This containment is the hypothesis under
which `f` induces `AlgebraicGeometry.Proj.map f : Proj ℬ ⟶ Proj 𝒜`.

## Main results

* `HomogeneousIdeal.irrelevant_le_map_of_surjective`: `ℬ₊ ≤ 𝒜₊.map f` for a surjective `f`.
-/

public section

namespace HomogeneousIdeal

variable {ι A B σ τ : Type*} [Semiring A] [Semiring B] [SetLike σ A] [SetLike τ B]
  [AddSubmonoidClass σ A] [AddSubmonoidClass τ B] [DecidableEq ι] [AddCommMonoid ι]
  [PartialOrder ι] [CanonicallyOrderedAdd ι] {𝒜 : ι → σ} {ℬ : ι → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- For a surjective graded ring homomorphism `f : 𝒜 →+*ᵍ ℬ`, the irrelevant ideal `ℬ₊` is
contained in the image `𝒜₊.map f` of the irrelevant ideal `𝒜₊`. -/
theorem irrelevant_le_map_of_surjective (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f) :
    irrelevant ℬ ≤ (irrelevant 𝒜).map f := by
  refine (irrelevant_le _).mpr fun i hi b hb ↦ ?_
  obtain ⟨a, rfl⟩ := hf b
  -- `f a` is homogeneous of degree `i`, so it is the image of the degree-`i` component of `a`
  rw [← DirectSum.decompose_of_mem_same ℬ (hb : f a ∈ ℬ i), ← f.map_directSumDecompose]
  exact Ideal.mem_map_of_mem _ (mem_irrelevant_of_mem _ hi (SetLike.coe_mem _))

end HomogeneousIdeal
