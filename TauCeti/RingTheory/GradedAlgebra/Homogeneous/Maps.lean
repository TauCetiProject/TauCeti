/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps

/-!
# The irrelevant ideal under ring homomorphisms

For a surjective graded ring homomorphism `f : 𝒜 →+*ᵍ ℬ`, the irrelevant ideal `ℬ₊` is contained
in the image `𝒜₊.map f` of the irrelevant ideal `𝒜₊`. This containment is the hypothesis under
which `f` induces `AlgebraicGeometry.Proj.map f : Proj ℬ ⟶ Proj 𝒜`.

Degreewise rescaling by powers of a unit preserves the condition that a coordinate map
sends the irrelevant ideal to the unit ideal, allowing the rescaled coordinates to define
a morphism to `Proj` as well.

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

namespace TauCeti.HomogeneousIdeal

variable {A B σ : Type*} [Semiring A] [CommSemiring B] [SetLike σ A]
  [AddSubmonoidClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- Unit rescaling in positive degrees preserves the condition that the irrelevant ideal maps
to the unit ideal. -/
theorem map_irrelevant_eq_top_of_unit_rescaling
    (f g : A →+* B) (c : Bˣ)
    (h : ∀ n, 0 < n → ∀ a ∈ 𝒜 n, g a = c ^ n * f a)
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤) :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map g = ⊤ := by
  have hle : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f ≤
      (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map g := by
    rw [Ideal.map_le_iff_le_comap, HomogeneousIdeal.toIdeal_irrelevant_le]
    intro n hn a ha
    exact (Ideal.unit_mul_mem_iff_mem _ (c.isUnit.pow n)).mp
      (h n hn a ha ▸ Ideal.mem_map_of_mem g (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hn ha))
  rw [hf] at hle
  exact top_unique hle

end TauCeti.HomogeneousIdeal
