/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps

/-!
# The irrelevant ideal under a surjective graded ring homomorphism

A surjective graded ring homomorphism `f : 𝒜 →+*ᵍ ℬ` maps the irrelevant ideal `𝒜₊` onto the
irrelevant ideal `ℬ₊`. The inequality `ℬ₊ ≤ 𝒜₊.map f` is the hypothesis under which `f` induces
`AlgebraicGeometry.Proj.map f : Proj ℬ ⟶ Proj 𝒜`.

## Main results

* `HomogeneousIdeal.irrelevant_le_map_of_surjective`: `ℬ₊ ≤ 𝒜₊.map f` for a surjective `f`.
-/

public section

namespace HomogeneousIdeal

variable {ι A B σ τ : Type*} [CommRing A] [CommRing B] [SetLike σ A] [SetLike τ B]
  [AddSubgroupClass σ A] [AddSubgroupClass τ B] [DecidableEq ι] [AddCommMonoid ι] [PartialOrder ι]
  [CanonicallyOrderedAdd ι] {𝒜 : ι → σ} {ℬ : ι → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- A surjective graded ring homomorphism `f` maps the irrelevant ideal onto the irrelevant
ideal: if `f a = b` with `b` of zero degree-zero part, then `a` minus its degree-zero part lies
in `𝒜₊` and still maps to `b`. -/
theorem irrelevant_le_map_of_surjective (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f) :
    irrelevant ℬ ≤ (irrelevant 𝒜).map f := by
  intro b hb
  obtain ⟨a, rfl⟩ := hf b
  have ha : a - GradedRing.proj 𝒜 0 a ∈ irrelevant 𝒜 := by
    rw [mem_irrelevant_iff, map_sub, GradedRing.proj_apply, GradedRing.proj_apply,
      DirectSum.decompose_of_mem_same 𝒜 (SetLike.coe_mem _), sub_self]
  have hfa : f (a - GradedRing.proj 𝒜 0 a) = f a := by
    rw [map_sub, GradedRing.proj_apply, f.map_directSumDecompose, ← GradedRing.proj_apply,
      (mem_irrelevant_iff _ _).mp hb, sub_zero]
  exact hfa ▸ Ideal.mem_map_of_mem _ ha

end HomogeneousIdeal
