/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.RingHom
public import Mathlib.RingTheory.Localization.Defs

/-!
# Graded localizations at degree-zero elements

Let `f : 𝒜 →+*ᵍ ℬ` be a graded ring homomorphism exhibiting `B` as the localization of `A` at a
submonoid `M` of degree-zero elements. Then every homogeneous element of `B` is, up to the image of
an element of `M`, the image of a homogeneous element of `A` of the same degree: write it as a
fraction `a / m` and replace `a` by its homogeneous component of that degree.

## Main results

* `GradedRingHom.exists_mem_mul_eq_of_isLocalization`: if `b ∈ ℬ k`, then `b * f m = f a` for
  some `m ∈ M` and `a ∈ 𝒜 k`.
-/

public section

namespace GradedRingHom

variable {ι A B σ τ : Type*} [CommSemiring A] [CommSemiring B] [SetLike σ A] [SetLike τ B]
  [AddSubmonoidClass σ A] [AddSubmonoidClass τ B] [DecidableEq ι] [AddMonoid ι]
  {𝒜 : ι → σ} {ℬ : ι → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- If a graded ring homomorphism `f : 𝒜 →+*ᵍ ℬ` exhibits `B` as the localization of `A` at a
submonoid `M` of degree-zero elements, then a homogeneous element `b` of `B` of degree `k` is, up
to the image of an element of `M`, the image of a homogeneous element of `A` of degree `k`. -/
theorem exists_mem_mul_eq_of_isLocalization (f : 𝒜 →+*ᵍ ℬ) {M : Submonoid A}
    (hloc : letI := f.toRingHom.toAlgebra; IsLocalization M B) (hM : ∀ m ∈ M, m ∈ 𝒜 0) {k : ι}
    {b : B} (hb : b ∈ ℬ k) : ∃ a ∈ 𝒜 k, ∃ m : M, b * f m = f a := by
  let := f.toRingHom.toAlgebra
  have := hloc
  -- the algebra map of `f.toRingHom.toAlgebra` is `f`
  obtain ⟨⟨a, m⟩, h : b * f m = f a⟩ := IsLocalization.surj M b
  have hfa : f a ∈ ℬ k := h ▸ by simpa using SetLike.mul_mem_graded hb (Graded.map_mem f (hM _ m.2))
  refine ⟨_, (DirectSum.decompose 𝒜 a k).2, m, h.trans ?_⟩
  rw [f.map_directSumDecompose, DirectSum.decompose_of_mem_same ℬ hfa]

end GradedRingHom
