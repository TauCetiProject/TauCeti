/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import TauCeti.Analysis.CStarAlgebra.State.Space
import TauCeti.Topology.Algebra.Module.Spaces.WeakDual

/-!
# Pure states: minimal projections and pullbacks

Let `A` be a unital C⋆-algebra and `p` a projection in `A` that compresses every element to a
multiple of itself, `p a p = ω(a) p`, through a state `ω` with `ω(p) = 1`. For matrices, `p` is the
projection onto the line spanned by a unit vector `ξ` and `ω` is the vector state
`a ↦ ⟪ξ, a ξ⟫`.

Every state `φ` vanishing at `1 - p` equals `ω`: by the Cauchy–Schwarz inequality for positive
functionals, `φ` kills `a (1 - p)` and `(1 - p) a`, so `φ(a) = φ(p a p) = ω(a) φ(p) = ω(a)`. If `ω`
is a convex combination of two states with positive weights, both vanish at the positive
element `1 - p`, because `ω` does, and hence both equal `ω`. So `ω` is a pure state, an extreme
point of the state space.

Pure states also pull back along surjective star homomorphisms `f : A → B` of C⋆-algebras, not
necessarily unital: a functional `φ` of `B` is a pure state if and only if `φ ∘ f` is a pure state
of `A`. This produces pure states of `A` from those of its quotients, for instance pure extensions
of states through evaluation maps.

## Main results

* `TauCeti.eq_of_mem_stateSpace_of_map_one_sub_eq_zero`: a state vanishing at `1 - p` is `ω`.
* `TauCeti.mem_extremePoints_stateSpace_of_mul_mul_eq_smul`: `ω` is an extreme point of the state
  space.
* `TauCeti.pullbackFunctional_mem_extremePoints_stateSpace`: the pullback of a pure state along a
  surjective star homomorphism is pure.
* `TauCeti.pullbackFunctional_mem_extremePoints_stateSpace_iff`: a functional is a pure state if
  and only if its pullback along a surjective star homomorphism is a pure state.

## References

* B. Blackadar, *Operator Algebras*, Encyclopaedia of Mathematical Sciences 122, Springer (2006),
  II.6.3.
-/

public section

open WeakDual
open scoped ComplexOrder

namespace TauCeti

section Projection

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {ω φ : WeakDual ℂ A}
  {p : A}

/-- **A state supported on a minimal projection is determined.** Let `p` be a projection with
`p a p = ω(a) p` for every `a`. A state `φ` with `φ(1 - p) = 0` is `ω`. -/
theorem eq_of_mem_stateSpace_of_map_one_sub_eq_zero (hp : IsStarProjection p)
    (hpap : ∀ a, p * a * p = ω a • p) (hφ : φ ∈ stateSpace A) (hφp : φ (1 - p) = 0) : φ = ω := by
  have hq := hp.one_sub
  have hφ1 : φ p = 1 := by
    rw [map_sub, map_one_of_mem_stateSpace hφ, sub_eq_zero] at hφp
    exact hφp.symm
  obtain ⟨f, -, hf⟩ := mem_stateSpace_iff_exists_positiveLinearMap.1 hφ
  have hφf (x : A) : φ x = f x := by simp [← hf]
  have hfq : f (1 - p) = 0 := by rw [← hφf, hφp]
  refine DFunLike.ext _ _ fun a ↦ ?_
  have ha : a * p = p * a * p + (1 - p) * (a * p) := by noncomm_ring
  have h₁ : φ (a * (1 - p)) = 0 := by
    rw [hφf]
    exact PositiveLinearMap.map_mul_eq_zero_of_map_star_mul_eq_zero f
      (by rw [hq.isSelfAdjoint.star_eq, hq.isIdempotentElem.eq, hfq]) a
  have h₂ : φ ((1 - p) * (a * p)) = 0 := by
    rw [hφf]
    exact PositiveLinearMap.map_mul_eq_zero_of_map_mul_star_eq_zero f
      (by rw [hq.isSelfAdjoint.star_eq, hq.isIdempotentElem.eq, hfq]) (a * p)
  calc φ a = φ (a * p) + φ (a * (1 - p)) := by rw [← map_add]; congr 1; noncomm_ring
    _ = ω a := by rw [h₁, add_zero, ha]; simp [h₂, hpap, hφ1]

/-- **Vector-type states are pure.** Let `ω` be a state and `p` a projection with `ω(p) = 1` and
`p a p = ω(a) p` for every `a`. Then `ω` is an extreme point of the state space. -/
theorem mem_extremePoints_stateSpace_of_mul_mul_eq_smul (hω : ω ∈ stateSpace A)
    (hp : IsStarProjection p) (hpap : ∀ a, p * a * p = ω a • p) (hωp : ω p = 1) :
    ω ∈ Set.extremePoints ℝ (stateSpace A) := by
  refine mem_extremePoints.2 ⟨hω, fun φ hφ ψ hψ hseg ↦ ?_⟩
  have hq := hp.one_sub
  have hωq : ω (1 - p) = 0 := by rw [map_sub, map_one_of_mem_stateSpace hω, hωp, sub_self]
  obtain ⟨hφ0, hψ0⟩ :=
    map_eq_zero_of_mem_openSegment_of_mem_stateSpace hφ hψ hq.nonneg hseg hωq
  exact ⟨eq_of_mem_stateSpace_of_map_one_sub_eq_zero hp hpap hφ hφ0,
    eq_of_mem_stateSpace_of_map_one_sub_eq_zero hp hpap hψ hψ0⟩

end Projection

section Pullback

variable {A B F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]

/-- **Pullback of pure states along a surjective star homomorphism.** If `f : A → B` is a
surjective star homomorphism of C⋆-algebras, not necessarily unital, the pullback `φ ∘ f` of a
pure state `φ` of `B` is a pure state of `A`. -/
theorem pullbackFunctional_mem_extremePoints_stateSpace (f : F) (hf : Function.Surjective f)
    {φ : WeakDual ℂ B} (hφ : φ ∈ Set.extremePoints ℝ (stateSpace B)) :
    pullbackFunctional A f φ ∈ Set.extremePoints ℝ (stateSpace A) := by
  refine mem_extremePoints.2 ⟨mapsTo_pullbackFunctional_stateSpace_of_surjective f hf hφ.1,
    fun ψ₁ hψ₁ ψ₂ hψ₂ hseg ↦ ?_⟩
  -- both states vanish on `star k * k` for `k` in the kernel, as their combination does
  have hker (k : A) (hk : f k = 0) : ψ₁ (star k * k) = 0 ∧ ψ₂ (star k * k) = 0 :=
    map_eq_zero_of_mem_openSegment_of_mem_stateSpace hψ₁ hψ₂ (star_mul_self_nonneg k) hseg
      (by simp [hk])
  -- so, by Cauchy–Schwarz, on the kernel, and they factor through `f`
  have hfac {ψ : WeakDual ℂ A} (hψ : ψ ∈ stateSpace A)
      (h0 : ∀ k, f k = 0 → ψ (star k * k) = 0) : ψ ∈ pullbackFunctional A f '' stateSpace B :=
    (mem_image_pullbackFunctional_stateSpace_iff f hf).2 ⟨hψ, fun k hk ↦
      (PositiveContinuousLinearMap.mk₀ (toStrongDual ψ) fun _ ↦
        map_nonneg_of_mem_stateSpace hψ).map_eq_zero_of_map_star_mul_self_eq_zero (h0 k hk)⟩
  obtain ⟨χ₁, hχ₁, rfl⟩ := hfac hψ₁ fun k hk ↦ (hker k hk).1
  obtain ⟨χ₂, hχ₂, rfl⟩ := hfac hψ₂ fun k hk ↦ (hker k hk).2
  obtain ⟨s, t, hs, ht, hst, h⟩ := hseg
  have hseg' : φ ∈ openSegment ℝ χ₁ χ₂ :=
    ⟨s, t, hs, ht, hst, pullbackFunctional_injective_of_surjective f hf (by
      rw [map_add, (pullbackFunctional A f).map_smul_of_tower,
        (pullbackFunctional A f).map_smul_of_tower]
      exact h)⟩
  obtain ⟨e₁, e₂⟩ := (mem_extremePoints.1 hφ).2 χ₁ hχ₁ χ₂ hχ₂ hseg'
  exact ⟨congrArg _ e₁, congrArg _ e₂⟩

/-- **Purity is detected by pullback along a surjective star homomorphism.** If `f : A → B` is a
surjective star homomorphism of C⋆-algebras, not necessarily unital, a functional `φ` of `B` is a
pure state if and only if its pullback `φ ∘ f` is a pure state of `A`. -/
theorem pullbackFunctional_mem_extremePoints_stateSpace_iff (f : F) (hf : Function.Surjective f)
    {φ : WeakDual ℂ B} :
    pullbackFunctional A f φ ∈ Set.extremePoints ℝ (stateSpace A) ↔
      φ ∈ Set.extremePoints ℝ (stateSpace B) := by
  refine ⟨fun h ↦ ?_, pullbackFunctional_mem_extremePoints_stateSpace f hf⟩
  -- the pullback is a state vanishing on the kernel, hence the pullback of a state
  obtain ⟨χ, hχ, hχφ⟩ := (mem_image_pullbackFunctional_stateSpace_iff f hf).2
    ⟨h.1, fun k hk ↦ by simp [hk]⟩
  obtain rfl := pullbackFunctional_injective_of_surjective f hf hχφ
  refine mem_extremePoints.2 ⟨hχ, fun χ₁ hχ₁ χ₂ hχ₂ hseg ↦ ?_⟩
  obtain ⟨s, t, hs, ht, hst, hφseg⟩ := hseg
  obtain ⟨e₁, e₂⟩ := (mem_extremePoints.1 h).2 _
    (mapsTo_pullbackFunctional_stateSpace_of_surjective f hf hχ₁) _
    (mapsTo_pullbackFunctional_stateSpace_of_surjective f hf hχ₂)
    ⟨s, t, hs, ht, hst, by
      rw [← hφseg, map_add, (pullbackFunctional A f).map_smul_of_tower,
        (pullbackFunctional A f).map_smul_of_tower]⟩
  exact ⟨pullbackFunctional_injective_of_surjective f hf e₁,
    pullbackFunctional_injective_of_surjective f hf e₂⟩

end Pullback

end TauCeti
