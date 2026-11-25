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
# Pure states supported on a minimal projection

Let `A` be a unital C⋆-algebra and `p` a projection in `A` that compresses every element to a
multiple of itself, `p a p = ω(a) p`, through a state `ω` with `ω(p) = 1`. For matrices, `p` is the
projection onto the line spanned by a unit vector `ξ` and `ω` is the vector state
`a ↦ ⟪ξ, a ξ⟫`.

Every state `φ` vanishing at `1 - p` equals `ω`: by the Cauchy–Schwarz inequality for positive
functionals, `φ` kills `a (1 - p)` and `(1 - p) a`, so `φ(a) = φ(p a p) = ω(a) φ(p) = ω(a)`. If `ω`
is a convex combination of two states with positive weights, both vanish at the positive
element `1 - p`, because `ω` does, and hence both equal `ω`. So `ω` is a pure state, an extreme
point of the state space.

## Main results

* `TauCeti.eq_of_mem_stateSpace_of_map_one_sub_eq_zero`: a state vanishing at `1 - p` is `ω`.
* `TauCeti.mem_extremePoints_stateSpace_of_mul_mul_eq_smul`: `ω` is an extreme point of the state
  space.
* `TauCeti.pullbackFunctional_mem_extremePoints_stateSpace`: the pullback of a pure state along a
  surjective star homomorphism is pure.

## References

* B. Blackadar, *Operator Algebras*, Encyclopaedia of Mathematical Sciences 122, Springer (2006),
  II.6.3.
-/

public section

open WeakDual
open scoped ComplexOrder

namespace TauCeti

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
  refine mem_extremePoints.2 ⟨hω, fun φ hφ ψ hψ ⟨s, t, hs, ht, _, h⟩ ↦ ?_⟩
  have hq := hp.one_sub
  have hωq : ω (1 - p) = 0 := by rw [map_sub, map_one_of_mem_stateSpace hω, hωp, sub_self]
  have hφq := map_nonneg_of_mem_stateSpace hφ hq.nonneg
  have hψq := map_nonneg_of_mem_stateSpace hψ hq.nonneg
  have hsum : (s : ℂ) * φ (1 - p) + (t : ℂ) * ψ (1 - p) = 0 := by
    rw [← hωq, ← h]
    simp [Complex.real_smul]
  -- Both terms are nonnegative, and their sum vanishes.
  obtain ⟨h₁, h₂⟩ := (add_eq_zero_iff_of_nonneg (mul_nonneg (Complex.zero_le_real.2 hs.le) hφq)
    (mul_nonneg (Complex.zero_le_real.2 ht.le) hψq)).1 hsum
  have hφ0 := (mul_eq_zero.1 h₁).resolve_left (Complex.ofReal_ne_zero.2 hs.ne')
  have hψ0 := (mul_eq_zero.1 h₂).resolve_left (Complex.ofReal_ne_zero.2 ht.ne')
  exact ⟨eq_of_mem_stateSpace_of_map_one_sub_eq_zero hp hpap hφ hφ0,
    eq_of_mem_stateSpace_of_map_one_sub_eq_zero hp hpap hψ hψ0⟩

section Pullback

variable {B F : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]

/-- A state of `A` that vanishes at `star k * k` for every `k` in the kernel of a surjective star
homomorphism `f : A → B` is the pullback of a state of `B`. -/
private theorem exists_mem_stateSpace_pullbackFunctional_eq (f : F) (hf : Function.Surjective f)
    {ψ : WeakDual ℂ A} (hψ : ψ ∈ stateSpace A) (hker : ∀ k, f k = 0 → ψ (star k * k) = 0) :
    ∃ χ ∈ stateSpace B, pullbackFunctional A f χ = ψ := by
  let ω : A →P[ℂ] ℂ := .mk₀ (toStrongDual ψ) fun _ ↦ map_nonneg_of_mem_stateSpace hψ
  let fₗ : A →ₗ[ℂ] B := (f : A →ₗ[ℂ] B)
  have hle : LinearMap.ker fₗ ≤ LinearMap.ker (toStrongDual ψ : A →ₗ[ℂ] ℂ) := fun k hk ↦
    ω.map_eq_zero_of_map_star_mul_self_eq_zero (hker k hk)
  let g : B →ₗ[ℂ] ℂ := ((LinearMap.ker fₗ).liftQ (toStrongDual ψ : A →ₗ[ℂ] ℂ) hle).comp
    (fₗ.quotKerEquivOfSurjective hf).symm.toLinearMap
  have hg (a : A) : g (f a) = ψ a := by
    have : (fₗ.quotKerEquivOfSurjective hf).symm (f a) = Submodule.Quotient.mk a :=
      (LinearEquiv.symm_apply_eq _).mpr rfl
    simp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]
    rfl
  have hgpos (b : B) (hb : 0 ≤ b) : 0 ≤ g b := by
    obtain ⟨c, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hb
    obtain ⟨a, rfl⟩ := hf c
    rw [← map_star, ← map_mul, hg]
    exact map_nonneg_of_mem_stateSpace hψ (star_mul_self_nonneg a)
  let σ : B →ₚ[ℂ] ℂ := .mk₀ g hgpos
  let χ : WeakDual ℂ B := StrongDual.toWeakDual (PositiveContinuousLinearMap.ofClass σ)
  have hχ (b : B) : χ b = g b := rfl
  have hf1 : f 1 = 1 := by
    obtain ⟨a, ha⟩ := hf 1
    rw [← mul_one (f 1), ← ha, ← map_mul, one_mul]
  refine ⟨χ, mem_stateSpace_iff_map_one.mpr ⟨fun b hb ↦ hgpos b hb, ?_⟩, ?_⟩
  · rw [hχ, ← hf1, hg, map_one_of_mem_stateSpace hψ]
  · exact DFunLike.ext _ _ fun a ↦ by rw [pullbackFunctional_apply, hχ, hg]

/-- **Pullback of pure states along a surjective star homomorphism.** If `f : A → B` is a
surjective star homomorphism of unital C⋆-algebras, the pullback `φ ∘ f` of a pure state `φ` of
`B` is a pure state of `A`. A state in an open segment through `φ ∘ f` is dominated by a multiple
of `φ ∘ f`, so it vanishes on the kernel of `f` and is itself a pullback; the segment then comes
from one through `φ`. -/
theorem pullbackFunctional_mem_extremePoints_stateSpace (f : F) (hf : Function.Surjective f)
    {φ : WeakDual ℂ B} (hφ : φ ∈ Set.extremePoints ℝ (stateSpace B)) :
    pullbackFunctional A f φ ∈ Set.extremePoints ℝ (stateSpace A) := by
  refine mem_extremePoints.2 ⟨mapsTo_pullbackFunctional_stateSpace_of_surjective f hf hφ.1,
    fun ψ₁ hψ₁ ψ₂ hψ₂ ⟨s, t, hs, ht, hst, h⟩ ↦ ?_⟩
  -- both states vanish on `star k * k` for `k` in the kernel, as their combination does
  have hker : ∀ k, f k = 0 → ψ₁ (star k * k) = 0 ∧ ψ₂ (star k * k) = 0 := fun k hk ↦ by
    have h₁ := map_nonneg_of_mem_stateSpace hψ₁ (star_mul_self_nonneg k)
    have h₂ := map_nonneg_of_mem_stateSpace hψ₂ (star_mul_self_nonneg k)
    have hsum : (s : ℂ) * ψ₁ (star k * k) + (t : ℂ) * ψ₂ (star k * k) = 0 := by
      have h0 : pullbackFunctional A f φ (star k * k) = 0 := by simp [hk]
      rw [← h0, ← h]
      simp [Complex.real_smul]
    obtain ⟨e₁, e₂⟩ := (add_eq_zero_iff_of_nonneg (mul_nonneg (Complex.zero_le_real.2 hs.le) h₁)
      (mul_nonneg (Complex.zero_le_real.2 ht.le) h₂)).1 hsum
    exact ⟨(mul_eq_zero.1 e₁).resolve_left (Complex.ofReal_ne_zero.2 hs.ne'),
      (mul_eq_zero.1 e₂).resolve_left (Complex.ofReal_ne_zero.2 ht.ne')⟩
  obtain ⟨χ₁, hχ₁, rfl⟩ :=
    exists_mem_stateSpace_pullbackFunctional_eq f hf hψ₁ fun k hk ↦ (hker k hk).1
  obtain ⟨χ₂, hχ₂, rfl⟩ :=
    exists_mem_stateSpace_pullbackFunctional_eq f hf hψ₂ fun k hk ↦ (hker k hk).2
  have hinj : Function.Injective (pullbackFunctional A f) := fun χ χ' hχ ↦
    DFunLike.ext _ _ fun b ↦ by
      obtain ⟨a, rfl⟩ := hf b
      simpa using congrArg (fun χ'' : WeakDual ℂ A ↦ χ'' a) hχ
  have hseg : φ ∈ openSegment ℝ χ₁ χ₂ :=
    ⟨s, t, hs, ht, hst, hinj (by
      rw [map_add, (pullbackFunctional A f).map_smul_of_tower,
        (pullbackFunctional A f).map_smul_of_tower]
      exact h)⟩
  obtain ⟨e₁, e₂⟩ := (mem_extremePoints.1 hφ).2 χ₁ hχ₁ χ₂ hχ₂ hseg
  exact ⟨congrArg _ e₁, congrArg _ e₂⟩

end Pullback

end TauCeti
