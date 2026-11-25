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

end TauCeti
