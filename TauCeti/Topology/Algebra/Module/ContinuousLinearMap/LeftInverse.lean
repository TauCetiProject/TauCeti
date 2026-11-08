/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.ContinuousInverse
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Left inverses for triangular operators

An operator on a product which retains the first coordinate admits a continuous linear
left inverse exactly when its restriction to the second factor does. This is the linear
algebra of the differential of a parameter-preserving family of immersions.

The construction uses Mathlib's `ContinuousLinearMap.HasLeftInverse`: subtract the
contribution of the first coordinate, then apply a left inverse on the second factor.

If a compression `P ∘L A` is invertible, the left inverse `(P ∘L A).inverse ∘L P` also gives a
projection off the range of `A`. Composing a linear map with this projection annihilates `A`.

A continuous linear injection of `𝕜ᵏ` into a space of dimension `k + 1` over a complete field has a
continuous left inverse and a nonzero continuous covector annihilating its range
(`ContinuousLinearMap.exists_leftInverse_ne_zero_comp_eq_zero`).
-/

public section

namespace ContinuousLinearMap

variable {R E F G : Type*} [Ring R]
  [TopologicalSpace E] [AddCommGroup E] [Module R E]
  [TopologicalSpace F] [AddCommGroup F] [Module R F]
  [TopologicalSpace G] [AddCommGroup G] [Module R G] [IsTopologicalAddGroup G]

/-- A continuous linear operator retaining the first coordinate is split-injective
exactly when its restriction to the second factor is split-injective. -/
theorem hasLeftInverse_fst_prod_iff (A : E × F →L[R] G) :
    ((fst R E F).prod A).HasLeftInverse ↔ (A.comp (inr R E F)).HasLeftInverse := by
  constructor
  · rintro ⟨L, hL⟩
    refine ⟨(snd R E F).comp (L.comp (inr R E G)), fun y => ?_⟩
    have hy := congrArg Prod.snd (hL (0, y))
    simpa using hy
  · rintro ⟨L, hL⟩
    refine ⟨(fst R E G).prod
      (L.comp ((snd R E G) - (A.comp (inl R E F)).comp (fst R E G))), ?_⟩
    rintro ⟨x, y⟩
    have hA : A (x, y) - A (x, 0) = A (0, y) := by
      rw [← map_sub]
      simp
    simpa [hA] using congrArg (Prod.mk x) (hL y)

/-- Projecting a continuous linear map off the range of an operator with invertible compression
annihilates that operator. -/
theorem sub_comp_inverse_comp_comp_eq_zero (a : E →L[R] G) (A : F →L[R] E)
    (P : E →L[R] F) (hQ : (P ∘L A).IsInvertible) :
    (a - a ∘L A ∘L (P ∘L A).inverse ∘L P) ∘L A = 0 := by
  ext v
  have hi := hQ.inverse_apply_self v
  simp only [comp_apply] at hi
  simp only [comp_apply, sub_apply, zero_apply]
  rw [hi, sub_self]

section FiniteDimensional

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [AddCommGroup E]
  [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E]
  [FiniteDimensional 𝕜 E] {k : ℕ}

/-- A continuous linear injection of a space `𝕜ᵏ` of dimension `k` into a space of dimension
`k + 1` has a continuous left inverse and a nonzero continuous covector annihilating its range. -/
theorem exists_leftInverse_ne_zero_comp_eq_zero (A : (Fin k → 𝕜) →L[𝕜] E)
    (hA : Function.Injective A) (hk : k + 1 = Module.finrank 𝕜 E) :
    ∃ (P : E →L[𝕜] (Fin k → 𝕜)) (a : E →L[𝕜] 𝕜),
      Function.LeftInverse P A ∧ a ≠ 0 ∧ a ∘L A = 0 := by
  obtain ⟨p, hp⟩ := A.toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hA)
  have hrank : Module.finrank 𝕜 (LinearMap.range A.toLinearMap) = k := by
    rw [LinearMap.finrank_range_of_inj hA, Module.finrank_pi, Fintype.card_fin]
  have hlt : LinearMap.range A.toLinearMap < ⊤ := by
    apply lt_of_le_of_ne le_top
    intro h
    have := congrArg (fun S : Submodule 𝕜 E ↦ Module.finrank 𝕜 S) h
    rw [hrank, finrank_top, ← hk] at this
    omega
  obtain ⟨a, ha, haA⟩ := (LinearMap.range A.toLinearMap).exists_le_ker_of_lt_top hlt
  refine ⟨p.toContinuousLinearMap, a.toContinuousLinearMap, fun v ↦ LinearMap.congr_fun hp v,
    fun hz ↦ ha (congrArg ContinuousLinearMap.toLinearMap hz), ?_⟩
  ext c
  exact haA (LinearMap.mem_range_self _ c)

end FiniteDimensional

end ContinuousLinearMap
