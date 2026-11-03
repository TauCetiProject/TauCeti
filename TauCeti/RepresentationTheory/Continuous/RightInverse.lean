/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Continuous.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.RepresentationTheory.Invariants
import TauCeti.Algebra.BigOperators.Finset.Average

/-!
# Fixed right inverses of invariant linear maps

A surjective invariant continuous linear map to a finite-dimensional trivial representation
has a continuous linear right inverse with image in the fixed subspace. This gives normal
coordinates fixed individually by a finite group, without requiring the action to be faithful.
The construction uses Mathlib's `Representation.averageMap` on an ordinary right inverse.
-/

public noncomputable section

namespace ContRepresentation

variable {𝕜 G E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [Group G] [Fintype G] [Invertible (Fintype.card G : 𝕜)]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- An invariant surjection onto a finite-dimensional space has a continuous linear right
inverse whose image is fixed by the group, provided the group order is invertible. -/
theorem exists_fixed_rightInverse (ρ : ContRepresentation 𝕜 G E) (q : E →L[𝕜] F)
    (hq : Function.Surjective q) (hinv : ∀ g : G, q.comp (ρ g) = q) :
    ∃ s : F →L[𝕜] E, q.comp s = ContinuousLinearMap.id 𝕜 F ∧
      ∀ (g : G) (v : F), ρ g (s v) = s v := by
  classical
  obtain ⟨s₀, hs₀⟩ := q.exists_rightInverse_of_surjective (q.range_eq_top_of_surjective hq)
  let A : E →L[𝕜] E := ⅟(Fintype.card G : 𝕜) • ∑ g : G, ρ g
  have hA (v : E) : A v = ρ.toRepresentation.averageMap v := by
    rw [Representation.averageMap_eq_invOf_card_smul_norm]
    simp [A, Representation.norm, toMonoidHom_apply]
  refine ⟨A.comp s₀, ?_, fun g v ↦ ?_⟩
  · ext v
    have hqs (g : G) : q (ρ g (s₀ v)) = v := by
      have h := DFunLike.congr_fun (hinv g) (s₀ v)
      have h₀ := DFunLike.congr_fun hs₀ v
      simpa using h.trans h₀
    simp only [ContinuousLinearMap.comp_apply, A, smul_apply,
      sum_apply, map_smul, map_sum, hqs, ContinuousLinearMap.id_apply]
    exact Fintype.invOf_card_smul_sum_const v
  · simpa [hA, toMonoidHom_apply] using
      ρ.toRepresentation.averageMap_invariant (s₀ v) g

end ContRepresentation
