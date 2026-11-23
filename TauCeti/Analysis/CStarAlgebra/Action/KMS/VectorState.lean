/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.KMS.Basic
public import TauCeti.Analysis.CStarAlgebra.GNS.VonNeumannAlgebra
import TauCeti.Analysis.CStarAlgebra.Action.KMS.Separating

/-!
# The vector trace of a tracial state

Let `ω` be a state of a unital C⋆-algebra `A`, with GNS representation `π_ω`, GNS vector
`Ω = [1]` and GNS von Neumann algebra `M = π_ω(A)''`. The GNS vector state
`τ''(x) = ⟪Ω, x Ω⟫` on `M` (`PositiveLinearMap.gnsVectorState`) extends `ω` along `π_ω`.

* `TauCeti.CStarAction.IsKMSState.gnsVectorState_star_mul_self_eq_zero_iff`: if `ω` is a β-KMS
  state of some dynamics, `τ''` is faithful. Indeed `τ''(x⋆ x) = ‖x Ω‖ ^ 2`, and `Ω` is
  separating for `M`, `TauCeti.CStarAction.IsKMSState.eq_zero_of_apply_toPreGNS_one_eq_zero`.
* `TauCeti.CStarAction.IsKMSState.isKMSState_gnsVectorState`: if `ω` is a tracial state, that is
  a `0`-KMS state, then `τ''` is a tracial state of `M`, the *vector trace* of `ω`. Its
  traciality is `PositiveLinearMap.gnsVectorState_mul_comm`, and it has norm `τ''(1) = ω(1) = 1`.

## References

N. P. Brown, *Invariant means and finite representation theory of C⋆-algebras*, Mem. Amer. Math.
Soc. 184 (2006), Chapter 2 and §3.1, for the vector trace of the GNS von Neumann algebra of a
tracial state.
-/

public section

open Complex PositiveLinearMap
open scoped ComplexOrder InnerProductSpace

namespace TauCeti.CStarAction

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {α : CStarAction (Multiplicative ℝ) A} {β : ℝ} {ω : A →P[ℂ] ℂ}

/-- **The GNS vector state of a KMS state is faithful.** For a β-KMS state `ω` of a unital
C⋆-algebra and `x` in the GNS von Neumann algebra, `⟪Ω, x⋆ x Ω⟫ = 0` only for `x = 0`. -/
theorem IsKMSState.gnsVectorState_star_mul_self_eq_zero_iff (hω : α.IsKMSState β ω)
    {x : ω.toPositiveLinearMap.gnsVonNeumannAlgebra.toStarSubalgebra} :
    ω.toPositiveLinearMap.gnsVectorState (star x * x) = 0 ↔ x = 0 := by
  refine ⟨fun hx => Subtype.ext ?_, by rintro rfl; simp⟩
  rw [gnsVectorState_star_mul_self, ofReal_eq_zero, sq_eq_zero_iff, norm_eq_zero,
    gnsVector_def] at hx
  refine hω.eq_zero_of_apply_toPreGNS_one_eq_zero ?_ hx
  rw [← gnsVonNeumannAlgebra_eq_adjoin_range_gnsStarAlgHom]
  exact x.property

/-- **The vector trace.** For a tracial state, that is a `0`-KMS state, `ω` of a unital
C⋆-algebra, the GNS vector state `x ↦ ⟪Ω, x Ω⟫` is a tracial state of the GNS von Neumann algebra
`π_ω(A)''`. Since the `0`-KMS condition does not involve the dynamics, it is a `0`-KMS state for
every action `γ` on `π_ω(A)''`. -/
theorem IsKMSState.isKMSState_gnsVectorState (hω : α.IsKMSState 0 ω)
    {γ : CStarAction (Multiplicative ℝ)
      ω.toPositiveLinearMap.gnsVonNeumannAlgebra.toStarSubalgebra} :
    γ.IsKMSState 0 ω.toPositiveLinearMap.gnsVectorState := by
  refine isKMSState_zero_iff.mpr
    ⟨?_, gnsVectorState_mul_comm _ (isKMSState_zero_iff.mp hω).2⟩
  have h1 := ω.ofReal_opNorm_eq_map_one
  rw [hω.norm_eq_one] at h1
  exact_mod_cast (ofReal_opNorm_gnsVectorState _).trans h1.symm

end TauCeti.CStarAction
