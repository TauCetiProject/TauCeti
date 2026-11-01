/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.FiniteDimension
public import TauCeti.LinearAlgebra.TotallyReal.Maslov.Phase

/-!
# Continuity of the Maslov phase along continuous frames

The Maslov phase `ρ(L₀, Λ x) = ρ(L₀, L₁) · det(A x) / conj (det A x)` relative to a fixed
maximal totally real subspace `L₀` varies continuously along any continuous frame
`x ↦ A x L₁` of maximal totally real subspaces over a topological space `X`
(`TauCeti.IsMaximalTotallyReal.continuous_maslovPhase_of_frame`), where `ρ` is
`TauCeti.IsMaximalTotallyReal.maslovPhase`. The lemma constructs continuous circle-valued phase
maps from families of maximal totally real subspaces that admit continuous frames, covering in
particular paths and loops of frames.

The loop and path theorems in `TauCeti.LinearAlgebra.TotallyReal.Maslov.Index` and
`TauCeti.LinearAlgebra.TotallyReal.Maslov.Path` are specializations to the parameter spaces
`[0, 1]`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix C.3.
-/

public section

open scoped ComplexConjugate

namespace TauCeti

namespace IsMaximalTotallyReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- The Maslov phase relative to a fixed maximal totally real subspace varies continuously along
any continuous frame `x ↦ A x L₁` of maximal totally real subspaces over a topological space
`X`. -/
theorem continuous_maslovPhase_of_frame {X : Type*} [TopologicalSpace X]
    {L₀ L₁ : Submodule ℝ E}
    (hL₀ : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L₀)
    (hL₁ : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L₁)
    {Λ : X → Submodule ℝ E}
    (hΛ : ∀ x, IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) (Λ x))
    {A : X → E ≃L[ℂ] E} (hAc : Continuous fun x => (A x : E →L[ℂ] E))
    (hA : ∀ x, Λ x = L₁.map (((A x).toLinearEquiv : E →ₗ[ℂ] E).restrictScalars ℝ)) :
    Continuous fun x => hL₀.maslovPhase (hΛ x) := by
  have hphase (x : X) : hL₀.maslovPhase (hΛ x) =
      hL₀.maslovPhase hL₁ * (LinearMap.det ((A x).toLinearEquiv : E →ₗ[ℂ] E) /
        conj (LinearMap.det ((A x).toLinearEquiv : E →ₗ[ℂ] E))) := by
    rw [← hL₀.maslovPhase_mul_maslovPhase hL₁ (hΛ x),
      hL₁.maslovPhase_congr (hΛ x)
        (hL₁.map_linearEquiv (A x).toLinearEquiv) (hA x),
      IsMaximalTotallyReal.maslovPhase_map]
  simp_rw [hphase]
  exact continuous_const.mul (continuous_det_div_conj A hAc)

end IsMaximalTotallyReal

end TauCeti
