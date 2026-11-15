/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.LyapunovSchmidt
import TauCeti.Analysis.Normed.Module.ContinuousInverse

/-!
# Continuity of the Lyapunov–Schmidt projections of a family of operators

Let `L(σ) : X →L[𝕜] Y` and `P(σ) : Y →L[𝕜] Z` be families of continuous linear maps between
normed spaces, depending on a parameter `σ` in a topological space, with `X` complete. At a
parameter where `P(σ) L(σ)` is invertible and both families are continuous, the
Lyapunov–Schmidt projections `Π_σ = id - L(σ) (P(σ) L(σ))⁻¹ P(σ)`
(`ContinuousLinearMap.lyapunovSchmidtProj`) depend continuously on `σ`
(`ContinuousAt.lyapunovSchmidtProj`, with `ContinuousWithinAt`, `ContinuousOn` and `Continuous`
variants). Invertibility of `P(σ) L(σ)` itself persists near such a parameter, by
`(hP.clm_comp hL).eventually h.eventually_nhds`.
-/

public section

open ContinuousLinearMap Set

variable {𝕜 E X Y Z : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace E]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X] [SeminormedAddCommGroup Y]
  [NormedSpace 𝕜 Y] [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
  {L : E → X →L[𝕜] Y} {P : E → Y →L[𝕜] Z} {s : Set E} {σ : E}

/-- The Lyapunov–Schmidt projections of families `L` and `P` continuous within `s` at `σ` are
continuous within `s` at `σ`, if `P(σ) L(σ)` is invertible. -/
@[fun_prop]
theorem ContinuousWithinAt.lyapunovSchmidtProj (hL : ContinuousWithinAt L s σ)
    (hP : ContinuousWithinAt P s σ) (h : (P σ ∘L L σ).IsInvertible) :
    ContinuousWithinAt (fun σ => (L σ).lyapunovSchmidtProj (P σ)) s σ := by
  simp only [lyapunovSchmidtProj_def]
  exact continuousWithinAt_const.sub (hL.clm_comp (((hP.clm_comp hL).clm_inverse h).clm_comp hP))

/-- The Lyapunov–Schmidt projections of families `L` and `P` continuous at `σ` are continuous at
`σ`, if `P(σ) L(σ)` is invertible. -/
@[fun_prop]
theorem ContinuousAt.lyapunovSchmidtProj (hL : ContinuousAt L σ) (hP : ContinuousAt P σ)
    (h : (P σ ∘L L σ).IsInvertible) :
    ContinuousAt (fun σ => (L σ).lyapunovSchmidtProj (P σ)) σ :=
  (continuousWithinAt_univ _ _).1 <|
    hL.continuousWithinAt.lyapunovSchmidtProj hP.continuousWithinAt h

/-- The Lyapunov–Schmidt projections of families `L` and `P` continuous on `s` are continuous on
`s`, if `P(σ) L(σ)` is invertible for every `σ ∈ s`. -/
@[fun_prop]
theorem ContinuousOn.lyapunovSchmidtProj (hL : ContinuousOn L s) (hP : ContinuousOn P s)
    (h : ∀ σ ∈ s, (P σ ∘L L σ).IsInvertible) :
    ContinuousOn (fun σ => (L σ).lyapunovSchmidtProj (P σ)) s :=
  fun σ hσ => (hL σ hσ).lyapunovSchmidtProj (hP σ hσ) (h σ hσ)

/-- The Lyapunov–Schmidt projections of continuous families `L` and `P` are continuous, if
`P(σ) L(σ)` is invertible for every `σ`. -/
@[fun_prop]
theorem Continuous.lyapunovSchmidtProj (hL : Continuous L) (hP : Continuous P)
    (h : ∀ σ, (P σ ∘L L σ).IsInvertible) :
    Continuous (fun σ => (L σ).lyapunovSchmidtProj (P σ)) :=
  continuous_iff_continuousAt.2 fun σ => hL.continuousAt.lyapunovSchmidtProj hP.continuousAt (h σ)
