/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Dynamics.BirkhoffSum.Semiconj
public import TauCeti.Dynamics.Entropy.Pressure
public import TauCeti.Dynamics.TopologicalEntropy.Semiconj
public import Mathlib.Topology.UniformSpace.Equiv

/-!
# Topological pressure under factors and conjugacies

Let `h : X → Y` semiconjugate `T : X → X` to `S : Y → Y`, that is `h ∘ T = S ∘ h`. If `h` is
surjective, every `(U, n)`-dynamical net of `S` lifts, through a right inverse of `h`, to a
dynamical net of `T` for the pulled-back entourage `Prod.map h h ⁻¹' U`
(`Dynamics.IsDynNetIn.image_of_semiconj`), with the same weights
`exp (birkhoffSum S ψ n y) = exp (birkhoffSum T (ψ ∘ h) n x)`
(`Function.Semiconj.birkhoffSum_comp_apply`). Hence the pressure of a factor is at
most the pressure of the lifted potential, `P(S, ψ) ≤ P(T, ψ ∘ h)`, when `h` is uniformly
continuous and surjective, and pressure is invariant under uniform conjugacy:
`P(S, ψ) = P(T, ψ ∘ e)` for `e : X ≃ᵤ Y` conjugating `T` to `S`.

## Main results

* `TauCeti.pressureNetSum_le_of_semiconj`: comparison of pressure sums.
* `TauCeti.topologicalPressure_le_of_semiconj`: `P(S, ψ) ≤ P(T, ψ ∘ h)` for a uniformly
  continuous surjective semiconjugacy `h`.
* `TauCeti.topologicalPressure_of_semiconj_uniformEquiv`: `P(S, ψ) = P(T, ψ ∘ e)` for a uniform
  conjugacy `e`.

## References

* Peter Walters, *An Introduction to Ergodic Theory*, Graduate Texts in Mathematics 79, Springer,
  1982, Chapter 9 (properties of topological pressure).
-/

public section

namespace TauCeti

open Dynamics Set Function
open scoped Uniformity

variable {X Y : Type*} {T : X → X} {S : Y → Y} {h : X → Y}

/-- If a surjective map `h` semiconjugates `T` to `S`, the pressure sums of `S` and `ψ` at `U` are
at most those of `T` and `ψ ∘ h` at the pulled-back entourage `Prod.map h h ⁻¹' U`. -/
theorem pressureNetSum_le_of_semiconj (hsc : Semiconj h T S) (hs : Surjective h) (ψ : Y → ℝ)
    (U : SetRel Y Y) (n : ℕ) :
    pressureNetSum S ψ U n ≤ pressureNetSum T (ψ ∘ h) (Prod.map h h ⁻¹' U) n := by
  classical
  rw [pressureNetSum_le_iff]
  intro s hs_net
  -- A right inverse of `h` lifts each net of `S` to a net of `T` with the same weights.
  have hhg : RightInverse (surjInv hs) h := rightInverse_surjInv hs
  have hnet := hs_net.image_of_semiconj hsc hhg
  rw [preimage_univ, ← Finset.coe_image] at hnet
  refine le_trans (le_of_eq ?_) hnet.sum_le_pressureNetSum
  rw [Finset.sum_image fun _ _ _ _ h' ↦ hhg.injective h']
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [hsc.birkhoffSum_comp_apply, hhg y]

variable [UniformSpace X] [UniformSpace Y]

/-- **Pressure of a factor.** If a uniformly continuous surjection `h` semiconjugates `T` to `S`,
then `P(S, ψ) ≤ P(T, ψ ∘ h)`. -/
theorem topologicalPressure_le_of_semiconj (hsc : Semiconj h T S) (hs : Surjective h)
    (hh : UniformContinuous h) (ψ : Y → ℝ) :
    topologicalPressure S ψ ≤ topologicalPressure T (ψ ∘ h) := by
  rw [topologicalPressure_le_iff]
  intro U hU
  refine le_trans ?_ (netPressureEntourage_le_topologicalPressure (hh hU))
  rw [netPressureEntourage_def, netPressureEntourage_def]
  exact ExpGrowth.expGrowthSup_monotone fun n ↦ pressureNetSum_le_of_semiconj hsc hs ψ U n

/-- **Conjugacy invariance of pressure.** If a uniform isomorphism `e : X ≃ᵤ Y` conjugates `T` to
`S`, then `P(S, ψ) = P(T, ψ ∘ e)`. -/
theorem topologicalPressure_of_semiconj_uniformEquiv (e : X ≃ᵤ Y) (hsc : Semiconj e T S)
    (ψ : Y → ℝ) : topologicalPressure S ψ = topologicalPressure T (ψ ∘ e) := by
  refine le_antisymm (topologicalPressure_le_of_semiconj hsc e.surjective e.uniformContinuous ψ)
    ?_
  have := topologicalPressure_le_of_semiconj (hsc.inverse_left e.symm_apply_apply
    e.apply_symm_apply) e.symm.surjective e.symm.uniformContinuous (ψ ∘ e)
  rwa [comp_assoc, e.self_comp_symm, comp_id] at this

end TauCeti
