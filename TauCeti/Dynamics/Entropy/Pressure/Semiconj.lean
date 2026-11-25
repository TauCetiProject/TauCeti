/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Dynamics.Entropy.Pressure
public import Mathlib.Topology.UniformSpace.Equiv

/-!
# Topological pressure under factors and conjugacies

Let `h : X → Y` semiconjugate `T : X → X` to `S : Y → Y`, that is `h ∘ T = S ∘ h`. If `h` is
surjective, every `(U, n)`-dynamical net of `S` lifts, through a right inverse of `h`, to a
dynamical net of `T` for the pulled-back entourage `Prod.map h h ⁻¹' U`, with the same weights
`exp (birkhoffSum S ψ n y) = exp (birkhoffSum T (ψ ∘ h) n x)`. Hence the pressure of a factor is at
most the pressure of the lifted potential, `P(S, ψ) ≤ P(T, ψ ∘ h)`, when `h` is uniformly
continuous and surjective, and pressure is invariant under uniform conjugacy:
`P(S, ψ) = P(T, ψ ∘ e)` for `e : X ≃ᵤ Y` conjugating `T` to `S`.

## Main results

* `TauCeti.birkhoffSum_comp_of_semiconj`: Birkhoff sums of `ψ ∘ h` along `T` are Birkhoff sums of
  `ψ` along `S`.
* `TauCeti.pressureNetSum_le_of_semiconj`: comparison of pressure sums.
* `TauCeti.topologicalPressure_le_of_semiconj`: `P(S, ψ) ≤ P(T, ψ ∘ h)` for a uniformly
  continuous surjective semiconjugacy `h`.
* `TauCeti.topologicalPressure_of_semiconj_uniformEquiv`: `P(S, ψ) = P(T, ψ ∘ e)` for a uniform
  conjugacy `e`.

## References

This is item 6 of §5.4 of the Tau Ceti roadmap `ClassicalErgodicTheory`.
-/

public section

namespace TauCeti

open Dynamics Set Function
open scoped Uniformity

variable {X Y : Type*} {T : X → X} {S : Y → Y} {h : X → Y}

/-- If `h` semiconjugates `T` to `S`, the Birkhoff sums of `ψ ∘ h` along `T` are the Birkhoff sums
of `ψ` along `S` at the image point. -/
theorem birkhoffSum_comp_of_semiconj (hsc : Semiconj h T S) (ψ : Y → ℝ) (n : ℕ) (x : X) :
    birkhoffSum T (ψ ∘ h) n x = birkhoffSum S ψ n (h x) :=
  Finset.sum_congr rfl fun k _ ↦ by rw [comp_apply, (hsc.iterate_right k) x]

/-- If a surjective map `h` semiconjugates `T` to `S`, the pressure sums of `S` and `ψ` at `U` are
at most those of `T` and `ψ ∘ h` at the pulled-back entourage `Prod.map h h ⁻¹' U`: a right inverse
of `h` lifts dynamical nets of `S` to dynamical nets of `T` with the same weights. -/
theorem pressureNetSum_le_of_semiconj (hsc : Semiconj h T S) (hs : Surjective h) (ψ : Y → ℝ)
    (U : SetRel Y Y) (n : ℕ) :
    pressureNetSum S ψ U n ≤ pressureNetSum T (ψ ∘ h) (Prod.map h h ⁻¹' U) n := by
  classical
  rw [pressureNetSum_le_iff]
  intro s hs_net
  set g := surjInv hs
  have hg : Injective g := injective_surjInv hs
  have hhg : ∀ y, h (g y) = y := surjInv_eq hs
  have hnet : IsDynNetIn T univ (Prod.map h h ⁻¹' U) n (s.image g) := by
    refine ⟨subset_univ _, fun x₁ hx₁ x₂ hx₂ hne ↦ ?_⟩
    simp only [Finset.coe_image, mem_image, Finset.mem_coe] at hx₁ hx₂
    obtain ⟨y₁, hy₁, rfl⟩ := hx₁
    obtain ⟨y₂, hy₂, rfl⟩ := hx₂
    have hne' : y₁ ≠ y₂ := fun h' ↦ hne (congrArg g h')
    have hdisj := hs_net.2 hy₁ hy₂ hne'
    rw [Function.onFun, ← hsc.preimage_dynEntourage]
    refine Set.disjoint_left.mpr fun z hz₁ hz₂ ↦ Set.disjoint_left.mp hdisj
      (show h z ∈ _ by simpa [SetRel.mem_ball, hhg] using hz₁) ?_
    simpa [SetRel.mem_ball, hhg] using hz₂
  refine le_trans (le_of_eq ?_) hnet.sum_le_pressureNetSum
  rw [Finset.sum_image fun _ _ _ _ h' ↦ hg h']
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [birkhoffSum_comp_of_semiconj hsc, hhg]

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
  have hsc' : Semiconj e.symm S T := fun y ↦ by
    apply e.injective
    rw [e.apply_symm_apply, hsc, e.apply_symm_apply]
  have := topologicalPressure_le_of_semiconj hsc' e.symm.surjective e.symm.uniformContinuous
    (ψ ∘ e)
  rwa [comp_assoc, show (e : X → Y) ∘ e.symm = id from funext e.apply_symm_apply,
    comp_id] at this

end TauCeti
