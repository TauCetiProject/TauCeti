/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.InnerProductSpace.LaxMilgram

/-!
# Existence and uniqueness form of Lax--Milgram

Mathlib's Lax--Milgram theorem is packaged as
`IsCoercive.continuousLinearEquivOfBilin`: a coercive continuous bilinear form
`B : V →L[ℝ] V →L[ℝ] ℝ` induces a continuous linear equivalence `V ≃L[ℝ] V` sending
`u` to the Riesz representative of the functional `v ↦ B u v`.

The PDE roadmap's energy-method lane needs the corresponding variational-solution API:
given a represented forcing functional `v ↦ ⟪F, v⟫`, there is a unique `u` satisfying
`B u v = ⟪F, v⟫` for every test vector `v`.  This file records that direct
existence/uniqueness form without changing Mathlib's theorem or introducing any PDE-specific
bundled structure.

## Main declarations

* `IsCoercive.solutionOfInner`: the solution of the variational equation with forcing
  represented by `F`.
* `IsCoercive.solutionOfInner_spec`: the defining variational identity.
* `IsCoercive.eq_solutionOfInner`: uniqueness of a vector satisfying the variational
  identity.
* `IsCoercive.existsUnique_forall_eq_inner`: the combined existence-and-uniqueness theorem.
* `IsCoercive.solutionOfFunctional` and `IsCoercive.existsUnique_forall_eq`: the same API
  for an arbitrary continuous linear functional, using Fréchet--Riesz representation.

The proof is a thin wrapper around Mathlib's `IsCoercive.continuousLinearEquivOfBilin` and
its characteristic identity.
-/

public section

noncomputable section

namespace TauCeti

open scoped InnerProductSpace

namespace IsCoercive

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable {B : V →L[ℝ] V →L[ℝ] ℝ}

/-- The solution supplied by Lax--Milgram for a represented forcing functional.

For `F : V`, `solutionOfInner hB F` is the unique vector `u` satisfying
`B u v = ⟪F, v⟫` for every `v`. -/
def solutionOfInner (hB : IsCoercive B) (F : V) : V :=
  hB.continuousLinearEquivOfBilin.symm F

/-- The Lax--Milgram solution satisfies the variational equation. -/
@[simp]
theorem solutionOfInner_spec (hB : IsCoercive B) (F v : V) :
    B (solutionOfInner hB F) v = ⟪F, v⟫_ℝ := by
  rw [← hB.continuousLinearEquivOfBilin_apply]
  simp [solutionOfInner]

/-- A vector satisfying the represented variational equation is the Lax--Milgram solution. -/
theorem eq_solutionOfInner (hB : IsCoercive B) {F u : V}
    (hu : ∀ v : V, B u v = ⟪F, v⟫_ℝ) :
    u = solutionOfInner hB F := by
  apply hB.continuousLinearEquivOfBilin.injective
  apply ext_inner_right ℝ
  intro v
  rw [hB.continuousLinearEquivOfBilin_apply, hu]
  simp [solutionOfInner]

/-- Lax--Milgram as an existence-and-uniqueness theorem for represented functionals.

If `B` is coercive, then for every `F : V` there is a unique `u` such that
`B u v = ⟪F, v⟫` for all test vectors `v`. -/
theorem existsUnique_forall_eq_inner (hB : IsCoercive B) (F : V) :
    ∃! u : V, ∀ v : V, B u v = ⟪F, v⟫_ℝ :=
  ⟨solutionOfInner hB F, solutionOfInner_spec hB F,
    fun _ hu => eq_solutionOfInner hB hu⟩

/-- Lax--Milgram as an existence theorem for represented functionals. -/
theorem exists_forall_eq_inner (hB : IsCoercive B) (F : V) :
    ∃ u : V, ∀ v : V, B u v = ⟪F, v⟫_ℝ :=
  (existsUnique_forall_eq_inner hB F).exists

/-- The Lax--Milgram solution for an arbitrary continuous linear functional.

This is `solutionOfInner` applied to the Fréchet--Riesz representative of the functional. -/
def solutionOfFunctional (hB : IsCoercive B) (ℓ : StrongDual ℝ V) : V :=
  solutionOfInner hB ((InnerProductSpace.toDual ℝ V).symm ℓ)

/-- The Lax--Milgram solution for a continuous linear functional satisfies the variational
equation. -/
@[simp]
theorem solutionOfFunctional_spec (hB : IsCoercive B) (ℓ : StrongDual ℝ V) (v : V) :
    B (solutionOfFunctional hB ℓ) v = ℓ v := by
  rw [solutionOfFunctional, solutionOfInner_spec, InnerProductSpace.toDual_symm_apply]

/-- A vector satisfying the variational equation for a continuous linear functional is the
Lax--Milgram solution for that functional. -/
theorem eq_solutionOfFunctional (hB : IsCoercive B) {ℓ : StrongDual ℝ V} {u : V}
    (hu : ∀ v : V, B u v = ℓ v) :
    u = solutionOfFunctional hB ℓ := by
  apply eq_solutionOfInner hB
  intro v
  rw [hu, InnerProductSpace.toDual_symm_apply]

/-- Lax--Milgram as an existence-and-uniqueness theorem for arbitrary continuous linear
functionals. -/
theorem existsUnique_forall_eq (hB : IsCoercive B) (ℓ : StrongDual ℝ V) :
    ∃! u : V, ∀ v : V, B u v = ℓ v :=
  ⟨solutionOfFunctional hB ℓ, solutionOfFunctional_spec hB ℓ,
    fun _ hu => eq_solutionOfFunctional hB hu⟩

/-- Lax--Milgram as an existence theorem for arbitrary continuous linear functionals. -/
theorem exists_forall_eq (hB : IsCoercive B) (ℓ : StrongDual ℝ V) :
    ∃ u : V, ∀ v : V, B u v = ℓ v :=
  (existsUnique_forall_eq hB ℓ).exists

end IsCoercive

end TauCeti
