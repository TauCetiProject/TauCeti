/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.DiscreteSubset

/-!
# Fréchet derivatives on countably many levels

An injective Fréchet derivative isolates a point of a level set of a map from a finite-dimensional
real normed space. The points at which such a map takes a value in a countable set and has
injective derivative are therefore countable. This is the Fréchet counterpart of
`TauCeti.countable_setOf_mem_and_deriv_ne_zero` in
`TauCeti.Analysis.Calculus.Deriv.CountableLevels`.

## Main results

* `TauCeti.countable_of_forall_injective_fderiv`: the points at which a map takes a value in a
  countable set and has injective derivative are countable.
-/

public section

open Function Set

namespace TauCeti

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}

/-- **Points of injective derivative over countably many values are countable.** Let `f` be a map
from a finite-dimensional real normed space. The points at which `f` takes a value in a countable
set `C` and has injective Fréchet derivative form a countable set, since near each of them `f`
takes the same value nowhere else; `TauCeti.countable_setOf_mem_and_deriv_ne_zero` is the case of
a map on a field. In equal dimensions an injective derivative is surjective, so together with
`TauCeti.dense_setOf_forall_surjective_fderiv` this yields countable sets of regular values with
countable preimages. -/
theorem countable_of_forall_injective_fderiv {C : Set F} {Z : Set E} (hC : C.Countable)
    (hZ : ∀ z ∈ Z, DifferentiableAt ℝ f z ∧ Injective (fderiv ℝ f z) ∧ f z ∈ C) :
    Z.Countable := by
  have hsub : Z ⊆ ⋃ c ∈ C, Z ∩ f ⁻¹' {c} := fun z hz ↦
    mem_iUnion₂.2 ⟨f z, (hZ z hz).2.2, hz, rfl⟩
  refine (hC.biUnion fun c _ ↦ ?_).mono hsub
  refine (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete
    (isDiscrete_iff_nhdsNE.2 fun z hz ↦ Filter.inf_principal_eq_bot.2 ?_)
  obtain ⟨hd, hinj, -⟩ := hZ z hz.1
  obtain ⟨K, -, hK⟩ :=
    (fderiv ℝ f z : E →ₗ[ℝ] F).exists_antilipschitzWith (LinearMap.ker_eq_bot.2 hinj)
  filter_upwards [hd.hasFDerivAt.eventually_ne ⟨K, hK⟩] with w hw hwZ
  exact hw (hwZ.2.trans hz.2.symm)

end TauCeti
