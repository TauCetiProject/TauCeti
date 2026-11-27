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
normed space over a complete nontrivially normed field. When that space is second countable, the
points at which such a map takes a value in a countable set and has injective derivative are
therefore countable. This is the Fréchet counterpart of
`TauCeti.countable_setOf_mem_and_deriv_ne_zero` in
`TauCeti.Analysis.Calculus.Deriv.CountableLevels`.

## Main results

* `TauCeti.countable_of_forall_injective_fderiv`: the points at which a map takes a value in a
  countable set and has injective derivative are countable.
-/

public section

open Function Set

namespace TauCeti

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F}

/-- **Points of injective derivative over countably many values are countable.** Let `f` be a map
from a second countable finite-dimensional normed space over a complete nontrivially normed field.
The points at which `f` takes a value in a countable set `C` and has injective Fréchet derivative
form a countable set, since near each of them `f` takes the same value nowhere else. No
differentiability is assumed: where `f` is not differentiable its derivative is zero, which is
injective only on the trivial space. `TauCeti.countable_setOf_mem_and_deriv_ne_zero` is the
one-variable counterpart, phrased with `deriv`. In equal dimensions an injective derivative is
surjective, so together with `TauCeti.dense_setOf_forall_surjective_fderiv` this yields countable
sets of regular values with countable preimages. -/
theorem countable_of_forall_injective_fderiv {C : Set F} {Z : Set E} (hC : C.Countable)
    (hZ : ∀ z ∈ Z, Injective (fderiv 𝕜 f z) ∧ f z ∈ C) :
    Z.Countable := by
  rcases subsingleton_or_nontrivial E with _ | _
  · exact Set.subsingleton_of_subsingleton.countable
  have hsub : Z ⊆ ⋃ c ∈ C, Z ∩ f ⁻¹' {c} := fun z hz ↦
    mem_iUnion₂.2 ⟨f z, (hZ z hz).2, hz, rfl⟩
  refine (hC.biUnion fun c _ ↦ ?_).mono hsub
  refine (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete
    (isDiscrete_iff_nhdsNE.2 fun z hz ↦ Filter.inf_principal_eq_bot.2 ?_)
  obtain ⟨hinj, -⟩ := hZ z hz.1
  have hd : DifferentiableAt 𝕜 f z := by
    by_contra h
    rw [fderiv_zero_of_not_differentiableAt h] at hinj
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    exact hx (hinj (by simp))
  obtain ⟨K, -, hK⟩ :=
    (fderiv 𝕜 f z : E →ₗ[𝕜] F).exists_antilipschitzWith (LinearMap.ker_eq_bot.2 hinj)
  filter_upwards [hd.hasFDerivAt.eventually_ne ⟨K, hK⟩] with w hw hwZ
  exact hw (hwZ.2.trans hz.2.symm)

end TauCeti
