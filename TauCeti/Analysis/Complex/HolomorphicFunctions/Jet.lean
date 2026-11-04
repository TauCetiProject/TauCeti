/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.HolomorphicFunctions.Basic
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Finite jets of holomorphic functions

The first `n` derivatives at a point give a linear map from holomorphic functions on an
open domain to `Fin n → ℂ`. Its kernel consists of functions vanishing to order at least
`n`, and has finite codimension. These kernels let one impose finitely many local conditions
before estimating restriction to a smaller domain.

The derivative criterion for vanishing order is Mathlib's
`natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero`.
-/

public noncomputable section

open Filter Topology TopologicalSpace

namespace TauCeti.HolomorphicFunctions

/-- Fix the inherited additive group before forming submodules, so quotients use its
additive-monoid projection instead of independently inferring the subalgebra's additive monoid. -/
local instance (U : Opens ℂ) : AddCommGroup (holomorphicFunctions U) := inferInstance

variable {U : Opens ℂ} {a : ℂ}

/-- The first `n` derivatives at a point of an open domain, without factorial normalization.
The zeroth derivative is the value of the function. -/
def jet (ha : a ∈ U) (n : ℕ) : holomorphicFunctions U →ₗ[ℂ] (Fin n → ℂ) where
  toFun f i := iteratedDeriv i (extend f) a
  map_add' f g := by
    funext i
    have he : extend (f + g) =ᶠ[𝓝 a] extend f + extend g := by
      filter_upwards [U.isOpen.mem_nhds ha] with z hz
      simp [extend_apply _ ⟨z, hz⟩, Subalgebra.coe_add]
    rw [he.iteratedDeriv_eq, iteratedDeriv_add
      ((analyticOnNhd_extend (Set.Subset.refl _) f) a ha).contDiffAt
      ((analyticOnNhd_extend (Set.Subset.refl _) g) a ha).contDiffAt]
    rfl
  map_smul' c f := by
    funext i
    have he : extend (c • f) =ᶠ[𝓝 a] c • extend f := by
      filter_upwards [U.isOpen.mem_nhds ha] with z hz
      simp [extend_apply _ ⟨z, hz⟩]
    rw [he.iteratedDeriv_eq, iteratedDeriv_const_smul_field]
    rfl

/-- A jet is computed using any ambient holomorphic representative. -/
@[simp]
theorem jet_of (ha : a ∈ U) (n : ℕ) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U)
    (i : Fin n) : jet ha n (of U f hf) i = iteratedDeriv i f a := by
  apply Filter.EventuallyEq.iteratedDeriv_eq
  filter_upwards [U.isOpen.mem_nhds ha] with z hz
  exact (extend_apply _ ⟨z, hz⟩).trans (of_apply f hf ⟨z, hz⟩)

/-- The components of a jet are the iterated derivatives of the zero extension. -/
theorem jet_apply (ha : a ∈ U) (n : ℕ) (f : holomorphicFunctions U) (i : Fin n) :
    jet ha n f i = iteratedDeriv i (extend f) a := (rfl)

/-- The `n`-jet vanishes exactly when the function has vanishing order at least `n`. -/
@[simp]
theorem jet_eq_zero_iff (ha : a ∈ U) (n : ℕ) (f : holomorphicFunctions U) :
    jet ha n f = 0 ↔ (n : ℕ∞) ≤ analyticOrderAt (extend f) a := by
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
    ((analyticOnNhd_extend (Set.Subset.refl _) f) a ha)]
  simp [funext_iff, Fin.forall_iff, jet_apply]

/-- Passing to a smaller open neighbourhood does not change the jet. -/
@[simp]
theorem jet_restrict {V : Opens ℂ} (h : V ≤ U) (ha : a ∈ V) (n : ℕ)
    (f : holomorphicFunctions U) : jet ha n (restrict h f) = jet (h ha) n f := by
  funext i
  apply Filter.EventuallyEq.iteratedDeriv_eq
  filter_upwards [V.isOpen.mem_nhds ha] with z hz
  simp only [extend_apply _ ⟨z, hz⟩, restrict_apply, extend_apply _ ⟨z, h hz⟩]

/-- The kernel of a finite jet has finite codimension, even though the space of holomorphic
functions need not be finite dimensional. -/
instance finiteDimensional_quotient_ker_jet (ha : a ∈ U) (n : ℕ) :
    FiniteDimensional ℂ (holomorphicFunctions U ⧸ (jet ha n).ker) :=
  FiniteDimensional.of_injective (jet ha n).quotKerEquivRange.toLinearMap
    (jet ha n).quotKerEquivRange.injective

/-- Imposing the first `n` vanishing derivatives imposes at most `n` independent conditions. -/
theorem finrank_quotient_ker_jet_le (ha : a ∈ U) (n : ℕ) :
    Module.finrank ℂ (holomorphicFunctions U ⧸ (jet ha n).ker) ≤ n := by
  rw [(jet ha n).quotKerEquivRange.finrank_eq]
  simpa using Submodule.finrank_le (jet ha n).range

end TauCeti.HolomorphicFunctions
