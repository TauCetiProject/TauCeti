/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.SimpleRing.Basic
public import TauCeti.Analysis.CStarAlgebra.Calkin
import Mathlib.RingTheory.SimpleRing.Congr
import TauCeti.Algebra.CentralSimple.End

/-!
# Sanity checks for compact-operator ideals and the Calkin algebra

This file collects concrete typeclass synthesis and specialization checks for
`ContinuousLinearMap.compactIdeal` and `TauCeti.CalkinAlgebra`:
* `↥(compactIdeal ℂ H)` synthesizes `NonUnitalCStarAlgebra` and `CalkinAlgebra H` synthesizes
  `CStarAlgebra`.
* On finite-dimensional complex Euclidean spaces `EuclideanSpace ℂ (Fin d)`, `compactIdeal` is `⊤`,
  the endomorphism algebra has only `⊥` and `⊤` as two-sided ideals, and `CalkinAlgebra` is a
  subsingleton.
* On `ℓ²(ℕ, ℂ)`, `CalkinAlgebra ℓ²(ℕ, ℂ)` synthesizes `IsSimpleRing` with zero hypotheses.
-/

public noncomputable section

open scoped lp

section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

-- Verify that `↥(compactIdeal ℂ H)` automatically carries a `NonUnitalCStarAlgebra` structure.
example : NonUnitalCStarAlgebra ↥(ContinuousLinearMap.compactIdeal ℂ H) := inferInstance

-- Verify that `CalkinAlgebra H` inherits a unital `CStarAlgebra` structure automatically.
example : CStarAlgebra (TauCeti.CalkinAlgebra H) := inferInstance

end

section

/-- On a nontrivial finite-dimensional Hausdorff topological vector space over a complete
nontrivially normed field, the endomorphism ring `V →L[𝕜] V` is simple. -/
local instance instIsSimpleRingContinuousLinearMap {𝕜 V : Type*} [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜] [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [T2Space V]
    [IsTopologicalAddGroup V] [ContinuousSMul 𝕜 V] [FiniteDimensional 𝕜 V] [Nontrivial V] :
    IsSimpleRing (V →L[𝕜] V) := by
  let e : Module.End 𝕜 V ≃+* (V →L[𝕜] V) :=
    { LinearMap.toContinuousLinearMap (𝕜 := 𝕜) (E := V) (F' := V) with
      map_mul' := fun _ _ ↦ rfl }
  exact IsSimpleRing.of_ringEquiv e (IsSimpleRing.moduleEnd_of_field 𝕜 V)

-- Sanity checks on finite-dimensional complex Euclidean spaces.
example (d : ℕ) : ContinuousLinearMap.compactIdeal ℂ (EuclideanSpace ℂ (Fin d)) = ⊤ :=
  ContinuousLinearMap.compactIdeal_eq_top

example (I : TwoSidedIdeal (EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2))) :
    I = ⊥ ∨ I = ⊤ :=
  IsSimpleOrder.eq_bot_or_eq_top I

example (n : Type*) [Fintype n] :
    Subsingleton (TauCeti.CalkinAlgebra (EuclideanSpace ℂ n)) :=
  inferInstance

end

-- Non-vacuity check on `ℓ²(ℕ, ℂ)` with zero hypotheses.
example : IsSimpleRing (TauCeti.CalkinAlgebra ℓ²(ℕ, ℂ)) := inferInstance

end
