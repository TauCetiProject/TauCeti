/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.RepresentationTheory.Continuous.Subrepresentation

/-!
# Strong continuity of continuous representations

A continuous representation `π` of a topological monoid is *strongly continuous* when every orbit
`g ↦ π g v` is continuous. This is weaker than continuity of `g ↦ π g` into the continuous linear
endomorphisms, which carry the topology of uniform convergence on bounded sets (the operator norm
topology on a normed space): translation by `ℝ` on `L²(ℝ)` is strongly continuous but not
continuous. In finite dimensions the two notions agree, which is how finite-dimensional
pieces of a strongly continuous representation become genuine continuous representations.

## Main results

* `ContRepresentation.continuous_iff_continuous_apply`: a representation on a finite-dimensional
  normed space is continuous exactly when it is strongly continuous.
* `ContRepresentation.continuous_subrepresentation_apply` and
  `ContRepresentation.continuous_quotient_apply`: restriction to an invariant submodule and descent
  to the quotient by it preserve strong continuity.
* `ContRepresentation.Equiv.continuous_iff`: equivalent representations are continuous together.
-/

public section

namespace ContRepresentation

section FiniteDimensional

variable {𝕜 G V : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [Monoid G]
  [TopologicalSpace G] [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]

/-- **Strong continuity is continuity in finite dimensions.** A representation on a
finite-dimensional normed space is continuous for the operator norm exactly when every orbit
`g ↦ π g v` is continuous. This is `continuous_clm_apply` for the action map. -/
theorem continuous_iff_continuous_apply {π : ContRepresentation 𝕜 G V} :
    Continuous π ↔ ∀ v, Continuous fun g ↦ π g v :=
  continuous_clm_apply

end FiniteDimensional

section StrongContinuity

variable {R G V : Type*} [Ring R] [Monoid G] [TopologicalSpace G] [AddCommGroup V]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [Module R V]
  {π : ContRepresentation R G V} {W : Submodule R V} {hW : ∀ g, ∀ v ∈ W, π g v ∈ W}

/-- Restricting a strongly continuous representation to an invariant submodule gives a strongly
continuous representation. -/
theorem continuous_subrepresentation_apply (hπ : ∀ v, Continuous fun g ↦ π g v) (w : W) :
    Continuous fun g ↦ subrepresentation π W hW g w := by
  rw [Topology.IsInducing.subtypeVal.continuous_iff]
  simpa only [Function.comp_def, coe_subrepresentation_apply] using hπ w

/-- Descending a strongly continuous representation to the quotient by an invariant submodule
gives a strongly continuous representation. -/
theorem continuous_quotient_apply (hπ : ∀ v, Continuous fun g ↦ π g v) (x : V ⧸ W) :
    Continuous fun g ↦ quotient π W hW g x := by
  obtain ⟨v, rfl⟩ := W.mkQ_surjective x
  simp only [Submodule.mkQ_apply, quotient_apply_mk]
  exact W.mkQL.continuous.comp (hπ v)

end StrongContinuity

section Equiv

variable {𝕜 G V W : Type*} [NormedField 𝕜] [Monoid G] [TopologicalSpace G]
  [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [Module 𝕜 V]
  [ContinuousConstSMul 𝕜 V] [AddCommGroup W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  [Module 𝕜 W] [ContinuousConstSMul 𝕜 W]
  {ρ : ContRepresentation 𝕜 G V} {σ : ContRepresentation 𝕜 G W}

omit [TopologicalSpace G] [ContinuousConstSMul 𝕜 V] [ContinuousConstSMul 𝕜 W] in
/-- An equivalence of representations conjugates each action operator of one into the other. -/
theorem Equiv.symm_comp_comp (φ : ρ.Equiv σ) (g : G) :
    φ.symm.toContinuousLinearMap ∘L σ g ∘L φ.toContinuousLinearMap = ρ g := by
  ext v
  have h := φ.toContIntertwiningMap.isIntertwining g v
  simp only [Equiv.coe_toContIntertwiningMap] at h
  simp [Equiv.toContinuousLinearEquiv_apply, ← h]

/-- **Equivalent representations are continuous together.** Each action operator of `ρ` is the
conjugate `φ⁻¹ ∘ σ g ∘ φ` of the corresponding one of `σ`, and composition with a fixed continuous
linear map is continuous on the space of continuous linear maps. -/
theorem Equiv.continuous_iff (φ : ρ.Equiv σ) : Continuous ρ ↔ Continuous σ := by
  refine ⟨fun hρ ↦ ?_, fun hσ ↦ ?_⟩
  · have h : Continuous fun g ↦
        φ.symm.symm.toContinuousLinearMap ∘L ρ g ∘L φ.symm.toContinuousLinearMap :=
      (ContinuousLinearMap.postcomp W _).continuous.comp
        ((ContinuousLinearMap.precomp V _).continuous.comp hρ)
    simpa only [φ.symm.symm_comp_comp] using h
  · have h : Continuous fun g ↦ φ.symm.toContinuousLinearMap ∘L σ g ∘L φ.toContinuousLinearMap :=
      (ContinuousLinearMap.postcomp V _).continuous.comp
        ((ContinuousLinearMap.precomp W _).continuous.comp hσ)
    simpa only [φ.symm_comp_comp] using h

end Equiv

end ContRepresentation
