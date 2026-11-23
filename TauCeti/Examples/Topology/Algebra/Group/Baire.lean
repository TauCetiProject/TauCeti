/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Analysis.Real.Cardinality
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Instances.RealVectorSpace
import TauCeti.Topology.Algebra.Group.Baire

/-!
# Counterexample: a discontinuous, non-Borel additive homomorphism `ℝ →+ ℝ`

A `ℚ`-linear coordinate projection along a Hamel basis of `ℝ` over `ℚ` sends one basis vector to `1`
and another distinct basis vector to `0`. Because every continuous additive homomorphism `ℝ →+ ℝ` is
`ℝ`-linear (`map_real_smul`), this homomorphism is not continuous; by Pettis automatic continuity
(`TauCeti.continuous_of_measurable_addMonoidHom`), it is therefore not Borel-measurable either,
showing that the measurability hypothesis in automatic continuity cannot be dropped.

## Main results

* `TauCeti.exists_addMonoidHom_not_continuous_and_not_measurable`: there exists an additive
  homomorphism `ℝ →+ ℝ` that is neither continuous nor Borel-measurable.

## References

* B. J. Pettis, *On continuity and openness of homomorphisms in topological groups*, Ann. of Math.
  (2) **52** (1950), 293–308.
* D. P. Williams, *Crossed Products of C*-Algebras*, Mathematical Surveys and Monographs 134, AMS,
  2007, Remark D.17.
-/

public section

open MeasureTheory

namespace TauCeti

/-- **Measurability cannot be dropped in automatic continuity.** There exists an additive
homomorphism `ℝ →+ ℝ` that is neither continuous nor Borel-measurable. -/
theorem exists_addMonoidHom_not_continuous_and_not_measurable :
    ∃ f : ℝ →+ ℝ, ¬ Continuous f ∧ ¬ Measurable f := by
  let b := Module.Basis.ofVectorSpace ℚ ℝ
  have hnt : Nontrivial (Module.Basis.ofVectorSpaceIndex ℚ ℝ) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have : Countable (Module.Basis.ofVectorSpaceIndex ℚ ℝ →₀ ℚ) :=
      Finsupp.equivFunOnFinite.countable_iff.2 inferInstance
    have hcnt : Countable ℝ := b.repr.toEquiv.countable_iff.2 this
    exact not_countable hcnt
  obtain ⟨i, j, hij⟩ := exists_pair_ne (Module.Basis.ofVectorSpaceIndex ℚ ℝ)
  let L : ℝ →ₗ[ℚ] ℝ := (Algebra.linearMap ℚ ℝ).comp (b.coord i)
  let f : ℝ →+ ℝ := L.toAddMonoidHom
  have hfi : f (b i) = 1 := by
    simp [f, L, Module.Basis.coord_apply, b.repr_self]
  have hfj : f (b j) = 0 := by
    simp [f, L, Module.Basis.coord_apply, b.repr_self, hij.symm]
  have hnc : ¬ Continuous f := fun hc => by
    have hmul : ∀ r y : ℝ, f (r * y) = r * f y := map_real_smul f hc
    have hbj : b j = 0 := by
      calc
        b j = b j * f (b i) := by rw [hfi, mul_one]
        _ = f (b j * b i) := (hmul (b j) (b i)).symm
        _ = f (b i * b j) := by rw [mul_comm]
        _ = b i * f (b j) := hmul (b i) (b j)
        _ = 0 := by rw [hfj, mul_zero]
    exact b.ne_zero j hbj
  exact ⟨f, hnc, fun hm => hnc (continuous_of_measurable_addMonoidHom f hm)⟩

end TauCeti
