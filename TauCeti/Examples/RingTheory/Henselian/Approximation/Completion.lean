/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Henselian.Approximation.Completion
import Mathlib.Tactic.NormNum

/-!
# Checks for the `(t, I)`-adic completion

The unit-parameter completion kills `I` immediately, while the principal adic
completion retains elements visible in a deeper residue. These examples also
exercise the zero-ideal case and the inverse-limit mapping property.
-/

open TauCeti.HenselianApproximation

namespace TauCeti.Examples.HenselianApproximation

variable {R : Type*} [CommRing R]

/-- The completion needs neither completeness nor separatedness of the original ring. -/
example (t : R) (I : Ideal R) :
    CompleteSpace (completion t I) ∧ T2Space (completion t I) ∧
      IsTopologicalRing (completion t I) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- `topology_adic_agreement`: the total ideal gives the ordinary principal adic topology. -/
example (t : R) : ringTopology t (⊤ : Ideal R) = (Ideal.span {t}).adicTopology :=
  ringTopology_top t

/-- `topology_zero_ideal`: the zero ideal gives the discrete topology. -/
example (t : R) : ringTopology t (⊥ : Ideal R) = ⊥ := by simp

/-- `completion_zero_ideal`: no elements are lost or added, for any parameter. -/
example (t : R) : Function.Bijective (completionMap t (⊥ : Ideal R)) :=
  completionMap_bot_bijective t

/-- `completion_unit_parameter`: the actual completion is the quotient, with its specified map. -/
example (I : Ideal R) (a : R) :
    completionOneEquiv I (completionMap 1 I a) = Ideal.Quotient.mk I a := by simp

/-- `henselian_completion_test_unit_parameter`: the unit-parameter kernel is exactly `I`. -/
example (I : Ideal R) : RingHom.ker (completionMap 1 I) = I := by
  simp [ker_completionMap]

/-- `henselian_completion_test_distinct_filtrations`: 3 vanishes for parameter 1 and ideal (3). -/
example : completionMap (1 : ℤ) (Ideal.span {3}) 3 = 0 := by
  apply (completionOneEquiv (Ideal.span {3})).injective
  simp only [completionOneEquiv_completionMap, map_zero]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

/-- The same integer survives for parameter 3 and the total ideal, as witnessed modulo 9. -/
example : completionMap (3 : ℤ) ⊤ 3 ≠ 0 := by
  intro h
  have hm : (3 : ℤ) ∈ filtrationIdeal 3 ⊤ 2 :=
    (residueMap_eq_zero_iff 3 ⊤ 2 3).mp (by
      simpa only [eval_completionMap, map_zero] using congrArg (eval 3 ⊤ 2) h)
  norm_num [filtrationIdeal_def, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hm

/-- The inverse-limit lift recovers completion of an element from its residue maps. -/
example (t : R) (I : Ideal R) :
    lift t I (residueMap t I)
      (fun _ _ _ ↦ by ext; simp) = completionMap t I := by
  apply completion_hom_ext
  intro n
  ext a
  simp

/-- Density does not impose separatedness: this canonical map kills the nonzero integer 3. -/
example : DenseRange (completionMap (1 : ℤ) (Ideal.span {3})) ∧
    ¬ Function.Injective (completionMap (1 : ℤ) (Ideal.span {3})) := by
  refine ⟨denseRange_completionMap 1 _, fun h ↦ ?_⟩
  have hzero : completionMap (1 : ℤ) (Ideal.span {3}) 3 = 0 :=
    RingHom.mem_ker.mp (by simp [ker_completionMap])
  have : (3 : ℤ) = 0 := h (hzero.trans (map_zero _).symm)
  norm_num at this

end TauCeti.Examples.HenselianApproximation
