/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Independence.InfinitePi

/-!
# Laws and independence on product extensions

When a probability space is extended by an infinite product of probability measures, each new
coordinate has its prescribed law and the coordinates remain mutually independent.
-/

public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

variable {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {E : ι → Type*} [∀ i, MeasurableSpace (E i)]
  (ν : ∀ i, Measure (E i)) [∀ i, IsProbabilityMeasure (ν i)]

/-- Every added coordinate has its prescribed law on the extended product probability space. -/
theorem HasLaw.eval_prod_infinitePi (i : ι) :
    HasLaw (fun z : Ω × (∀ i, E i) => z.2 i) (ν i)
      (P.prod (Measure.infinitePi ν)) :=
  ((measurePreserving_eval_infinitePi ν i).comp measurePreserving_snd).hasLaw

/-- The added coordinates remain mutually independent on the extended product probability space. -/
theorem iIndepFun_eval_prod_infinitePi :
    iIndepFun (fun i (z : Ω × (∀ j, E j)) => z.2 i)
      (P.prod (Measure.infinitePi ν)) := by
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)]
  have hmap :
      (P.prod (Measure.infinitePi ν)).map
          (fun z : Ω × (∀ i, E i) => fun i => z.2 i) =
        Measure.infinitePi ν := by
    simp
  have hcoord (i : ι) :
      (P.prod (Measure.infinitePi ν)).map (fun z : Ω × (∀ j, E j) => z.2 i) = ν i :=
    (HasLaw.eval_prod_infinitePi ν i).map_eq
  rw [hmap]
  simp_rw [hcoord]

end ProbabilityTheory
