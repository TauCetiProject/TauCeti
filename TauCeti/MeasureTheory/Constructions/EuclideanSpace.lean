/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Map

/-!
# Measurable sets and measures on Euclidean space

A coordinate box `{x | ∀ i, x i ∈ s i}` with measurable sides is a measurable subset of
`EuclideanSpace ℝ ι` for a countable index type `ι`.

Over a one-element index type `ι`, reading off the unique coordinate and including it back with
`EuclideanSpace.single` are inverse to each other. So every measure on `EuclideanSpace ℝ ι` is the
image of its law on the unique coordinate under `EuclideanSpace.single default`. This reduces a
one-dimensional identification of a law on `EuclideanSpace ℝ ι` to its coordinate marginal.

With at least two coordinates, the points `x` whose coordinate line in the `i`-th direction passes
through a given point `c` form the line `c + ℝ eᵢ`, a translate of a proper subspace, hence a
null set.

## Main results

* `EuclideanSpace.measurableSet_setOf_forall_mem`: a coordinate box with measurable sides is
  measurable.
* `EuclideanSpace.measurable_single`: the inclusion of one coordinate is measurable.
* `EuclideanSpace.map_single_map_eval`: over a one-element index type, a measure is the image of
  its coordinate law under `EuclideanSpace.single default`.
* `EuclideanSpace.volume_setOf_forall_ne_eq_zero`: with at least two coordinates, the coordinate
  line `{x | ∀ j ≠ i, x j = c j}` is a null set.
-/

public section

open MeasureTheory

namespace EuclideanSpace

/-- A coordinate box `{x | ∀ i, x i ∈ s i}` with measurable sides `s i` is measurable. -/
theorem measurableSet_setOf_forall_mem {ι : Type*} [Countable ι] {s : ι → Set ℝ}
    (hs : ∀ i, MeasurableSet (s i)) : MeasurableSet {x : EuclideanSpace ℝ ι | ∀ i, x i ∈ s i} := by
  rw [Set.ofPred_forall]
  exact MeasurableSet.iInter fun i ↦ (PiLp.continuous_apply 2 _ i).measurable (hs i)

variable {ι : Type*} [DecidableEq ι]

/-- The inclusion `EuclideanSpace.single i` of the `i`-th coordinate is measurable. -/
theorem measurable_single (i : ι) :
    Measurable (EuclideanSpace.single i : ℝ → EuclideanSpace ℝ ι) := by
  -- `EuclideanSpace.single` is `toLp` applied to `Pi.single`.
  have h (a : ℝ) : EuclideanSpace.single i a =
      WithLp.toLp 2 (Pi.single (M := fun _ : ι => ℝ) i a) :=
    (PiLp.toLp_single 2 (β := fun _ : ι => ℝ) i a).symm
  rw [funext h]
  exact (WithLp.measurable_toLp 2 _).comp (measurable_update (0 : ι → ℝ) (a := i))

/-- **A measure on one-dimensional Euclidean space is determined by its coordinate law.** Over a
one-element index type, pushing a measure forward to the unique coordinate and back along
`EuclideanSpace.single default` returns the measure. -/
theorem map_single_map_eval [Unique ι] (μ : Measure (EuclideanSpace ℝ ι)) :
    (μ.map fun x => x default).map (EuclideanSpace.single default) = μ := by
  have hcomp : (EuclideanSpace.single (default : ι)) ∘
      (fun x : EuclideanSpace ℝ ι => x default) = id := by
    funext x
    ext i
    simp [Unique.eq_default i]
  rw [Measure.map_map (measurable_single default) (by fun_prop), hcomp, Measure.map_id]

omit [DecidableEq ι] in
/-- With at least two coordinates, the points `x` whose coordinate line in the `i`-th direction
passes through `c`, those with `x j = c j` for every `j ≠ i`, form a null set. -/
theorem volume_setOf_forall_ne_eq_zero [Fintype ι] [Nontrivial ι] (c : EuclideanSpace ℝ ι)
    (i : ι) : volume {x : EuclideanSpace ℝ ι | ∀ j, j ≠ i → x j = c j} = 0 := by
  classical
  obtain ⟨j, hji⟩ := exists_ne i
  let s : Submodule ℝ (EuclideanSpace ℝ ι) := ℝ ∙ EuclideanSpace.single i 1
  have hsub : {x : EuclideanSpace ℝ ι | ∀ j, j ≠ i → x j = c j} ⊆ (· + -c) ⁻¹' s := by
    intro x hx
    refine Submodule.mem_span_singleton.2 ⟨x i - c i, ?_⟩
    ext k
    by_cases hk : k = i
    · subst hk; simp [sub_eq_add_neg]
    · simp [hk, hx k hk]
  have hs : s ≠ ⊤ := by
    intro htop
    have hmem : EuclideanSpace.single j (1 : ℝ) ∈ s := htop ▸ Submodule.mem_top
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hmem
    have := congrArg (fun y : EuclideanSpace ℝ ι ↦ y j) ha
    simp [hji] at this
  refine measure_mono_null hsub ?_
  rw [measure_preimage_add_right]
  exact Measure.addHaar_submodule volume s hs

end EuclideanSpace
