/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Uniform.Finite
public import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Uniform laws from finite transitive actions

A uniformly chosen element of a finite group sends any fixed point of a transitive action to a
uniformly distributed point. No measurable-action hypothesis is needed: finiteness and measurable
singletons make the maps measurable. This identifies sampling by a random symmetry with uniform
sampling on the space on which it acts.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace TauCeti.Probability

/-- A finite group's transitive action sends its uniform law to the uniform law on the target.
The target is automatically finite, since it is the image of the group under the orbit map. -/
theorem map_smul_uniformOn_univ {G α : Type*} [Group G] [Finite G]
    [MeasurableSpace G] [MeasurableSingletonClass G]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MulAction G α] [MulAction.IsPretransitive G α] (a : α) :
    (uniformOn (univ : Set G)).map (fun g ↦ g • a) = uniformOn (univ : Set α) := by
  classical
  let : Finite α := Finite.of_surjective (fun g : G ↦ g • a)
    (fun b ↦ MulAction.exists_smul_eq G a b)
  let : Fintype α := Fintype.ofFinite α
  let : Fintype G := Fintype.ofFinite G
  let : Nonempty α := ⟨a⟩
  let μ := (uniformOn (univ : Set G)).map (fun g ↦ g • a)
  have hmeas : Measurable (fun g : G ↦ g • a) := measurable_of_countable _
  have hinv (g : G) : μ.map (fun b ↦ g • b) = μ := by
    calc
      μ.map (fun b ↦ g • b) =
          (uniformOn (univ : Set G)).map ((fun h : G ↦ h • a) ∘ Equiv.mulLeft g) := by
        rw [Measure.map_map (measurable_of_countable _) hmeas]
        congr 1
        funext h
        exact (mul_smul g h a).symm
      _ = μ := by
        rw [← Measure.map_map hmeas (measurable_of_countable _),
          (Equiv.mulLeft g).map_uniformOn_univ]
  have hmass (b : α) : μ {b} = μ {a} := by
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G a b
    calc
      μ {g • a} = μ.map (fun b ↦ g • b) {g • a} := by rw [hinv]
      _ = μ {a} := by
        rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
        congr 1
        ext b
        simp
  have hatom : μ {a} = (Fintype.card α : ℝ≥0∞)⁻¹ := by
    apply ENNReal.eq_inv_of_mul_eq_one_left
    calc
      μ {a} * Fintype.card α = ∑ b : α, μ {b} := by simp [hmass, mul_comm]
      _ = 1 := by simp [μ]
  apply Measure.ext_of_singleton
  intro b
  rw [hmass, hatom, uniformOn_univ, Measure.count_singleton, one_div]

end TauCeti.Probability
