/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.Basic
public import TauCeti.RepresentationTheory.Quiver.Radical

/-!
# The quadratic bound on preprojective relations

Every local preprojective relation is a linear combination of length-two backtracks. Thus the
preprojective relation ideal lies in the square of the arrow ideal of the doubled path algebra.
This is the upper bound in admissibility; finite-dimensional Dynkin cases also need a lower bound
by some arrow-ideal power.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra

universe u v w

/-- **The preprojective relation ideal is contained in the square of the arrow ideal.**
Every term of the global relator is a backtrack of length two. -/
theorem preprojectiveIdeal_le_arrowIdeal_sq (k : Type w) {Q : Type u} [CommRing k]
    [Quiver.{v} Q] [Fintype Q] [∀ i j : Q, Fintype (i ⟶ j)] :
    (preprojectiveIdeal k Q).asIdeal ≤ arrowIdeal k (Symmetrify Q) ^ 2 := by
  rw [← Ideal.asIdeal_toTwoSided (arrowIdeal k (Symmetrify Q) ^ 2)]
  refine TwoSidedIdeal.asIdeal.monotone ?_
  rw [preprojectiveIdeal_eq_span, TwoSidedIdeal.span_le]
  intro x hx
  obtain rfl := Set.mem_singleton_iff.mp hx
  rw [SetLike.mem_coe, Ideal.mem_toTwoSided, preprojectiveRelator_def]
  refine sum_mem fun i _ => sum_mem fun j _ => sum_mem fun a _ => ?_
  -- Both backtracks have length two; expose the length across the path wrappers.
  have hhead : headBacktrackElem k a ∈ arrowIdeal k (Symmetrify Q) ^ 2 := by
    rw [headBacktrackElem_def]
    exact Ideal.pow_le_pow_right (by simp only [Path.length_comp, Path.length_toPath]; omega)
      (ofPath_mem_arrowIdeal_pow _)
  have htail : tailBacktrackElem k a ∈ arrowIdeal k (Symmetrify Q) ^ 2 := by
    rw [tailBacktrackElem_def]
    exact Ideal.pow_le_pow_right (by simp only [Path.length_comp, Path.length_toPath]; omega)
      (ofPath_mem_arrowIdeal_pow _)
  exact sub_mem hhead htail

end TauCeti
