/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Basic
public import Mathlib.Analysis.Convex.Hull

/-! # Closed invariant sets and determination by dense orbits

This file develops the continuity consequences of the semigroup action: agreement on dense
initial vectors determines a semigroup, common fixed sets are closed, and invariant sets
have invariant closed convex hulls.
-/

public section

noncomputable section

open Set Filter
open scoped NNReal Topology

namespace TauCeti.Semigroups.StronglyContinuousSemigroup

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Two semigroups agreeing on a dense set of initial vectors are equal. -/
theorem eq_of_orbits_eq_on_dense (S T :
    StronglyContinuousSemigroup X) {D : Set X} (hD : Dense D) (h : ∀ t : ℝ≥0, ∀ x ∈ D, S t x = T
    t x) :
    S = T := by
  ext t x
  have h_closed : IsClosed {y : X | S t y = T t y} :=
    isClosed_eq (S t).continuous (T t).continuous
  have hD_sub : D ⊆ {y : X | S t y = T t y} := fun y hy => h t y hy
  have hx : x ∈ closure {y : X | S t y = T t y} :=
    closure_mono hD_sub (by rw [hD.closure_eq]; exact Set.mem_univ x)
  rwa [h_closed.closure_eq] at hx

/-- The set of vectors fixed at every time is closed. -/
theorem isClosed_common_fixed_set (S :
    StronglyContinuousSemigroup X) :
    IsClosed {x : X | ∀ t : ℝ≥0, S t x = x} := by
  have h : {x : X | ∀ t : ℝ≥0, S t x = x} = ⋂ t : ℝ≥0, {x : X | S t x = x} := by
    ext x; simp
  rw [h]
  exact isClosed_iInter fun t => isClosed_eq (S t).cont continuous_id

/-- A semigroup preserves the closed convex hull of every invariant set. -/
theorem preserves_closed_convexHull (S :
    StronglyContinuousSemigroup X) {K : Set X} (hK : ∀ t : ℝ≥0, ∀ x ∈ K, S t x ∈ K) (t : ℝ≥0) {x
    : X} (hx : x ∈ closure (convexHull ℝ K)) :
    S t x ∈ closure (convexHull ℝ K) := by
  have hconv : Convex ℝ (convexHull ℝ K) := convex_convexHull ℝ K
  have h1 : ∀ x ∈ convexHull ℝ K, S t x ∈ convexHull ℝ K := by
    have hpre : Convex ℝ ((S t : X → X) ⁻¹' (convexHull ℝ K)) := by
      intro x hx y hy a b ha hb hab
      simp only [Set.mem_preimage] at hx hy ⊢
      have hlin : S t (a • x + b • y) = a • S t x + b • S t y := by
        rw [ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul,
          ContinuousLinearMap.map_smul]
      rw [hlin]
      exact hconv hx hy ha hb hab
    have hK_sub : K ⊆ (S t : X → X) ⁻¹' (convexHull ℝ K) := by
      intro x hx
      simp only [Set.mem_preimage]
      exact subset_convexHull ℝ K (hK t x hx)
    have hsub : convexHull ℝ K ⊆ (S t : X → X) ⁻¹' (convexHull ℝ K) :=
      convexHull_min hK_sub hpre
    intro x hx
    simpa only [Set.mem_preimage] using hsub hx
  have h_closed : IsClosed ((S t : X → X) ⁻¹' (closure (convexHull ℝ K))) :=
    IsClosed.preimage (S t).cont isClosed_closure
  have h_subset : convexHull ℝ K ⊆ (S t : X → X) ⁻¹' (closure (convexHull ℝ K)) := by
    intro y hy
    simp only [Set.mem_preimage]
    exact subset_closure (h1 y hy)
  have h_closure_in : closure (convexHull ℝ K) ⊆ (S t : X → X) ⁻¹' (closure (convexHull ℝ K)) :=
    closure_minimal h_subset h_closed
  simpa only [Set.mem_preimage] using h_closure_in hx

end TauCeti.Semigroups.StronglyContinuousSemigroup
