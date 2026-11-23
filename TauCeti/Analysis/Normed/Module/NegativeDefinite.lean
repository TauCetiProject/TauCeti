/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giada Franz, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.Analysis.Matrix.PosDef

/-!
# Negative definite subspaces through a dense map

Let `Q` be a continuous bilinear form on a seminormed space `X`, and `ι : Y → X` a linear map with
dense range. If `Q` is negative definite on a finite-dimensional subspace `W` of `X`, then `Y` has
a subspace of the same dimension on whose image `Q` is negative definite
(`ContinuousLinearMap.exists_finrank_eq_forall_apply_lt_zero_of_denseRange`).
Negative definiteness on the span of a basis is an open condition on its matrix, so it survives
approximating the basis vectors in the range of `ι`.

This is how an index computed on a completion is attained on a dense space of smooth sections.
-/

public section

open Module Set Topology

open scoped Matrix

variable {X Y : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- **Negative definite subspaces through a dense map.** If the continuous bilinear form `Q` on `X`
is negative definite on a finite-dimensional subspace `W`, and `ι : Y → X` is linear with dense
range, then some subspace of `Y` of dimension `finrank W` is mapped by `ι` to vectors on which `Q`
is negative, except for `0`. -/
theorem ContinuousLinearMap.exists_finrank_eq_forall_apply_lt_zero_of_denseRange
    (Q : X →L[ℝ] X →L[ℝ] ℝ)
    {ι : Y →ₗ[ℝ] X} (hι : DenseRange ι) (W : Submodule ℝ X) [FiniteDimensional ℝ W]
    (hW : ∀ w ∈ W, w ≠ 0 → Q w w < 0) :
    ∃ W' : Submodule ℝ Y, finrank ℝ W' = finrank ℝ W ∧ ∀ y ∈ W', y ≠ 0 → Q (ι y) (ι y) < 0 := by
  classical
  set n := finrank ℝ W
  set v : Fin n → X := fun i ↦ (Module.finBasis ℝ W i : X)
  have hv : LinearIndependent ℝ v :=
    (Module.finBasis ℝ W).linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  let M (d : Fin n → X) : Matrix (Fin n) (Fin n) ℝ := fun i j ↦ -Q (d i) (d j)
  have hM (d : Fin n → X) (a : Fin n → ℝ) :
      star a ⬝ᵥ M d *ᵥ a = -Q (∑ i, a i • d i) (∑ i, a i • d i) := by
    simp only [M, star_trivial, dotProduct, Matrix.mulVec, map_sum, sum_apply, map_smul,
      smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp [mul_comm, mul_left_comm]
  have hMc : Continuous M := by
    fun_prop
  have hO := (TauCeti.isOpen_setOfPred_re_dotProduct_pos
    (ι := Fin n) (𝕜 := ℝ)).preimage hMc
  have hvO : M v ∈ {A : Matrix (Fin n) (Fin n) ℝ |
      ∀ a : Fin n → ℝ, a ≠ 0 → 0 < RCLike.re (star a ⬝ᵥ A *ᵥ a)} := by
    intro a ha
    rw [hM, RCLike.re_to_real, neg_pos]
    refine hW _
      (Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Module.finBasis ℝ W i).property)
      fun h ↦ ha (funext fun i ↦ ?_)
    exact Fintype.linearIndependent_iff.1 hv a h i
  have hdense : DenseRange fun y : Fin n → Y ↦ fun i ↦ ι (y i) :=
    DenseRange.piMap fun _ ↦ hι
  obtain ⟨y, hy⟩ := hdense.exists_mem_open hO ⟨v, hvO⟩
  have hneg (a : Fin n → ℝ) (ha : a ≠ 0) : Q (ι (∑ i, a i • y i)) (ι (∑ i, a i • y i)) < 0 := by
    have h := hy a ha
    rw [hM, RCLike.re_to_real, neg_pos] at h
    simpa only [map_sum, map_smul] using h
  have hyli : LinearIndependent ℝ y := Fintype.linearIndependent_iff.2 fun a ha i ↦ by
    by_contra hai
    have := hneg a fun h ↦ hai (by simp [h])
    simp [ha] at this
  refine ⟨Submodule.span ℝ (Set.range y), ?_, fun z hz hz0 ↦ ?_⟩
  · rw [finrank_span_eq_card hyli, Fintype.card_fin]
  · obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hz
    exact hneg a fun h ↦ hz0 (by simp [h])
