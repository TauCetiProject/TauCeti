/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Huber.WeightedEval.Newton

/-!
# Checks for Newton's method on restricted power series

For the linear system `Fᵢ = Xᵢ - aᵢ` with `a ∈ A₀^N`, the Jacobian matrix is the identity, so
Newton's method applies with `k = 0` and `M = 1` at every `t ≡ a mod ϖ` and produces a unique
zero in the class of `t`. This checks that the hypotheses of
`TauCeti.Huber.existsUnique_weightedEval_eq_zero` are satisfiable for a nontrivial family.
-/

open Pointwise TauCeti.Huber

namespace TauCeti.Examples

variable {C : Type*} [CommRing C] [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C]
  [CompleteSpace C] [T0Space C] (P : PairOfDefinition C) {N : ℕ}

-- The linear system `Xᵢ - aᵢ` has a unique zero in the class of any `t ≡ a mod ϖ`.
example {ϖ : P.ringOfDefinition} (hϖ : IsPseudoUniformizer (ϖ : C))
    (a t : Fin N → P.ringOfDefinition) (ht : ∀ i, ϖ ∣ t i - a i) :
    ∃! u : Fin N → P.ringOfDefinition, (∀ i, ϖ ∣ u i - t i) ∧
      ∀ i, weightedEval (RingHom.id C) (fun l ↦ (u l : C))
        (MvPowerSeries.X i + MvPowerSeries.C (-(a i : C))) = 0 := by
  classical
  have := P.toNonarchimedeanRing
  have hF (i : Fin N) : IsWeightedRestricted (fun _ : Fin N ↦ ({1} : Set C))
      (MvPowerSeries.X i + MvPowerSeries.C (-(a i : C))) :=
    (isWeightedRestricted_X _ i).add (isWeightedRestricted_C _ _)
  have hF₀ (i : Fin N) (ν : Fin N →₀ ℕ) : MvPowerSeries.coeff ν
      (MvPowerSeries.X i + MvPowerSeries.C (-(a i : C))) ∈ P.ringOfDefinition := by
    rw [map_add, MvPowerSeries.coeff_X, MvPowerSeries.coeff_C]
    refine add_mem ?_ ?_ <;> split_ifs
    exacts [one_mem _, zero_mem _, neg_mem (a i).2, zero_mem _]
  -- The value at a point `x ∈ A₀^N` is `xᵢ - aᵢ`.
  have heval (x : Fin N → P.ringOfDefinition) (i : Fin N) :
      weightedEval (RingHom.id C) (fun l ↦ (x l : C))
        (MvPowerSeries.X i + MvPowerSeries.C (-(a i : C))) = x i - a i := by
    rw [weightedEval_add_of_forall_isPowerBounded continuous_id.continuousAt
      (fun l ↦ P.isBounded_ringOfDefinition.isPowerBounded_of_mem (x l).2)
      (isWeightedRestricted_X _ i) (isWeightedRestricted_C _ _), weightedEval_X, weightedEval_C]
    simp [sub_eq_add_neg]
  -- The Jacobian matrix is the identity.
  have hJ : (1 : Matrix (Fin N) (Fin N) P.ringOfDefinition).map ((↑) : P.ringOfDefinition → C) *
      Matrix.of (fun i j ↦ weightedEval (RingHom.id C) (fun l ↦ (t l : C))
        (MvPowerSeries.pderiv j (MvPowerSeries.X i + MvPowerSeries.C (-(a i : C))))) =
        (ϖ : C) ^ 0 • (1 : Matrix (Fin N) (Fin N) C) := by
    have h1 : weightedEval (RingHom.id C) (fun l ↦ (t l : C)) 1 = 1 := by
      simpa using weightedEval_C (RingHom.id C) (fun l ↦ (t l : C)) 1
    ext i j
    by_cases hij : i = j <;> simp [MvPowerSeries.pderiv_X, hij, h1]
  have hFt (i : Fin N) : weightedEval (RingHom.id C) (fun l ↦ (t l : C))
      (MvPowerSeries.X i + MvPowerSeries.C (-(a i : C))) ∈
        (ϖ : C) ^ (2 * 0 + 1) • (P.ringOfDefinition : Set C) := by
    obtain ⟨r, hr⟩ := ht i
    refine ⟨r, r.2, ?_⟩
    rw [heval]
    simpa using congrArg ((↑) : P.ringOfDefinition → C) hr.symm
  simpa using existsUnique_weightedEval_eq_zero P hϖ hF hF₀ t hJ hFt

end TauCeti.Examples
