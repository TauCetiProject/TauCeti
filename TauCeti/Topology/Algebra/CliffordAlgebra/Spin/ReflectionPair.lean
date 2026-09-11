/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.ReflectionPair
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.Connected

/-!
# Paths to normalized reflection-pair lifts

A path between two unit vectors maps to a path from the identity to their reflection-pair lift by
Clifford multiplication by the first vector. For the positive-definite real Clifford form, the
Euclidean unit sphere supplies such a path for every pair of unit vectors.

The dimension bound in the real specialization is sharp for this construction: the unit sphere is
path-connected precisely from dimension two onward. The resulting path is the input needed to
place reflection-pair lifts in the identity path component of the compact real Spin group.

## Main results

* `CliffordAlgebra.joined_one_spinReflectionPair_of_joined` maps a path in a unit quadric to a
  path from the identity to its reflection-pair lift.
* `CliffordAlgebra.joined_one_spinReflectionPair_realCliffordForm_zero` joins every normalized
  reflection-pair lift to the identity in the positive-definite real form of dimension at least two.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, Section 2.
-/

public section

namespace CliffordAlgebra

open Metric TauCeti

universe u v

variable {R : Type u} [CommRing R] [TopologicalSpace R]
  {M : Type v} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsModuleTopology R M]
  {Q : QuadraticForm R M} [ContinuousMul (CliffordAlgebra Q)]

/-- Mapping a path between unit vectors by Clifford multiplication with the first vector joins the
identity to their normalized reflection-pair lift. -/
theorem joined_one_spinReflectionPair_of_joined (v w : M) (hv : Q v = 1) (hw : Q w = 1)
    (h : Joined (⟨v, hv⟩ : {u : M // Q u = 1}) ⟨w, hw⟩) :
    Joined (1 : spinGroup Q) (spinReflectionPair Q v w hv hw) := by
  let f : {u : M // Q u = 1} → spinGroup Q :=
    fun u => spinReflectionPair Q v u hv u.2
  have hf : Continuous f := by
    apply continuous_induced_rng.mpr
    have hval : Continuous (fun u : {u : M // Q u = 1} => ι Q v * ι Q u.1) :=
      continuous_const.mul ((continuous_ι Q).comp continuous_subtype_val)
    convert hval using 1
    funext u
    exact coe_spinReflectionPair _ _ _ _ _
  simpa only [f, spinReflectionPair_self] using h.map hf

private theorem realCliffordForm_zero_euclidean_norm_sq {n : ℕ}
    (u : EuclideanSpace ℝ (Fin n)) :
    realCliffordForm n 0 (EuclideanSpace.equiv (Fin n) ℝ u) = ‖u‖ ^ 2 := by
  rw [realCliffordForm_zero_eq_weightedSumSquares_one,
    QuadraticMap.weightedSumSquares_apply]
  simp only [Pi.one_apply, one_smul, PiLp.continuousLinearEquiv_apply]
  simpa only [pow_two] using (EuclideanSpace.real_norm_sq_eq u).symm

private theorem euclidean_norm_eq_one_of_realCliffordForm_zero_eq_one {n : ℕ}
    {v : Fin n → ℝ} (hv : realCliffordForm n 0 v = 1) :
    ‖(EuclideanSpace.equiv (Fin n) ℝ).symm v‖ = 1 := by
  have hsquare : ‖(EuclideanSpace.equiv (Fin n) ℝ).symm v‖ ^ 2 = 1 := by
    rw [← realCliffordForm_zero_euclidean_norm_sq]
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hv
  nlinarith [norm_nonneg ((EuclideanSpace.equiv (Fin n) ℝ).symm v)]

private theorem realCliffordForm_zero_euclidean_eq_one {n : ℕ}
    (u : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    realCliffordForm n 0 (EuclideanSpace.equiv (Fin n) ℝ u) = 1 := by
  rw [realCliffordForm_zero_euclidean_norm_sq]
  have hu : ‖(u : EuclideanSpace ℝ (Fin n))‖ = 1 := by
    simpa only [mem_sphere, dist_zero_right] using u.2
  rw [hu, one_pow]

/-- In dimension at least two, every normalized reflection-pair lift for the positive-definite real
Clifford form is joined to the identity in the Spin group. -/
theorem joined_one_spinReflectionPair_realCliffordForm_zero {n : ℕ} (hn : 2 ≤ n)
    (v w : Fin n → ℝ) (hv : realCliffordForm n 0 v = 1)
    (hw : realCliffordForm n 0 w = 1) :
    Joined (1 : realCliffordSpinGroupZero n)
      (spinReflectionPair (realCliffordForm n 0) v w hv hw) := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  let uv : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
    ⟨e.symm v, by
      rw [mem_sphere, dist_zero_right]
      exact euclidean_norm_eq_one_of_realCliffordForm_zero_eq_one hv⟩
  let uw : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
    ⟨e.symm w, by
      rw [mem_sphere, dist_zero_right]
      exact euclidean_norm_eq_one_of_realCliffordForm_zero_eq_one hw⟩
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin n)) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin, Nat.one_lt_cast]
    omega
  have hjoined : Joined uv uw :=
    ((isPathConnected_sphere hrank (0 : EuclideanSpace ℝ (Fin n)) zero_le_one).joinedIn
      uv.1 uv.2 uw.1 uw.2).joined_subtype
  let g : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 →
      {u : Fin n → ℝ // realCliffordForm n 0 u = 1} :=
    fun u => ⟨e u, realCliffordForm_zero_euclidean_eq_one u⟩
  have hg : Continuous g :=
    continuous_induced_rng.mpr (e.continuous.comp continuous_subtype_val)
  have hcoordinates :
      Joined (⟨v, hv⟩ : {u : Fin n → ℝ // realCliffordForm n 0 u = 1}) ⟨w, hw⟩ := by
    simpa only [g, uv, uw, e, ContinuousLinearEquiv.apply_symm_apply] using hjoined.map hg
  exact joined_one_spinReflectionPair_of_joined v w hv hw hcoordinates

end CliffordAlgebra
