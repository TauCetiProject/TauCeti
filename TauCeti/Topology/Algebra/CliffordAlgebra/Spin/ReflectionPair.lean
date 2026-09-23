/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.ReflectionPair
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Basic
public import TauCeti.Topology.Algebra.CliffordAlgebra.RealForm
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Real.UnitLevel
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

* `CliffordAlgebra.continuous_spinReflectionPair` shows that continuously varying unit vectors
  determine continuously varying reflection-pair lifts.
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

universe u v w

variable {R : Type u} [CommRing R] [TopologicalSpace R]
  {M : Type v} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsModuleTopology R M]
  {Q : QuadraticForm R M} [ContinuousMul (CliffordAlgebra Q)]

/-- Two continuous families of unit vectors determine a continuous family of their normalized
reflection-pair lifts. -/
theorem continuous_spinReflectionPair {X : Type w} [TopologicalSpace X] (v w : X → M)
    (hv : ∀ x, Q (v x) = 1) (hw : ∀ x, Q (w x) = 1)
    (hvc : Continuous v) (hwc : Continuous w) :
    Continuous (fun x ↦ spinReflectionPair Q (v x) (w x) (hv x) (hw x)) := by
  apply continuous_induced_rng.mpr
  have hval : Continuous (fun x ↦ ι Q (v x) * ι Q (w x)) :=
    ((continuous_ι Q).comp hvc).mul ((continuous_ι Q).comp hwc)
  convert hval using 1
  funext x
  exact coe_spinReflectionPair Q (v x) (w x) (hv x) (hw x)

/-- Mapping a path between unit vectors by Clifford multiplication with the first vector joins the
identity to their normalized reflection-pair lift. -/
theorem joined_one_spinReflectionPair_of_joined (v w : M) (hv : Q v = 1) (hw : Q w = 1)
    (h : Joined (⟨v, hv⟩ : {u : M // Q u = 1}) ⟨w, hw⟩) :
    Joined (1 : spinGroup Q) (spinReflectionPair Q v w hv hw) := by
  let f : {u : M // Q u = 1} → spinGroup Q :=
    fun u => spinReflectionPair Q v u hv u.2
  have hf : Continuous f :=
    continuous_spinReflectionPair (fun _ ↦ v) Subtype.val (fun _ ↦ hv) (fun u ↦ u.2)
      continuous_const continuous_subtype_val
  simpa only [f, spinReflectionPair_self] using h.map hf

/-- In dimension at least two, every normalized reflection-pair lift for the positive-definite real
Clifford form is joined to the identity in the Spin group. -/
theorem joined_one_spinReflectionPair_realCliffordForm_zero {n : ℕ} (hn : 2 ≤ n)
    (v w : Fin n → ℝ) (hv : realCliffordForm n 0 v = 1)
    (hw : realCliffordForm n 0 w = 1) :
    Joined (1 : realCliffordSpinGroupZero n)
      (spinReflectionPair (realCliffordForm n 0) v w hv hw) := by
  let e := realCliffordUnitLevelHomeomorphSphere n
  let uv : realCliffordUnitLevel n :=
    ⟨v, (mem_realCliffordUnitLevel n v).mpr hv⟩
  let uw : realCliffordUnitLevel n :=
    ⟨w, (mem_realCliffordUnitLevel n w).mpr hw⟩
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin n)) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin, Nat.one_lt_cast]
    omega
  have hjoined : Joined (e uv) (e uw) :=
    ((isPathConnected_sphere hrank (0 : EuclideanSpace ℝ (Fin n)) zero_le_one).joinedIn
      (e uv).1 (e uv).2 (e uw).1 (e uw).2).joined_subtype
  let g : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 →
      {u : Fin n → ℝ // realCliffordForm n 0 u = 1} :=
    fun u => ⟨(e.symm u).1, (mem_realCliffordUnitLevel n _).mp (e.symm u).2⟩
  have hg : Continuous g := by
    apply continuous_induced_rng.mpr
    dsimp only [g]
    convert continuous_subtype_val.comp e.symm.continuous using 1
    rfl
  have hcoordinates :
      Joined (⟨v, hv⟩ : {u : Fin n → ℝ // realCliffordForm n 0 u = 1}) ⟨w, hw⟩ := by
    simpa only [g, uv, uw, e, Homeomorph.symm_apply_apply] using hjoined.map hg
  exact joined_one_spinReflectionPair_of_joined v w hv hw hcoordinates

end CliffordAlgebra
