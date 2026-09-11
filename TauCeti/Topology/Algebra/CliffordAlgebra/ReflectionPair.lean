/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.ReflectionPair
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.Connected

/-!
# Paths to normalized reflection-pair lifts

For the positive-definite real Clifford form, every pair of unit vectors determines a Spin element
joined to the identity. The path is obtained by connecting the two vectors in the Euclidean unit
sphere and mapping that path through Clifford multiplication by the first vector.

The dimension bound is sharp for this construction: the unit sphere is path-connected precisely
from dimension two onward. The resulting path is the input needed to place reflection-pair lifts
in the identity path component of the compact real Spin group.

## Main result

* `CliffordAlgebra.joined_one_spinReflectionPair_realCliffordForm_zero` joins every normalized
  reflection-pair lift to the identity in dimension at least two.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, Section 2.
-/

public section

namespace CliffordAlgebra

open Metric TauCeti

private theorem euclidean_norm_eq_one_of_realCliffordForm_zero_eq_one {n : ℕ}
    {v : Fin n → ℝ} (hv : realCliffordForm n 0 v = 1) :
    ‖(EuclideanSpace.equiv (Fin n) ℝ).symm v‖ = 1 := by
  rw [realCliffordForm_apply] at hv
  have hweight (i : Fin (n + 0)) : realCliffordWeight n 0 i = 1 :=
    realCliffordWeight_of_lt (by omega)
  simp_rw [hweight, one_mul] at hv
  have hsquare : ‖(EuclideanSpace.equiv (Fin n) ℝ).symm v‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change ∑ i, v i ^ 2 = 1
    simpa only [Nat.add_zero, pow_two] using hv
  nlinarith [norm_nonneg ((EuclideanSpace.equiv (Fin n) ℝ).symm v)]

private theorem realCliffordForm_zero_euclidean_eq_one {n : ℕ}
    (u : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    realCliffordForm n 0 (EuclideanSpace.equiv (Fin n) ℝ u) = 1 := by
  rw [realCliffordForm_apply]
  have hweight (i : Fin (n + 0)) : realCliffordWeight n 0 i = 1 :=
    realCliffordWeight_of_lt (by omega)
  simp_rw [hweight, one_mul]
  simp only [Nat.add_zero, PiLp.continuousLinearEquiv_apply]
  have hu : ‖(u : EuclideanSpace ℝ (Fin n))‖ = 1 := by
    simpa only [mem_sphere, dist_zero_right] using u.2
  have hsq := EuclideanSpace.real_norm_sq_eq (u : EuclideanSpace ℝ (Fin n))
  rw [hu, one_pow] at hsq
  simpa only [pow_two] using hsq.symm

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
  let f : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → realCliffordSpinGroupZero n :=
    fun u => spinReflectionPair (realCliffordForm n 0) v (e u) hv
      (realCliffordForm_zero_euclidean_eq_one u)
  have hf : Continuous f := by
    apply continuous_induced_rng.mpr
    have hval : Continuous (fun u : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
        ι (realCliffordForm n 0) v * ι (realCliffordForm n 0) (e u)) :=
      continuous_const.mul
        ((continuous_ι (realCliffordForm n 0)).comp (e.continuous.comp continuous_subtype_val))
    convert hval using 1
    funext u
    exact coe_spinReflectionPair _ _ _ _ _
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin n)) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin, Nat.one_lt_cast]
    omega
  have hjoined : Joined uv uw :=
    ((isPathConnected_sphere hrank (0 : EuclideanSpace ℝ (Fin n)) zero_le_one).joinedIn
      uv.1 uv.2 uw.1 uw.2).joined_subtype
  have hmap := hjoined.map hf
  have hleft : f uv = 1 := by
    apply Subtype.ext
    simp only [f, uv, coe_spinReflectionPair]
    rw [e.apply_symm_apply, ι_sq_scalar, hv, map_one]
    simp
  have hright : f uw = spinReflectionPair (realCliffordForm n 0) v w hv hw := by
    apply Subtype.ext
    simp only [f, uw, coe_spinReflectionPair]
    rw [e.apply_symm_apply]
  rw [hleft, hright] at hmap
  exact hmap

end CliffordAlgebra
