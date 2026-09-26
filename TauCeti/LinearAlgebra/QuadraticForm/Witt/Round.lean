/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Quaternion.NormForm
public import TauCeti.LinearAlgebra.QuadraticForm.Binary

/-!
# Round one- and two-fold Pfister forms

This file proves that the one- and two-fold Pfister forms are round: every nonzero value they
represent is a similarity factor.

## Main results

* `TauCeti.oneFoldPfister_smul_equivalent_of_mem_unitValueSet` states roundness for
  one-fold Pfister forms.
* `TauCeti.twoFoldPfister_smul_equivalent_of_mem_unitValueSet` states roundness for
  two-fold Pfister forms.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter X, §1.
-/

public section

open QuadraticMap
open scoped Quaternion

namespace TauCeti

universe u

variable {K : Type u} [Field K]

/-- A one-fold Pfister form is round: every unit it represents is a similarity factor. -/
theorem oneFoldPfister_smul_equivalent_of_mem_unitValueSet (a : K) (c : Kˣ)
    (hc : c ∈ unitValueSet (weightedSumSquares K ![1, -a])) :
    ((c : K) • weightedSumSquares K ![1, -a]).Equivalent
      (weightedSumSquares K ![1, -a]) := by
  have hscale :
      (c : K) • weightedSumSquares K ![1, -a] =
        weightedSumSquares K ![(c : K), (1 : K) * -a * c] := by
    ext x
    simp [weightedSumSquares_apply, Fin.sum_univ_two]
    ring
  rw [hscale]
  exact (mem_unitValueSet_binary_iff_equivalent (1 : K) (-a) c).mp hc |>.symm

/-- A two-fold Pfister form is round: every unit it represents is a similarity factor. -/
theorem twoFoldPfister_smul_equivalent_of_mem_unitValueSet (a b : K) (c : Kˣ)
    (hc : c ∈ unitValueSet (weightedSumSquares K ![1, -a, -b, a * b])) :
    ((c : K) • weightedSumSquares K ![1, -a, -b, a * b]).Equivalent
      (weightedSumSquares K ![1, -a, -b, a * b]) := by
  let e := QuaternionAlgebra.normFormIsometryEquivWeightedSumSquares a b
  have hc' : Represents (QuaternionAlgebra.normForm a 0 b) (c : K) :=
    (e.represents_iff (c : K)).mpr (mem_unitValueSet.mp hc)
  rw [represents_iff, Set.mem_range] at hc'
  obtain ⟨q, hq⟩ := hc'
  have hqUnit : IsUnit q :=
    (QuaternionAlgebra.isUnit_iff_normForm_isUnit a 0 b q).mpr (by
    rw [hq]
    exact c.isUnit)
  let u : ℍ[K,a,b]ˣ := hqUnit.unit
  have hu : QuaternionAlgebra.normForm a 0 b (u : ℍ[K,a,b]) = c := by
    rw [hqUnit.unit_spec]
    exact hq
  refine ⟨{
    toLinearEquiv :=
      (e.symm.toLinearEquiv.trans (Units.mulLeftLinearEquiv K ℍ[K,a,b] u)).trans e.toLinearEquiv
    map_app' := ?_
  }⟩
  intro x
  -- Expose the three maps in the composite linear equivalence to apply their quadratic-form laws.
  change weightedSumSquares K ![1, -a, -b, a * b]
      (e ((u : ℍ[K,a,b]) * e.symm x)) =
    (c : K) * weightedSumSquares K ![1, -a, -b, a * b] x
  rw [e.map_app, QuaternionAlgebra.normForm_mul, hu, e.symm.map_app]

end TauCeti
