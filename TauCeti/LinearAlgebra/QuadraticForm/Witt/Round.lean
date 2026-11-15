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

This file proves that the one- and two-fold Pfister forms are round: their represented units
are exactly their unit similarity factors. The results hold over any commutative ring, and
the parameters of the forms need not be units.

## Main results

* `TauCeti.oneFoldPfister_smul_equivalent_iff` characterizes similarity factors for
  one-fold Pfister forms.
* `TauCeti.twoFoldPfister_smul_equivalent_iff` characterizes similarity factors for
  two-fold Pfister forms.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter X, §1.
-/

public section

open QuadraticMap
open scoped Quaternion

namespace TauCeti

universe u

variable {R : Type u} [CommRing R]

/-- A unit is a similarity factor of the one-fold Pfister form `⟨1, -a⟩` exactly when
the form represents it. -/
@[simp]
theorem oneFoldPfister_smul_equivalent_iff (a : R) (c : Rˣ) :
    ((c : R) • weightedSumSquares R ![1, -a]).Equivalent
      (weightedSumSquares R ![1, -a]) ↔
        c ∈ unitValueSet (weightedSumSquares R ![1, -a]) := by
  have hscale :
      (c : R) • weightedSumSquares R ![1, -a] =
        weightedSumSquares R ![(c : R), (1 : R) * -a * c] := by
    ext x
    simp [weightedSumSquares_apply, Fin.sum_univ_two]
    ring
  rw [hscale]
  exact ⟨fun h => (mem_unitValueSet_binary_iff_equivalent (1 : R) (-a) c).mpr h.symm,
    fun h => ((mem_unitValueSet_binary_iff_equivalent (1 : R) (-a) c).mp h).symm⟩

/-- A unit is a similarity factor of the two-fold Pfister form `⟨1, -a, -b, ab⟩` exactly
when the form represents it. -/
@[simp]
theorem twoFoldPfister_smul_equivalent_iff (a b : R) (c : Rˣ) :
    ((c : R) • weightedSumSquares R ![1, -a, -b, a * b]).Equivalent
      (weightedSumSquares R ![1, -a, -b, a * b]) ↔
        c ∈ unitValueSet (weightedSumSquares R ![1, -a, -b, a * b]) := by
  constructor
  · intro h
    rw [← h.unitValueSet_eq, mem_unitValueSet, represents_iff]
    exact ⟨![1, 0, 0, 0], by simp [weightedSumSquares_apply, Fin.sum_univ_four]⟩
  intro hc
  let e := QuaternionAlgebra.normFormIsometryEquivWeightedSumSquares a b
  have hc' : Represents (QuaternionAlgebra.normForm a 0 b) (c : R) :=
    (e.represents_iff (c : R)).mpr (mem_unitValueSet.mp hc)
  rw [represents_iff, Set.mem_range] at hc'
  obtain ⟨q, hq⟩ := hc'
  have hqUnit : IsUnit q :=
    (QuaternionAlgebra.isUnit_iff_normForm_isUnit a 0 b q).mpr (by
      rw [hq]
      exact c.isUnit)
  let u : ℍ[R,a,b]ˣ := hqUnit.unit
  have hu : QuaternionAlgebra.normForm a 0 b (u : ℍ[R,a,b]) = c := by
    rw [hqUnit.unit_spec]
    exact hq
  refine ⟨{
    toLinearEquiv :=
      (e.symm.toLinearEquiv.trans (Units.mulLeftLinearEquiv R ℍ[R,a,b] u)).trans e.toLinearEquiv
    map_app' := ?_
  }⟩
  intro x
  -- Expose the three maps in the composite linear equivalence to apply their quadratic-form laws.
  change weightedSumSquares R ![1, -a, -b, a * b]
      (e ((u : ℍ[R,a,b]) * e.symm x)) =
    (c : R) * weightedSumSquares R ![1, -a, -b, a * b] x
  rw [e.map_app, QuaternionAlgebra.normForm_mul, hu, e.symm.map_app]

end TauCeti
