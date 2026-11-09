/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CyclicCohomology.Matrix
public import TauCeti.RingTheory.CyclicCohomology.Relative.Basic

/-!
# Matrix extension of relative cyclic cochains

A relative cyclic cochain on the forced unitization `A⁺ = Unitization R A` vanishes when all its
arguments are scalar. Its matrix extension `φ#Tr` is a sum of values of `φ` on entries of the
matrix arguments, so it vanishes when all its arguments are scalar matrices, that is matrices with
entries in the image of `R → A⁺`. This is why the classes of scalar matrices pair trivially with
relative cyclic cohomology.

## Main results

* `TauCeti.matrixCochainExtension_map_algebraMap_eq_zero`: the matrix extension of a relative
  cyclic cochain vanishes when all its arguments are scalar matrices.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §1 and §3.
* J.-L. Loday, *Cyclic Homology*, §1.4.
-/

public section

namespace TauCeti

variable {R A M : Type*} [CommSemiring R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- The matrix extension of a relative cyclic cochain vanishes when all its arguments are scalar
matrices. -/
theorem matrixCochainExtension_map_algebraMap_eq_zero {ι : Type*} [Fintype ι] {n : ℕ}
    (φ : relativeCyclicCochains R A M n) (a : Fin (n + 1) → Matrix ι ι R) :
    matrixCochainExtension ι n (φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ Unitization R A) M)
      (fun k ↦ (a k).map (algebraMap R (Unitization R A))) = 0 := by
  rw [matrixCochainExtension_apply]
  exact Finset.sum_eq_zero fun p _ ↦
    (mem_reducedCyclicCochains_iff_forall R (Unitization R A) M).1 φ.2 _

end TauCeti
