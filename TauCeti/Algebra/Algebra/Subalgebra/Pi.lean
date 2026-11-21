/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Units in subalgebras of finite products

Let `O` be a commutative ring, `ι` a finite index type, and `A : Subalgebra O (ι → O)` an
`O`-subalgebra of the finite product `ι → O`. An element `y ∈ A` is a unit in `A` (and not merely
in the ambient product `ι → O`) if and only if every coordinate `y i` is a unit in `O`, equivalently
if and only if the product `∏ i, y i` is a unit in `O`. Indeed, `y` is a root of the monic
polynomial `P(X) = ∏ i, (X - y i) ∈ O[X]`, whose constant term `± ∏ i, y i` lies in `O ∩ (y) A`
by `Ideal.coeff_zero_mem_comap_of_root_mem`.

## Main results

* `Subalgebra.isUnit_iff`: an element of a subalgebra of a finite product `ι → O` is a unit if and
  only if all of its coordinates are units in `O`.
* `Subalgebra.isUnit_iff_isUnit_prod`: product criterion for units in a subalgebra of `ι → O`.
-/

public section

namespace Subalgebra

variable {O ι : Type*} [CommRing O]

/-- **Units in a subalgebra of a finite product**: for a finite index type `ι` and a subalgebra
`A : Subalgebra O (ι → O)`, an element `y ∈ A` is a unit in `A` if and only if every coordinate
`y i` is a unit in `O`. -/
theorem isUnit_iff [Finite ι] {A : Subalgebra O (ι → O)} {y : A} :
    IsUnit y ↔ ∀ i : ι, IsUnit ((y : ι → O) i) := by
  classical
  let := Fintype.ofFinite ι
  refine ⟨fun hy i ↦ ?_, fun hy ↦ ?_⟩
  · simpa using hy.map ((Pi.evalAlgHom O (fun _ : ι ↦ O) i).comp A.val)
  · let P : Polynomial O := ∏ i : ι, (Polynomial.X - Polynomial.C ((y : ι → O) i))
    have hroot : P.eval₂ (algebraMap O A) y = 0 := by
      rw [← Polynomial.aeval_def]
      refine Subtype.ext (funext fun j ↦ ?_)
      have hj : ((Polynomial.aeval y P : A) : ι → O) j =
          ((Pi.evalAlgHom O (fun _ : ι ↦ O) j).comp A.val) (Polynomial.aeval y P) := rfl
      rw [hj, ← Polynomial.aeval_algHom_apply, Polynomial.coe_aeval_eq_eval,
        Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp)
    have hP0_mem : P.coeff 0 ∈ (Ideal.span {y}).comap (algebraMap O A) :=
      Ideal.coeff_zero_mem_comap_of_root_mem (Ideal.mem_span_singleton_self y) hroot
    have hP0_unit : IsUnit (P.coeff 0) := by
      rw [← Polynomial.constantCoeff_apply, map_prod, IsUnit.prod_univ_iff]
      intro i
      simpa using (hy i).neg
    exact Ideal.span_singleton_eq_top.mp <|
      Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_comap.mp hP0_mem)
        (hP0_unit.map (algebraMap O A))

/-- **Product criterion for units in a subalgebra of a finite product**: for a finite index type `ι`
and `A : Subalgebra O (ι → O)`, `y ∈ A` is a unit in `A` if and only if the product `∏ i, y i` is a
unit in `O`. -/
theorem isUnit_iff_isUnit_prod [Fintype ι] {A : Subalgebra O (ι → O)} {y : A} :
    IsUnit y ↔ IsUnit (∏ i : ι, (y : ι → O) i) := by
  rw [isUnit_iff, IsUnit.prod_univ_iff]

end Subalgebra
