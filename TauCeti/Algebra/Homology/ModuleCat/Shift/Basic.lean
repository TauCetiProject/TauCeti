/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Abelian
import TauCeti.Algebra.Homology.ModuleCat.Basic

/-!
# Chain complexes of modules shifted with negated differentials

Let `C` and `D` be chain complexes of modules over a ring, and let `D` be `C` shifted up by one
degree with negated differentials: isomorphisms `e i : D.X (i + 1) ≃ C.X i` turn the differential
of `D` into the negative of that of `C`. Then `e` identifies the boundaries and the cycles of `D`
with those of `C` one degree down (`HomologicalComplex.map_range_d_of_shift`,
`HomologicalComplex.boundaryEquivOfShift`, `HomologicalComplex.map_ker_d_of_shift`), so `D` is
exact in degree `i + 1 + 1` exactly when `C` is exact in degree `i + 1`
(`HomologicalComplex.exactAt_iff_of_shift`), and `D` is acyclic exactly when `C` is
(`HomologicalComplex.acyclic_iff_of_shift`). The identifications of boundaries and cycles are the
case `u = -1` of the transport along linear equivalences intertwining the differentials up to a
unit `u` (`HomologicalComplex.range_d_eq_map_of_linearEquiv`,
`HomologicalComplex.boundaryEquivOfLinearEquiv`, `HomologicalComplex.ker_d_eq_map_of_linearEquiv`),
and the exactness statement is the corresponding case of
`HomologicalComplex.exactAt_iff_of_linearEquiv`.

The mapping cone of `K ⟶ 0` is such a shift of `K`; this is how the torsion of a mapping cone is
computed in `TauCeti.Algebra.Homology.ReidemeisterTorsion.MappingCone`.
-/

public section

noncomputable section

open CategoryTheory

namespace HomologicalComplex

variable {R : Type*} [Ring R] {C D : ChainComplex (ModuleCat R) ℤ}
  (e : ∀ i, D.X (i + 1) ≃ₗ[R] C.X i)
  (he : ∀ i x, e i ((D.d (i + 1 + 1) (i + 1)).hom x) = -(C.d (i + 1) i).hom (e (i + 1) x))

include he in
/-- Under a shift `e` with negated differentials, the boundaries of `D` in degree `i + 1` are
sent to the boundaries of `C` in degree `i`. -/
theorem map_range_d_of_shift (i : ℤ) :
    (LinearMap.range (D.d (i + 1 + 1) (i + 1)).hom).map (e i : D.X (i + 1) →ₗ[R] C.X i) =
      LinearMap.range (C.d (i + 1) i).hom :=
  (range_d_eq_map_of_linearEquiv (e i) (e (i + 1)) isUnit_one.neg (by simp [he])).symm

/-- The isomorphism between the boundaries of `D` in degree `i + 1` and those of `C` in degree `i`
induced by a shift `e` with negated differentials. -/
def boundaryEquivOfShift (i : ℤ) :
    LinearMap.range (D.d (i + 1 + 1) (i + 1)).hom ≃ₗ[R] LinearMap.range (C.d (i + 1) i).hom :=
  boundaryEquivOfLinearEquiv (e i) (e (i + 1)) isUnit_one.neg (by simp [he])

/-- The isomorphism `boundaryEquivOfShift` is the restriction of `e i`. -/
@[simp]
theorem coe_boundaryEquivOfShift (i : ℤ)
    (x : LinearMap.range (D.d (i + 1 + 1) (i + 1)).hom) :
    (boundaryEquivOfShift e he i x : C.X i) = e i x := by
  simp [boundaryEquivOfShift]

include he in
/-- Under a shift `e` with negated differentials, the cycles of `D` in degree `i + 1 + 1` are sent
to the cycles of `C` in degree `i + 1`. -/
theorem map_ker_d_of_shift (i : ℤ) :
    (LinearMap.ker (D.d (i + 1 + 1) (i + 1)).hom).map
        (e (i + 1) : D.X (i + 1 + 1) →ₗ[R] C.X (i + 1)) =
      LinearMap.ker (C.d (i + 1) i).hom :=
  (ker_d_eq_map_of_linearEquiv (e (i + 1)) (e i) isUnit_one.neg (by simp [he])).symm

include he in
/-- Under a shift `e` with negated differentials, `D` is exact in degree `i + 1 + 1` exactly when
`C` is exact in degree `i + 1`. -/
theorem exactAt_iff_of_shift (i : ℤ) : D.ExactAt (i + 1 + 1) ↔ C.ExactAt (i + 1) :=
  (exactAt_iff_of_linearEquiv (by simp) (by simp) (by simp) (by simp) (e (i + 1 + 1)) (e (i + 1))
    (e i) isUnit_one.neg isUnit_one.neg (by simp [he]) (by simp [he])).symm

include he in
/-- If the terms of `D` are those of `C` shifted up by one degree, through isomorphisms
`e i : D.X (i + 1) ≃ C.X i` under which the differentials of `D` become the negatives of those of
`C`, then `D` is acyclic exactly when `C` is. -/
theorem acyclic_iff_of_shift : D.Acyclic ↔ C.Acyclic := by
  refine ⟨fun h j ↦ ?_, fun h j ↦ ?_⟩
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    exact (exactAt_iff_of_shift e he i).1 (h _)
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 + 1 := ⟨j - 2, by omega⟩
    exact (exactAt_iff_of_shift e he i).2 (h _)

end HomologicalComplex
