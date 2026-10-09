/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Derived.Functoriality
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Smooth
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Commutator
import TauCeti.RingTheory.FiniteType.PointSeparation
import TauCeti.RingTheory.Smooth.GeometricallyReduced
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The derived subgroup of the general linear group

Over every field, the scheme-theoretic derived subgroup of `GLₙ` is `SLₙ`. This is an equality
of the defining Hopf ideals in `O(GLₙ)`, so it identifies the actual closed subgroup schemes,
including all their algebra-valued points.

The determinant gives containment in `SLₙ` over any commutative ring. For the reverse inclusion
over a field, every algebraic-closure-valued point of `SLₙ` is in the abstract commutator subgroup
of `GLₙ` over that closure. These points separate the reduced finite-type coordinate algebra of
`SLₙ`. Thus a function vanishing on the scheme-theoretic derived subgroup already vanishes on
`SLₙ`. In particular the result holds over the field with two elements, even though the analogous
claim about its rational-point groups fails in dimension two.

## Main declaration

* `TauCeti.GeneralLinear.derivedDefiningIdeal_eq_specialLinear`: the equality of defining ideals.

## References

* J. S. Milne, *Algebraic Groups* (2017), §6d, for the scheme-theoretic derived subgroup.

The argument uses the existing derived-subgroup universal property, the transvection generation
of special linear groups, and `TauCeti.eq_of_forall_algHom_apply_eq` for point separation.
-/

public section

open CategoryTheory WithConv

namespace TauCeti

universe u

noncomputable section

namespace SpecialLinear

/-- Every general-linear commutator has determinant one, over any commutative base ring.
In Hopf-ideal order, the determinant-one ideal is contained in the derived defining ideal. -/
theorem definingHopfIdeal_le_derivedDefiningIdeal (R : Type u) [CommRing R] (n : ℕ) :
    definingHopfIdeal R n ≤
      CommHopfAlgCat.derivedDefiningIdeal (GeneralLinear.coordinateHopfAlgebra R n) := by
  rw [definingHopfIdeal, CommHopfAlgCat.kernelHopfIdeal_def]
  have hcomm : CommHopfAlgCat.derivedDefiningIdeal
      (R := R) (MonoidAlgebra R (Multiplicative ℤ)) =
        HopfIdeal.augmentation R (MonoidAlgebra R (Multiplicative ℤ)) :=
    CommHopfAlgCat.derivedDefiningIdeal_eq_augmentation_iff_isCocomm _ |>.mpr inferInstance
  rw [← hcomm]
  exact CommHopfAlgCat.derivedDefiningIdeal_map_le (GeneralLinear.determinantCoordinateMap R n).hom

end SpecialLinear

namespace GeneralLinear

/-- **The scheme-theoretic derived subgroup of `GLₙ` over every field is `SLₙ`.**
The equality is in the ambient coordinate Hopf algebra and therefore identifies the closed
subgroup schemes, rather than just their rational points. No perfection or characteristic
assumption is required. -/
@[simp]
theorem derivedDefiningIdeal_eq_specialLinear (k : Type u) [Field k] (n : ℕ) :
    CommHopfAlgCat.derivedDefiningIdeal (coordinateHopfAlgebra k n) =
      SpecialLinear.definingHopfIdeal k n := by
  classical
  apply le_antisymm _ (SpecialLinear.definingHopfIdeal_le_derivedDefiningIdeal k n)
  intro x hx
  rw [← CommHopfAlgCat.mkQuotient_eq_zero_iff]
  let K := AlgebraicClosure k
  let _ : IsReduced (SpecialLinear.coordinateHopfAlgebra k n) :=
    isReduced_of_smooth k _
  apply eq_of_forall_algHom_apply_eq (k := k)
    (A := SpecialLinear.coordinateHopfAlgebra k n) (K := K)
  intro f
  rw [map_zero]
  let g := CommHopfAlgCat.quotientPointsHom (coordinateHopfAlgebra k n)
    (SpecialLinear.definingHopfIdeal k n) (CommAlgCat.of k K) (toConv f)
  have hgdet : Matrix.GeneralLinearGroup.det (pointsMulEquiv n g) = 1 := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
    exact (SpecialLinear.mem_definingPointsSubgroup_iff_det_eq_one k n g).mp
      (CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup
        (coordinateHopfAlgebra k n) (SpecialLinear.definingHopfIdeal k n)
        (CommAlgCat.of k K) (toConv f))
  obtain ⟨a, ha⟩ := (Finset.exists_notMem ({0, 1} : Finset K))
  have ha₀ : a ≠ 0 := fun h ↦ ha (by simp [h])
  have ha₁ : a ≠ 1 := fun h ↦ ha (by simp [h])
  have hmatrix : pointsMulEquiv n g ∈ commutator (Matrix.GeneralLinearGroup (Fin n) K) := by
    rw [Matrix.GeneralLinearGroup.commutator_eq_ker_det ha₀ ha₁, MonoidHom.mem_ker]
    exact hgdet
  have hg : g ∈ commutator (WithConv (coordinateHopfAlgebra k n →ₐ[k] K)) := by
    have heq : (commutator (WithConv (coordinateHopfAlgebra k n →ₐ[k] K))).map
        (pointsMulEquiv (R := k) (A := K) n).toMonoidHom =
        commutator (Matrix.GeneralLinearGroup (Fin n) K) := by
      rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _
        (pointsMulEquiv n).surjective, ← commutator_def]
    rw [← heq] at hmatrix
    simpa only [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] using hmatrix
  have hvanish := CommHopfAlgCat.commutator_le_quotientPointsSubgroup_of_le_derivedDefiningIdeal
    (coordinateHopfAlgebra k n) (CommHopfAlgCat.derivedDefiningIdeal (coordinateHopfAlgebra k n))
    le_rfl (CommAlgCat.of k K) hg
  have hzero := (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).mp hvanish x hx
  exact (CommHopfAlgCat.quotientPointsHom_apply_apply (coordinateHopfAlgebra k n)
    (SpecialLinear.definingHopfIdeal k n) (CommAlgCat.of k K) (toConv f) x).symm.trans hzero

end GeneralLinear

end

end TauCeti
