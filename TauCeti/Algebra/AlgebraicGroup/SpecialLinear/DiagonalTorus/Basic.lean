/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.BaseChange
public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.Basic

/-!
# The diagonal torus of the special linear group

The determinant-one diagonal matrices of `SL_{r+1}` form a split torus of rank `r`. This file
parametrizes it in fundamental-weight coordinates: a point `s = (s₀, …, s_{r-1})` of the split
torus goes to

```text
diag(s₀, s₁ s₀⁻¹, …, s_{r-1} s_{r-2}⁻¹, s_{r-1}⁻¹),
```

whose `k`-th entry is the value of the standard weight `ε_k` of `sl_{r+1}`, written in the basis
of fundamental weights as `TauCeti.SlStd.weight r k`. These are the coordinates of the pinned
simply connected root datum of type `A_r`, in which the simple roots are the rows of the Cartan
matrix.

The coordinate morphism `O(SL_{r+1}) ⟶ R[X*(T)]` is obtained by factoring the general-linear
weight torus `TauCeti.GeneralLinear.weightTorusCoordinateMap` through the determinant-one quotient:
the standard weights sum to zero, so the generic determinant restricts to one. Since the standard
weights span the character lattice, the coordinate morphism is surjective over every commutative
base ring; contravariantly, the torus is a closed subgroup of `SL_{r+1}`.

## Main declarations

* `TauCeti.SpecialLinear.diagonalTorusWeight`: the standard weights, indexed by the
  universe-lifted torus coordinates.
* `TauCeti.SpecialLinear.diagonalTorusCoordinateMap`: the coordinate morphism of the diagonal
  torus of `SL_{r+1}`.
* `TauCeti.SpecialLinear.coordinateMap_comp_diagonalTorusCoordinateMap`: its composite with the
  quotient `O(GL_{r+1}) ⟶ O(SL_{r+1})` is the general-linear weight torus.
* `TauCeti.SpecialLinear.diagonalTorusCoordinateMap_surjective`: the coordinate morphism is
  surjective.
* `TauCeti.SpecialLinear.toGL_pointsMulEquiv_mapPointsFunctor_diagonalTorusCoordinateMap`: on
  algebra-valued points it is the diagonal matrix of the standard weight characters.
* `TauCeti.SpecialLinear.diagonalTorusCoordinateMap_baseChange`: compatibility with scalar
  extension.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 12 and 21.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), §§15.3 and 26.3.
* The factorization through the general-linear weight torus combines
  `TauCeti.SpecialLinear.definingHopfIdeal_toIdeal_le_ker_of_map_determinant_eq_one` with
  `TauCeti.GeneralLinear.weightTorusCoordinateMap_determinantGroupLike`, and the base-change
  argument follows `TauCeti.Symplectic.diagonalTorusCoordinateMap_baseChange`.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.SpecialLinear

universe u w

variable (r : ℕ)

/-- The standard weight `ε_k` of `sl_{r+1}` in fundamental-weight coordinates, indexed by the
universe-lifted coordinates of the rank-`r` split torus. -/
def diagonalTorusWeight (k : Fin (r + 1)) : ULift.{u} (Fin r) → ℤ :=
  fun i ↦ SlStd.weight r k i.down

@[simp]
theorem diagonalTorusWeight_apply (k : Fin (r + 1)) (i : ULift.{u} (Fin r)) :
    diagonalTorusWeight.{u} r k i = SlStd.weight r k i.down :=
  (rfl)

/-- The standard weights sum to zero. -/
theorem sum_diagonalTorusWeight_eq_zero : ∑ k, diagonalTorusWeight.{u} r k = 0 := by
  funext i
  simpa only [Finset.sum_apply, diagonalTorusWeight_apply, Pi.zero_apply] using
    congrFun (SlStd.sum_weight_eq_zero r) i.down

/-- The standard weights span the character lattice of the rank-`r` split torus. -/
theorem span_range_diagonalTorusWeight_eq_top :
    Submodule.span ℤ (Set.range (diagonalTorusWeight.{u} r)) = ⊤ := by
  let e : (Fin r → ℤ) ≃ₗ[ℤ] (ULift.{u} (Fin r) → ℤ) :=
    LinearEquiv.funCongrLeft ℤ ℤ Equiv.ulift
  have hrange : Set.range (diagonalTorusWeight.{u} r) = e '' Set.range (SlStd.weight r) := by
    rw [← Set.range_comp]
    apply congrArg Set.range
    funext k i
    rw [Function.comp_apply, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
      Equiv.ulift_apply, diagonalTorusWeight_apply]
  rw [hrange, ← LinearEquiv.coe_toLinearMap, Submodule.span_image,
    SlStd.span_range_weight_eq_top, Submodule.map_top, LinearEquiv.range]

/-- A split-torus character of a standard weight, read in the original torus coordinates. -/
@[simp]
theorem torusCharacter_diagonalTorusWeight {A : Type w} [CommRing A]
    (s : ULift.{u} (Fin r) → Aˣ) (k : Fin (r + 1)) :
    torusCharacter s (diagonalTorusWeight.{u} r k) =
      torusCharacter (fun i : Fin r ↦ s (ULift.up i)) (SlStd.weight r k) := by
  rw [torusCharacter_def, torusCharacter_def]
  exact (Fintype.prod_equiv Equiv.ulift _ _ fun _ ↦ rfl)

variable (R : Type u) [CommRing R]

/-- The general-linear weight torus of the standard weights has determinant one. -/
private theorem weightTorusCoordinateMap_determinantGroupLike_diagonalTorusWeight :
    (GeneralLinear.weightTorusCoordinateMap (R := R) (diagonalTorusWeight.{u} r)).hom
      (GeneralLinear.determinantGroupLike R (r + 1) :
        GeneralLinear.coordinateHopfAlgebra R (r + 1)) = 1 :=
  GeneralLinear.weightTorusCoordinateMap_determinantGroupLike _
    (sum_diagonalTorusWeight_eq_zero r)

/-- **The coordinate morphism of the diagonal torus of `SL_{r+1}`.** It restricts functions on
`SL_{r+1}` to the rank-`r` split torus embedded through the standard weights. Its direction is
opposite to the represented group-scheme morphism. -/
noncomputable def diagonalTorusCoordinateMap :
    coordinateHopfAlgebra R (r + 1) ⟶
      (DiagonalizableGroup.coordinateRing R
        (SplitTorus.characterGroup (ULift.{u} (Fin r)))).obj :=
  CommHopfAlgCat.liftQuotient (definingHopfIdeal R (r + 1))
    (GeneralLinear.weightTorusCoordinateMap (diagonalTorusWeight r))
    (definingHopfIdeal_toIdeal_le_ker_of_map_determinant_eq_one R (r + 1) _
      (weightTorusCoordinateMap_determinantGroupLike_diagonalTorusWeight r R))

/-- Restricting from `GL_{r+1}` to `SL_{r+1}` and then to the diagonal torus is the general-linear
weight torus of the standard weights. -/
@[simp]
theorem coordinateMap_comp_diagonalTorusCoordinateMap :
    coordinateMap R (r + 1) ≫ diagonalTorusCoordinateMap r R =
      GeneralLinear.weightTorusCoordinateMap (diagonalTorusWeight r) :=
  CommHopfAlgCat.mkQuotient_comp_liftQuotient _ _ _

/-- The coordinate morphism of the diagonal torus of `SL_{r+1}` is surjective over every
commutative base ring. -/
theorem diagonalTorusCoordinateMap_surjective :
    Function.Surjective (diagonalTorusCoordinateMap r R).hom :=
  CommHopfAlgCat.liftQuotient_surjective_of_surjective _ _ _
    (GeneralLinear.weightTorusCoordinateMap_surjective _
      (span_range_diagonalTorusWeight_eq_top r))

/-- **The diagonal torus of `SL_{r+1}` on algebra-valued points.** A point `s` of the split torus
goes to the diagonal matrix whose `k`-th entry is the character of the standard weight `ε_k`. -/
theorem toGL_pointsMulEquiv_mapPointsFunctor_diagonalTorusCoordinateMap
    (A : Type w) [CommRing A] [Algebra R A]
    (p : HopfAlgebra.points (R := R)
      (H := MonoidAlgebra R (SplitTorus.characterGroup (ULift.{u} (Fin r))))
      (CommAlgCat.of R A)) :
    Matrix.SpecialLinearGroup.toGL
        (pointsMulEquiv (R := R) (A := A) (r + 1)
          ((CommHopfAlgCat.mapPointsFunctor (diagonalTorusCoordinateMap r R)).app
            (CommAlgCat.of R A) p)) =
      diagGL fun k ↦ torusCharacter (SplitTorus.pointsMulEquiv p) (diagonalTorusWeight r k) := by
  -- `quotientPointsHom` is by definition the point map of the quotient coordinate morphism.
  have hquot : CommHopfAlgCat.quotientPointsHom (GeneralLinear.coordinateHopfAlgebra R (r + 1))
      (definingHopfIdeal R (r + 1)) (CommAlgCat.of R A)
        ((CommHopfAlgCat.mapPointsFunctor (diagonalTorusCoordinateMap r R)).app
          (CommAlgCat.of R A) p) =
      (CommHopfAlgCat.mapPointsFunctor
        (coordinateMap R (r + 1) ≫ diagonalTorusCoordinateMap r R)).app (CommAlgCat.of R A) p :=
    by rw [CommHopfAlgCat.mapPointsFunctor_comp_app_apply]; rfl
  refine (pointsMulEquiv_toGL R (r + 1) _).symm.trans ?_
  rw [hquot, coordinateMap_comp_diagonalTorusCoordinateMap]
  exact GeneralLinear.pointsMulEquiv_mapPointsFunctor_weightTorusCoordinateMap _ _ p

/-- **The diagonal-torus coordinate morphism of `SL_{r+1}` commutes with base change.** -/
theorem diagonalTorusCoordinateMap_baseChange (K : Type u) [CommRing K] [Algebra R K] :
    (coordinateHopfAlgebraBaseChangeIso R K (r + 1)).inv ≫
        CommHopfAlgCat.baseChangeMap (diagonalTorusCoordinateMap r R) ≫
        (DiagonalizableGroup.baseChangeCoordinateHopfAlgebraIso R K
          (SplitTorus.characterGroup (ULift.{u} (Fin r)))).hom =
      diagonalTorusCoordinateMap r K := by
  have hpre :
      coordinateMap K (r + 1) ≫ (coordinateHopfAlgebraBaseChangeIso R K (r + 1)).inv =
        (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K (r + 1)).inv ≫
          CommHopfAlgCat.baseChangeMap (coordinateMap R (r + 1)) := by
    apply (cancel_mono (coordinateHopfAlgebraBaseChangeIso R K (r + 1)).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      baseChangeMap_coordinateMap_comp_coordinateHopfAlgebraBaseChangeIso_hom,
      Iso.inv_hom_id_assoc]
  apply CommHopfAlgCat.mkQuotient_hom_ext
  rw [← Category.assoc, hpre, Category.assoc,
    ← Category.assoc (CommHopfAlgCat.baseChangeMap (coordinateMap R (r + 1))),
    ← (CommHopfAlgCat.baseChangeFunctor (K := K)).map_comp]
  rw [coordinateMap_comp_diagonalTorusCoordinateMap, coordinateMap_comp_diagonalTorusCoordinateMap]
  rw [← GeneralLinear.weightTorusBaseChangeCoordinateMap_def]
  exact GeneralLinear.weightTorusBaseChangeCoordinateMap_eq R K _

end TauCeti.SpecialLinear
