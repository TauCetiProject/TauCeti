/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Root.Subgroup
public import TauCeti.AlgebraicGeometry.GroupScheme.ClosedSubgroup
import TauCeti.AlgebraicGeometry.AffineGroupScheme.ClosedImmersion
public import TauCeti.CategoryTheory.Comma.Over

/-!
# Matrix root subgroups are closed additive groups

Over any commutative base ring, the root map `xᵢⱼ : 𝔾ₐ → GLₙ` identifies the additive group
with a closed subgroup scheme. Its coordinate morphism is surjective: the `(i, j)` entry of
the generic matrix maps to the additive parameter. This is a scheme-theoretic statement,
including over nonreduced rings, rather than just injectivity on rational points.

The closed subgroup `rootSubgroupClosedSubgroup` retains the explicit parametrization by
`rootSubgroup`; `rootSubgroupClosedSubgroupIso` identifies it with `𝔾ₐ`. These closed additive
subgroups are the root subgroups used in pinnings of the general and special linear groups.

The surjectivity argument generalizes the private integral argument formerly in
`TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.AllRootSubgroups.Basic`. The passage from
coordinates to closed subgroups follows
`TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ClosedImmersion`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §21.
* R. W. Carter, *Simple Groups of Lie Type* (1972), §11.3.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.GeneralLinear

universe u

variable {R : Type u} [CommRing R] {N : ℕ} {i j : Fin N}

/-- The root-subgroup coordinate morphism is surjective over every commutative base ring. -/
theorem rootSubgroupCoordinateMap_surjective (hij : i ≠ j) :
    Function.Surjective (rootSubgroupCoordinateMap (R := R) hij).hom := by
  classical
  let f := (rootSubgroupCoordinateMap (R := R) hij).hom.toAlgHom
  have hgen : SymmetricAlgebra.ι R R 1 ∈ f.range := by
    refine (AlgHom.mem_range _).mpr ⟨coordinateHopfAlgebraAlgEquiv R N
      (coordinateRingMap R N (MvPolynomial.X (i, j))), ?_⟩
    simpa [f, BialgHom.coe_toAlgHom, Matrix.one_apply, hij] using
      rootSubgroupCoordinateMap_apply_X (R := R) hij i j
  intro y
  have hy : y ∈ f.range := by
    induction y using SymmetricAlgebra.induction with
    | algebraMap r => exact f.range.algebraMap_mem r
    | ι r =>
        have hr : SymmetricAlgebra.ι R R r = r • SymmetricAlgebra.ι R R 1 := by
          rw [← map_smul]
          simp
        rw [hr]
        exact Submodule.smul_mem f.range.toSubmodule r hgen
    | mul y z hy hz => exact mul_mem hy hz
    | add y z hy hz => exact add_mem hy hz
  exact (AlgHom.mem_range _).mp hy

/-- Every matrix root map identifies `𝔾ₐ` with a closed subscheme of `GLₙ`. -/
instance isClosedImmersion_rootSubgroup (hij : i ≠ j) :
    IsClosedImmersion (rootSubgroup (R := R) hij).hom.hom.left := by
  rw [rootSubgroup_def]
  simp only [Grp.comp', Mon.comp_hom', Over.comp_left]
  rw [MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion),
    MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion)]
  exact (CommHopfAlgCat.isClosedImmersion_hopfSpec_map_iff _).mpr
    (rootSubgroupCoordinateMap_surjective hij)

/-- The closed additive root subgroup of `GLₙ` attached to `εᵢ - εⱼ`, parametrized by
`rootSubgroup hij`. -/
noncomputable def rootSubgroupClosedSubgroup (hij : i ≠ j) :
    ClosedSubgroupScheme (groupScheme R N) :=
  ClosedSubgroupScheme.mk (rootSubgroup hij)

/-- The root map represents its named closed root subgroup. -/
@[simp]
theorem coe_rootSubgroupClosedSubgroup (hij : i ≠ j) :
    (rootSubgroupClosedSubgroup (R := R) hij).1 = Subobject.mk (rootSubgroup hij) :=
  ClosedSubgroupScheme.coe_mk _

/-- The closed matrix root subgroup is canonically isomorphic to the additive group scheme. -/
noncomputable def rootSubgroupClosedSubgroupIso (hij : i ≠ j) :
    ((rootSubgroupClosedSubgroup (R := R) hij).1 :
      Grp (Over (Spec (CommRingCat.of R)))) ≅ AdditiveGroup.groupScheme R :=
  ClosedSubgroupScheme.mkIso (rootSubgroup hij)

/-- The additive parametrization followed by the closed subgroup inclusion is the root map. -/
@[simp]
theorem rootSubgroupClosedSubgroupIso_inv_comp_arrow (hij : i ≠ j) :
    (rootSubgroupClosedSubgroupIso (R := R) hij).inv ≫
        (rootSubgroupClosedSubgroup (R := R) hij).1.arrow = rootSubgroup hij :=
  ClosedSubgroupScheme.mkIso_inv_comp_arrow _

end TauCeti.GeneralLinear
