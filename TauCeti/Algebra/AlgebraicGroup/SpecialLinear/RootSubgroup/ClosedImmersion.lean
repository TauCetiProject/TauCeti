/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.RootSubgroup.Basic
public import TauCeti.AlgebraicGeometry.GroupScheme.ClosedSubgroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Basic
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Kernel
import TauCeti.AlgebraicGeometry.AffineGroupScheme.ClosedImmersion
import TauCeti.Algebra.AlgebraicGroup.Hopf.KernelPoints

/-!
# Closed additive root subgroups of the special linear group

The elementary root map `xᵢⱼ : 𝔾ₐ → SLₙ` is a closed immersion over every commutative ring.
Its composite with `SLₙ → GLₙ` is the general-linear root map, so the surjectivity of that
coordinate morphism gives surjectivity of the special-linear coordinate morphism as well.

Thus `rootSubgroupClosedSubgroup` is a closed subgroup scheme isomorphic to `𝔾ₐ` through
its specified root map, as required to use the elementary root maps in a pinning.
The isomorphism `rootSubgroupClosedSubgroupIso` records this parametrization, and its
inverse followed by the inclusion recovers the original root map.

On coordinate rings, the closed root subgroup is cut out by the Hopf ideal
`rootSubgroupHopfIdeal`, the kernel of the surjective coordinate morphism `O(SLₙ) → O(𝔾ₐ)`;
its points are exactly the elementary transvections `1 + t Eᵢⱼ`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §21.
* R. W. Carter, *Simple Groups of Lie Type* (1972), §11.3.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.SpecialLinear

universe u

variable {R : Type u} [CommRing R] {N : ℕ} {i j : Fin N}

/-- Every elementary root map identifies `𝔾ₐ` with a closed subscheme of `SLₙ`. -/
instance isClosedImmersion_rootSubgroup (hij : i ≠ j) :
    IsClosedImmersion (rootSubgroup (R := R) hij).hom.hom.left := by
  rw [rootSubgroup_def]
  exact (CommHopfAlgCat.isClosedImmersion_eqToHom_comp_hopfSpec_map_comp_eqToHom_iff
    (AdditiveGroup.groupScheme_def R) (groupScheme_def R N) _).mpr
    (rootSubgroupCoordinateMap_surjective hij)

/-- The closed additive root subgroup of `SLₙ` attached to `εᵢ - εⱼ`, with its elementary
parametrization. -/
noncomputable def rootSubgroupClosedSubgroup (hij : i ≠ j) :
    ClosedSubgroupScheme (groupScheme R N) :=
  ClosedSubgroupScheme.mk (rootSubgroup hij)

/-- The special-linear root map represents its named closed root subgroup. -/
@[simp]
theorem coe_rootSubgroupClosedSubgroup (hij : i ≠ j) :
    (rootSubgroupClosedSubgroup (R := R) hij).1 = Subobject.mk (rootSubgroup hij) :=
  ClosedSubgroupScheme.coe_mk _

/-- The closed special-linear root subgroup is canonically isomorphic to `𝔾ₐ`. -/
noncomputable def rootSubgroupClosedSubgroupIso (hij : i ≠ j) :
    ((rootSubgroupClosedSubgroup (R := R) hij).1 :
      Grp (Over (Spec (CommRingCat.of R)))) ≅ AdditiveGroup.groupScheme R :=
  ClosedSubgroupScheme.mkIso (rootSubgroup hij)

/-- The parametrization followed by the closed subgroup inclusion is the special-linear
root map. -/
@[simp]
theorem rootSubgroupClosedSubgroupIso_inv_comp_arrow (hij : i ≠ j) :
    (rootSubgroupClosedSubgroupIso (R := R) hij).inv ≫
        (rootSubgroupClosedSubgroup (R := R) hij).1.arrow = rootSubgroup hij :=
  ClosedSubgroupScheme.mkIso_inv_comp_arrow _

/-! ### The Hopf ideal of a root subgroup -/

/-- The Hopf ideal of the closed root subgroup `xᵢⱼ(𝔾ₐ) ⊆ SLₙ`: the kernel of the surjective
root-subgroup coordinate morphism `O(SLₙ) → O(𝔾ₐ)`. -/
noncomputable def rootSubgroupHopfIdeal (hij : i ≠ j) :
    HopfIdeal R (coordinateHopfAlgebra R N) :=
  HopfIdeal.kerOfSurjective (rootSubgroupCoordinateMap hij).hom
    (rootSubgroupCoordinateMap_surjective hij)

/-- A function lies in the root-subgroup Hopf ideal exactly when it vanishes on the root
subgroup. -/
@[simp]
theorem mem_rootSubgroupHopfIdeal (hij : i ≠ j) {h : coordinateHopfAlgebra R N} :
    h ∈ rootSubgroupHopfIdeal hij ↔ (rootSubgroupCoordinateMap hij).hom h = 0 :=
  HopfIdeal.mem_kerOfSurjective _ _

variable {A : Type u} [CommRing A] [Algebra R A]

/-- The points of `SLₙ` lying in the root subgroup `xᵢⱼ(𝔾ₐ)` are exactly the elementary
transvections `1 + t Eᵢⱼ`. -/
theorem mem_quotientPointsSubgroup_rootSubgroupHopfIdeal_iff (hij : i ≠ j)
    (g : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R N) (CommAlgCat.of R A)) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra R N)
        (rootSubgroupHopfIdeal hij) (CommAlgCat.of R A) ↔
      ∃ t : A, pointsMulEquiv (R := R) (A := A) N g =
        Matrix.SpecialLinearGroup.transvection hij t := by
  rw [rootSubgroupHopfIdeal,
    HopfIdeal.quotientPointsSubgroup_kerOfSurjective_eq_range_mapPointsFunctor]
  constructor
  · rintro ⟨f, rfl⟩
    refine ⟨Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := R) (A := A) f), ?_⟩
    rw [← pointsMulEquiv_rootSubgroupPoints hij f,
      ← mapPointsFunctor_rootSubgroupCoordinateMap_app hij (CommAlgCat.of R A) f]
  · rintro ⟨t, ht⟩
    refine ⟨(AdditiveGroup.gaPointsMulEquiv (R := R) (A := A)).symm (Multiplicative.ofAdd t), ?_⟩
    apply (pointsMulEquiv (R := R) (A := A) N).injective
    have hf := mapPointsFunctor_rootSubgroupCoordinateMap_app hij (CommAlgCat.of R A)
      ((AdditiveGroup.gaPointsMulEquiv (R := R) (A := A)).symm (Multiplicative.ofAdd t))
    rw [ht]
    refine (congrArg (pointsMulEquiv (R := R) (A := A) N) hf).trans ?_
    rw [pointsMulEquiv_rootSubgroupPoints, MulEquiv.apply_symm_apply, toAdd_ofAdd]

end TauCeti.SpecialLinear
