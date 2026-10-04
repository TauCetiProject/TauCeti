/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.RootSubgroup.Basic
public import TauCeti.AlgebraicGeometry.GroupScheme.ClosedSubgroup
import TauCeti.AlgebraicGeometry.AffineGroupScheme.ClosedImmersion

/-!
# Closed additive root subgroups of the special linear group

The elementary root map `xᵢⱼ : 𝔾ₐ → SLₙ` is a closed immersion over every commutative ring.
Its composite with `SLₙ → GLₙ` is the general-linear root map, so the surjectivity of that
coordinate morphism gives surjectivity of the special-linear coordinate morphism as well.

Thus `rootSubgroupClosedSubgroup` is a closed subgroup scheme isomorphic to `𝔾ₐ` through
its specified root map, as required to use the elementary root maps in a pinning.
The isomorphism `rootSubgroupClosedSubgroupIso` records this parametrization, and its
inverse followed by the inclusion recovers the original root map.

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

end TauCeti.SpecialLinear
