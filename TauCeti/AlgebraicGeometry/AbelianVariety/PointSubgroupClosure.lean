/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AbelianVariety.Hom.Basic
public import TauCeti.AlgebraicGeometry.GroupScheme.ClosedSubgroup.Closure
public import TauCeti.AlgebraicGeometry.GroupScheme.IdentityComponent
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyIntegral
import TauCeti.AlgebraicGeometry.Noetherian
import TauCeti.Topology.NoetherianSpace.ConnectedComponents

/-!
# The identity component of the closure of a subgroup of abelian variety points

For an abelian variety over a perfect field, the reduced Zariski closure of a subgroup of
rational points has finitely many connected components. Its identity component is an abelian
variety, and the inclusion into the original variety is a closed immersion. Applied to the
subgroup of prime-power torsion points, this supplies the abelian subvariety used in the
dimension comparison in Milne, *Abelian Varieties* (2022), §12, in the lemma on torsion density.
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open scoped MonObj

namespace TauCeti.AlgebraicGeometry.AbelianVariety

universe u

variable {K : Type u} [Field K] [PerfectField K] (A : AbelianVariety K)
  (H : Subgroup (𝟙_ (Over (Spec (.of K))) ⟶ A.toOver))

private abbrev closureGroup : Grp (Over (Spec (.of K))) :=
  (ClosedSubgroupScheme.ofPointSubgroup (G := Grp.mk A.toOver) H).val

/-- The identity component of the reduced closure of a subgroup of rational points of an abelian
variety is itself an abelian variety. -/
def pointSubgroupClosureIdentityComponent : AbelianVariety K where
  toOver := (closureGroup A H).identityComponent.X
  grpObj := inferInstance
  isProper := inferInstance
  geometricallyIntegral := inferInstance

@[simp]
theorem pointSubgroupClosureIdentityComponent_toOver :
    (A.pointSubgroupClosureIdentityComponent H).toOver =
      (((ClosedSubgroupScheme.ofPointSubgroup (G := Grp.mk A.toOver) H).val :
        Grp (Over (Spec (.of K)))).identityComponent).X :=
  (rfl)

/-- The inclusion from the identity component of the reduced closure into the original abelian
variety. -/
def pointSubgroupClosureIdentityComponentι : A.pointSubgroupClosureIdentityComponent H ⟶ A :=
  let f := (closureGroup A H).identityComponentι ≫
    (ClosedSubgroupScheme.ofPointSubgroup (G := Grp.mk A.toOver) H).val.arrow
  Hom.mk' f.hom.hom f.hom.isMonHom_hom.one_hom f.hom.isMonHom_hom.mul_hom

private theorem toSchemeHom_pointSubgroupClosureIdentityComponentι :
    Hom.toSchemeHom (A.pointSubgroupClosureIdentityComponentι H) =
      (closureGroup A H).identityComponentι.hom.hom.left ≫
        (ClosedSubgroupScheme.ofPointSubgroup (G := Grp.mk A.toOver) H).val.arrow.hom.hom.left := by
  let i := (closureGroup A H).identityComponentι
  let j := (ClosedSubgroupScheme.ofPointSubgroup (G := Grp.mk A.toOver) H).val.arrow
  let f := i ≫ j
  have h := Hom.toSchemeHom_mk' (A := A.pointSubgroupClosureIdentityComponent H) (B := A)
    f.hom.hom f.hom.isMonHom_hom.one_hom f.hom.isMonHom_hom.mul_hom
  exact h.trans ((congrArg Over.Hom.left (Grp.comp_hom_hom i j)).trans (Over.comp_left _ _ _ _ _))

/-- The image of the inclusion is the image of the connected component of the identity in the
closure group. -/
theorem range_pointSubgroupClosureIdentityComponentι :
    Set.range (Hom.toSchemeHom (A.pointSubgroupClosureIdentityComponentι H)) =
      (ClosedSubgroupScheme.ofPointSubgroup (G := Grp.mk A.toOver) H).val.arrow.hom.hom.left ''
        Set.range (((ClosedSubgroupScheme.ofPointSubgroup (G := Grp.mk A.toOver) H).val :
          Grp (Over (Spec (.of K)))).identityComponentι).hom.hom.left := by
  let i := (closureGroup A H).identityComponentι.hom.hom.left
  let j := (ClosedSubgroupScheme.ofPointSubgroup (G := Grp.mk A.toOver) H).val.arrow.hom.hom.left
  calc
    _ = Set.range (i ≫ j) := congrArg
      (fun f : (A.pointSubgroupClosureIdentityComponent H).toScheme ⟶ A.toScheme ↦ Set.range f)
      (toSchemeHom_pointSubgroupClosureIdentityComponentι A H)
    _ = _ := Set.range_comp j i

/-- The identity component of the closure is a closed abelian subvariety of the original
variety. -/
instance isClosedImmersion_pointSubgroupClosureIdentityComponentι :
    IsClosedImmersion (Hom.toSchemeHom (A.pointSubgroupClosureIdentityComponentι H)) := by
  exact (toSchemeHom_pointSubgroupClosureIdentityComponentι A H).symm ▸
    inferInstanceAs (IsClosedImmersion ((closureGroup A H).identityComponentι.hom.hom.left ≫
      (ClosedSubgroupScheme.ofPointSubgroup (G := Grp.mk A.toOver) H).val.arrow.hom.hom.left))

/-- The reduced closure of a subgroup of points of an abelian variety has finitely many
connected components. -/
instance finite_connectedComponents_pointSubgroupClosure :
    Finite (ConnectedComponents ((ClosedSubgroupScheme.ofPointSubgroup
      (G := Grp.mk A.toOver) H).val : Grp (Over (Spec (.of K)))).X.left) := by
  have := TauCeti.AlgebraicGeometry.isNoetherian_of_finiteType (closureGroup A H).X.hom
  infer_instance

end TauCeti.AlgebraicGeometry.AbelianVariety
