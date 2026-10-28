/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Points
public import TauCeti.Algebra.AlgebraicGroup.Representation.Tannaka.GroupFunctor

/-!
# Tannakian reconstruction of affine group-scheme points

For an affine group scheme over a field, its algebra-valued points are naturally the
tensor automorphisms of scalar extension on finite comodules of its coordinate Hopf
algebra. This transports the native reconstruction theorem
`TauCeti.Tannaka.pointsFunctorIsoTensorAutFunctor` through the scheme/coordinate-point
dictionary, rather than reconstructing points a second time.

The coordinate Hopf algebra and its presentation of the group scheme come from
`TauCeti.commHopfAlgCatOpEquivAffineGroupSchemeCat`. The comparison retains the universe
lift of native Tannakian reconstruction. The component equations characterize both the
tensor action of a scheme point and the scheme point reconstructed from a tensor
automorphism. Naturality is in every commutative value algebra, including nonreduced
algebras, with no finite-type or smoothness hypothesis on the group scheme.

## References

* J. S. Milne, *Algebraic Groups* (2017), §9.4.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace TauCeti.AffineGroupSchemeCat

universe u

variable (k : Type u) [Field k] (G : AffineGroupSchemeCat (CommRingCat.of k))

/-- Algebra-valued scheme points of an affine group scheme are tensor automorphisms of
scalar extension on finite comodules of its coordinate Hopf algebra, naturally in the
value algebra. The universe lift is the one in native Tannakian reconstruction. -/
noncomputable def algebraPointsFunctorIsoTensorAutFunctor :
    GroupScheme.algebraPointsFunctor k G.obj ⋙ GrpCat.uliftFunctor.{u + 1, u} ≅
      Tannaka.tensorAutFunctor k
        ((commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of k)).inverse.obj G).unop :=
  Functor.isoWhiskerRight (algebraPointsFunctorIsoCoordinatePointsFunctor k G)
      GrpCat.uliftFunctor ≪≫
    Tannaka.pointsFunctorIsoTensorAutFunctor k _

/-- The tensor automorphism of a scheme point is the tensor action of the corresponding
coordinate point. This equation also fixes its direction relative to scheme points. -/
theorem algebraPointsFunctorIsoTensorAutFunctor_hom_app_apply (A : CommAlgCat.{u} k)
    (p : ULift.{u + 1}
      ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of k)) ⟶ G.obj.X)) :
    eqToHom (Tannaka.tensorAutFunctor_obj k _ A)
        ((algebraPointsFunctorIsoTensorAutFunctor k G).hom.app A p) =
      Tannaka.fgPointTensorIso k _ A
        ((algebraPointsFunctorIsoCoordinatePointsFunctor k G).hom.app A p.down) := by
  rw [algebraPointsFunctorIsoTensorAutFunctor, Iso.trans_hom, NatTrans.comp_app]
  -- Whiskering by `GrpCat.uliftFunctor` sends `p` to `ULift.up` of the coordinate
  -- comparison at `p.down`; evaluating the `GrpCat` composite reduces to that application.
  exact Tannaka.pointsFunctorIsoTensorAutFunctor_hom_app_apply k _ A _

/-- The inverse comparison reconstructs the native coordinate point and then transports it
back to the affine group scheme. -/
theorem algebraPointsFunctorIsoTensorAutFunctor_inv_app_apply (A : CommAlgCat.{u} k)
    (eta : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor k
      ((commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of k)).inverse.obj G).unop A)) :
    (algebraPointsFunctorIsoTensorAutFunctor k G).inv.app A
        (eqToHom (Tannaka.tensorAutFunctor_obj k _ A).symm eta) =
      ULift.up ((algebraPointsFunctorIsoCoordinatePointsFunctor k G).inv.app A
        (Tannaka.reconstructedPoint k _ A eta)) := by
  rw [algebraPointsFunctorIsoTensorAutFunctor, Iso.trans_inv, NatTrans.comp_app]
  -- The inverse whiskered component applies the coordinate comparison under `ULift.up`
  -- to the reconstructed point; `GrpCat` composition and `.down` reduce definitionally.
  have h := Tannaka.pointsFunctorIsoTensorAutFunctor_inv_app_apply k _ A eta
  exact congrArg (fun p ↦ ULift.up
    ((algebraPointsFunctorIsoCoordinatePointsFunctor k G).inv.app A p)) h

end TauCeti.AffineGroupSchemeCat
