/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import TauCeti.AlgebraicGeometry.Geometrically.Connected
public import TauCeti.CategoryTheory.Monoidal.Grp.Subobject
import TauCeti.AlgebraicGeometry.Noetherian
import TauCeti.AlgebraicGeometry.Scheme.Connected.Component

/-!
# The identity component of a group scheme

For a group scheme locally of finite type over a field, the connected component containing
the identity is an open and closed subgroup scheme. Its identity gives a rational point, so
the component is geometrically connected. It inherits smoothness and properness from the
ambient group scheme.

## References

* The Stacks Project, Proposition 39.7.11, Tag [0B7R](https://stacks.math.columbia.edu/tag/0B7R).
-/

public section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace CategoryTheory.Grp

universe u

noncomputable section

section LocallyOfFiniteType

variable {k : Type u} [Field k] (G : Grp (Over (Spec (.of k))))
  [LocallyOfFiniteType G.X.hom]

private def identityOpen : G.X.left.Opens :=
  have : IsLocallyNoetherian G.X.left := LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  G.X.left.connectedComponentOpen (η[G.X].left (IsLocalRing.closedPoint k))

private theorem coe_identityOpen : (identityOpen G : Set G.X.left) =
    connectedComponent (η[G.X].left (IsLocalRing.closedPoint k)) := by
  have : IsLocallyNoetherian G.X.left := LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  unfold identityOpen
  exact Scheme.coe_connectedComponentOpen _ _

private instance : ConnectedSpace (identityOpen G).toScheme := by
  unfold identityOpen
  infer_instance

private abbrev identityOver : Over (Spec (.of k)) :=
  Over.mk ((identityOpen G).ι ≫ G.X.hom)

private abbrev identityOverι : identityOver G ⟶ G.X :=
  Over.homMk (identityOpen G).ι (by rfl)

private instance : Mono (identityOverι G) := Over.mono_of_mono_left _

private def liftIdentityOver {X : Over (Spec (.of k))} (f : X ⟶ G.X)
    (hf : Set.range f.left ⊆ connectedComponent (η[G.X].left (IsLocalRing.closedPoint k))) :
    X ⟶ identityOver G :=
  Over.homMk (IsOpenImmersion.lift (identityOpen G).ι f.left (by
    rwa [Scheme.Opens.range_ι, coe_identityOpen])) (by simp [identityOver])

@[simp]
private theorem liftIdentityOver_ι {X : Over (Spec (.of k))} (f : X ⟶ G.X)
    (hf : Set.range f.left ⊆ connectedComponent (η[G.X].left (IsLocalRing.closedPoint k))) :
    liftIdentityOver G f hf ≫ identityOverι G = f := by
  ext1
  simp [liftIdentityOver]

private def identityOne : 𝟙_ (Over (Spec (.of k))) ⟶ identityOver G :=
  liftIdentityOver G η[G.X] (by
    have : Subsingleton (𝟙_ (Over (Spec (.of k)))).left :=
      inferInstanceAs (Subsingleton (Spec (.of k)))
    rintro _ ⟨s, rfl⟩
    rw [Subsingleton.elim s (IsLocalRing.closedPoint k)]
    exact mem_connectedComponent)

@[simp]
private theorem identityOne_ι : identityOne G ≫ identityOverι G = η[G.X] :=
  liftIdentityOver_ι _ _ _

private instance : GeometricallyConnected (identityOver G).hom := by
  have : ConnectedSpace (identityOver G).left := inferInstanceAs
    (ConnectedSpace (identityOpen G).toScheme)
  exact TauCeti.geometricallyConnected_of_section
    (Over.w (identityOne G) |>.trans Over.tensorUnit_hom)

omit [LocallyOfFiniteType G.X.hom] in
private theorem range_subset_identityComponent_of_comp_eq_one
    {X : Over (Spec (.of k))} [PreconnectedSpace X.left]
    (f : X ⟶ G.X) (a : 𝟙_ (Over (Spec (.of k))) ⟶ X) (h : a ≫ f = η[G.X]) :
    Set.range f.left ⊆ connectedComponent (η[G.X].left (IsLocalRing.closedPoint k)) := by
  let p : (𝟙_ (Over (Spec (.of k)))).left := IsLocalRing.closedPoint k
  apply (isPreconnected_range f.left.continuous).subset_connectedComponent
  refine ⟨a.left p, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, h]

private theorem range_identityMul :
    Set.range (((identityOverι G) ⊗ₘ (identityOverι G)) ≫ μ[G.X]).left ⊆
      connectedComponent (η[G.X].left (IsLocalRing.closedPoint k)) := by
  have hconnected : ConnectedSpace ((identityOver G) ⊗ (identityOver G)).left := by
    have : ConnectedSpace (identityOver G).left := inferInstanceAs
      (ConnectedSpace (identityOpen G).toScheme)
    have : LocallyOfFiniteType (identityOver G).hom := inferInstanceAs
      (LocallyOfFiniteType ((identityOpen G).ι ≫ G.X.hom))
    rw [Over.tensorObj_left]
    infer_instance
  apply range_subset_identityComponent_of_comp_eq_one G _ (lift (identityOne G) (identityOne G))
  simp [← Hom.mul_def, MonObj.one_eq_one]

private theorem range_identityInv :
    Set.range (identityOverι G ≫ ι[G.X]).left ⊆
      connectedComponent (η[G.X].left (IsLocalRing.closedPoint k)) := by
  have : ConnectedSpace (identityOver G).left := inferInstanceAs
    (ConnectedSpace (identityOpen G).toScheme)
  apply range_subset_identityComponent_of_comp_eq_one G _ (identityOne G)
  rw [← Category.assoc, identityOne_ι, GrpObj.one_inv]

private instance identityOverGrpObj : GrpObj (identityOver G) :=
  TauCeti.grpObjOfMono (identityOverι G) (identityOne G)
    (liftIdentityOver G _ (range_identityMul G)) (liftIdentityOver G _ (range_identityInv G))
    (identityOne_ι G) (liftIdentityOver_ι _ _ _) (liftIdentityOver_ι _ _ _)

private instance : IsMonHom (identityOverι G) :=
  TauCeti.isMonHom_grpObjOfMono ..

/-- The identity component of a group scheme locally of finite type over a field, equipped with
its open subscheme structure and the induced group law. -/
def identityComponent : Grp (Over (Spec (.of k))) :=
  Grp.mk (identityOver G)

/-- The inclusion of the identity component into the original group scheme. -/
def identityComponentι : G.identityComponent ⟶ G :=
  Grp.ofHom (identityOverι G)

instance isOpenImmersion_identityComponentι : IsOpenImmersion G.identityComponentι.hom.hom.left :=
  inferInstanceAs (IsOpenImmersion (identityOpen G).ι)

instance isClosedImmersion_identityComponentι :
    IsClosedImmersion G.identityComponentι.hom.hom.left := by
  have : IsLocallyNoetherian G.X.left := LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  exact inferInstanceAs (IsClosedImmersion
    (G.X.left.connectedComponentOpen (η[G.X].left (IsLocalRing.closedPoint k))).ι)

/-- The image of the inclusion is the connected component of the identity point. -/
@[simp]
theorem range_identityComponentι :
    Set.range G.identityComponentι.hom.hom.left =
      connectedComponent (η[G.X].left (IsLocalRing.closedPoint k)) := by
  rw [← coe_identityOpen, ← Scheme.Opens.range_ι]
  rfl

instance connectedSpace_identityComponent : ConnectedSpace G.identityComponent.X.left :=
  inferInstanceAs (ConnectedSpace (identityOpen G).toScheme)

instance geometricallyConnected_identityComponent :
    GeometricallyConnected G.identityComponent.X.hom :=
  inferInstanceAs (GeometricallyConnected (identityOver G).hom)

instance locallyOfFiniteType_identityComponent : LocallyOfFiniteType G.identityComponent.X.hom :=
  inferInstanceAs (LocallyOfFiniteType (G.identityComponentι.hom.hom.left ≫ G.X.hom))

end LocallyOfFiniteType

variable {k : Type u} [Field k] (G : Grp (Over (Spec (.of k))))

instance smooth_identityComponent [Smooth G.X.hom] : Smooth G.identityComponent.X.hom :=
  inferInstanceAs (Smooth (G.identityComponentι.hom.hom.left ≫ G.X.hom))

instance isProper_identityComponent [IsProper G.X.hom] : IsProper G.identityComponent.X.hom :=
  inferInstanceAs (IsProper (G.identityComponentι.hom.hom.left ≫ G.X.hom))

end

end CategoryTheory.Grp
