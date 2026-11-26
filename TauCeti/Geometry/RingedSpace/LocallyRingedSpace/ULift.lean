/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Mathlib.Topology.Category.TopCat.ULift
public import TauCeti.Algebra.Category.Ring.ULift
public import TauCeti.Topology.Sheaves.Homeomorph
import Mathlib.CategoryTheory.Filtered.Final

/-!
# The universe lift of a locally ringed space

For a locally ringed space `X` in universe `u`, `X.ulift` is the locally ringed space in universe
`max u v` whose points are `ULift X` and whose ring of sections over the open set corresponding to
`U ⊆ X` is `ULift 𝒪_X(U)`. This transports locally ringed spaces built from types in universe `0`,
such as spaces of holomorphic functions on open subsets of `ℂⁿ`, to any universe.

## Main definitions

* `AlgebraicGeometry.LocallyRingedSpace.uliftOpensEquiv X`: the open sets of `ULift X` are those
  of `X`.
* `AlgebraicGeometry.LocallyRingedSpace.ulift X`: the universe lift of `X`.
* `AlgebraicGeometry.LocallyRingedSpace.uliftStalkIso X x`: the stalk of `X.ulift` at
  `ULift.up x` is `ULift` of the stalk of `X` at `x`; `uliftStalkRingEquiv X x` is the resulting
  ring isomorphism with the stalk of `X` at `x`.
* `AlgebraicGeometry.LocallyRingedSpace.uliftΓIso X`: the global sections of `X.ulift` are `ULift`
  of those of `X`.

The sheaf condition is transported along `CommRingCat.uliftFunctor`, which preserves `u`-small
limits, and along the equivalence of the sites of open sets. The stalks are computed with
`CommRingCat.uliftFunctor`, which preserves `u`-small filtered colimits, and with the finality of
the corresponding functor between open neighbourhoods.
-/

public noncomputable section

universe v u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.LocallyRingedSpace

variable (X : LocallyRingedSpace.{u})

/-- The open sets of the universe lift `ULift X` of the underlying space of `X` correspond to
those of `X`, by taking preimages along `ULift.up`. -/
@[expose]
def uliftOpensEquiv : Opens (TopCat.uliftFunctor.{v}.obj X.carrier) ≌ Opens X.carrier :=
  (TopCat.uliftFunctorObjHomeo.{v} X.carrier).symm.opensCongr.equivalence

/-- A point `x` lies in the open set of `X` corresponding to an open set `U` of `ULift X` exactly
when `ULift.up x` lies in `U`. -/
@[simp]
theorem mem_uliftOpensEquiv_functor_obj {U : Opens (TopCat.uliftFunctor.{v}.obj X.carrier)}
    {x : X.carrier} : x ∈ (uliftOpensEquiv.{v} X).functor.obj U ↔ ULift.up x ∈ U :=
  Iff.rfl

/-- The whole space of `ULift X` corresponds to the whole space of `X`. -/
@[simp]
theorem uliftOpensEquiv_functor_obj_top :
    (uliftOpensEquiv.{v} X).functor.obj ⊤ = ⊤ :=
  (rfl)

/-- The correspondence of open sets is a continuous functor of sites, by
`Homeomorph.opensCongr_isDenseSubsite`; this transports the sheaf condition from `X` to its
universe lift. -/
instance : (uliftOpensEquiv.{v} X).functor.IsContinuous (Opens.grothendieckTopology _)
    (Opens.grothendieckTopology _) :=
  inferInstanceAs
    ((TopCat.uliftFunctorObjHomeo.{v} X.carrier).symm.opensCongr.equivalence.functor.IsContinuous
      (Opens.grothendieckTopology _) (Opens.grothendieckTopology _))

/-- The structure presheaf of the universe lift: its sections over an open set `U` of `ULift X`
are `ULift` of the sections of `X` over the corresponding open set of `X`. -/
@[expose]
def uliftPresheaf :
    (TopCat.uliftFunctor.{v}.obj X.carrier).Presheaf CommRingCat.{max u v} :=
  (uliftOpensEquiv.{v} X).functor.op ⋙ X.presheaf ⋙ CommRingCat.uliftFunctor.{v}

/-- The sections of the lifted structure presheaf over `U` are `ULift` of the sections of `X` over
the corresponding open set. -/
theorem uliftPresheaf_obj (U : Opens (TopCat.uliftFunctor.{v}.obj X.carrier)) :
    (uliftPresheaf.{v} X).obj (op U) =
      CommRingCat.uliftFunctor.{v}.obj
        (X.presheaf.obj (op ((uliftOpensEquiv.{v} X).functor.obj U))) :=
  (rfl)

/-- The lifted structure presheaf is a sheaf. -/
theorem isSheaf_uliftPresheaf : (uliftPresheaf.{v} X).IsSheaf :=
  Functor.op_comp_isSheaf_of_isSheaf _ _ _ _ (Presheaf.isSheaf_comp_of_isSheaf _ _ _ X.IsSheaf)

/-- Open neighbourhoods of `ULift.up x` in `ULift X` give open neighbourhoods of `x` in `X`. -/
def uliftOpenNhdsFunctor (x : X.carrier) :
    OpenNhds (TopCat.uliftFunctorObjHomeo.{v} X.carrier x) ⥤ OpenNhds x :=
  Monotone.functor (f := fun U ↦ (⟨(uliftOpensEquiv.{v} X).functor.obj U.val, U.property⟩ :
      OpenNhds x))
    fun _ _ h ↦ ((uliftOpensEquiv.{v} X).functor.map (homOfLE h)).le

/-- Every open neighbourhood of `x` contains one coming from `ULift X`, so stalks of the universe
lift may be computed on the neighbourhoods of `x`. -/
instance (x : X.carrier) : (uliftOpenNhdsFunctor.{v} X x).op.Final := by
  refine Functor.final_of_exists_of_isFiltered _ (fun U ↦ ?_) fun _ _ ↦ ?_
  · exact ⟨op ⟨(uliftOpensEquiv.{v} X).inverse.obj U.unop.val, U.unop.property⟩,
      ⟨(homOfLE ((uliftOpensEquiv.{v} X).counitIso.hom.app U.unop.val).le).op⟩⟩
  · exact ⟨_, 𝟙 _, Subsingleton.elim _ _⟩

/-- The stalk of the lifted structure presheaf, computed as the image of the stalk of `X` under
`CommRingCat.uliftFunctor`; `uliftStalkIso` restates it for `X.ulift`. -/
private def uliftPresheafStalkIso (x : X.carrier) :
    (uliftPresheaf.{v} X).stalk (ULift.up x) ≅
      CommRingCat.uliftFunctor.{v}.obj (X.presheaf.stalk x) :=
  (colimit.isColimit _).coconePointUniqueUpToIso
    ((Functor.Final.isColimitWhiskerEquiv (uliftOpenNhdsFunctor.{v} X x).op _).symm
      (isColimitOfPreserves CommRingCat.uliftFunctor.{v}
        (colimit.isColimit ((OpenNhds.inclusion x).op ⋙ X.presheaf))))

/-- **The universe lift of a locally ringed space.** The points of `X.ulift` are `ULift X`, and its
sections over an open set `U` are `ULift` of the sections of `X` over the corresponding open set
`(uliftOpensEquiv X).functor.obj U` of `X`. -/
@[expose, pp_with_univ]
def ulift : LocallyRingedSpace.{max u v} where
  carrier := TopCat.uliftFunctor.{v}.obj X.carrier
  presheaf := uliftPresheaf.{v} X
  IsSheaf := isSheaf_uliftPresheaf.{v} X
  isLocalRing := by
    rintro ⟨x⟩
    have : IsLocalRing (CommRingCat.uliftFunctor.{v}.obj (X.presheaf.stalk x)) :=
      ULift.ringEquiv.symm.isLocalRing
    exact (uliftPresheafStalkIso.{v} X x).symm.commRingCatIsoToRingEquiv.isLocalRing

/-- The underlying space of the universe lift is `ULift` of the underlying space. -/
@[simp]
theorem ulift_carrier : (ulift.{v} X).carrier = TopCat.uliftFunctor.{v}.obj X.carrier :=
  (rfl)

/-- The structure sheaf of the universe lift is `uliftPresheaf`. -/
@[simp]
theorem ulift_presheaf : (ulift.{v} X).presheaf = uliftPresheaf.{v} X :=
  (rfl)

/-- The stalk of the universe lift at `ULift.up x` is `ULift` of the stalk of `X` at `x`. -/
def uliftStalkIso (x : X.carrier) :
    (ulift.{v} X).presheaf.stalk (ULift.up x) ≅
      CommRingCat.uliftFunctor.{v}.obj (X.presheaf.stalk x) :=
  uliftPresheafStalkIso.{v} X x

/-- The stalk isomorphism of the universe lift sends the germ of a section at `ULift.up x` to the
lift of its germ at `x`. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem germ_uliftStalkIso_hom (U : Opens (ulift.{v} X).carrier) (x : X.carrier)
    (hx : ULift.up x ∈ U) :
    (ulift.{v} X).presheaf.germ U (ULift.up x) hx ≫ (uliftStalkIso.{v} X x).hom =
      CommRingCat.uliftFunctor.{v}.map
        (X.presheaf.germ ((uliftOpensEquiv.{v} X).functor.obj U) x hx) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom _ _
    (op (⟨U, hx⟩ : OpenNhds (TopCat.uliftFunctorObjHomeo.{v} X.carrier x)))

/-- The stalk of the universe lift at `ULift.up x` is isomorphic, as a ring, to the stalk of `X`
at `x`. -/
def uliftStalkRingEquiv (x : X.carrier) :
    (ulift.{v} X).presheaf.stalk (ULift.up x) ≃+* X.presheaf.stalk x :=
  (uliftStalkIso.{v} X x).commRingCatIsoToRingEquiv.trans ULift.ringEquiv

/-- The stalk ring isomorphism of the universe lift sends the germ of a section at `ULift.up x` to
the germ at `x` of the corresponding section of `X`. -/
@[simp]
theorem uliftStalkRingEquiv_germ (U : Opens (ulift.{v} X).carrier) (x : X.carrier)
    (hx : ULift.up x ∈ U) (f : (ulift.{v} X).presheaf.obj (op U)) :
    uliftStalkRingEquiv.{v} X x ((ulift.{v} X).presheaf.germ U (ULift.up x) hx f) =
      X.presheaf.germ ((uliftOpensEquiv.{v} X).functor.obj U) x hx f.down :=
  congrArg ULift.down (germ_uliftStalkIso_hom_apply.{v} X U x hx f)

/-- The global sections of the universe lift are `ULift` of the global sections. -/
def uliftΓIso :
    Γ.obj (op (ulift.{v} X)) ≅ CommRingCat.uliftFunctor.{v}.obj (Γ.obj (op X)) :=
  Iso.refl _

/-- The global sections isomorphism of the universe lift is the identity on underlying values. -/
theorem uliftΓIso_hom_apply (f : Γ.obj (op (ulift.{v} X))) :
    (uliftΓIso.{v} X).hom f = ULift.up (ULift.down f : Γ.obj (op X)) :=
  (rfl)

/-- The inverse global sections isomorphism of the universe lift is the identity on underlying
values. -/
theorem uliftΓIso_inv_apply (f : CommRingCat.uliftFunctor.{v}.obj (Γ.obj (op X))) :
    (uliftΓIso.{v} X).inv f = (ULift.up f.down : (ulift.{v} X).presheaf.obj (op ⊤)) :=
  (rfl)

end AlgebraicGeometry.LocallyRingedSpace
