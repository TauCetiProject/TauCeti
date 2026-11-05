/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Sites.LocalSite
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import TauCeti.Algebra.Category.Grp.Projective
public import TauCeti.Algebra.Category.ModuleCat.ForgetCorepresentable

/-!
# Étale sheaves on a separably closed field

Let `Ω` be a separably closed field. Every étale covering of `Spec Ω` has a section, so the small
étale site of `Spec Ω` is a local site in the sense of Mathlib's
`CategoryTheory.GrothendieckTopology.IsLocalSite`: the only covering sieve of its terminal
object is the maximal one. This file deduces that étale sheaves on `Spec Ω` are just their global
sections. For a coefficient category `A` such as `ModuleCat Λ`, `AddCommGrpCat` or `Type u`, the
constant sheaf functor and the global sections functor are inverse equivalences between `A` and
the sheaves on the small étale site of `Spec Ω` with values in `A`. In particular a geometric
point has no étale cohomology in positive degrees.

The global sections functor is identified with the stalk functor at the geometric point
`𝟙 (Spec Ω)`, and that point alone is a conservative family of points by Mathlib's
`AlgebraicGeometry.Scheme.isConservative_pointSmallEtale`. More generally, the stalk at any
geometric point `s : Spec Ω ⟶ S` which is itself étale is the value at `s`, viewed as an object of
the small étale site of `S`, because `s` corepresents the fibre functor of the point.
The fully faithfulness of the constant sheaf functor and the description of global sections come
from Mathlib's theory of local sites.

## Main results

* `AlgebraicGeometry.Scheme.pointSmallEtaleSheafFiberIso`: the stalk of a sheaf at an étale
  geometric point `s` is its sections over `s`.
* `AlgebraicGeometry.Scheme.isLocalSite_smallEtaleTopology`: the small étale site of a separably
  closed field is a local site.
* `AlgebraicGeometry.Scheme.pointSmallEtaleIdSheafFiberIso`: the stalk at the geometric point of
  `Spec Ω` is the global sections functor.
* `AlgebraicGeometry.Scheme.isEquivalence_constantSheaf`,
  `AlgebraicGeometry.Scheme.isEquivalence_Γ`: étale sheaves on `Spec Ω` are equivalent to the
  coefficient category, through constant sheaves and global sections.
* `AlgebraicGeometry.Scheme.subsingleton_H_succ_of_isSepClosed`: abelian sheaves on the small étale
  site of `Spec Ω` have no cohomology in positive degrees.

## References

* M. Artin, A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé VIII, §2, for sheaves on the étale
  site of a field as discrete Galois modules; here the Galois group is trivial.
-/

public section

universe w u u'

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

section EtalePoint

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S)
  [Etale s]

/-- An étale geometric point `s` of `S` is an object of the small étale site of `S`, and it
corepresents the fibre functor of the point `pointSmallEtale s`: a lift of `s` to an étale
`S`-scheme `X` is a morphism from `s` to `X` in the small étale site. -/
noncomputable def pointSmallEtaleFiberCorepresentableBy :
    (pointSmallEtale s).fiber.CorepresentableBy (Etale.mk s) where
  homEquiv := (Etale.forgetFullyFaithful S).homEquiv
  homEquiv_comp _ _ := (Etale.forget S).map_comp _ _

/-- The bijection of `pointSmallEtaleFiberCorepresentableBy` sends a morphism of the small étale
site to the underlying morphism of `S`-schemes. -/
@[simp]
lemma pointSmallEtaleFiberCorepresentableBy_homEquiv_apply {X : S.Etale} (f : Etale.mk s ⟶ X) :
    (pointSmallEtaleFiberCorepresentableBy s).homEquiv f = (Etale.forget S).map f := by
  rfl

/-- The inverse bijection of `pointSmallEtaleFiberCorepresentableBy` sends a lift of `s` to `X`
to the morphism of the small étale site whose underlying morphism of `S`-schemes is that lift. -/
@[simp]
lemma forget_map_pointSmallEtaleFiberCorepresentableBy_homEquiv_symm {X : S.Etale}
    (x : (pointSmallEtale s).fiber.obj X) :
    (Etale.forget S).map ((pointSmallEtaleFiberCorepresentableBy s).homEquiv.symm x) = x :=
  (pointSmallEtaleFiberCorepresentableBy s).homEquiv.apply_symm_apply x

/-- Every covering sieve of an object `X` of the small étale site contains every morphism to `X`
from an étale geometric point. -/
theorem mem_of_mem_smallEtaleTopology {X : S.Etale} {R : Sieve X}
    (hR : R ∈ smallEtaleTopology S X) (f : Etale.mk s ⟶ X) : R f := by
  obtain ⟨Y, g, hg, y, hy⟩ :=
    (pointSmallEtale s).jointly_surjective R hR ((Etale.forget S).map f)
  -- A point of the fibre of `Y` is a lift of `s` to `Y`, that is, a morphism of `S`-schemes.
  let y' : (Etale.forget S).obj (Etale.mk s) ⟶ (Etale.forget S).obj Y := y
  have : f = (Etale.forget S).preimage y' ≫ g :=
    (Etale.forget S).map_injective (by rw [Functor.map_comp, Functor.map_preimage]; exact hy.symm)
  exact this ▸ R.downward_closed hg _

variable {A : Type u'} [Category.{w} A] [HasColimitsOfSize.{u, u} A]

/-- The stalk of a presheaf at an étale geometric point `s` is its value at `s`, viewed as an
object of the small étale site. -/
noncomputable def pointSmallEtalePresheafFiberIso (P : S.Etaleᵒᵖ ⥤ A) :
    (pointSmallEtale s).presheafFiber.obj P ≅ P.obj (op (Etale.mk s)) :=
  (colimit.isColimit _).coconePointUniqueUpToIso
    (colimitOfDiagramTerminal (Functor.Elements.isInitialOfCorepresentableBy
      (pointSmallEtaleFiberCorepresentableBy s)).op _)

/-- Under `pointSmallEtalePresheafFiberIso`, the germ at the geometric point `s` of a section
over `X`, through a lift `x` of `s` to `X`, is its restriction along that lift. -/
@[reassoc (attr := simp)]
theorem toPresheafFiber_pointSmallEtalePresheafFiberIso_hom (P : S.Etaleᵒᵖ ⥤ A) (X : S.Etale)
    (x : (pointSmallEtale s).fiber.obj X) :
    (pointSmallEtale s).toPresheafFiber X x P ≫ (pointSmallEtalePresheafFiberIso s P).hom =
      P.map ((pointSmallEtaleFiberCorepresentableBy s).homEquiv.symm x).op :=
  -- `toPresheafFiber` is by definition a leg of the colimit cocone, and the legs of the cocone
  -- over a diagram with terminal object are the maps to that object.
  IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _

/-- The stalk functor on presheaves at an étale geometric point `s` is evaluation at `s`. -/
noncomputable def pointSmallEtalePresheafFiberNatIso :
    (pointSmallEtale s).presheafFiber (A := A) ≅
      (CategoryTheory.evaluation _ A).obj (op (Etale.mk s)) :=
  NatIso.ofComponents (pointSmallEtalePresheafFiberIso s) fun f ↦ by ext; simp

@[simp]
lemma pointSmallEtalePresheafFiberNatIso_hom_app (P : S.Etaleᵒᵖ ⥤ A) :
    (pointSmallEtalePresheafFiberNatIso s).hom.app P =
      (pointSmallEtalePresheafFiberIso s P).hom := by
  rfl

@[simp]
lemma pointSmallEtalePresheafFiberNatIso_inv_app (P : S.Etaleᵒᵖ ⥤ A) :
    (pointSmallEtalePresheafFiberNatIso s).inv.app P =
      (pointSmallEtalePresheafFiberIso s P).inv := by
  rfl

/-- **The stalk of a sheaf at an étale geometric point is its sections there.** -/
noncomputable def pointSmallEtaleSheafFiberIso :
    (pointSmallEtale s).sheafFiber (A := A) ≅
      (sheafSections (smallEtaleTopology S) A).obj (op (Etale.mk s)) :=
  Functor.isoWhiskerLeft (sheafToPresheaf _ A) (pointSmallEtalePresheafFiberNatIso s)

@[simp]
lemma pointSmallEtaleSheafFiberIso_hom_app (F : Sheaf (smallEtaleTopology S) A) :
    (pointSmallEtaleSheafFiberIso s).hom.app F = (pointSmallEtalePresheafFiberIso s F.obj).hom := by
  rfl

@[simp]
lemma pointSmallEtaleSheafFiberIso_inv_app (F : Sheaf (smallEtaleTopology S) A) :
    (pointSmallEtaleSheafFiberIso s).inv.app F = (pointSmallEtalePresheafFiberIso s F.obj).inv := by
  rfl

/-- Under `pointSmallEtaleSheafFiberIso`, the germ at the geometric point `s` of a section over
`X`, through a lift `x` of `s` to `X`, is its restriction along that lift. -/
@[reassoc]
theorem toPresheafFiber_pointSmallEtaleSheafFiberIso_hom_app (F : Sheaf (smallEtaleTopology S) A)
    (X : S.Etale) (x : (pointSmallEtale s).fiber.obj X) :
    (pointSmallEtale s).toPresheafFiber X x F.obj ≫ (pointSmallEtaleSheafFiberIso s).hom.app F =
      F.obj.map ((pointSmallEtaleFiberCorepresentableBy s).homEquiv.symm x).op := by
  simp

end EtalePoint

/-- The identity of `S`, as an object of the small étale site of `S`, is a terminal object. -/
noncomputable def Etale.mkIdTerminal (S : Scheme.{u}) : IsTerminal (Etale.mk (𝟙 S)) :=
  IsTerminal.isTerminalOfObj (Etale.forget S) _ Over.mkIdTerminal

section SepClosed

variable (Ω : Type u) [Field Ω] [IsSepClosed Ω]

/-- **The small étale site of a separably closed field is a local site**: the only covering sieve
of its terminal object is the maximal sieve, since every étale covering of `Spec Ω` has a
section. -/
instance isLocalSite_smallEtaleTopology :
    (smallEtaleTopology (Spec (.of Ω))).IsLocalSite where
  eq_top_of_mem R hR := by
    let e := terminalIsoIsTerminal (Etale.mkIdTerminal (Spec (.of Ω)))
    rw [← Sieve.id_mem_iff_eq_top, ← e.hom_inv_id]
    exact R.downward_closed (mem_of_mem_smallEtaleTopology (𝟙 _) hR e.inv) _

/-- The geometric point `𝟙 (Spec Ω)` alone is a conservative family of points of the small
étale site of `Spec Ω`. -/
private theorem isConservativeFamilyOfPoints_pointSmallEtale_id :
    (ObjectProperty.ofObj fun _ : Unit ↦
      pointSmallEtale (𝟙 (Spec (.of Ω)))).IsConservativeFamilyOfPoints :=
  isConservative_pointSmallEtale _
    (Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 ⟨(), x, rfl⟩)

variable {A : Type u'} [Category.{w} A] [HasColimitsOfSize.{u, u} A]
  [HasWeakSheafify (smallEtaleTopology (Spec (.of Ω))) A]

/-- The stalk functor at the geometric point `𝟙 (Spec Ω)` is the global sections functor. -/
noncomputable def pointSmallEtaleIdSheafFiberIso :
    (pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber (A := A) ≅
      Sheaf.Γ (smallEtaleTopology (Spec (.of Ω))) A :=
  pointSmallEtaleSheafFiberIso (𝟙 _) ≪≫
    (Sheaf.ΓNatIsoSheafSections _ A (Etale.mkIdTerminal _)).symm

@[simp]
lemma pointSmallEtaleIdSheafFiberIso_hom_app (F : Sheaf (smallEtaleTopology (Spec (.of Ω))) A) :
    (pointSmallEtaleIdSheafFiberIso Ω).hom.app F =
      (pointSmallEtalePresheafFiberIso (𝟙 _) F.obj).hom ≫
        (Sheaf.ΓNatIsoSheafSections _ A (Etale.mkIdTerminal _)).inv.app F := by
  rfl

@[simp]
lemma pointSmallEtaleIdSheafFiberIso_inv_app (F : Sheaf (smallEtaleTopology (Spec (.of Ω))) A) :
    (pointSmallEtaleIdSheafFiberIso Ω).inv.app F =
      (Sheaf.ΓNatIsoSheafSections _ A (Etale.mkIdTerminal _)).hom.app F ≫
        (pointSmallEtalePresheafFiberIso (𝟙 _) F.obj).inv := by
  rfl

/-- Under `pointSmallEtaleIdSheafFiberIso`, the germ at the geometric point of `Spec Ω` of a
section over `X`, through a point `x` of `X` over it, is the global section given by restricting
along `x`. -/
@[reassoc]
theorem toPresheafFiber_pointSmallEtaleIdSheafFiberIso_hom_app
    (F : Sheaf (smallEtaleTopology (Spec (.of Ω))) A) (X : (Spec (.of Ω)).Etale)
    (x : (pointSmallEtale (𝟙 (Spec (.of Ω)))).fiber.obj X) :
    (pointSmallEtale (𝟙 _)).toPresheafFiber X x F.obj ≫
        (pointSmallEtaleIdSheafFiberIso Ω).hom.app F =
      F.obj.map ((pointSmallEtaleFiberCorepresentableBy (𝟙 _)).homEquiv.symm x).op ≫
        (Sheaf.ΓNatIsoSheafSections _ A (Etale.mkIdTerminal _)).inv.app F := by
  simp

variable {FC : A → A → Type*} {CC : A → Type u} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
  [ConcreteCategory.{u} A FC] [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)]
  [(smallEtaleTopology (Spec (.of Ω))).HasSheafCompose (CategoryTheory.forget A)]

include FC CC in
/-- On the small étale site of a separably closed field, a morphism of sheaves is an isomorphism
if it is an isomorphism on global sections. -/
instance reflectsIsomorphisms_Γ :
    (Sheaf.Γ (smallEtaleTopology (Spec (.of Ω))) A).ReflectsIsomorphisms where
  reflects {F G} f _ := by
    have : ∀ Φ : (ObjectProperty.ofObj fun _ : Unit ↦
        pointSmallEtale (𝟙 (Spec (.of Ω)))).FullSubcategory,
        IsIso (Φ.obj.sheafFiber.map f) := by
      rintro ⟨_, ⟨⟩⟩
      exact (NatIso.isIso_map_iff (pointSmallEtaleIdSheafFiberIso Ω) f).mpr ‹_›
    exact
      ((isConservativeFamilyOfPoints_pointSmallEtale_id Ω).jointlyReflectIsomorphisms A).isIso f

variable [HasProducts.{u} A]

include FC CC in
/-- **Étale sheaves on a separably closed field are constant**: the constant sheaf functor is an
equivalence from `A` to the sheaves on the small étale site of `Spec Ω` with values in `A`. -/
instance isEquivalence_constantSheaf :
    (constantSheaf (smallEtaleTopology (Spec (.of Ω))) A).IsEquivalence := by
  let adj := constantSheafΓAdj (smallEtaleTopology (Spec (.of Ω))) A
  -- The constant sheaf functor is fully faithful on a local site, so `Γ` maps the counit to an
  -- isomorphism, and `Γ` reflects isomorphisms.
  have (F : Sheaf (smallEtaleTopology (Spec (.of Ω))) A) : IsIso (adj.counit.app F) :=
    isIso_of_reflects_iso (adj.counit.app F) (Sheaf.Γ _ A)
  exact adj.toEquivalence.isEquivalence_functor

include FC CC in
/-- On the small étale site of a separably closed field, the global sections functor is an
equivalence of categories. -/
instance isEquivalence_Γ : (Sheaf.Γ (smallEtaleTopology (Spec (.of Ω))) A).IsEquivalence :=
  (constantSheafΓAdj _ A).isEquivalence_right_of_isEquivalence_left

end SepClosed

section Cohomology

variable (Ω : Type u) [Field Ω] [IsSepClosed Ω]

/-- **A geometric point has no higher étale cohomology**: every abelian sheaf on the small étale
site of a separably closed field has vanishing cohomology in positive degrees. -/
instance subsingleton_H_succ_of_isSepClosed
    [HasExt.{w} (Sheaf (smallEtaleTopology (Spec (.of Ω))) AddCommGrpCat.{u})]
    (F : Sheaf (smallEtaleTopology (Spec (.of Ω))) AddCommGrpCat.{u}) (n : ℕ) :
    Subsingleton (F.H (n + 1)) :=
  -- The constant sheaf on `ℤ` is projective, being the image of a projective object under a
  -- left adjoint whose right adjoint `Γ` is an equivalence.
  have : Projective ((constantSheaf (smallEtaleTopology (Spec (.of Ω))) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift ℤ))) :=
    (constantSheafΓAdj _ _).map_projective _ inferInstance
  Abelian.Ext.subsingleton_of_projective _ F n

end Cohomology

end AlgebraicGeometry.Scheme
