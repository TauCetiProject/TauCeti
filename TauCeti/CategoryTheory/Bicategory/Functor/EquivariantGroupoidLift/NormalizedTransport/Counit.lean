/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
public import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.Comparison
public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.Equivariance
public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.NormalizedTransport.Functor
public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.NormalizedTransport.Reconstruction

/-!
# Normalizing a reconstructed lift recovers the normalized transport

Normalized transport data `N` reconstruct a lift `N.toLift` whose fiber comparisons have
identity components, and normalizing it gives back transport functors `N.toLift.transport g`
that differ from `N.transport g` only by the chosen inverse fiber comparisons and the identity
action. The canonical isomorphisms `N.toLiftTransportIso g` remove these choices. Since they
preserve the units, compositors and commuting isomorphisms with the actions, they form an
isomorphism `N.toLiftNormalizedTransportIso : N.toLift.normalizedTransport ≅ N` in the groupoid
of normalized transports.

These isomorphisms are natural for comparisons `φ : N ⟶ N'` of normalized transports: the
normalization of the reconstructed lift morphism `φ.toLiftHom`, followed by the isomorphism at
`N'`, is the isomorphism at `N` followed by `φ`. Hence they assemble into a strong
transformation `normalizationCounitHom actions` from reconstruction followed by
normalization to the identity pseudofunctor of the locally discrete bicategory of
normalized transports, and with their inverses into an equivalence

`normalizationCounitEquiv actions :
  (reconstructionPseudofunctor actions).comp (normalizationPseudofunctor actions) ≌
    Pseudofunctor.id (LocallyDiscrete (NormalizedTransport Γ actions))`

in the bicategory of pseudofunctors, strong transformations and modifications. This is the
counit of the comparison between the bicategory of equivariant lifts and normalized transport;
it does not compare a lift with the reconstruction of its normalization, which is the unit.
Since the target bicategory is locally discrete, the naturality cells of these strong
transformations and the components of their modifications are equalities.

## Main declarations

* `TauCeti.EquivariantGroupoidLift.NormalizedTransport.toLiftNormalizedTransportIso`: the
  isomorphism of normalized transports with transport components `toLiftTransportIso`;
* `TauCeti.EquivariantGroupoidLift.NormalizedTransport.toLiftNormalizedTransportIso_hom_naturality`:
  its naturality for comparisons of normalized transports;
* `TauCeti.EquivariantGroupoidLift.normalizationCounitHom`,
  `TauCeti.EquivariantGroupoidLift.normalizationCounitInv`: the strong transformations between
  normalization after reconstruction and the identity;
* `TauCeti.EquivariantGroupoidLift.normalizationCounitEquiv`: the resulting equivalence of
  pseudofunctors.

## References

* Niles Johnson and Donald Yau, *2-Dimensional Categories*, Oxford University Press (2021),
  [arXiv:2002.06055](https://arxiv.org/abs/2002.06055), Chapter 4: strong transformations,
  modifications and biequivalences.
-/

public section

universe w v u₂ v₁ u₁

namespace TauCeti.EquivariantGroupoidLift.NormalizedTransport

open CategoryTheory Bicategory

variable {Γ : Type u₁} [Category.{v₁} Γ] {H : Type u₂} [Monoid H]
  {actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}}

/-- Normalizing the reconstructed lift recovers the normalized transport. The comparison of
transport functors along each arrow is the canonical isomorphism `toLiftTransportIso`, which
removes the chosen inverse fiber comparisons and the identity action. -/
noncomputable def toLiftNormalizedTransportIso (N : NormalizedTransport Γ actions) :
    N.toLift.normalizedTransport ≅ N :=
  asIso
    { transportIso := N.toLiftTransportIso
      transportIso_unit := N.toLiftTransportIso_hom_app_comp_transportId
      transportIso_comp g h gh hgh x := by
        have hc := N.toLiftTransportIso_transportComp_hom_app g h gh hgh x
        have hn := (N.toLiftTransportIso h).hom.naturality ((N.toLiftTransportIso g).hom.app x)
        exact hc.trans ((reassoc_of% hn) _)
      transportIso_comm g a x := (N.toLiftTransportIso_hom_app_comp_transportCommIso g a x).symm :
      N.toLift.normalizedTransport ⟶ N }

@[simp]
lemma toLiftNormalizedTransportIso_hom_transportIso (N : NormalizedTransport Γ actions)
    {p q : Γ} (g : p ⟶ q) :
    (toLiftNormalizedTransportIso N).hom.transportIso g = N.toLiftTransportIso g :=
  (rfl)

@[simp]
lemma toLiftNormalizedTransportIso_inv_transportIso (N : NormalizedTransport Γ actions)
    {p q : Γ} (g : p ⟶ q) :
    (toLiftNormalizedTransportIso N).inv.transportIso g = (N.toLiftTransportIso g).symm := by
  rw [toLiftNormalizedTransportIso, asIso_inv, inv_transportIso]
  rfl

namespace Hom

variable {N N' : NormalizedTransport Γ actions}

/-- The transport comparison of the reconstructed lift morphism, followed by the canonical
return comparison of the target, is the return comparison of the source followed by `φ`. -/
@[reassoc]
lemma toLiftHom_transportIso_hom_app_comp_toLiftTransportIso_hom_app (φ : N ⟶ N') {p q : Γ}
    (g : p ⟶ q) (x : fiber actions p) :
    (φ.toLiftHom.transportIso g).hom.app x ≫ (N'.toLiftTransportIso g).hom.app x =
      (N.toLiftTransportIso g).hom.app x ≫ (φ.transportIso g).hom.app x := by
  -- Name the inverse-comparison carriers in the prescribed fibers.
  let y : fiber actions p := (N.toLift.fiberEquivalence p).inverse.obj x
  let y' : fiber actions p := (N'.toLift.fiberEquivalence p).inverse.obj x
  let ε : y ⟶ x := (N.toLift.fiberEquivalence p).counit.app x
  let ε' : y' ⟶ x := (N'.toLift.fiberEquivalence p).counit.app x
  let i : y ⟶ y' := ((toLiftHom φ).inverseFiberIso p).hom.app x
  let A := act actions p (𝟙 (SingleObj.star H))
  let θ := (φ.transportIso g).hom
  -- The comparison of chosen inverses is the mate of the identity fiber comparison.
  have hi : i ≫ ε' = ε := by
    have h := (toLiftHom φ).functor_map_inverseFiberIso_hom_app_comp_counit p x
    rw [EquivariantGroupoidLift.Hom.fiberFunctorIso_hom_app, toLiftHom_fiberIso_hom_as_app,
      Cat.leftUnitor_hom_toNatTrans] at h
    erw [Functor.leftUnitor_hom_app, Category.id_comp] at h
    -- The fiber comparison functor of a reconstructed lift is the identity functor.
    exact h
  have key : (N'.transport g).map (A.map i) ≫ (N'.transport g).map (A.map ε') =
      (N'.transport g).map (A.map ε) := by
    rw [← Functor.map_comp, ← Functor.map_comp, hi]
  rw [EquivariantGroupoidLift.Hom.transportIso_hom_app]
  simp only [toLiftHom_fiberIso_inv_as_app, EquivariantGroupoidLift.Hom.fiberFunctorIso_inv_app,
    EquivariantGroupoidLift.Hom.jointMapIso_hom_app, toLiftTransportIso_hom_app]
  erw [jointHom_naturality_hom_app]
  -- The fiber comparisons of reconstructed lifts are identity functors, and the joint functor
  -- along `(g, 1)` is `T_1 ⋙ E_g`; display the remaining cells in the prescribed fibers.
  change (𝟙 _ ≫ θ.app (A.obj y) ≫ (N'.transport g).map (A.map i)) ≫
      (N'.transport g).map (A.map ε') ≫ (N'.transport g).map ((actId actions p).hom.app x) =
    ((N.transport g).map (A.map ε) ≫ (N.transport g).map ((actId actions p).hom.app x)) ≫
      θ.app x
  rw [Category.id_comp, Category.assoc, reassoc_of% key, ← θ.naturality_assoc, ← θ.naturality,
    Category.assoc]
  -- The remaining difference is the object `(𝟭 _).obj x`, which is `x` by definition.
  rfl

end Hom

/-- The return comparisons are natural for comparisons `φ` of normalized transports: normalizing
the reconstructed lift morphism `φ.toLiftHom` and then returning to `N'` agrees with returning to
`N` and then applying `φ`. -/
@[reassoc]
lemma toLiftNormalizedTransportIso_hom_naturality {N N' : NormalizedTransport Γ actions}
    (φ : N ⟶ N') :
    φ.toLiftHom.normalizedTransportHom ≫ (toLiftNormalizedTransportIso N').hom =
      (toLiftNormalizedTransportIso N).hom ≫ φ := by
  refine Hom.ext fun p q g ↦ Iso.ext (NatTrans.ext (funext fun x ↦ ?_))
  simp only [comp_transportIso, EquivariantGroupoidLift.Hom.normalizedTransportHom_transportIso,
    toLiftNormalizedTransportIso_hom_transportIso]
  exact φ.toLiftHom_transportIso_hom_app_comp_toLiftTransportIso_hom_app g x

/-- The inverse return comparisons are natural for comparisons of normalized transports. -/
@[reassoc]
lemma toLiftNormalizedTransportIso_inv_naturality {N N' : NormalizedTransport Γ actions}
    (φ : N ⟶ N') :
    φ ≫ (toLiftNormalizedTransportIso N').inv =
      (toLiftNormalizedTransportIso N).inv ≫ φ.toLiftHom.normalizedTransportHom := by
  rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq,
    toLiftNormalizedTransportIso_hom_naturality]

end TauCeti.EquivariantGroupoidLift.NormalizedTransport

namespace TauCeti.EquivariantGroupoidLift

open CategoryTheory Bicategory Pseudofunctor.StrongTrans NormalizedTransport

variable {Γ : Type u₁} [Category.{v₁} Γ] {H : Type u₂} [Monoid H]
  (actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w})

/-- The return comparisons form a strong transformation from reconstruction followed by
normalization to the identity. Its naturality cells are the equalities
`toLiftNormalizedTransportIso_hom_naturality` in the locally discrete target. -/
noncomputable def normalizationCounitHom :
    (reconstructionPseudofunctor actions).comp (normalizationPseudofunctor actions) ⟶
      Pseudofunctor.id (LocallyDiscrete (NormalizedTransport Γ actions)) where
  app N := (toLiftNormalizedTransportIso N.as).hom.toLoc
  naturality φ :=
    eqToIso (congrArg Quiver.Hom.toLoc (toLiftNormalizedTransportIso_hom_naturality φ.as))
  naturality_naturality _ := Subsingleton.elim _ _
  naturality_id _ := Subsingleton.elim _ _
  naturality_comp _ _ := Subsingleton.elim _ _

@[simp]
lemma normalizationCounitHom_app (N : LocallyDiscrete (NormalizedTransport Γ actions)) :
    (normalizationCounitHom actions).app N = (toLiftNormalizedTransportIso N.as).hom.toLoc :=
  (rfl)

/-- The inverse return comparisons form a strong transformation from the identity to
reconstruction followed by normalization. -/
noncomputable def normalizationCounitInv :
    Pseudofunctor.id (LocallyDiscrete (NormalizedTransport Γ actions)) ⟶
      (reconstructionPseudofunctor actions).comp (normalizationPseudofunctor actions) where
  app N := (toLiftNormalizedTransportIso N.as).inv.toLoc
  naturality φ :=
    eqToIso (congrArg Quiver.Hom.toLoc (toLiftNormalizedTransportIso_inv_naturality φ.as))
  naturality_naturality _ := Subsingleton.elim _ _
  naturality_id _ := Subsingleton.elim _ _
  naturality_comp _ _ := Subsingleton.elim _ _

@[simp]
lemma normalizationCounitInv_app (N : LocallyDiscrete (NormalizedTransport Γ actions)) :
    (normalizationCounitInv actions).app N = (toLiftNormalizedTransportIso N.as).inv.toLoc :=
  (rfl)

/-- Reconstruction followed by normalization is equivalent to the identity pseudofunctor of the
locally discrete bicategory of normalized transports, through the return comparisons. -/
noncomputable def normalizationCounitEquiv :
    (reconstructionPseudofunctor actions).comp (normalizationPseudofunctor actions) ≌
      Pseudofunctor.id (LocallyDiscrete (NormalizedTransport Γ actions)) :=
  Equivalence.mkOfAdjointifyCounit (f := normalizationCounitHom actions)
    (g := normalizationCounitInv actions)
    (Pseudofunctor.StrongTrans.isoMk
      (fun N ↦ eqToIso
        (congrArg Quiver.Hom.toLoc (toLiftNormalizedTransportIso N.as).hom_inv_id.symm))
      (fun _ ↦ Subsingleton.elim _ _))
    (Pseudofunctor.StrongTrans.isoMk
      (fun N ↦ eqToIso
        (congrArg Quiver.Hom.toLoc (toLiftNormalizedTransportIso N.as).inv_hom_id))
      (fun _ ↦ Subsingleton.elim _ _))

@[simp]
lemma normalizationCounitEquiv_hom :
    (normalizationCounitEquiv actions).hom = normalizationCounitHom actions :=
  (rfl)

@[simp]
lemma normalizationCounitEquiv_inv :
    (normalizationCounitEquiv actions).inv = normalizationCounitInv actions :=
  (rfl)

end TauCeti.EquivariantGroupoidLift
