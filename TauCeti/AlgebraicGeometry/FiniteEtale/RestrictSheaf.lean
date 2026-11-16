/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Equivalence
public import TauCeti.AlgebraicGeometry.FiniteEtale.Sheaf
public import TauCeti.CategoryTheory.Sites.LocallyConstant
import Mathlib.CategoryTheory.Sites.LocalProperties
import TauCeti.AlgebraicGeometry.Sites.EtaleSepClosed

/-!
# Small étale restriction and trivial finite étale covers

This file develops the restriction of sheaves on the small étale site along an étale morphism
`p : T ⟶ S`, together with the sheaf of sections of a trivial finite étale cover.

For an étale morphism `p : T ⟶ S`, the small étale site `T.Etale` is equivalent to the slice
category `Over (etaleMk p)` of `S.Etale` (`TauCeti.FiniteEtaleScheme.etaleOverEquiv`), inducing the
restriction functor `TauCeti.FiniteEtaleScheme.restrictSheaf p` on sheaves with values in any
category `A`. When `F` is the sheaf of sections of a finite étale `S`-scheme `X`, its restriction
along `p` is naturally isomorphic to the sheaf of sections of the base change `X ×_S T`
(`TauCeti.FiniteEtaleScheme.toSheafCompRestrictSheafIso`). For a finite set `M`, the sheaf of
sections of the trivial cover `trivialCover S M` is the constant sheaf with value `M`
(`TauCeti.FiniteEtaleScheme.toSheafTrivialCoverIso`).

## Main definitions

* `TauCeti.FiniteEtaleScheme.trivialCover`: the finite étale cover of `S` given by a finite
  coproduct of copies of `S`.
* `TauCeti.FiniteEtaleScheme.etaleOverEquiv`: equivalence between `T.Etale` and
  `Over (etaleMk p)` for an étale morphism `p : T ⟶ S`.
* `TauCeti.FiniteEtaleScheme.restrictSheaf`: restriction of sheaves on the small étale site along an
  étale morphism `p : T ⟶ S`.
* `TauCeti.FiniteEtaleScheme.toSheafCompRestrictSheafIso`: compatibility of `toSheaf` with
  `restrictSheaf` and base change.

## Main results

* `TauCeti.FiniteEtaleScheme.toSheafTrivialCoverIso`: the sheaf of sections of `trivialCover S M`
  is the constant étale sheaf with value `M`.
* `TauCeti.FiniteEtaleScheme.isLocallyConstantIn_restrictSheaf`: étale restriction preserves
  locally constant finite sheaves of sets.

## References

* M. Artin, A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé IX, §2.
* The Stacks Project, [Tag 03Q4](https://stacks.math.columbia.edu/tag/03Q4).
-/

public section

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

namespace TauCeti.FiniteEtaleScheme

section TrivialCover

variable (S : Scheme.{u})

/-- The trivial finite étale cover of `S` indexed by a finite type `M`: the coproduct of `M`
copies of the identity `S ⟶ S`. -/
noncomputable def trivialCover (M : Type u) [Finite M] : FiniteEtaleScheme S :=
  ∐ fun _ : M ↦ ofHom (𝟙 S)

/-- Identification of `trivialCover S M` with the coproduct of `M` copies of `ofHom (𝟙 S)`. -/
noncomputable def trivialCoverIso (M : Type u) [Finite M] :
    trivialCover S M ≅ ∐ fun _ : M ↦ ofHom (𝟙 S) :=
  Iso.refl _

/-- The identity of `S`, seen as a finite étale scheme in the small étale site, is terminal. -/
private noncomputable def isTerminalToEtaleOfHomId :
    IsTerminal ((toEtale S).obj (ofHom (𝟙 S))) :=
  IsTerminal.isTerminalOfObj (Scheme.Etale.forget S) _
    (Over.mkIdTerminal.ofIso (eqToIso (by simp)))

/-- The sheaf of sections of the base `S` itself is the constant sheaf on a singleton. -/
noncomputable def toSheafOfHomIdIso :
    (toSheaf S).obj (ofHom (𝟙 S)) ≅
      (constantSheaf (Scheme.smallEtaleTopology S) (Type u)).obj PUnit.{u + 1} :=
  let hT := isTerminalToEtaleOfHomId S
  let e : (Functor.const S.Etaleᵒᵖ).obj PUnit.{u + 1} ≅
      (sheafToPresheaf (Scheme.smallEtaleTopology S) (Type u)).obj
        ((toSheaf S).obj (ofHom (𝟙 S))) :=
    NatIso.ofComponents (fun U ↦ Equiv.toIso
      { toFun _ := hT.from U.unop
        invFun _ := PUnit.unit
        left_inv _ := rfl
        right_inv _ := hT.hom_ext _ _ }) (fun _ ↦ by
      ext _
      exact hT.hom_ext _ _)
  ((presheafToSheaf (Scheme.smallEtaleTopology S) (Type u)).mapIso e ≪≫
    (asIso (sheafificationAdjunction (Scheme.smallEtaleTopology S) (Type u)).counit).app
      ((toSheaf S).obj (ofHom (𝟙 S)))).symm

/-- The sheaf of sections of `trivialCover S M` is the constant étale sheaf with value `M`. -/
noncomputable def toSheafTrivialCoverIso (M : Type u) [Finite M] :
    (toSheaf S).obj (trivialCover S M) ≅
      (constantSheaf (Scheme.smallEtaleTopology S) (Type u)).obj M :=
  haveI : Fintype M := Fintype.ofFinite M
  have := hasColimitsOfShape_of_hasFiniteColimits
    (C := Sheaf (Scheme.smallEtaleTopology S) (Type u)) (Discrete M)
  have : (constantSheaf (Scheme.smallEtaleTopology S) (Type u)).IsLeftAdjoint :=
    (constantSheafAdj (Scheme.smallEtaleTopology S) (Type u) (Scheme.Etale.mkIdTerminal S))
      |>.isLeftAdjoint
  PreservesCoproduct.iso (toSheaf S) _ ≪≫
    Sigma.mapIso (fun _ ↦ toSheafOfHomIdIso S) ≪≫
    (PreservesCoproduct.iso (constantSheaf (Scheme.smallEtaleTopology S) (Type u)) _).symm ≪≫
    (constantSheaf (Scheme.smallEtaleTopology S) (Type u)).mapIso
      (Types.coproductIso _ ≪≫ Equiv.toIso (Equiv.sigmaPUnit M))

/-- Pulling back a trivial finite étale cover along any morphism yields the trivial cover with the
same index type. -/
noncomputable def pullbackTrivialCoverIso {S T : Scheme.{u}} (f : T ⟶ S) (M : Type u) [Finite M] :
    (pullback f).obj (trivialCover S M) ≅ trivialCover T M :=
  PreservesCoproduct.iso (pullback f) _ ≪≫
    Sigma.mapIso fun _ ↦
      ((isTerminalOfHomId S).isTerminalObj (pullback f) _).uniqueUpToIso (isTerminalOfHomId T)

end TrivialCover

section EtaleRestriction

variable {S : Scheme.{u}}

/-- Non-reducible wrapper around `Scheme.Etale.mk`, isolating `MorphismProperty.Over.mk @Etale`
from implicit-transparency reduction. -/
def etaleMk {S X : Scheme.{u}} (f : X ⟶ S) [Etale f] : S.Etale :=
  Scheme.Etale.mk f

/-- Underlying scheme of `U : S.Etale`, via `Scheme.Etale.forget`. -/
def etaleObj {S : Scheme.{u}} (U : S.Etale) : Scheme.{u} :=
  ((Scheme.Etale.forget S).obj U).left

/-- Structure morphism of `U : S.Etale`, via `Scheme.Etale.forget`. -/
def etaleHom {S : Scheme.{u}} (U : S.Etale) : etaleObj U ⟶ S :=
  ((Scheme.Etale.forget S).obj U).hom

instance instEtaleEtaleHom {S : Scheme.{u}} (U : S.Etale) : Etale (etaleHom U) :=
  U.prop

/-- Underlying scheme morphism of `f : U ⟶ V` in `S.Etale`, via `Scheme.Etale.forget`. -/
def etaleMap {S : Scheme.{u}} {U V : S.Etale} (f : U ⟶ V) : etaleObj U ⟶ etaleObj V :=
  ((Scheme.Etale.forget S).map f).left

lemma etaleMap_w {S : Scheme.{u}} {U V : S.Etale} (f : U ⟶ V) :
    etaleMap f ≫ etaleHom V = etaleHom U :=
  Over.w ((Scheme.Etale.forget S).map f)

lemma etaleMap_w_assoc {S : Scheme.{u}} {U V : S.Etale} {T : Scheme.{u}}
    (f : U ⟶ V) (g : S ⟶ T) :
    etaleMap f ≫ etaleHom V ≫ g = etaleHom U ≫ g := by
  rw [← Category.assoc, etaleMap_w]

lemma etaleMap_id {S : Scheme.{u}} (U : S.Etale) :
    etaleMap (𝟙 U) = 𝟙 (etaleObj U) :=
  (rfl)

lemma etaleMap_comp {S : Scheme.{u}} {U V W : S.Etale} (f : U ⟶ V) (g : V ⟶ W) :
    etaleMap (f ≫ g) = etaleMap f ≫ etaleMap g :=
  (rfl)

lemma etale_hom_ext {S : Scheme.{u}} {U V : S.Etale} {f g : U ⟶ V}
    (h : etaleMap f = etaleMap g) : f = g :=
  MorphismProperty.Over.Hom.ext h

/-- Construct a morphism in `S.Etale` from a morphism of underlying schemes commuting with
structure maps. -/
def etaleHomMk {S : Scheme.{u}} {U V : S.Etale}
    (f : etaleObj U ⟶ etaleObj V) (w : f ≫ etaleHom V = etaleHom U) : U ⟶ V :=
  MorphismProperty.Over.homMk f w trivial

lemma etaleMap_etaleHomMk {S : Scheme.{u}} {U V : S.Etale}
    (f : etaleObj U ⟶ etaleObj V) (w : f ≫ etaleHom V = etaleHom U) :
    etaleMap (etaleHomMk f w) = f :=
  (rfl)

/-- Construct an isomorphism in `S.Etale` from an isomorphism of underlying schemes commuting with
structure maps. -/
def etaleIsoMk {S : Scheme.{u}} {U V : S.Etale}
    (e : etaleObj U ≅ etaleObj V) (w : e.hom ≫ etaleHom V = etaleHom U) : U ≅ V :=
  MorphismProperty.Over.isoMk e w

lemma etaleMap_etaleIsoMk_hom {S : Scheme.{u}} {U V : S.Etale}
    (e : etaleObj U ≅ etaleObj V) (w : e.hom ≫ etaleHom V = etaleHom U) :
    etaleMap (etaleIsoMk e w).hom = e.hom :=
  (rfl)

lemma etaleMap_etaleIsoMk_inv {S : Scheme.{u}} {U V : S.Etale}
    (e : etaleObj U ≅ etaleObj V) (w : e.hom ≫ etaleHom V = etaleHom U) :
    etaleMap (etaleIsoMk e w).inv = e.inv :=
  (rfl)

/-- Explicit isomorphism identifying `etaleObj (etaleMk f)` with `X`. -/
def etaleMkObjIso {S X : Scheme.{u}} (f : X ⟶ S) [Etale f] :
    etaleObj (etaleMk f) ≅ X :=
  Iso.refl X

lemma etaleMkObjIso_hom_comp {S X : Scheme.{u}} (f : X ⟶ S) [Etale f] :
    (etaleMkObjIso f).hom ≫ f = etaleHom (etaleMk f) :=
  Category.id_comp f

lemma etaleMkObjIso_hom_comp_assoc {S X T : Scheme.{u}} (f : X ⟶ S) [Etale f] (g : S ⟶ T) :
    (etaleMkObjIso f).hom ≫ f ≫ g = etaleHom (etaleMk f) ≫ g := by
  rw [← Category.assoc, etaleMkObjIso_hom_comp]

lemma etaleMkObjIso_inv_comp {S X : Scheme.{u}} (f : X ⟶ S) [Etale f] :
    (etaleMkObjIso f).inv ≫ etaleHom (etaleMk f) = f :=
  Category.id_comp f

lemma etaleMkObjIso_inv_comp_assoc {S X T : Scheme.{u}} (f : X ⟶ S) [Etale f] (g : S ⟶ T) :
    (etaleMkObjIso f).inv ≫ etaleHom (etaleMk f) ≫ g = f ≫ g := by
  rw [← Category.assoc, etaleMkObjIso_inv_comp]

/-- Construct an isomorphism `etaleMk f ≅ etaleMk g` from `e : X ≅ Y` with `e.hom ≫ g = f`. -/
def etaleMkIso {S X Y : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} [Etale f] [Etale g]
    (e : X ≅ Y) (w : e.hom ≫ g = f) : etaleMk f ≅ etaleMk g :=
  etaleIsoMk (etaleMkObjIso f ≪≫ e ≪≫ (etaleMkObjIso g).symm) (by
    rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Category.assoc, Category.assoc,
      etaleMkObjIso_inv_comp, w, etaleMkObjIso_hom_comp])

lemma etaleMap_etaleMkIso_hom {S X Y : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} [Etale f] [Etale g]
    (e : X ≅ Y) (w : e.hom ≫ g = f) :
    etaleMap (etaleMkIso e w).hom = (etaleMkObjIso f).hom ≫ e.hom ≫ (etaleMkObjIso g).inv :=
  (rfl)

/-- Explicit isomorphism identifying `etaleObj ((toEtale S).obj X)` with `X.obj.left`. -/
def toEtaleObjIso {S : Scheme.{u}} (X : FiniteEtaleScheme S) :
    etaleObj ((toEtale S).obj X) ≅ X.obj.left :=
  Iso.refl X.obj.left

lemma toEtaleObjIso_hom_comp {S : Scheme.{u}} (X : FiniteEtaleScheme S) :
    (toEtaleObjIso X).hom ≫ X.obj.hom = etaleHom ((toEtale S).obj X) :=
  Category.id_comp _

lemma toEtaleObjIso_hom_comp_assoc {S T : Scheme.{u}} (X : FiniteEtaleScheme S) (g : S ⟶ T) :
    (toEtaleObjIso X).hom ≫ X.obj.hom ≫ g = etaleHom ((toEtale S).obj X) ≫ g := by
  rw [← Category.assoc, toEtaleObjIso_hom_comp]

lemma toEtaleObjIso_inv_comp {S : Scheme.{u}} (X : FiniteEtaleScheme S) :
    (toEtaleObjIso X).inv ≫ etaleHom ((toEtale S).obj X) = X.obj.hom :=
  Category.id_comp _

lemma etaleMap_toEtale {S : Scheme.{u}} {X Y : FiniteEtaleScheme S} (f : X ⟶ Y) :
    etaleMap ((toEtale S).map f) =
      (toEtaleObjIso X).hom ≫ f.hom.left ≫ (toEtaleObjIso Y).inv := by
  change f.hom.left = 𝟙 _ ≫ f.hom.left ≫ 𝟙 _
  simp

/-- Covering characterization for a family of arrows in `S.Etale` phrased via `etaleMap`. -/
lemma ofArrows_mem_smallEtaleTopology_iff_etale {S : Scheme.{u}} {W : S.Etale}
    {ι : Type*} {Z : ι → S.Etale} (f : ∀ i, Z i ⟶ W) :
    Sieve.ofArrows Z f ∈ Scheme.smallEtaleTopology S W ↔
      ⋃ i, Set.range (etaleMap (f i)) = .univ :=
  Scheme.ofArrows_mem_smallEtaleTopology_iff f

/-- The terminal object `𝟙 S` in `S.Etale`, wrapped via `etaleMk`. -/
noncomputable def etaleIdTerminal (S : Scheme.{u}) : IsTerminal (etaleMk (𝟙 S)) :=
  Scheme.Etale.mkIdTerminal S

lemma etaleIdTerminal_from_map {S : Scheme.{u}} (U : S.Etale) :
    etaleMap ((etaleIdTerminal S).from U) = etaleHom U ≫ (etaleMkObjIso (𝟙 S)).inv := by
  have hw := etaleMap_w ((etaleIdTerminal S).from U)
  rw [← etaleMkObjIso_hom_comp (𝟙 S), Category.comp_id] at hw
  rw [← hw, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Pre- and post-composing a family of scheme morphisms with isomorphisms preserves joint
surjectivity. -/
lemma iUnion_range_iso_comp_eq_univ {ι : Type*} {X X' : ι → Scheme.{u}} {Y Z : Scheme.{u}}
    (eX : ∀ i, X' i ≅ X i) (f : ∀ i, X i ⟶ Y) (eY : Y ≅ Z) :
    (⋃ i, Set.range ((eX i).hom ≫ f i ≫ eY.hom) = .univ) ↔ (⋃ i, Set.range (f i) = .univ) := by
  constructor
  · intro h
    ext y
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨i, x', hx'⟩ := Set.mem_iUnion.mp (h.symm ▸ Set.mem_univ (eY.hom y))
    refine ⟨i, (eX i).hom x', ?_⟩
    have h' := congrArg eY.inv hx'
    have hid (w : Y) : eY.inv (eY.hom w) = w := congrArg (· w) eY.hom_inv_id
    simpa only [Scheme.Hom.comp_apply, hid] using h'
  · intro h
    ext z
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨i, x, hx⟩ := Set.mem_iUnion.mp (h.symm ▸ Set.mem_univ (eY.inv z))
    refine ⟨i, (eX i).inv x, ?_⟩
    have hX (w : X i) : (eX i).hom ((eX i).inv w) = w := congrArg (· w) (eX i).inv_hom_id
    have hZ (w : Z) : eY.hom (eY.inv w) = w := congrArg (· w) eY.inv_hom_id
    simp only [Scheme.Hom.comp_apply, hX, hx, hZ]

/-- Pushforward functor `T.Etale ⥤ S.Etale` along an étale morphism `p : T ⟶ S`, sending `V ⟶ T`
to `V ⟶ T ⟶ S`. -/
abbrev etaleComp {S T : Scheme.{u}} (p : T ⟶ S) [Etale p] : T.Etale ⥤ S.Etale where
  obj V := etaleMk (etaleHom V ≫ p)
  map {V W} a := etaleHomMk
    ((etaleMkObjIso (etaleHom V ≫ p)).hom ≫ etaleMap a ≫ (etaleMkObjIso (etaleHom W ≫ p)).inv)
    (by
      rw [Category.assoc, Category.assoc, etaleMkObjIso_inv_comp, ← Category.assoc (etaleMap a),
        etaleMap_w, etaleMkObjIso_hom_comp])
  map_id V := by
    apply etale_hom_ext
    simp [etaleMap_etaleHomMk, etaleMap_id]
  map_comp f g := by
    apply etale_hom_ext
    simp [etaleMap_comp, etaleMap_etaleHomMk]

lemma etaleMap_etaleComp_map {S T : Scheme.{u}} (p : T ⟶ S) [Etale p]
    {V W : T.Etale} (a : V ⟶ W) :
    etaleMap ((etaleComp p).map a) =
      (etaleMkObjIso (etaleHom V ≫ p)).hom ≫ etaleMap a ≫ (etaleMkObjIso (etaleHom W ≫ p)).inv :=
  (rfl)

private lemma etale_over_hom {T : Scheme.{u}} (p : T ⟶ S) [Etale p]
    (U : S.Etale) (eU : etaleObj U ≅ T) (hp : eU.hom ≫ p = etaleHom U) (W : Over U) :
    Etale (etaleMap W.hom ≫ eU.hom) := by
  have : Etale ((etaleMap W.hom ≫ eU.hom) ≫ p) := by
    rw [Category.assoc, hp, etaleMap_w]
    exact instEtaleEtaleHom W.left
  exact Etale.of_comp _ p

/-- Object part of the forward equivalence `T.Etale ⥤ Over U`. -/
private abbrev etaleOverFunObj {T : Scheme.{u}} (p : T ⟶ S) [Etale p]
    (U : S.Etale) (eU : etaleObj U ≅ T) (hp : eU.hom ≫ p = etaleHom U) (V : T.Etale) : Over U :=
  Over.mk <| etaleHomMk (U := etaleMk (etaleHom V ≫ p)) (V := U)
    ((etaleMkObjIso (etaleHom V ≫ p)).hom ≫ etaleHom V ≫ eU.inv)
    (by rw [Category.assoc, Category.assoc, ← hp, Iso.inv_hom_id_assoc, etaleMkObjIso_hom_comp])

private lemma etaleMap_etaleOverFunObj_hom {T : Scheme.{u}} (p : T ⟶ S) [Etale p]
    (U : S.Etale) (eU : etaleObj U ≅ T) (hp : eU.hom ≫ p = etaleHom U) (V : T.Etale) :
    etaleMap (etaleOverFunObj p U eU hp V).hom =
      (etaleMkObjIso (etaleHom V ≫ p)).hom ≫ etaleHom V ≫ eU.inv :=
  (rfl)

/-- Object part of the inverse equivalence `Over U ⥤ T.Etale`. -/
private def etaleOverInvObj {T : Scheme.{u}} (p : T ⟶ S) [Etale p]
    (U : S.Etale) (eU : etaleObj U ≅ T) (hp : eU.hom ≫ p = etaleHom U) (W : Over U) : T.Etale :=
  @etaleMk T (etaleObj W.left) (etaleMap W.hom ≫ eU.hom) (etale_over_hom p U eU hp W)

private def etaleOverInvObjIso {T : Scheme.{u}} (p : T ⟶ S) [Etale p]
    (U : S.Etale) (eU : etaleObj U ≅ T) (hp : eU.hom ≫ p = etaleHom U) (W : Over U) :
    etaleObj (etaleOverInvObj p U eU hp W) ≅ etaleObj W.left :=
  Iso.refl (etaleObj W.left)

private lemma etaleOverInvObjIso_hom_comp {T : Scheme.{u}} (p : T ⟶ S) [Etale p]
    (U : S.Etale) (eU : etaleObj U ≅ T) (hp : eU.hom ≫ p = etaleHom U) (W : Over U) :
    (etaleOverInvObjIso p U eU hp W).hom ≫ etaleMap W.hom ≫ eU.hom =
      etaleHom (etaleOverInvObj p U eU hp W) :=
  Category.id_comp _

private lemma etaleOverInvObjIso_inv_comp {T : Scheme.{u}} (p : T ⟶ S) [Etale p]
    (U : S.Etale) (eU : etaleObj U ≅ T) (hp : eU.hom ≫ p = etaleHom U) (W : Over U) :
    (etaleOverInvObjIso p U eU hp W).inv ≫ etaleHom (etaleOverInvObj p U eU hp W) =
      etaleMap W.hom ≫ eU.hom :=
  Category.id_comp _

private abbrev etaleOverFunctor {T : Scheme.{u}} (p : T ⟶ S) [Etale p]
    (U : S.Etale) (eU : etaleObj U ≅ T) (hp : eU.hom ≫ p = etaleHom U) :
    T.Etale ⥤ Over U where
  obj V := etaleOverFunObj p U eU hp V
  map {V W} f := Over.homMk ((etaleComp p).map f) (by
    apply etale_hom_ext
    rw [etaleMap_comp, etaleMap_etaleComp_map, etaleMap_etaleOverFunObj_hom,
      etaleMap_etaleOverFunObj_hom, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc,
      etaleMap_w_assoc])
  map_id V := by
    ext1
    apply etale_hom_ext
    simp only [Over.homMk_left, Over.id_left, etaleMap_etaleHomMk, etaleMap_id, Category.id_comp,
      Iso.hom_inv_id]
    rfl
  map_comp f g := by
    ext1
    apply etale_hom_ext
    simp only [Over.homMk_left, Over.comp_left, etaleMap_comp, etaleMap_etaleHomMk, Category.assoc,
      Iso.inv_hom_id_assoc]

private def etaleOverInverse {T : Scheme.{u}} (p : T ⟶ S) [Etale p]
    (U : S.Etale) (eU : etaleObj U ≅ T) (hp : eU.hom ≫ p = etaleHom U) :
    Over U ⥤ T.Etale where
  obj W := etaleOverInvObj p U eU hp W
  map {W₁ W₂} f :=
    etaleHomMk ((etaleOverInvObjIso p U eU hp W₁).hom ≫ etaleMap f.left ≫
      (etaleOverInvObjIso p U eU hp W₂).inv) (by
      rw [Category.assoc, Category.assoc, etaleOverInvObjIso_inv_comp]
      have hw := congrArg etaleMap (Over.w f)
      rw [etaleMap_comp] at hw
      rw [reassoc_of% hw, etaleOverInvObjIso_hom_comp])
  map_id W := by
    apply etale_hom_ext
    simp only [Over.id_left, etaleMap_etaleHomMk, etaleMap_id, Category.id_comp, Iso.hom_inv_id]
  map_comp f g := by
    apply etale_hom_ext
    simp only [Over.comp_left, etaleMap_comp, etaleMap_etaleHomMk, Category.assoc,
      Iso.inv_hom_id_assoc]

/-- For an étale `S`-scheme `U` identified with `p : T ⟶ S` via `eU : etaleObj U ≅ T`, the small
étale site `T.Etale` is equivalent to the slice category `Over U` of `S.Etale`. -/
noncomputable def etaleOverEquiv {T : Scheme.{u}} (p : T ⟶ S) [Etale p]
    (U : S.Etale) (eU : etaleObj U ≅ T) (hp : eU.hom ≫ p = etaleHom U) :
    T.Etale ≌ Over U where
  functor := etaleOverFunctor p U eU hp
  inverse := etaleOverInverse p U eU hp
  unitIso := NatIso.ofComponents
    (fun V ↦
      etaleIsoMk ((etaleMkObjIso (etaleHom V ≫ p)).symm ≪≫
        (etaleOverInvObjIso p U eU hp (etaleOverFunObj p U eU hp V)).symm) (by
        dsimp only [Functor.comp_obj, Functor.id_obj, etaleOverFunctor, etaleOverInverse]
        rw [Iso.trans_hom, Iso.symm_hom, Iso.symm_hom, Category.assoc,
          etaleOverInvObjIso_inv_comp, etaleMap_etaleOverFunObj_hom, Category.assoc,
          Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]))
    (fun {V W} f ↦ by
      apply etale_hom_ext
      simp only [Functor.id_map, Functor.comp_map, etaleOverFunctor, etaleOverInverse,
        etaleMap_comp, etaleMap_etaleIsoMk_hom, etaleMap_etaleHomMk, Over.homMk_left,
        Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc])
  counitIso := NatIso.ofComponents
    (fun W ↦
      Over.isoMk
        (etaleIsoMk (etaleMkObjIso (etaleHom (etaleOverInvObj p U eU hp W) ≫ p) ≪≫
          etaleOverInvObjIso p U eU hp W) (by
          dsimp only [Functor.comp_obj, Functor.id_obj, etaleOverFunctor, etaleOverInverse]
          rw [Iso.trans_hom, Category.assoc, ← etaleMap_w W.hom, ← hp,
            ← Category.assoc (etaleMap W.hom),
            ← Category.assoc (etaleOverInvObjIso p U eU hp W).hom,
            etaleOverInvObjIso_hom_comp, etaleMkObjIso_hom_comp]
          rfl))
        (by
          apply etale_hom_ext
          rw [etaleMap_comp]
          change (etaleMkObjIso (etaleHom (etaleOverInvObj p U eU hp W) ≫ p) ≪≫
              etaleOverInvObjIso p U eU hp W).hom ≫ etaleMap W.hom =
            etaleMap (etaleOverFunObj p U eU hp (etaleOverInvObj p U eU hp W)).hom
          rw [etaleMap_etaleOverFunObj_hom, Iso.trans_hom, Category.assoc]
          congr 1
          rw [← etaleOverInvObjIso_hom_comp p U eU hp W, Category.assoc, Category.assoc,
            Iso.hom_inv_id, Category.comp_id]))
    (fun {W₁ W₂} f ↦ by
      ext1
      apply etale_hom_ext
      simp only [Functor.id_map, Functor.comp_map, etaleOverFunctor, etaleOverInverse,
        Over.comp_left, Over.isoMk_hom_left, Over.homMk_left, etaleMap_comp,
        etaleMap_etaleIsoMk_hom, etaleMap_etaleHomMk, Iso.trans_hom, Category.assoc,
        Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id])

/-- Explicit isomorphism identifying `etaleObj ((etaleOverEquiv ...).inverse.obj W)` with
`etaleObj W.left`. -/
private def etaleOverInverseObjIso {T : Scheme.{u}} (p : T ⟶ S) [Etale p]
    (U : S.Etale) (eU : etaleObj U ≅ T) (hp : eU.hom ≫ p = etaleHom U) (W : Over U) :
    etaleObj ((etaleOverEquiv p U eU hp).inverse.obj W) ≅ etaleObj W.left :=
  etaleOverInvObjIso p U eU hp W

private lemma etaleOverInverseObjIso_hom_comp {T : Scheme.{u}} (p : T ⟶ S) [Etale p]
    (U : S.Etale) (eU : etaleObj U ≅ T) (hp : eU.hom ≫ p = etaleHom U) (W : Over U) :
    (etaleOverInverseObjIso p U eU hp W).hom ≫ etaleMap W.hom ≫ eU.hom =
      etaleHom ((etaleOverEquiv p U eU hp).inverse.obj W) :=
  etaleOverInvObjIso_hom_comp p U eU hp W

private lemma etaleMap_etaleOverEquiv_inverse_map {T : Scheme.{u}} (p : T ⟶ S) [Etale p]
    (U : S.Etale) (eU : etaleObj U ≅ T) (hp : eU.hom ≫ p = etaleHom U)
    {W₁ W₂ : Over U} (f : W₁ ⟶ W₂) :
    etaleMap ((etaleOverEquiv p U eU hp).inverse.map f) =
      (etaleOverInverseObjIso p U eU hp W₁).hom ≫ etaleMap f.left ≫
        (etaleOverInverseObjIso p U eU hp W₂).inv :=
  (rfl)

instance instIsDenseSubsiteEtaleOverEquivInverse {T : Scheme.{u}} (p : T ⟶ S) [Etale p]
    (U : S.Etale) (eU : etaleObj U ≅ T) (hp : eU.hom ≫ p = etaleHom U) :
    (etaleOverEquiv p U eU hp).inverse.IsDenseSubsite
      ((Scheme.smallEtaleTopology S).over U) (Scheme.smallEtaleTopology T) where
  functorPushforward_mem_iff {W R} := by
    obtain ⟨ι, Z, f, rfl⟩ := R.exists_eq_ofArrows
    rw [Sieve.functorPushforward_ofArrows, ofArrows_mem_smallEtaleTopology_iff_etale,
      GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows,
      ofArrows_mem_smallEtaleTopology_iff_etale]
    simp only [etaleMap_etaleOverEquiv_inverse_map]
    exact iUnion_range_iso_comp_eq_univ (fun i ↦ etaleOverInverseObjIso p U eU hp (Z i))
      (fun i ↦ etaleMap (f i).left) (etaleOverInverseObjIso p U eU hp W).symm

instance instIsContinuousEtaleComp {T : Scheme.{u}} (p : T ⟶ S) [Etale p] :
    (etaleComp p).IsContinuous (Scheme.smallEtaleTopology T) (Scheme.smallEtaleTopology S) where
  op_comp_isSheaf_of_types G :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      ((((etaleOverEquiv p (etaleMk p) (etaleMkObjIso p) (etaleMkObjIso_hom_comp p)).sheafCongr
        (Scheme.smallEtaleTopology T)
        ((Scheme.smallEtaleTopology S).over (etaleMk p)) _).inverse.obj
          (((Scheme.smallEtaleTopology S).overPullback _ (etaleMk p)).obj G)).property)

/-- Restricting a sheaf on the small étale site of `S` along an étale morphism `p : T ⟶ S` to a
sheaf on the small étale site of `T`. On `V : T.Etale`, its value is `F(etaleMk (etaleHom V ≫ p))`.
-/
noncomputable abbrev restrictSheaf {A : Type*} [Category A] {T : Scheme.{u}} (p : T ⟶ S) [Etale p] :
    Sheaf (Scheme.smallEtaleTopology S) A ⥤ Sheaf (Scheme.smallEtaleTopology T) A :=
  (etaleComp p).sheafPushforwardContinuous A (Scheme.smallEtaleTopology T)
    (Scheme.smallEtaleTopology S)

/-- Compatibility between `restrictSheaf p` and `sheafCongr` on `Over (etaleMk p)`. -/
noncomputable def restrictSheafMkOverIso {A : Type*} [Category A] {T : Scheme.{u}} (p : T ⟶ S)
    [Etale p] (F : Sheaf (Scheme.smallEtaleTopology S) A) :
    (restrictSheaf p).obj F ≅
      (((etaleOverEquiv p (etaleMk p) (etaleMkObjIso p) (etaleMkObjIso_hom_comp p)).sheafCongr
        (Scheme.smallEtaleTopology T)
        ((Scheme.smallEtaleTopology S).over (etaleMk p)) A).inverse).obj (F.over (etaleMk p)) :=
  ObjectProperty.isoMk _ (Iso.refl _)

/-- Compatibility between `restrictSheaf (etaleHom U)` and `sheafCongr` on `Over U`. -/
noncomputable def restrictSheafOverIso {A : Type*} [Category A] (U : S.Etale)
    (F : Sheaf (Scheme.smallEtaleTopology S) A) :
    (restrictSheaf (etaleHom U)).obj F ≅
      (((etaleOverEquiv (etaleHom U) U (Iso.refl _) (Category.id_comp _)).sheafCongr
        (Scheme.smallEtaleTopology (etaleObj U))
        ((Scheme.smallEtaleTopology S).over U) A).inverse).obj (F.over U) :=
  ObjectProperty.isoMk _ (Iso.refl _)

/-- Comparison isomorphism in `S.Etale` between `V ⟶ T ⟶ S` along two equal étale morphisms
`f = g`. -/
def etaleEqIso {T : Scheme.{u}} {f g : T ⟶ S} [Etale f] [Etale g] (h : f = g) (V : T.Etale) :
    etaleMk (etaleHom V ≫ g) ≅ etaleMk (etaleHom V ≫ f) :=
  etaleMkIso (Iso.refl (etaleObj V)) (by simp [h])

@[simp]
lemma etaleMap_etaleEqIso_hom {T : Scheme.{u}} {f g : T ⟶ S} [Etale f] [Etale g] (h : f = g)
    (V : T.Etale) :
    etaleMap (etaleEqIso h V).hom =
      (etaleMkObjIso (etaleHom V ≫ g)).hom ≫ (etaleMkObjIso (etaleHom V ≫ f)).inv := by
  simp [etaleEqIso, etaleMap_etaleMkIso_hom]

/-- Restricting along two equal étale morphisms gives naturally isomorphic sheaves. -/
noncomputable def restrictSheafEqIso {A : Type*} [Category A] {T : Scheme.{u}} {f g : T ⟶ S}
    [Etale f] [Etale g] (h : f = g) (F : Sheaf (Scheme.smallEtaleTopology S) A) :
    (restrictSheaf f).obj F ≅ (restrictSheaf g).obj F :=
  ObjectProperty.isoMk _ <| NatIso.ofComponents
    (fun V : T.Etaleᵒᵖ ↦ F.obj.mapIso (etaleEqIso h V.unop).op)
    (fun {V W} a ↦ by
      change F.obj.map ((etaleComp f).map a.unop).op ≫ F.obj.map (etaleEqIso h W.unop).hom.op =
        F.obj.map (etaleEqIso h V.unop).hom.op ≫ F.obj.map ((etaleComp g).map a.unop).op
      rw [← F.obj.map_comp, ← F.obj.map_comp, ← op_comp, ← op_comp]
      refine congrArg (fun k ↦ F.obj.map (Quiver.Hom.op k)) ?_
      apply etale_hom_ext
      simp only [etaleMap_comp, etaleEqIso, etaleMap_etaleMkIso_hom, etaleMap_etaleHomMk,
        Iso.refl_hom, Category.id_comp, Category.assoc, Iso.inv_hom_id_assoc])

/-- Comparison isomorphism in `S.Etale` between `V ⟶ W ⟶ T ⟶ S` formed in one step versus two
steps. -/
def etaleCompIso {T W : Scheme.{u}} (f : W ⟶ T) (g : T ⟶ S) [Etale f] [Etale g] (V : W.Etale) :
    etaleMk (etaleHom V ≫ f ≫ g) ≅ etaleMk (etaleHom (etaleMk (etaleHom V ≫ f)) ≫ g) :=
  etaleMkIso (etaleMkObjIso (etaleHom V ≫ f)).symm
    (by rw [Iso.symm_hom, ← Category.assoc, etaleMkObjIso_inv_comp, Category.assoc])

@[simp]
lemma etaleMap_etaleCompIso_hom {T W : Scheme.{u}} (f : W ⟶ T) (g : T ⟶ S) [Etale f] [Etale g]
    (V : W.Etale) :
    etaleMap (etaleCompIso f g V).hom =
      (etaleMkObjIso (etaleHom V ≫ f ≫ g)).hom ≫ (etaleMkObjIso (etaleHom V ≫ f)).inv ≫
        (etaleMkObjIso (etaleHom (etaleMk (etaleHom V ≫ f)) ≫ g)).inv := by
  simp [etaleCompIso, etaleMap_etaleMkIso_hom]

/-- Composing two étale restrictions agrees with restriction along the composite étale morphism. -/
noncomputable def restrictSheafCompIso {A : Type*} [Category A] {T W : Scheme.{u}}
    (f : W ⟶ T) (g : T ⟶ S) [Etale f] [Etale g] (F : Sheaf (Scheme.smallEtaleTopology S) A) :
    (restrictSheaf f).obj ((restrictSheaf g).obj F) ≅ (restrictSheaf (f ≫ g)).obj F :=
  ObjectProperty.isoMk _ <| NatIso.ofComponents
    (fun V : W.Etaleᵒᵖ ↦ F.obj.mapIso (etaleCompIso f g V.unop).op)
    (fun {V₁ V₂} a ↦ by
      change F.obj.map ((etaleComp g).map ((etaleComp f).map a.unop)).op ≫
          F.obj.map (etaleCompIso f g V₂.unop).hom.op =
        F.obj.map (etaleCompIso f g V₁.unop).hom.op ≫ F.obj.map ((etaleComp (f ≫ g)).map a.unop).op
      rw [← F.obj.map_comp, ← F.obj.map_comp, ← op_comp, ← op_comp]
      refine congrArg (fun k ↦ F.obj.map (Quiver.Hom.op k)) ?_
      apply etale_hom_ext
      simp only [etaleMap_comp, etaleCompIso, etaleMap_etaleMkIso_hom, etaleMap_etaleHomMk,
        Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc])

lemma restrictSheaf_map_app {A : Type*} [Category A] {T : Scheme.{u}} (p : T ⟶ S) [Etale p]
    {G F : Sheaf (Scheme.smallEtaleTopology S) A} (φ : G ⟶ F) (V : T.Etale) :
    ((restrictSheaf p).map φ).hom.app (op V) = φ.hom.app (op ((etaleComp p).obj V)) :=
  (rfl)

lemma restrictSheafEqIso_hom_app {A : Type*} [Category A] {T : Scheme.{u}} {f g : T ⟶ S}
    [Etale f] [Etale g] (h : f = g) (F : Sheaf (Scheme.smallEtaleTopology S) A) (V : T.Etale) :
    (restrictSheafEqIso h F).hom.hom.app (op V) = F.obj.map (etaleEqIso h V).hom.op :=
  (rfl)

lemma restrictSheafCompIso_hom_app {A : Type*} [Category A] {T W : Scheme.{u}} (f : W ⟶ T)
    (g : T ⟶ S) [Etale f] [Etale g] (F : Sheaf (Scheme.smallEtaleTopology S) A) (V : W.Etale) :
    (restrictSheafCompIso f g F).hom.hom.app (op V) = F.obj.map (etaleCompIso f g V).hom.op :=
  (rfl)

/-- Explicit isomorphism identifying `((pullback p).obj X).obj.left` with
`Limits.pullback X.obj.hom p`. -/
noncomputable def pullbackObjIso {S T : Scheme.{u}} (p : T ⟶ S) (X : FiniteEtaleScheme S) :
    ((pullback p).obj X).obj.left ≅ Limits.pullback X.obj.hom p :=
  Iso.refl _

lemma pullbackObjIso_hom {S T : Scheme.{u}} (p : T ⟶ S) (X : FiniteEtaleScheme S) :
    (pullbackObjIso p X).hom = 𝟙 _ :=
  (rfl)

lemma pullbackObjIso_hom_snd {S T : Scheme.{u}} (p : T ⟶ S) (X : FiniteEtaleScheme S) :
    (pullbackObjIso p X).hom ≫ Limits.pullback.snd X.obj.hom p = ((pullback p).obj X).obj.hom :=
  Category.id_comp _

lemma pullbackObjIso_inv_hom {S T : Scheme.{u}} (p : T ⟶ S) (X : FiniteEtaleScheme S) :
    (pullbackObjIso p X).inv ≫ ((pullback p).obj X).obj.hom = Limits.pullback.snd X.obj.hom p :=
  Category.id_comp _

private lemma pullbackMap_fst {S T : Scheme.{u}} (p : T ⟶ S) {X Y : FiniteEtaleScheme S}
    (f : X ⟶ Y) :
    ((pullback p).map f).hom.left ≫ (pullbackObjIso p Y).hom ≫ Limits.pullback.fst Y.obj.hom p =
      (pullbackObjIso p X).hom ≫ Limits.pullback.fst X.obj.hom p ≫ f.hom.left := by
  change Limits.pullback.lift (Limits.pullback.fst X.obj.hom p ≫ f.hom.left)
    (Limits.pullback.snd X.obj.hom p) _ ≫ 𝟙 _ ≫ Limits.pullback.fst Y.obj.hom p =
    𝟙 _ ≫ Limits.pullback.fst X.obj.hom p ≫ f.hom.left
  simp

private lemma pullbackMap_snd {S T : Scheme.{u}} (p : T ⟶ S) {X Y : FiniteEtaleScheme S}
    (f : X ⟶ Y) :
    ((pullback p).map f).hom.left ≫ (pullbackObjIso p Y).hom ≫ Limits.pullback.snd Y.obj.hom p =
      (pullbackObjIso p X).hom ≫ Limits.pullback.snd X.obj.hom p := by
  change Limits.pullback.lift (Limits.pullback.fst X.obj.hom p ≫ f.hom.left)
    (Limits.pullback.snd X.obj.hom p) _ ≫ 𝟙 _ ≫ Limits.pullback.snd Y.obj.hom p =
    𝟙 _ ≫ Limits.pullback.snd X.obj.hom p
  simp

/-- Bijection between sections of `X` over `V ⟶ T ⟶ S` and sections of `X ×_S T` over `V ⟶ T`. -/
noncomputable def restrictSectionEquiv {T : Scheme.{u}} (p : T ⟶ S) [Etale p]
    (X : FiniteEtaleScheme S) (V : T.Etale) :
    (etaleMk (etaleHom V ≫ p) ⟶ (toEtale S).obj X) ≃
      (V ⟶ (toEtale T).obj ((pullback p).obj X)) where
  toFun g := etaleHomMk
    (Limits.pullback.lift (f := X.obj.hom) (g := p)
      ((etaleMkObjIso (etaleHom V ≫ p)).inv ≫ etaleMap g ≫ (toEtaleObjIso X).hom)
      (etaleHom V) (by
        rw [Category.assoc, Category.assoc, toEtaleObjIso_hom_comp, etaleMap_w,
          etaleMkObjIso_inv_comp]) ≫
      (pullbackObjIso p X).inv ≫ (toEtaleObjIso ((pullback p).obj X)).inv)
    (by
      simp only [Category.assoc, toEtaleObjIso_inv_comp, pullbackObjIso_inv_hom,
        Limits.pullback.lift_snd])
  invFun h := etaleHomMk
    ((etaleMkObjIso (etaleHom V ≫ p)).hom ≫
      (etaleMap h ≫ (toEtaleObjIso ((pullback p).obj X)).hom ≫
        (pullbackObjIso p X).hom ≫ Limits.pullback.fst X.obj.hom p) ≫
      (toEtaleObjIso X).inv)
    (by
      rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc, Category.assoc,
        toEtaleObjIso_inv_comp, Limits.pullback.condition,
        ← Category.assoc (pullbackObjIso p X).hom, pullbackObjIso_hom_snd,
        ← Category.assoc (toEtaleObjIso _).hom, toEtaleObjIso_hom_comp,
        ← Category.assoc (etaleMap h), etaleMap_w, etaleMkObjIso_hom_comp])
  left_inv g := by
    apply etale_hom_ext
    simp only [etaleMap_etaleHomMk, Category.assoc, Iso.inv_hom_id_assoc, Limits.pullback.lift_fst,
      Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  right_inv h := by
    apply etale_hom_ext
    rw [etaleMap_etaleHomMk, ← cancel_mono (toEtaleObjIso ((pullback p).obj X)).hom,
      ← cancel_mono (pullbackObjIso p X).hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    refine Limits.pullback.hom_ext ?_ ?_
    · simp only [Limits.pullback.lift_fst, etaleMap_etaleHomMk, Category.assoc,
        Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
    · simp only [Limits.pullback.lift_snd]
      rw [Category.assoc, Category.assoc, pullbackObjIso_hom_snd, toEtaleObjIso_hom_comp,
        etaleMap_w]

@[simp]
lemma etaleMap_restrictSectionEquiv_symm {T : Scheme.{u}} (p : T ⟶ S) [Etale p]
    (X : FiniteEtaleScheme S) (V : T.Etale)
    (h : V ⟶ (toEtale T).obj ((pullback p).obj X)) :
    etaleMap ((restrictSectionEquiv p X V).symm h) =
      (etaleMkObjIso (etaleHom V ≫ p)).hom ≫
        (etaleMap h ≫ (toEtaleObjIso ((pullback p).obj X)).hom ≫
          (pullbackObjIso p X).hom ≫ Limits.pullback.fst X.obj.hom p) ≫
        (toEtaleObjIso X).inv :=
  etaleMap_etaleHomMk _ _

/-- Restricting the sheaf of sections of a finite étale `S`-scheme along an étale morphism
`p : T ⟶ S` gives the sheaf of sections of its base change to `T`, naturally in `X`. -/
noncomputable def toSheafCompRestrictSheafIso {T : Scheme.{u}} (p : T ⟶ S) [Etale p] :
    toSheaf S ⋙ restrictSheaf p ≅ pullback p ⋙ toSheaf T :=
  NatIso.ofComponents
    (fun X ↦ ObjectProperty.isoMk _ <| NatIso.ofComponents
      (fun V ↦ (restrictSectionEquiv p X V.unop).toIso)
      (fun {V W} a ↦ by
        ext g
        apply etale_hom_ext
        let g' : etaleMk (etaleHom V.unop ≫ p) ⟶ (toEtale S).obj X := g
        change etaleMap (restrictSectionEquiv p X W.unop ((etaleComp p).map a.unop ≫ g')) =
          etaleMap (a.unop ≫ restrictSectionEquiv p X V.unop g')
        rw [etaleMap_comp]
        dsimp only [restrictSectionEquiv, Equiv.coe_fn_mk]
        rw [etaleMap_etaleHomMk, etaleMap_etaleHomMk,
          ← cancel_mono (toEtaleObjIso ((pullback p).obj X)).hom,
          ← cancel_mono (pullbackObjIso p X).hom]
        refine Limits.pullback.hom_ext ?_ ?_
        · simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id,
            Limits.pullback.lift_fst, etaleMap_comp, etaleMap_etaleHomMk]
        · simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
            Limits.pullback.lift_snd]
          exact (etaleMap_w a.unop).symm))
    (fun {X Y} f ↦ by
      ext V g
      apply etale_hom_ext
      let g' : etaleMk (etaleHom V.unop ≫ p) ⟶ (toEtale S).obj X := g
      change etaleMap (restrictSectionEquiv p Y V.unop (g' ≫ (toEtale S).map f)) =
        etaleMap (restrictSectionEquiv p X V.unop g' ≫ (toEtale T).map ((pullback p).map f))
      rw [etaleMap_comp]
      dsimp only [restrictSectionEquiv, Equiv.coe_fn_mk]
      rw [etaleMap_etaleHomMk, etaleMap_etaleHomMk,
        ← cancel_mono (toEtaleObjIso ((pullback p).obj Y)).hom,
        ← cancel_mono (pullbackObjIso p Y).hom]
      refine Limits.pullback.hom_ext ?_ ?_
      · simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id,
          Limits.pullback.lift_fst, etaleMap_comp, etaleMap_toEtale, pullbackMap_fst,
          Limits.pullback.lift_fst_assoc]
      · simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id,
          Limits.pullback.lift_snd, etaleMap_toEtale, pullbackMap_snd])

lemma toSheafCompRestrictSheafIso_inv_app {T : Scheme.{u}} (p : T ⟶ S) [Etale p]
    (X : FiniteEtaleScheme S) (V : T.Etale)
    (f : V ⟶ (toEtale T).obj ((pullback p).obj X)) :
    ((toSheafCompRestrictSheafIso p).app X).inv.hom.app (op V) f =
      (restrictSectionEquiv p X V).symm f :=
  (rfl)

/-- Restricting a constant étale sheaf with finite value along an étale morphism `p : T ⟶ S`
yields the constant étale sheaf with the same value on `T`. -/
noncomputable def restrictSheafConstantSheafIso {T : Scheme.{u}} (p : T ⟶ S) [Etale p]
    (M : Type u) [Finite M] :
    (restrictSheaf p).obj ((constantSheaf (Scheme.smallEtaleTopology S) (Type u)).obj M) ≅
      (constantSheaf (Scheme.smallEtaleTopology T) (Type u)).obj M :=
  (restrictSheaf p).mapIso (toSheafTrivialCoverIso S M).symm ≪≫
    (toSheafCompRestrictSheafIso p).app (trivialCover S M) ≪≫
    (toSheaf T).mapIso (pullbackTrivialCoverIso p M) ≪≫
    toSheafTrivialCoverIso T M

/-- On an empty étale `S`-scheme, every étale sheaf of sets has at most one section. -/
lemma subsingleton_of_isEmpty (F : Sheaf (Scheme.smallEtaleTopology S) (Type u))
    (Z : S.Etale) [IsEmpty (etaleObj Z)] :
    Subsingleton (F.obj.obj (op Z)) := by
  refine ⟨fun a b ↦ ?_⟩
  have hcov : Sieve.ofArrows (fun i : PEmpty.{1} ↦ i.elim) (fun i : PEmpty.{1} ↦ i.elim) ∈
      Scheme.smallEtaleTopology S Z := by
    rw [ofArrows_mem_smallEtaleTopology_iff_etale]
    ext z
    exact IsEmpty.elim ‹IsEmpty (etaleObj Z)› z
  have h := F.property.hom_ext_ofArrows (E := PUnit.{u + 1})
    (fun i : PEmpty.{1} ↦ i.elim) hcov (x := TypeCat.ofHom fun _ ↦ a)
    (y := TypeCat.ofHom fun _ ↦ b) (fun i ↦ i.elim)
  exact congrArg (fun k : PUnit.{u + 1} ⟶ F.obj.obj (op Z) ↦ k PUnit.unit) h

/-- Helper for `isLocallyConstantIn_restrictSheaf`: triviality over `Z` pulls back along
`etaleOverEquiv` to triviality of `(restrictSheaf p).obj F` over the corresponding object of
`T.Etale`. -/
private lemma restrictSheaf_over_iso_const {T : Scheme.{u}} (p : T ⟶ S) [Etale p]
    {F : Sheaf (Scheme.smallEtaleTopology S) (Type u)} {Z : S.Etale}
    (f : Z ⟶ etaleMk p) (M : Type u) [Finite M]
    (e : F.over Z ≅ ((constantSheaf (Scheme.smallEtaleTopology S) (Type u)).obj M).over Z) :
    let V := (etaleOverEquiv p (etaleMk p) (etaleMkObjIso p)
      (etaleMkObjIso_hom_comp p)).inverse.obj (Over.mk f)
    Nonempty (((restrictSheaf p).obj F).over V ≅
      ((constantSheaf (Scheme.smallEtaleTopology T) (Type u)).obj M).over V) := by
  intro V
  let eqvV := (etaleOverEquiv (etaleHom V) V (Iso.refl _) (Category.id_comp _)).sheafCongr
    (Scheme.smallEtaleTopology (etaleObj V))
    ((Scheme.smallEtaleTopology T).over V) (Type u)
  let eqvZ := (etaleOverEquiv (etaleHom Z) Z (Iso.refl _) (Category.id_comp _)).sheafCongr
    (Scheme.smallEtaleTopology (etaleObj Z))
    ((Scheme.smallEtaleTopology S).over Z) (Type u)
  let eIso : etaleObj V ≅ etaleObj Z :=
    etaleOverInverseObjIso p (etaleMk p) (etaleMkObjIso p) (etaleMkObjIso_hom_comp p) (Over.mk f)
  have hcompEq : etaleHom V ≫ p = eIso.hom ≫ etaleHom Z := by
    rw [← etaleOverInverseObjIso_hom_comp p (etaleMk p) (etaleMkObjIso p)
      (etaleMkObjIso_hom_comp p) (Over.mk f), Category.assoc, Category.assoc,
      etaleMkObjIso_hom_comp, etaleMap_w]
    rfl
  refine ⟨eqvV.inverse.preimageIso ?_⟩
  exact (restrictSheafOverIso V _).symm ≪≫
    restrictSheafCompIso (etaleHom V) p F ≪≫
    restrictSheafEqIso hcompEq F ≪≫
    (restrictSheafCompIso eIso.hom (etaleHom Z) F).symm ≪≫
    (restrictSheaf eIso.hom).mapIso
      (restrictSheafOverIso Z F ≪≫ eqvZ.inverse.mapIso e ≪≫
        (restrictSheafOverIso Z _).symm ≪≫
        restrictSheafConstantSheafIso (etaleHom Z) M) ≪≫
    restrictSheafConstantSheafIso eIso.hom M ≪≫
    (restrictSheafConstantSheafIso (etaleHom V) M).symm ≪≫
    restrictSheafOverIso V _

/-- An étale restriction of a locally constant finite sheaf of sets is locally constant with finite
values. -/
theorem isLocallyConstantIn_restrictSheaf {T : Scheme.{u}} (p : T ⟶ S) [Etale p]
    {F : Sheaf (Scheme.smallEtaleTopology S) (Type u)}
    (hF : F.IsLocallyConstantIn (Scheme.smallEtaleTopology S) Finite) :
    ((restrictSheaf p).obj F).IsLocallyConstantIn (Scheme.smallEtaleTopology T) Finite := by
  rw [Sheaf.isLocallyConstantIn_iff_of_isTerminal _ _ (etaleIdTerminal T)]
  let U : S.Etale := etaleMk p
  have hcov := (Sheaf.isLocallyConstantIn_iff _ _).mp hF U
  obtain ⟨ι, Z, f, hf⟩ := (F.locallyConstantSieve Finite U).exists_eq_ofArrows
  have hsurj : ⋃ i, Set.range (etaleMap (f i)) = .univ := by
    rw [← ofArrows_mem_smallEtaleTopology_iff_etale, ← hf]
    exact hcov
  let eqvU := etaleOverEquiv p U (etaleMkObjIso p) (etaleMkObjIso_hom_comp p)
  let V (i : ι) : T.Etale := eqvU.inverse.obj (Over.mk (f i))
  refine (Scheme.smallEtaleTopology T).superset_covering ?_
    ((ofArrows_mem_smallEtaleTopology_iff_etale
      (fun i ↦ (etaleIdTerminal T).from (V i))).2 ?_)
  · intro W g hg
    rw [Sieve.mem_ofArrows_iff] at hg
    obtain ⟨i, u, rfl⟩ := hg
    refine ((restrictSheaf p).obj F).locallyConstantSieve Finite _ |>.downward_closed ?_ u
    have hmem : F.locallyConstantSieve Finite U (f i) := by
      rw [hf, Sieve.mem_ofArrows_iff]
      exact ⟨i, 𝟙 _, (Category.id_comp _).symm⟩
    obtain ⟨M, hM, ⟨e⟩⟩ := (Sheaf.locallyConstantSieve_apply _ _ _).mp hmem
    rw [Sheaf.locallyConstantSieve_apply]
    exact ⟨M, hM, restrictSheaf_over_iso_const p (f i) M e⟩
  · simp only [etaleIdTerminal_from_map]
    have hV (i : ι) : etaleHom (V i) =
        (etaleOverInverseObjIso p U (etaleMkObjIso p) (etaleMkObjIso_hom_comp p)
          (Over.mk (f i))).hom ≫ etaleMap (f i) ≫ (etaleMkObjIso p).hom :=
      (etaleOverInverseObjIso_hom_comp p U (etaleMkObjIso p) (etaleMkObjIso_hom_comp p)
        (Over.mk (f i))).symm
    simp only [hV, Category.assoc]
    exact (iUnion_range_iso_comp_eq_univ _ (fun i ↦ etaleMap (f i))
      (etaleMkObjIso p ≪≫ (etaleMkObjIso (𝟙 T)).symm)).2 hsurj


end EtaleRestriction

end TauCeti.FiniteEtaleScheme
