/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.IsomTorsor.Functor
public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.Map

/-!
# The extended Isom torsors for change of band

Let `b` be an `A`-banding of a gerbe `F` and let `φ : A ⟶ B` be a homomorphism of abelian
sheaves. The Hom sheaves for change of band are obtained by extending the structure group of
`b.sheafHomTorsor x y` along `φ|_U`. This file constructs them as a functor of both endpoints,
using the existing `Sheaf.Torsor.map`. Their local representatives `[p, c]` are the sections
`c • [p, 0]`. Transport in either endpoint keeps `c`, and acting on `p` by `a` adds `φ a` to `c`.

For the identity homomorphism, these torsors are naturally isomorphic to the original Isom
torsors, compatibly with their actions and endpoint transport. The construction is the
Hom-sheaf part of change of band; composition and the pseudofunctor structure are not
constructed here.

## References

* Martin Olsson, *Stacks* (lecture notes), Lemma 31.3 and Theorem 31.7.
* J. Giraud, *Cohomologie non abélienne*, Chapitre III, §1.3, for extension of the structure
  group of a torsor.
-/

public noncomputable section

universe v u v' u'

open CategoryTheory Opposite Bicategory MonoidalCategory

namespace CategoryTheory.Pseudofunctor.AbelianBanding

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}} {A B : Sheaf J AddCommGrpCat.{v'}}
  (b : F.AbelianBanding J A) [F.IsGerbe J]

variable (φ : A ⟶ B) (U : C)
  [HasWeakSheafify (J.over U) (Type v')]
  [(J.over U).WEqualsLocallyBijective (Type v')]

/-- The extended Isom torsors for change of band, contravariant in the source and covariant in
the target. The coefficient group is the restriction of `B` to `J.over U`. -/
abbrev changeBandHomFunctor :
    (F.obj (.mk (op U)))ᵒᵖ × F.obj (.mk (op U)) ⥤
      Sheaf.Torsor ((abelianSheafToGrpSheaf (J.over U)).obj
        ((J.overPullback AddCommGrpCat.{v'} U).obj B)) :=
  b.sheafHomTorsorFunctor U ⋙ Sheaf.Torsor.mapFunctor
    ((abelianSheafToGrpSheaf (J.over U)).map
      ((J.overPullback AddCommGrpCat.{v'} U).map φ))

variable {U}

/-- The image of an original local isomorphism in the extended Hom torsor. -/
def toChangeBandHom (x y : F.obj (.mk (op U))) :
    F.sheafHom J x y ⟶ ((b.changeBandHomFunctor φ U).obj (op x, y)).sheaf :=
  (b.sheafHomTorsor x y (IsGerbe.exists_covering_iso _ _)).toMap _

/-- A local contracted-product representative `[p, c]` in an extended Hom torsor. -/
def changeBandHomMk {x y : F.obj (.mk (op U))} {T : (Over U)ᵒᵖ}
    (p : (F.presheafHom x y).obj T) (c : B.obj.obj (op T.unop.left)) :
    ((b.changeBandHomFunctor φ U).obj (op x, y)).sheaf.obj.obj T :=
  abelianSheafToGrpSheafObjEquiv ((J.overPullback AddCommGrpCat.{v'} U).obj B) T
    (.ofAdd c) • (b.toChangeBandHom φ x y).hom.app T p

/-- The representative with zero coefficient is the image of the original local isomorphism. -/
@[simp]
lemma changeBandHomMk_zero {x y : F.obj (.mk (op U))} {T : (Over U)ᵒᵖ}
    (p : (F.presheafHom x y).obj T) :
    b.changeBandHomMk φ p 0 = (b.toChangeBandHom φ x y).hom.app T p := by
  unfold changeBandHomMk
  exact (congrArg (· • _) (map_one _)).trans (one_smul _ _)

/-- Addition in the new coefficient is the action of the new band on a representative. -/
lemma changeBandHomMk_add {x y : F.obj (.mk (op U))} {T : (Over U)ᵒᵖ}
    (p : (F.presheafHom x y).obj T) (c d : B.obj.obj (op T.unop.left)) :
    b.changeBandHomMk φ p (c + d) =
      abelianSheafToGrpSheafObjEquiv ((J.overPullback AddCommGrpCat.{v'} U).obj B) T
        (.ofAdd c) • b.changeBandHomMk φ p d := by
  unfold changeBandHomMk
  exact (congrArg (· • (b.toChangeBandHom φ x y).hom.app T p) (map_mul
    (abelianSheafToGrpSheafObjEquiv ((J.overPullback AddCommGrpCat.{v'} U).obj B) T)
      (.ofAdd c) (.ofAdd d))).trans (mul_smul _ _ _)

/-- Restricting a local representative restricts both its local isomorphism and coefficient. -/
lemma changeBandHom_map_mk {x y : F.obj (.mk (op U))} {T T' : (Over U)ᵒᵖ}
    (f : T ⟶ T') (p : (F.presheafHom x y).obj T) (c : B.obj.obj (op T.unop.left)) :
    ((b.changeBandHomFunctor φ U).obj (op x, y)).sheaf.obj.map f
        (b.changeBandHomMk φ p c) =
      b.changeBandHomMk φ ((F.presheafHom x y).map f p) (B.obj.map f.unop.left.op c) := by
  simp only [changeBandHomMk]
  rw [Sheaf.Torsor.map_smul, abelianSheafToGrpSheaf_map_abelianSheafToGrpSheafObjEquiv]
  exact congrArg (_ • ·) (NatTrans.naturality_apply (b.toChangeBandHom φ x y).hom f p).symm

/-- The map from the old Isom sheaf is compatible with the homomorphism of bands. -/
lemma toChangeBandHom_homAct {x y : F.obj (.mk (op U))} {T : (Over U)ᵒᵖ}
    (p : (F.presheafHom x y).obj T) (a : A.obj.obj (op T.unop.left)) :
    (b.toChangeBandHom φ x y).hom.app T (b.homAct p (.ofAdd a)) =
      b.changeBandHomMk φ p (φ.hom.app (op T.unop.left) a) := by
  let P := b.sheafHomTorsor x y (IsGerbe.exists_covering_iso _ _)
  have h := P.toMap_smul
    ((abelianSheafToGrpSheaf (J.over U)).map
      ((J.overPullback AddCommGrpCat.{v'} U).map φ))
    (abelianSheafToGrpSheafObjEquiv ((J.overPullback AddCommGrpCat.{v'} U).obj A) T
      (.ofAdd a)) p
  have hs := (b.sheafHomTorsor_smul (IsGerbe.exists_covering_iso x y)
    (abelianSheafToGrpSheafObjEquiv ((J.overPullback AddCommGrpCat.{v'} U).obj A) T
      (.ofAdd a)) p).trans (congrArg (b.homAct p)
        ((abelianSheafToGrpSheafObjEquiv _ T).symm_apply_apply _))
  have ht := abelianSheafToGrpSheaf_map_hom_app_abelianSheafToGrpSheafObjEquiv
    ((J.overPullback AddCommGrpCat.{v'} U).map φ) T (.ofAdd a)
  exact (congrArg ((b.toChangeBandHom φ x y).hom.app T) hs).symm.trans
    (h.trans (congrArg (· • (b.toChangeBandHom φ x y).hom.app T p) ht))

/-- The relation defining extension of the structure group: acting on `p` adds the image of
the acting coefficient to the new coefficient. -/
lemma changeBandHomMk_homAct {x y : F.obj (.mk (op U))} {T : (Over U)ᵒᵖ}
    (p : (F.presheafHom x y).obj T) (a : A.obj.obj (op T.unop.left))
    (c : B.obj.obj (op T.unop.left)) :
    b.changeBandHomMk φ (b.homAct p (.ofAdd a)) c =
      b.changeBandHomMk φ p (c + φ.hom.app (op T.unop.left) a) := by
  exact (congrArg
    (abelianSheafToGrpSheafObjEquiv ((J.overPullback AddCommGrpCat.{v'} U).obj B) T
      (.ofAdd c) • ·) (b.toChangeBandHom_homAct φ p a)).trans
    (b.changeBandHomMk_add φ p c (φ.hom.app (op T.unop.left) a)).symm

/-- The morphism of sheaves taking `(p, c)` to the representative `[p, c]`. -/
def changeBandHomPairing (x y : F.obj (.mk (op U))) :
    F.sheafHom J x y ⊗ coefficientSheaf J B U ⟶
      ((b.changeBandHomFunctor φ U).obj (op x, y)).sheaf :=
  ObjectProperty.homMk
    { app T := ↾fun p ↦ b.changeBandHomMk φ p.1 p.2
      naturality T T' f := by
        ext p
        exact (b.changeBandHom_map_mk φ f p.1 p.2).symm }

/-- The pairing takes a pair of sections to its contracted-product representative. -/
lemma changeBandHomPairing_hom_app (x y : F.obj (.mk (op U))) (T : (Over U)ᵒᵖ)
    (p : (F.presheafHom x y).obj T) (c : B.obj.obj (op T.unop.left)) :
    (b.changeBandHomPairing φ x y).hom.app T (p, c) = b.changeBandHomMk φ p c := (rfl)

/-- Every section of an extended Hom torsor is locally a representative `[p, c]`. Only local
nonemptiness of the original Isom torsor is used, so no global isomorphism is chosen. -/
instance isLocallySurjective_changeBandHomPairing (x y : F.obj (.mk (op U))) :
    Sheaf.IsLocallySurjective (b.changeBandHomPairing φ x y) := by
  refine ⟨fun {T} q ↦ (J.over U).superset_covering ?_
    ((b.sheafHomTorsor x y (IsGerbe.exists_covering_iso _ _)).coversTop T)⟩
  rintro V f ⟨⟨W, ⟨p⟩⟩, ⟨g⟩⟩
  let p' := (F.sheafHom J x y).obj.map g.op p
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq
    (((abelianSheafToGrpSheaf (J.over U)).obj
      ((J.overPullback AddCommGrpCat.{v'} U).obj B)).obj.obj (op V))
    ((b.toChangeBandHom φ x y).hom.app (op V) p')
    (((b.changeBandHomFunctor φ U).obj (op x, y)).sheaf.obj.map f.op q)
  let E := abelianSheafToGrpSheafObjEquiv ((J.overPullback AddCommGrpCat.{v'} U).obj B) (op V)
  refine ⟨(p', (E.symm a).toAdd), ?_⟩
  exact (congrArg (· • (b.toChangeBandHom φ x y).hom.app (op V) p')
    (E.apply_symm_apply a)).trans ha

/-- Maps of sheaves out of an extended Hom torsor are determined on local representatives. -/
@[ext]
lemma changeBandHom_hom_ext {x y : F.obj (.mk (op U))} {Q : Sheaf (J.over U) (Type v')}
    {f g : ((b.changeBandHomFunctor φ U).obj (op x, y)).sheaf ⟶ Q}
    (h : ∀ (T : (Over U)ᵒᵖ) (p : (F.presheafHom x y).obj T)
      (c : B.obj.obj (op T.unop.left)),
      f.hom.app T (b.changeBandHomMk φ p c) = g.hom.app T (b.changeBandHomMk φ p c)) :
    f = g := by
  apply (cancel_epi (b.changeBandHomPairing φ x y)).1
  ext T p
  exact h T p.1 p.2

/-- The canonical images of the original Isom sheaves commute with transport in the endpoints. -/
@[reassoc]
lemma toChangeBandHom_naturality {p q : (F.obj (.mk (op U)))ᵒᵖ × F.obj (.mk (op U))}
    (f : p ⟶ q) :
    b.toChangeBandHom φ p.1.unop p.2 ≫ ((b.changeBandHomFunctor φ U).map f).hom =
      ((b.sheafHomTorsorFunctor U).map f).hom ≫ b.toChangeBandHom φ q.1.unop q.2 :=
  Sheaf.Torsor.toMap_mapLift _ _

/-- Transport in either endpoint keeps the new coefficient of a representative. -/
lemma changeBandHomFunctor_map_mk {p q : (F.obj (.mk (op U)))ᵒᵖ × F.obj (.mk (op U))}
    (f : p ⟶ q) (T : (Over U)ᵒᵖ) (h : (F.presheafHom p.1.unop p.2).obj T)
    (c : B.obj.obj (op T.unop.left)) :
    ((b.changeBandHomFunctor φ U).map f).hom.hom.app T (b.changeBandHomMk φ h c) =
      b.changeBandHomMk φ ((F.map T.unop.hom.op.toLoc).toFunctor.map f.1.unop ≫ h ≫
        (F.map T.unop.hom.op.toLoc).toFunctor.map f.2) c := by
  exact Sheaf.Torsor.mapFunctor_map_hom_app_smul_toMap _ _ _ _ _

variable (U)

/-- Change of band along the identity recovers the original Isom torsors, naturally in both
endpoints and equivariantly for their actions. -/
def changeBandHomIdIso : b.changeBandHomFunctor (𝟙 A) U ≅ b.sheafHomTorsorFunctor U := by
  exact Functor.isoWhiskerLeft (b.sheafHomTorsorFunctor U)
    (Sheaf.Torsor.mapIdIso (by simp)) ≪≫
    Functor.rightUnitor (b.sheafHomTorsorFunctor U)

variable {U}

/-- The identity-band comparison is inverse to the map from the original Isom sheaf. -/
@[reassoc (attr := simp)]
lemma toChangeBandHom_changeBandHomIdIso_hom (x y : F.obj (.mk (op U))) :
    b.toChangeBandHom (𝟙 A) x y ≫ ((b.changeBandHomIdIso U).hom.app (op x, y)).hom =
      𝟙 (F.sheafHom J x y) := by
  dsimp only [changeBandHomIdIso]
  exact Sheaf.Torsor.toMap_mapIdIso_hom (by simp) _

/-- On local representatives the identity-band comparison is the original band action. -/
lemma changeBandHomIdIso_hom_app_mk {x y : F.obj (.mk (op U))} (T : (Over U)ᵒᵖ)
    (p : (F.presheafHom x y).obj T) (a : A.obj.obj (op T.unop.left)) :
    ((b.changeBandHomIdIso U).hom.app (op x, y)).hom.hom.app T
        (b.changeBandHomMk (𝟙 A) p a) = b.homAct p (.ofAdd a) := by
  let E := abelianSheafToGrpSheafObjEquiv ((J.overPullback AddCommGrpCat.{v'} U).obj A) T
  have h := congrArg (fun k ↦ k.hom.app T p)
    (b.toChangeBandHom_changeBandHomIdIso_hom x y)
  exact (((b.changeBandHomIdIso U).hom.app (op x, y)).map_smul T (E (.ofAdd a)) _).trans
    ((congrArg (E (.ofAdd a) • ·) h).trans
      ((b.sheafHomTorsor_smul (IsGerbe.exists_covering_iso x y) (E (.ofAdd a)) p).trans
        (congrArg (b.homAct p) (E.symm_apply_apply _))))

end CategoryTheory.Pseudofunctor.AbelianBanding
