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
  refine (congrArg ((b.toChangeBandHom φ x y).hom.app T)
    (b.sheafHomTorsor_smul_ofAdd (IsGerbe.exists_covering_iso x y) a p)).symm.trans ?_
  refine h.trans ?_
  exact congrArg (· • (b.toChangeBandHom φ x y).hom.app T p)
    (abelianSheafToGrpSheaf_map_hom_app_abelianSheafToGrpSheafObjEquiv
      ((J.overPullback AddCommGrpCat.{v'} U).map φ) T (.ofAdd a))

/-- The relation defining extension of the structure group: acting on `p` adds the image of
the acting coefficient to the new coefficient. -/
@[simp]
lemma changeBandHomMk_homAct {x y : F.obj (.mk (op U))} {T : (Over U)ᵒᵖ}
    (p : (F.presheafHom x y).obj T) (a : A.obj.obj (op T.unop.left))
    (c : B.obj.obj (op T.unop.left)) :
    b.changeBandHomMk φ (b.homAct p (.ofAdd a)) c =
      b.changeBandHomMk φ p (c + φ.hom.app (op T.unop.left) a) := by
  rw [b.changeBandHomMk_add, changeBandHomMk, b.toChangeBandHom_homAct]

/-- The morphism of sheaves taking `(p, c)` to the representative `[p, c]`. -/
def changeBandHomPairing (x y : F.obj (.mk (op U))) :
    F.sheafHom J x y ⊗ coefficientSheaf J B U ⟶
      ((b.changeBandHomFunctor φ U).obj (op x, y)).sheaf :=
  let P := b.sheafHomTorsor x y (IsGerbe.exists_covering_iso _ _)
  let ψ := (abelianSheafToGrpSheaf (J.over U)).map
    ((J.overPullback AddCommGrpCat.{v'} U).map φ)
  (F.sheafHom J x y ◁ ObjectProperty.homMk
    { app T := ↾fun c ↦
        abelianSheafToGrpSheafObjEquiv ((J.overPullback AddCommGrpCat.{v'} U).obj B) T
          (.ofAdd c)
      naturality T T' f := by
        ext c
        exact (abelianSheafToGrpSheaf_map_abelianSheafToGrpSheafObjEquiv
          ((J.overPullback AddCommGrpCat.{v'} U).obj B) f (.ofAdd c)).symm }) ≫
    P.toContractedProduct (Sheaf.MulActionSheaf.mulRight ψ) ≫
      (P.contractedProductMulRightIso ψ).hom

/-- The pairing takes a pair of sections to its contracted-product representative. -/
lemma changeBandHomPairing_hom_app (x y : F.obj (.mk (op U))) (T : (Over U)ᵒᵖ)
    (p : (F.presheafHom x y).obj T) (c : B.obj.obj (op T.unop.left)) :
    (b.changeBandHomPairing φ x y).hom.app T (p, c) = b.changeBandHomMk φ p c := by
  let P := b.sheafHomTorsor x y (IsGerbe.exists_covering_iso _ _)
  let ψ := (abelianSheafToGrpSheaf (J.over U)).map
    ((J.overPullback AddCommGrpCat.{v'} U).map φ)
  let a := abelianSheafToGrpSheafObjEquiv ((J.overPullback AddCommGrpCat.{v'} U).obj B) T
    (.ofAdd c)
  refine (congrArg ((P.contractedProductMulRightIso ψ).hom.hom.app T)
    (P.toContractedProduct_hom_app (Sheaf.MulActionSheaf.mulRight ψ) (p, a))).trans ?_
  exact Sheaf.Torsor.contractedProductMulRightIso_hom_hom_app_contractedProductMk
    (φ := ψ) (P := P) p a

/-- Maps of sheaves out of an extended Hom torsor are determined on local representatives. -/
@[ext]
lemma changeBandHom_hom_ext {x y : F.obj (.mk (op U))} {Q : Sheaf (J.over U) (Type v')}
    {f g : ((b.changeBandHomFunctor φ U).obj (op x, y)).sheaf ⟶ Q}
    (h : ∀ (T : (Over U)ᵒᵖ) (p : (F.presheafHom x y).obj T)
      (c : B.obj.obj (op T.unop.left)),
      f.hom.app T (b.changeBandHomMk φ p c) = g.hom.app T (b.changeBandHomMk φ p c)) :
    f = g := by
  let P := b.sheafHomTorsor x y (IsGerbe.exists_covering_iso _ _)
  let ψ := (abelianSheafToGrpSheaf (J.over U)).map
    ((J.overPullback AddCommGrpCat.{v'} U).map φ)
  apply (cancel_epi (P.contractedProductMulRightIso ψ).hom).1
  apply Sheaf.Torsor.contractedProduct_hom_ext
  ext T ⟨p, a⟩
  let E := abelianSheafToGrpSheafObjEquiv ((J.overPullback AddCommGrpCat.{v'} U).obj B) T
  obtain ⟨a, rfl⟩ := E.surjective a
  have hpair := b.changeBandHomPairing_hom_app φ x y T p a.toAdd
  exact (congrArg (f.hom.app T) hpair).trans
    ((h T p a.toAdd).trans (congrArg (g.hom.app T) hpair).symm)

/-- Every section of an extended Hom torsor is locally a representative `[p, c]`. -/
instance isLocallySurjective_changeBandHomPairing (x y : F.obj (.mk (op U))) :
    Sheaf.IsLocallySurjective (b.changeBandHomPairing φ x y) := by
  let P := b.sheafHomTorsor x y (IsGerbe.exists_covering_iso _ _)
  let ψ := (abelianSheafToGrpSheaf (J.over U)).map
    ((J.overPullback AddCommGrpCat.{v'} U).map φ)
  have hq : Sheaf.IsLocallySurjective (P.toContractedProduct (Sheaf.MulActionSheaf.mulRight ψ)) :=
    Sheaf.Torsor.isLocallySurjective_toContractedProduct P _
  have hi : Sheaf.IsLocallySurjective (P.contractedProductMulRightIso ψ).hom :=
    Sheaf.isLocallySurjective_of_iso _
  have hc := Sheaf.isLocallySurjective_comp
    (P.toContractedProduct (Sheaf.MulActionSheaf.mulRight ψ))
    (P.contractedProductMulRightIso ψ).hom
  dsimp only [changeBandHomPairing]
  refine @Sheaf.isLocallySurjective_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?_ hc
  apply Presheaf.isLocallySurjective_of_surjective
  intro T
  rintro ⟨p, a⟩
  let E := abelianSheafToGrpSheafObjEquiv ((J.overPullback AddCommGrpCat.{v'} U).obj B) T
  exact ⟨(p, (E.symm a).toAdd), Prod.ext rfl (E.apply_symm_apply a)⟩

/-- The canonical images of the original Isom sheaves commute with transport in the endpoints. -/
@[reassoc]
lemma toChangeBandHom_naturality {p q : (F.obj (.mk (op U)))ᵒᵖ × F.obj (.mk (op U))}
    (f : p ⟶ q) :
    b.toChangeBandHom φ p.1.unop p.2 ≫ ((b.changeBandHomFunctor φ U).map f).hom =
      ((b.sheafHomTorsorFunctor U).map f).hom ≫ b.toChangeBandHom φ q.1.unop q.2 :=
  Sheaf.Torsor.toMap_mapFunctor_map _ _

/-- Transport in either endpoint keeps the new coefficient of a representative. -/
lemma changeBandHomFunctor_map_mk {p q : (F.obj (.mk (op U)))ᵒᵖ × F.obj (.mk (op U))}
    (f : p ⟶ q) (T : (Over U)ᵒᵖ) (h : (F.presheafHom p.1.unop p.2).obj T)
    (c : B.obj.obj (op T.unop.left)) :
    ((b.changeBandHomFunctor φ U).map f).hom.hom.app T (b.changeBandHomMk φ h c) =
      b.changeBandHomMk φ ((F.map T.unop.hom.op.toLoc).toFunctor.map f.1.unop ≫ h ≫
        (F.map T.unop.hom.op.toLoc).toFunctor.map f.2) c := by
  refine (Sheaf.Torsor.mapFunctor_map_hom_app_smul_toMap
    ((abelianSheafToGrpSheaf (J.over U)).map
      ((J.overPullback AddCommGrpCat.{v'} U).map φ))
    ((b.sheafHomTorsorFunctor U).map f) T h _).trans ?_
  exact congrArg (fun k ↦ b.changeBandHomMk φ k c)
    (b.sheafHomTorsorFunctor_map_hom_app f T h)

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
  refine (Sheaf.Torsor.mapIdIso_hom_app_smul_toMap (by simp)
    (b.sheafHomTorsor x y (IsGerbe.exists_covering_iso _ _)) T p (E (.ofAdd a))).trans ?_
  exact b.sheafHomTorsor_smul_ofAdd (IsGerbe.exists_covering_iso x y) a p

end CategoryTheory.Pseudofunctor.AbelianBanding
