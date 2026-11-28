/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Aut.Conjugation
public import TauCeti.CategoryTheory.Endomorphism
public import TauCeti.CategoryTheory.Sites.Descent.Banding
public import TauCeti.CategoryTheory.Sites.Descent.LocallyEssSurj

/-!
# Bandings and locally essentially surjective transformations

Two target bandings agree when a locally essentially surjective transformation preserves the
same source banding for both. Compatibility with a morphism of bands can likewise be checked
after a locally essentially surjective band-preserving precomposition. These statements use
automorphism separatedness supplied by the banding and need no prestack assumption.
-/

public section

noncomputable section

universe w v u v' u'

open CategoryTheory Opposite Bicategory

namespace CategoryTheory.Pseudofunctor.AbelianBanding

variable {C : Type u} [Category.{v} C]
  {F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  {J : GrothendieckTopology C} {A : Sheaf J AddCommGrpCat.{w}}
  (b : F.AbelianBanding J A) (η : StrongTrans F G)

/-- Two target bandings coincide if a locally essentially surjective strong transformation
preserves the same source banding for both. -/
theorem eq_of_bandPreserving [η.IsLocallyEssSurj J]
    (bG bG' : G.AbelianBanding J A) [BandPreserving b bG η] [BandPreserving b bG' η] :
    bG = bG' := by
  apply AbelianBanding.ext
  intro U z a
  refine bG.aut_ext (η.localImageSieve_mem J z) fun V g hg ↦ ?_
  rw [bG.mapAut_mulEquiv, bG'.mapAut_mulEquiv]
  obtain ⟨x, ⟨e⟩⟩ := (η.mem_localImageSieve_iff z g).1 hg
  have h := (BandPreserving.mapAut_mulEquiv (bF := b) (bG := bG) (η := η) V x
    (.ofAdd (A.obj.map g.op a.toAdd))).symm.trans
    (BandPreserving.mapAut_mulEquiv (bF := b) (bG := bG') (η := η) V x
      (.ofAdd (A.obj.map g.op a.toAdd)))
  have h' := congrArg (Aut.autMulEquivOfIso e) h
  simpa only [AbelianBanding.autMulEquivOfIso_mulEquiv] using h'

end CategoryTheory.Pseudofunctor.AbelianBanding

namespace CategoryTheory.Pseudofunctor

variable {C : Type u} [Category.{v} C]
  {F G H : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  {J : GrothendieckTopology C} {A B : Sheaf J AddCommGrpCat.{w}}
  {bF : F.AbelianBanding J A} {bG : G.AbelianBanding J A} {bH : H.AbelianBanding J B}

open scoped StrongTrans

variable (bG) in
/-- Compatibility with a morphism of bands can be checked after precomposition with a locally
essentially surjective band-preserving transformation. -/
theorem BandCompatible.of_comp (φ : A ⟶ B) (η : F ⟶ G) (θ : G ⟶ H)
    [η.IsLocallyEssSurj J] [BandPreserving bF bG η]
    [BandCompatible φ bF bH (η ≫ θ)] : BandCompatible φ bG bH θ where
  mapAut_mulEquiv U z a := by
    have hlocal (V : C) (y : G.obj (.mk (op V)))
        (hy : (η.app (.mk (op V))).toFunctor.essImage y)
        (c : Multiplicative (A.obj.obj (op V))) :
        (θ.app (.mk (op V))).toFunctor.mapAut y (bG.mulEquiv V y c) =
          bH.mulEquiv V ((θ.app (.mk (op V))).toFunctor.obj y)
            (.ofAdd (φ.hom.app (op V) c.toAdd)) := by
      rw [← bG.autMulEquivOfIso_mulEquiv hy.getIso c,
        Functor.mapAut_autMulEquivOfIso,
        ← BandPreserving.mapAut_mulEquiv (bF := bF) (η := η) V hy.witness c]
      have h : (θ.app (.mk (op V))).toFunctor.mapAut _
          ((η.app (.mk (op V))).toFunctor.mapAut hy.witness (bF.mulEquiv V hy.witness c)) =
          bH.mulEquiv V ((θ.app (.mk (op V))).toFunctor.obj
            ((η.app (.mk (op V))).toFunctor.obj hy.witness))
            (.ofAdd (φ.hom.app (op V) c.toAdd)) := by
        exact (Functor.comp_mapAut _ _ _ _).symm.trans
          (BandCompatible.mapAut_mulEquiv (bF := bF) (bG := bH) (φ := φ) (η := η ≫ θ)
            V hy.witness c)
      rw [h, bH.autMulEquivOfIso_mulEquiv]
    refine bH.aut_ext (η.localImageSieve_mem J z) fun V g hg ↦ ?_
    have h := Functor.mapAut_eq_autMulEquivOfIso_app
      (Cat.Hom.toNatIso (θ.naturality g.op.toLoc)) z (bG.mulEquiv U z a)
    simp only [Cat.Hom.comp_toFunctor, Functor.comp_mapAut, bG.mapAut_mulEquiv] at h
    rw [hlocal V _ ((η.mem_localImageSieve_iff z g).1 hg)] at h
    have h' := h.trans (bH.autMulEquivOfIso_mulEquiv
      ((Cat.Hom.toNatIso (θ.naturality g.op.toLoc)).app z)
      (.ofAdd (φ.hom.app (op V) (A.obj.map g.op a.toAdd))))
    have hφ : φ.hom.app (op V) (A.obj.map g.op a.toAdd) =
        B.obj.map g.op (φ.hom.app (op U) a.toAdd) :=
      ConcreteCategory.congr_hom (φ.hom.naturality g.op) a.toAdd
    simpa only [bH.mapAut_mulEquiv, Cat.Hom.comp_toFunctor, Functor.comp_obj,
      toAdd_ofAdd, hφ] using h'

variable (bG) in
/-- Band preservation can be checked after precomposition with a locally essentially surjective
band-preserving transformation. -/
theorem BandPreserving.of_comp {bH : H.AbelianBanding J A} (η : F ⟶ G) (θ : G ⟶ H)
    [η.IsLocallyEssSurj J] [BandPreserving bF bG η]
    [BandPreserving bF bH (η ≫ θ)] : BandPreserving bG bH θ :=
  (bandCompatible_id_iff θ).1 (BandCompatible.of_comp (bF := bF) bG (𝟙 A) η θ)

end CategoryTheory.Pseudofunctor

