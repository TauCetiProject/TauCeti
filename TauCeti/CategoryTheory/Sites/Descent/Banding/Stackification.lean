/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Aut.Conjugation
public import TauCeti.CategoryTheory.Endomorphism
public import TauCeti.CategoryTheory.Sites.Descent.Banding
public import TauCeti.CategoryTheory.Sites.Descent.Stackification.IsStack
public import TauCeti.CategoryTheory.Sites.Descent.Stackification.Universal

/-!
# Descent of an abelian banding

A strong transformation with fully faithful components, locally essentially surjective into a
prestack, transports an abelian banding to its target. In particular an abelian banding extends
to the stackification of a prestack. This supplies the band in the construction of change of
band in Olsson, *Stacks*, Theorem 31.7.

On the local-image sieve of an object, full faithfulness and conjugation identify each local
automorphism group with the coefficients. These identifications are independent of the lifts.
Their automorphisms descend through the fully faithful prestack descent functor; conversely,
the coefficients of any automorphism glue in the coefficient sheaf. No gerbe, groupoid or
effective object descent assumption is used.

* `AbelianBanding.descend` constructs the transported band, with its formula on any object
  isomorphic to an image and `existsUnique_bandPreserving`.
* `BandPreserving.of_comp` checks preservation after precomposition with a locally essentially
  surjective band-preserving transformation. Automorphism separatedness follows from the band,
  so this assertion needs no prestack assumption.
* `AbelianBanding.stackification` specializes the construction to the stackification unit;
  `bandPreserving_stackification_iff` checks preservation after composition with that unit.

## References

* [Martin Olsson, *Stacks* (lecture notes, notes by A. Geraschenko et al.)](https://stacky.net/files/written/Stacks/Stacks.pdf),
  Definition 31.1 and Theorem 31.7
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
  (hη : ∀ U : C, (η.app (.mk (op U))).toFunctor.FullyFaithful)

private def chart {U : C} {z : G.obj (.mk (op U))} (x : F.obj (.mk (op U)))
    (e : (η.app (.mk (op U))).toFunctor.obj x ≅ z) :
    Multiplicative (A.obj.obj (op U)) ≃* Aut z :=
  ((b.mulEquiv U x).trans ((hη U).autMulEquivOfFullyFaithful x)).trans
    (Aut.autMulEquivOfIso e)

private lemma chart_hom {U : C} {z : G.obj (.mk (op U))} (x : F.obj (.mk (op U)))
    (e : (η.app (.mk (op U))).toFunctor.obj x ≅ z)
    (a : Multiplicative (A.obj.obj (op U))) :
    (chart b η hη x e a).asIso.hom =
      e.inv ≫ (η.app (.mk (op U))).toFunctor.map (b.mulEquiv U x a).asIso.hom ≫ e.hom := by
  rfl

private lemma chart_eq {U : C} {z : G.obj (.mk (op U))}
    (x x' : F.obj (.mk (op U)))
    (e : (η.app (.mk (op U))).toFunctor.obj x ≅ z)
    (e' : (η.app (.mk (op U))).toFunctor.obj x' ≅ z) :
    chart b η hη x e = chart b η hη x' e' := by
  let d := (hη U).preimageIso (e ≪≫ e'.symm)
  -- Comparing the two conjugates cancels the chart maps.
  apply MulEquiv.ext
  intro a
  apply Aut.ext
  apply Iso.ext
  rw [chart_hom, chart_hom]
  have ha := congrArg ((η.app (.mk (op U))).toFunctor.map)
    (b.mulEquiv_hom_comp d a)
  simp only [Functor.map_comp] at ha
  rw [Functor.FullyFaithful.preimageIso_hom, (hη U).map_preimage] at ha
  simp only [Iso.trans_hom, Iso.symm_hom] at ha
  rw [← cancel_epi e.hom, ← cancel_mono e'.inv]
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id] using ha

private def localBand {U : C} {z : G.obj (.mk (op U))}
    (hz : (η.app (.mk (op U))).toFunctor.essImage z) :
    Multiplicative (A.obj.obj (op U)) ≃* Aut z :=
  chart b η hη hz.witness hz.getIso

private lemma localBand_eq {U : C} {z : G.obj (.mk (op U))}
    (hz : (η.app (.mk (op U))).toFunctor.essImage z) (x : F.obj (.mk (op U)))
    (e : (η.app (.mk (op U))).toFunctor.obj x ≅ z) :
    localBand b η hη hz = chart b η hη x e :=
  chart_eq b η hη _ _ _ _

private lemma conjugate_localBand {U : C} {z z' : G.obj (.mk (op U))}
    (hz : (η.app (.mk (op U))).toFunctor.essImage z)
    (hz' : (η.app (.mk (op U))).toFunctor.essImage z') (e : z ≅ z')
    (a : Multiplicative (A.obj.obj (op U))) :
    Aut.autMulEquivOfIso e (localBand b η hη hz a) = localBand b η hη hz' a := by
  rw [localBand_eq b η hη hz' hz.witness (hz.getIso ≪≫ e)]
  simp only [localBand, chart, MulEquiv.trans_apply, Aut.autMulEquivOfIso_trans]

private lemma map_localBand {U V : C} {z : G.obj (.mk (op U))}
    (hz : (η.app (.mk (op U))).toFunctor.essImage z) (g : V ⟶ U)
    (a : Multiplicative (A.obj.obj (op U))) :
    (G.map g.op.toLoc).toFunctor.mapAut z (localBand b η hη hz a) =
      localBand b η hη (StrongTrans.map_obj_mem_essImage η g.op.toLoc hz)
        (.ofAdd (A.obj.map g.op a.toAdd)) := by
  rw [localBand_eq b η hη _ ((F.map g.op.toLoc).toFunctor.obj hz.witness)
    (η.naturalityObjIso g.op.toLoc hz.witness ≪≫ (G.map g.op.toLoc).toFunctor.mapIso hz.getIso)]
  apply Aut.ext
  apply Iso.ext
  rw [Functor.mapAut_apply_asIso, Functor.mapIso_hom, chart_hom]
  simp only [localBand, chart_hom, Functor.map_comp, Iso.trans_inv, Iso.trans_hom,
    Functor.mapIso_inv, Functor.mapIso_hom, Category.assoc]
  rw [← b.map_mulEquiv_hom, StrongTrans.naturalityObjIso_inv, StrongTrans.naturalityObjIso_hom]
  simpa only [Category.assoc] using congrArg
    (fun t ↦ (G.map g.op.toLoc).toFunctor.map hz.getIso.inv ≫ t ≫
      (G.map g.op.toLoc).toFunctor.map hz.getIso.hom)
    (StrongTrans.naturality_naturality_1 η g.op.toLoc (b.mulEquiv U hz.witness a).asIso.hom).symm

/-- An abelian banding is determined by its pullback along a locally essentially
surjective strong transformation. -/
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

private lemma localBand_hom_comp {U : C} {z z' : G.obj (.mk (op U))}
    (hz : (η.app (.mk (op U))).toFunctor.essImage z)
    (hz' : (η.app (.mk (op U))).toFunctor.essImage z') (e : z ≅ z')
    (a : Multiplicative (A.obj.obj (op U))) :
    (localBand b η hη hz a).asIso.hom ≫ e.hom =
      e.hom ≫ (localBand b η hη hz' a).asIso.hom := by
  have h := congrArg (fun c ↦ c.asIso.hom) (conjugate_localBand b η hη hz hz' e a)
  simpa only [Aut.autMulEquivOfIso_apply_asIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_assoc] using congrArg (e.hom ≫ ·) h

private def bandDescentIso {U : C} (z : G.obj (.mk (op U)))
    (a : Multiplicative (A.obj.obj (op U))) :
    (G.toDescentData fun i : (η.localImageSieve z).arrows.category ↦ i.obj.hom).obj z ≅
      (G.toDescentData fun i : (η.localImageSieve z).arrows.category ↦ i.obj.hom).obj z :=
  DescentData.isoMk
    (fun i ↦ (localBand b η hη ((η.mem_localImageSieve_iff z i.obj.hom).1 i.property)
      (.ofAdd (A.obj.map i.obj.hom.op a.toAdd))).asIso)
    (fun Y q i j f₁ f₂ hf₁ hf₂ ↦ by
      let hi : (η.app (.mk (op i.obj.left))).toFunctor.essImage
          ((G.map i.obj.hom.op.toLoc).toFunctor.obj z) :=
        (η.mem_localImageSieve_iff z i.obj.hom).1 i.property
      let hj : (η.app (.mk (op j.obj.left))).toFunctor.essImage
          ((G.map j.obj.hom.op.toLoc).toFunctor.obj z) :=
        (η.mem_localImageSieve_iff z j.obj.hom).1 j.property
      have h₁ := map_localBand b η hη hi f₁ (.ofAdd (A.obj.map i.obj.hom.op a.toAdd))
      have h₂ := map_localBand b η hη hj f₂ (.ofAdd (A.obj.map j.obj.hom.op a.toAdd))
      have ha₁ : A.obj.map f₁.op (A.obj.map i.obj.hom.op a.toAdd) = A.obj.map q.op a.toAdd := by
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hf₁]
      have ha₂ : A.obj.map f₂.op (A.obj.map j.obj.hom.op a.toAdd) = A.obj.map q.op a.toAdd := by
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hf₂]
      have h := localBand_hom_comp b η hη
        (StrongTrans.map_obj_mem_essImage η f₁.op.toLoc hi)
        (StrongTrans.map_obj_mem_essImage η f₂.op.toLoc hj)
        (((G.toDescentData fun i : (η.localImageSieve z).arrows.category ↦ i.obj.hom).obj z).iso
          q f₁ f₂ hf₁ hf₂) (.ofAdd (A.obj.map q.op a.toAdd))
      simp only [toAdd_ofAdd, ha₁] at h₁
      simp only [toAdd_ofAdd, ha₂] at h₂
      have h₁' := congrArg (fun c ↦ c.asIso.hom) h₁
      have h₂' := congrArg (fun c ↦ c.asIso.hom) h₂
      simp only [Functor.mapAut_apply_asIso, Functor.mapIso_hom] at h₁' h₂'
      exact (congrArg (· ≫ _) h₁').trans (h.trans (congrArg (_ ≫ ·) h₂'.symm)))

variable [G.IsPrestack J] [η.IsLocallyEssSurj J]

private def bandAut {U : C} (z : G.obj (.mk (op U)))
    (a : Multiplicative (A.obj.obj (op U))) : Aut z :=
  .of ((G.isPrestackFor' (η.localImageSieve z)
    (η.localImageSieve_mem J z)).fullyFaithful.preimageIso
    (bandDescentIso b η hη z a))

private lemma map_bandAut {U V : C} (z : G.obj (.mk (op U)))
    (a : Multiplicative (A.obj.obj (op U))) (g : V ⟶ U) (hg : η.localImageSieve z g) :
    (G.map g.op.toLoc).toFunctor.mapAut z (bandAut b η hη z a) =
      localBand b η hη ((η.mem_localImageSieve_iff z g).1 hg)
        (.ofAdd (A.obj.map g.op a.toAdd)) := by
  apply Aut.ext
  apply Iso.ext
  exact congrArg (fun t ↦ DescentData.Hom.hom t ⟨Over.mk g, hg⟩)
    ((G.isPrestackFor' (η.localImageSieve z) (η.localImageSieve_mem J z)).fullyFaithful.map_preimage
      (bandDescentIso b η hη z a).hom)

private lemma bandAut_eq_localBand {U : C} {z : G.obj (.mk (op U))}
    (hz : (η.app (.mk (op U))).toFunctor.essImage z)
    (a : Multiplicative (A.obj.obj (op U))) :
    bandAut b η hη z a = localBand b η hη hz a := by
  apply Aut.ext
  apply Iso.ext
  refine IsPrestack.hom_ext (η.localImageSieve_mem J z) fun V g hg ↦ ?_
  exact congrArg (fun c ↦ c.asIso.hom)
    ((map_bandAut b η hη z a g hg).trans (map_localBand b η hη hz g a).symm)

private lemma bandAut_hom_comp {U : C} {z z' : G.obj (.mk (op U))} (e : z ≅ z')
    (a : Multiplicative (A.obj.obj (op U))) :
    (bandAut b η hη z a).asIso.hom ≫ e.hom = e.hom ≫ (bandAut b η hη z' a).asIso.hom := by
  refine IsPrestack.hom_ext
    (J.intersection_covering (η.localImageSieve_mem J z) (η.localImageSieve_mem J z'))
    fun V g ⟨hg, hg'⟩ ↦ ?_
  have h := localBand_hom_comp b η hη ((η.mem_localImageSieve_iff z g).1 hg)
    ((η.mem_localImageSieve_iff z' g).1 hg') ((G.map g.op.toLoc).toFunctor.mapIso e)
    (.ofAdd (A.obj.map g.op a.toAdd))
  have h₁ := congrArg (fun c ↦ c.asIso.hom) (map_bandAut b η hη z a g hg)
  have h₂ := congrArg (fun c ↦ c.asIso.hom) (map_bandAut b η hη z' a g hg')
  simp only [Functor.mapAut_apply_asIso, Functor.mapIso_hom] at h₁ h₂
  simp only [Functor.map_comp]
  exact (congrArg (· ≫ _) h₁).trans (h.trans (congrArg (_ ≫ ·) h₂.symm))

private def bandHom {U : C} (z : G.obj (.mk (op U))) :
    Multiplicative (A.obj.obj (op U)) →* Aut z where
  toFun := bandAut b η hη z
  map_one' := by
    apply Aut.ext
    apply Iso.ext
    refine IsPrestack.hom_ext (η.localImageSieve_mem J z) fun V g hg ↦ ?_
    have h := map_bandAut b η hη z 1 g hg
    simpa using congrArg (fun c ↦ c.asIso.hom) h
  map_mul' a a' := by
    apply Aut.ext
    apply Iso.ext
    refine IsPrestack.hom_ext (η.localImageSieve_mem J z) fun V g hg ↦ ?_
    have h := map_bandAut b η hη z (a * a') g hg
    have hm : Multiplicative.ofAdd (A.obj.map g.op (a * a').toAdd) =
        Multiplicative.ofAdd (A.obj.map g.op a.toAdd) *
          Multiplicative.ofAdd (A.obj.map g.op a'.toAdd) := by
      simp only [toAdd_mul, map_add, ofAdd_add]
    rw [hm, map_mul] at h
    have h' := ((G.map g.op.toLoc).toFunctor.mapAut z).map_mul
      (bandAut b η hη z a) (bandAut b η hη z a')
    rw [map_bandAut b η hη z a g hg, map_bandAut b η hη z a' g hg] at h'
    exact congrArg (fun c ↦ c.asIso.hom) (h.trans h'.symm)

private lemma bandAut_injective {U : C} (z : G.obj (.mk (op U))) :
    Function.Injective (bandAut b η hη z) := by
  intro a a' h
  have hA := (A.isSheaf_obj_comp (forget AddCommGrpCat)).isSeparated
    (η.localImageSieve z) (η.localImageSieve_mem J z)
  apply Multiplicative.toAdd.injective
  refine hA.ext fun V g hg ↦ ?_
  have h' := congrArg ((G.map g.op.toLoc).toFunctor.mapAut z) h
  rw [map_bandAut b η hη z a g hg, map_bandAut b η hη z a' g hg] at h'
  exact congrArg Multiplicative.toAdd ((localBand b η hη _).injective h')

omit [G.IsPrestack J] [η.IsLocallyEssSurj J] in
private lemma localBand_comp {U V W : C} (z : G.obj (.mk (op U)))
    (f : V ⟶ U) (g : W ⟶ V) (hf : η.localImageSieve z f)
    (hgf : η.localImageSieve z (g ≫ f)) (a : Multiplicative (A.obj.obj (op V))) :
    Aut.autMulEquivOfIso (G.compIso f.op g.op (g ≫ f).op op_comp.symm z)
        (localBand b η hη ((η.mem_localImageSieve_iff z (g ≫ f)).1 hgf)
          (.ofAdd (A.obj.map g.op a.toAdd))) =
      (G.map g.op.toLoc).toFunctor.mapAut _
        (localBand b η hη ((η.mem_localImageSieve_iff z f).1 hf) a) :=
  (conjugate_localBand b η hη _
    (StrongTrans.map_obj_mem_essImage η g.op.toLoc ((η.mem_localImageSieve_iff z f).1 hf))
    _ _).trans (map_localBand b η hη ((η.mem_localImageSieve_iff z f).1 hf) g a).symm

private def coefficient {U : C} (z : G.obj (.mk (op U))) (t : Aut z) :
    Presieve.FamilyOfElements (A.obj ⋙ forget AddCommGrpCat) (η.localImageSieve z).arrows :=
  fun _ f hf ↦ ((localBand b η hη ((η.mem_localImageSieve_iff z f).1 hf)).symm
    ((G.map f.op.toLoc).toFunctor.mapAut z t)).toAdd

omit [G.IsPrestack J] [η.IsLocallyEssSurj J] in
private lemma coefficient_compatible {U : C} (z : G.obj (.mk (op U))) (t : Aut z) :
    (coefficient b η hη z t).Compatible := by
  rw [Presieve.compatible_iff_sieveCompatible]
  intro V W f g hf
  apply Multiplicative.ofAdd.injective
  apply (localBand b η hη ((η.mem_localImageSieve_iff z (g ≫ f)).1
    ((η.localImageSieve z).downward_closed hf g))).injective
  apply (Aut.autMulEquivOfIso (G.compIso f.op g.op (g ≫ f).op op_comp.symm z)).injective
  rw [coefficient, coefficient, ofAdd_toAdd, MulEquiv.apply_symm_apply]
  have hc := localBand_comp b η hη z f g hf ((η.localImageSieve z).downward_closed hf g)
    ((localBand b η hη ((η.mem_localImageSieve_iff z f).1 hf)).symm
      ((G.map f.op.toLoc).toFunctor.mapAut z t))
  rw [MulEquiv.apply_symm_apply] at hc
  have h := Functor.mapAut_eq_autMulEquivOfIso_app
    (Cat.Hom.toNatIso (G.mapComp' f.op.toLoc g.op.toLoc (g ≫ f).op.toLoc
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp]))) z t
  simp only [Cat.Hom.comp_toFunctor, Functor.comp_mapAut] at h
  exact h.symm.trans hc.symm

private lemma bandAut_surjective {U : C} (z : G.obj (.mk (op U))) :
    Function.Surjective (bandAut b η hη z) := by
  intro t
  let s := coefficient b η hη z t
  have hs := coefficient_compatible b η hη z t
  have hA := A.isSheaf_obj_comp (forget AddCommGrpCat)
    (η.localImageSieve z) (η.localImageSieve_mem J z)
  refine ⟨.ofAdd (hA.amalgamate s hs), Aut.ext (Iso.ext ?_)⟩
  refine IsPrestack.hom_ext (η.localImageSieve_mem J z) fun V g hg ↦ ?_
  have h := map_bandAut b η hη z (.ofAdd (hA.amalgamate s hs)) g hg
  have hgA : A.obj.map g.op (hA.amalgamate s hs) = s g hg := hA.valid_glue hs g hg
  rw [toAdd_ofAdd, hgA] at h
  simpa only [s, coefficient, ofAdd_toAdd, MulEquiv.apply_symm_apply,
    Functor.mapAut_apply_asIso, Functor.mapIso_hom] using
    congrArg (fun c ↦ c.asIso.hom) h

private lemma mapAut_bandAut {U V : C} (f : V ⟶ U) (z : G.obj (.mk (op U)))
    (a : Multiplicative (A.obj.obj (op U))) :
    (G.map f.op.toLoc).toFunctor.mapAut z (bandAut b η hη z a) =
      bandAut b η hη ((G.map f.op.toLoc).toFunctor.obj z)
        (.ofAdd (A.obj.map f.op a.toAdd)) := by
  apply Aut.ext
  apply Iso.ext
  refine IsPrestack.hom_ext (J.pullback_stable f (η.localImageSieve_mem J z)) fun W g hg ↦ ?_
  let c := G.compIso f.op g.op (g ≫ f).op op_comp.symm z
  have hgf : η.localImageSieve z (g ≫ f) := hg
  have he : (η.app (.mk (op W))).toFunctor.essImage
      ((G.map g.op.toLoc).toFunctor.obj ((G.map f.op.toLoc).toFunctor.obj z)) :=
    Functor.essImage.ofIso c ((η.mem_localImageSieve_iff z (g ≫ f)).1 hgf)
  have hg' := (η.mem_localImageSieve_iff ((G.map f.op.toLoc).toFunctor.obj z) g).2 he
  have h₁ := map_bandAut b η hη z a (g ≫ f) hgf
  have h₂ := map_bandAut b η hη ((G.map f.op.toLoc).toFunctor.obj z)
    (.ofAdd (A.obj.map f.op a.toAdd)) g hg'
  have hnat := Functor.mapAut_eq_autMulEquivOfIso_app
    (Cat.Hom.toNatIso (G.mapComp' f.op.toLoc g.op.toLoc (g ≫ f).op.toLoc
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp]))) z (bandAut b η hη z a)
  rw [h₁] at hnat
  have hc := conjugate_localBand b η hη ((η.mem_localImageSieve_iff z (g ≫ f)).1 hgf)
    he c (.ofAdd (A.obj.map (g ≫ f).op a.toAdd))
  have hA : A.obj.map g.op (A.obj.map f.op a.toAdd) = A.obj.map (g ≫ f).op a.toAdd := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  simp only [toAdd_ofAdd, hA] at h₂
  have h := hnat.trans (hc.trans h₂.symm)
  simpa only [Cat.Hom.comp_toFunctor, Functor.comp_mapAut,
    Functor.mapAut_apply_asIso, Functor.mapIso_hom, Functor.comp_map] using
    congrArg (fun t ↦ t.asIso.hom) h

/-- Transport an abelian banding along a fully faithful, locally essentially surjective strong
transformation into a prestack. -/
def descend : G.AbelianBanding J A where
  mulEquiv U z := MulEquiv.ofBijective (bandHom b η hη z)
    ⟨bandAut_injective b η hη z, bandAut_surjective b η hη z⟩
  mapAut_mulEquiv f z a := mapAut_bandAut b η hη f z a
  autMulEquivOfIso_mulEquiv e a := Aut.ext <| Iso.ext <| by
    have h := bandAut_hom_comp b η hη e a
    simpa only [MulEquiv.ofBijective_apply, bandHom, MonoidHom.coe_mk, OneHom.coe_mk,
      Aut.autMulEquivOfIso_apply_asIso, Iso.trans_hom, Iso.symm_hom,
      Category.assoc, Iso.inv_hom_id_assoc] using congrArg (e.inv ≫ ·) h

/-- On an object in the image, the descended band is the image of the original band. -/
@[simp]
theorem descend_mulEquiv_image (U : C) (x : F.obj (.mk (op U)))
    (a : Multiplicative (A.obj.obj (op U))) :
    (b.descend η hη).mulEquiv U ((η.app (.mk (op U))).toFunctor.obj x) a =
      (η.app (.mk (op U))).toFunctor.mapAut x (b.mulEquiv U x a) := by
  have h := (bandAut_eq_localBand b η hη (Functor.obj_mem_essImage _ x) a).trans
    (congrArg (fun t : Multiplicative (A.obj.obj (op U)) ≃* Aut _ ↦ t a)
      (localBand_eq b η hη _ x (Iso.refl _)))
  simp only [chart, MulEquiv.trans_apply, Aut.autMulEquivOfIso_refl, MulEquiv.refl_apply] at h
  exact h

/-- The transformation used to descend a banding preserves that banding. -/
instance bandPreserving_descend : BandPreserving b (b.descend η hη) η where
  mapAut_mulEquiv U x a := (descend_mulEquiv_image b η hη U x a).symm

/-- The descended band can be computed using any presentation as an object in the image. -/
theorem descend_mulEquiv_of_iso {U : C} {z : G.obj (.mk (op U))}
    (x : F.obj (.mk (op U))) (e : (η.app (.mk (op U))).toFunctor.obj x ≅ z)
    (a : Multiplicative (A.obj.obj (op U))) :
    (b.descend η hη).mulEquiv U z a = Aut.autMulEquivOfIso e
      ((η.app (.mk (op U))).toFunctor.mapAut x (b.mulEquiv U x a)) := by
  rw [← (b.descend η hη).autMulEquivOfIso_mulEquiv e a, descend_mulEquiv_image]

include hη in
/-- There is a unique abelian banding on the target for which the given transformation
preserves the band. -/
theorem existsUnique_bandPreserving : ∃! bG : G.AbelianBanding J A, BandPreserving b bG η := by
  refine ⟨b.descend η hη, inferInstance, fun bG hbG ↦ ?_⟩
  let := hbG
  exact eq_of_bandPreserving b η bG (b.descend η hη)

end CategoryTheory.Pseudofunctor.AbelianBanding

namespace CategoryTheory.Pseudofunctor

variable {C : Type u} [Category.{v} C]
  {F G H : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  {J : GrothendieckTopology C} {A : Sheaf J AddCommGrpCat.{w}}
  {bF : F.AbelianBanding J A} {bG : G.AbelianBanding J A} {bH : H.AbelianBanding J A}

open scoped StrongTrans

variable (bG) in
/-- Band preservation can be checked after precomposition with a locally essentially surjective
band-preserving transformation. -/
theorem BandPreserving.of_comp (η : F ⟶ G) (θ : G ⟶ H)
    [η.IsLocallyEssSurj J] [BandPreserving bF bG η]
    [BandPreserving bF bH (η ≫ θ)] : BandPreserving bG bH θ where
  mapAut_mulEquiv U z a := by
    have hlocal (V : C) (y : G.obj (.mk (op V)))
        (hy : (η.app (.mk (op V))).toFunctor.essImage y)
        (c : Multiplicative (A.obj.obj (op V))) :
        (θ.app (.mk (op V))).toFunctor.mapAut y (bG.mulEquiv V y c) =
          bH.mulEquiv V ((θ.app (.mk (op V))).toFunctor.obj y) c := by
      rw [← bG.autMulEquivOfIso_mulEquiv hy.getIso c,
        Functor.mapAut_autMulEquivOfIso,
        ← BandPreserving.mapAut_mulEquiv (bF := bF) (η := η) V hy.witness c]
      have h : (θ.app (.mk (op V))).toFunctor.mapAut _
          ((η.app (.mk (op V))).toFunctor.mapAut hy.witness (bF.mulEquiv V hy.witness c)) =
          bH.mulEquiv V ((θ.app (.mk (op V))).toFunctor.obj
            ((η.app (.mk (op V))).toFunctor.obj hy.witness)) c := by
        apply Aut.ext
        apply Iso.ext
        have hh := BandPreserving.map_mulEquiv_hom (bF := bF) bH (η ≫ θ) V hy.witness c
        simp only [StrongTrans.comp_app, Cat.Hom.comp_toFunctor, Functor.comp_map,
          Functor.comp_obj] at hh
        simp only [Functor.mapAut_apply_asIso, Functor.mapIso_hom]
        exact hh
      rw [h, bH.autMulEquivOfIso_mulEquiv]
    refine bH.aut_ext (η.localImageSieve_mem J z) fun V g hg ↦ ?_
    have h := Functor.mapAut_eq_autMulEquivOfIso_app
      (Cat.Hom.toNatIso (θ.naturality g.op.toLoc)) z (bG.mulEquiv U z a)
    simp only [Cat.Hom.comp_toFunctor, Functor.comp_mapAut, bG.mapAut_mulEquiv] at h
    rw [hlocal V _ ((η.mem_localImageSieve_iff z g).1 hg)] at h
    have h' := h.trans (bH.autMulEquivOfIso_mulEquiv
      ((Cat.Hom.toNatIso (θ.naturality g.op.toLoc)).app z) (.ofAdd (A.obj.map g.op a.toAdd)))
    simpa only [bH.mapAut_mulEquiv, Cat.Hom.comp_toFunctor, Functor.comp_obj] using h'

end CategoryTheory.Pseudofunctor

namespace CategoryTheory.Pseudofunctor.AbelianBanding

universe t

open TauCeti.Stack

variable {C : Type u} [Category.{v} C] [Limits.HasPullbacks C]
  {J : GrothendieckTopology C} {A : Sheaf J AddCommGrpCat.{w}}
  {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{max t v', max (t + 1) u v v' u'}} [F.IsPrestack J]
  (b : F.AbelianBanding J A)

/-- The abelian banding of the stackification induced by a banding of the original prestack.
The fibre universes are the existing size hypotheses of the stackification unit. -/
def stackification :
    (TauCeti.Stack.stackification.{t} J F).AbelianBanding J A :=
  b.descend (toStackification.{t, v', u'} J F)
    (fun U ↦ Stackification.Obj.fullyFaithfulToObjFunctor.{t} J F U)

/-- The unit of stackification preserves the induced band. -/
instance bandPreserving_toStackification :
    BandPreserving b (stackification.{w, v, u, v', u', t} b)
      (toStackification.{t, v', u'} J F) :=
  b.bandPreserving_descend _ _

/-- At the image of an original object, the stackification band is the image of its original
band automorphism. -/
@[simp]
theorem stackification_mulEquiv_image (U : C) (x : F.obj (.mk (op U)))
    (a : Multiplicative (A.obj.obj (op U))) :
    (stackification.{w, v, u, v', u', t} b).mulEquiv U (((toStackification.{t, v', u'} J F).app
      (.mk (op U))).toFunctor.obj x) a =
      ((toStackification.{t, v', u'} J F).app (.mk (op U))).toFunctor.mapAut x
        (b.mulEquiv U x a) :=
  b.descend_mulEquiv_image _ _ U x a

open scoped StrongTrans in
/-- A transformation out of stackification into a banded pseudofunctor preserves the band exactly
when its composite with the unit does. -/
theorem bandPreserving_stackification_iff
    {H : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{max t v', max (t + 1) u v v' u'}}
    (bH : H.AbelianBanding J A)
    (θ : TauCeti.Stack.stackification.{t} J F ⟶ H) :
    BandPreserving (stackification.{w, v, u, v', u', t} b) bH θ ↔
      BandPreserving b bH (toStackification.{t, v', u'} J F ≫ θ) :=
  ⟨fun _ ↦ BandPreserving.comp (stackification.{w, v, u, v', u', t} b) _ θ,
    fun h ↦ by
      let := h
      exact BandPreserving.of_comp (bF := b) (stackification.{w, v, u, v', u', t} b)
        (toStackification.{t, v', u'} J F) θ⟩

end CategoryTheory.Pseudofunctor.AbelianBanding
