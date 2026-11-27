/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.IsGerbe
public import TauCeti.CategoryTheory.Sites.Descent.IsomTorsor.Sheaf
public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.ContractedProduct

/-!
# Composition after extension of an abelian band

For an abelian banding and a homomorphism of coefficient sheaves, composition of local
isomorphisms descends to their extended torsors on a fixed slice site. Locally the formula is
`([p, a], [q, c]) ↦ [p ≫ q, a * c]`, with the multiplicative notation for additive coefficients.

The construction uses the existing isomorphism torsors and extension of structure group.
Composition, identity and inversion are morphisms of sheaves; their laws hold on every object
of the slice. Evaluation at its terminal object gives `ChangeBandFiber`, a groupoid with the
positive coefficient action and the comparison functor `toChangeBandFiber`.

The object and arrow universes of the site and the fibres remain independent. In particular
the construction admits site objects in `Type (u+1)`, site arrows in `Type u`, and fibres in
`Cat.{u, u+1}`. Sheafification is required in the coefficient universe, as for `Torsor.map`.

## References

* [Martin Olsson, *Stacks*](https://stacky.net/files/written/Stacks/Stacks.pdf),
  Theorem 31.7 (reverse construction).
-/

public noncomputable section

universe v u v' u'

open CategoryTheory Opposite Bicategory MonoidalCategory

namespace CategoryTheory.Pseudofunctor.AbelianBanding

variable {C : Type u} [Category.{v} C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  {J : GrothendieckTopology C} {A B : Sheaf J AddCommGrpCat.{v'}}
  (b : F.AbelianBanding J A) (φ : A ⟶ B) {U : C} [F.IsGerbe J]
  [HasWeakSheafify (J.over U) (Type v')]
  [(J.over U).WEqualsLocallyBijective (Type v')]

private abbrev sourceTorsor (x y : F.obj (.mk (op U))) :=
  b.sheafHomTorsor x y (IsGerbe.exists_covering_iso (J := J) x y)

private abbrev bandMap :=
  (abelianSheafToGrpSheaf (J.over U)).map ((J.overPullback AddCommGrpCat U).map φ)

private abbrev extendedTorsor (x y : F.obj (.mk (op U))) :=
  (b.sourceTorsor x y).map (bandMap (U := U) φ)

private abbrev coefficient (T : (Over U)ᵒᵖ) :=
  ((abelianSheafToGrpSheaf (J.over U)).obj
    ((J.overPullback AddCommGrpCat U).obj B)).obj.obj T

private def chart {x y : F.obj (.mk (op U))} {T : (Over U)ᵒᵖ}
    (p : (F.presheafHom x y).obj T) :
    coefficient (B := B) T ≃ (b.extendedTorsor φ x y).sheaf.obj.obj T :=
  (Sheaf.Torsor.contractedProductObjEquiv (P := b.sourceTorsor x y)
    (X := Sheaf.MulActionSheaf.mulRight (bandMap (U := U) φ)) p).trans
      ((((sheafToPresheaf (J.over U) (Type v')).mapIso
        ((b.sourceTorsor x y).contractedProductMulRightIso (bandMap (U := U) φ))).app T).toEquiv)

private lemma chart_apply {x y : F.obj (.mk (op U))} {T : (Over U)ᵒᵖ}
    (p : (F.presheafHom x y).obj T) (a : coefficient (B := B) T) :
    b.chart φ p a = a • ((b.sourceTorsor x y).toMap (bandMap (U := U) φ)).hom.app T p := by
  unfold chart
  erw [Equiv.trans_apply, Sheaf.Torsor.contractedProductObjEquiv_apply]
  exact Sheaf.Torsor.contractedProductMulRightIso_hom_hom_app_contractedProductMk
    (φ := bandMap φ) (P := b.sourceTorsor x y) p a

private lemma chart_map {x y : F.obj (.mk (op U))} {T T' : (Over U)ᵒᵖ}
    (f : T ⟶ T') (p : (F.presheafHom x y).obj T) (a : coefficient (B := B) T) :
    (b.extendedTorsor φ x y).sheaf.obj.map f (b.chart φ p a) =
      b.chart φ ((F.presheafHom x y).map f p)
        (((abelianSheafToGrpSheaf (J.over U)).obj
          ((J.overPullback AddCommGrpCat U).obj B)).obj.map f a) := by
  simp only [chart_apply, Sheaf.Torsor.map_smul]
  congr 1
  exact (NatTrans.naturality_apply ((b.sourceTorsor x y).toMap (bandMap φ)).hom f p).symm

private lemma chart_action {x y : F.obj (.mk (op U))} {T : (Over U)ᵒᵖ}
    (p : (b.sourceTorsor x y).sheaf.obj.obj T)
    (g : ((abelianSheafToGrpSheaf (J.over U)).obj
      ((J.overPullback AddCommGrpCat U).obj A)).obj.obj T)
    (a : coefficient (B := B) T) :
    b.chart φ (b.homAct p ((abelianSheafToGrpSheafObjEquiv _ T).symm g)) a =
      b.chart φ p (a * (bandMap φ).hom.app T g) := by
  have h := Sheaf.Torsor.toMap_smul (bandMap φ) (b.sourceTorsor x y) g p
  erw [sheafHomTorsor_smul] at h
  erw [chart_apply, chart_apply, h, mul_smul]

omit [HasWeakSheafify (J.over U) (Type v')]
  [(J.over U).WEqualsLocallyBijective (Type v')] in
private lemma smul_comp {x y z : F.obj (.mk (op U))} {T : (Over U)ᵒᵖ}
    (p : (b.sourceTorsor x y).sheaf.obj.obj T)
    (q : (b.sourceTorsor y z).sheaf.obj.obj T)
    (g h : ((abelianSheafToGrpSheaf (J.over U)).obj
      ((J.overPullback AddCommGrpCat U).obj A)).obj.obj T) :
    (g • p) ≫ (h • q) = b.homAct (p ≫ q) ((abelianSheafToGrpSheafObjEquiv _ T).symm (g * h)) := by
  have : IsGroupoid (F.obj (.mk (op T.unop.left))) := IsGerbe.isGroupoid (J := J) _
  let q' : (F.map T.unop.hom.op.toLoc).toFunctor.obj y ⟶
      (F.map T.unop.hom.op.toLoc).toFunctor.obj z := q
  erw [sheafHomTorsor_smul, sheafHomTorsor_smul]
  erw [b.comp_homAct, b.homAct_comp_hom p (asIso q'), ← b.homAct_mul]
  congr 1
  exact (mul_comm _ _).trans (map_mul _ _ _).symm

private def chartComp {x y z : F.obj (.mk (op U))} {T : (Over U)ᵒᵖ}
    (p : (F.presheafHom x y).obj T) (q : (F.presheafHom y z).obj T)
    (s : (b.extendedTorsor φ x y).sheaf.obj.obj T)
    (t : (b.extendedTorsor φ y z).sheaf.obj.obj T) :
    (b.extendedTorsor φ x z).sheaf.obj.obj T :=
  b.chart φ ((presheafHomComp x y z).app T (p, q))
    ((b.chart φ p).symm s * (b.chart φ q).symm t)

private lemma chartComp_chart {x y z : F.obj (.mk (op U))} {T : (Over U)ᵒᵖ}
    (p : (F.presheafHom x y).obj T) (q : (F.presheafHom y z).obj T)
    (a c : coefficient (B := B) T) :
    b.chartComp φ p q (b.chart φ p a) (b.chart φ q c) = b.chart φ (p ≫ q) (a * c) := by
  dsimp only [chartComp]
  erw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, presheafHomComp_app_apply]

private lemma chartComp_change {x y z : F.obj (.mk (op U))} {T : (Over U)ᵒᵖ}
    (p p' : (F.presheafHom x y).obj T) (q q' : (F.presheafHom y z).obj T)
    (s : (b.extendedTorsor φ x y).sheaf.obj.obj T)
    (t : (b.extendedTorsor φ y z).sheaf.obj.obj T) :
    b.chartComp φ p q s t = b.chartComp φ p' q' s t := by
  obtain ⟨a, rfl⟩ := (b.chart φ p').surjective s
  obtain ⟨c, rfl⟩ := (b.chart φ q').surjective t
  obtain ⟨⟨g, p₀⟩, hg⟩ := (b.sourceTorsor x y).bijective T |>.2 (p', p)
  obtain ⟨rfl, rfl⟩ := Prod.ext_iff.1 hg
  obtain ⟨⟨h, q₀⟩, hh⟩ := (b.sourceTorsor y z).bijective T |>.2 (q', q)
  obtain ⟨rfl, rfl⟩ := Prod.ext_iff.1 hh
  dsimp only
  erw [chartComp_chart, smul_comp, chart_action]
  have hp := b.sheafHomTorsor_smul (IsGerbe.exists_covering_iso (J := J) x y) g p₀
  have hq := b.sheafHomTorsor_smul (IsGerbe.exists_covering_iso (J := J) y z) h q₀
  erw [hp, hq, chart_action, chart_action, chartComp_chart]
  congr 1
  erw [map_mul]
  apply (abelianSheafToGrpSheafObjEquiv ((J.overPullback AddCommGrpCat U).obj B) T).symm.injective
  simp only [map_mul]
  exact mul_mul_mul_comm _ _ _ _

private lemma chartComp_map {x y z : F.obj (.mk (op U))} {T T' : (Over U)ᵒᵖ}
    (f : T ⟶ T') (p : (F.presheafHom x y).obj T) (q : (F.presheafHom y z).obj T)
    (s : (b.extendedTorsor φ x y).sheaf.obj.obj T)
    (t : (b.extendedTorsor φ y z).sheaf.obj.obj T) :
    (b.extendedTorsor φ x z).sheaf.obj.map f (b.chartComp φ p q s t) =
      b.chartComp φ ((F.presheafHom x y).map f p) ((F.presheafHom y z).map f q)
        ((b.extendedTorsor φ x y).sheaf.obj.map f s)
        ((b.extendedTorsor φ y z).sheaf.obj.map f t) := by
  obtain ⟨a, rfl⟩ := (b.chart φ p).surjective s
  obtain ⟨c, rfl⟩ := (b.chart φ q).surjective t
  erw [chartComp_chart, chart_map, chart_map, chart_map, chartComp_chart, map_mul]
  congr 2
  exact pullHom_comp p q f.unop.left T'.unop.hom T'.unop.hom T'.unop.hom
    (Over.w f.unop) (Over.w f.unop) (Over.w f.unop)

private def compositionCover (x y z : F.obj (.mk (op U))) (T : Over U) : Sieve T where
  arrows V _ := Nonempty ((F.presheafHom x y).obj (op V)) ∧
    Nonempty ((F.presheafHom y z).obj (op V))
  downward_closed := fun ⟨hp, hq⟩ f ↦
    ⟨hp.map ((F.presheafHom x y).map f.op), hq.map ((F.presheafHom y z).map f.op)⟩

omit [HasWeakSheafify (J.over U) (Type v')]
  [(J.over U).WEqualsLocallyBijective (Type v')] in
private lemma compositionCover_mem (x y z : F.obj (.mk (op U))) (T : Over U) :
    compositionCover (F := F) x y z T ∈ (J.over U) T := by
  apply (J.over U).superset_covering _ ((J.over U).intersection_covering
    ((coversTop_presheafHom (IsGerbe.exists_covering_hom (J := J) x y)) T)
    ((coversTop_presheafHom (IsGerbe.exists_covering_hom (J := J) y z)) T))
  rintro V f ⟨⟨⟨P, ⟨p⟩⟩, ⟨a⟩⟩, ⟨⟨Q, ⟨q⟩⟩, ⟨c⟩⟩⟩
  exact ⟨⟨(F.presheafHom x y).map a.op p⟩, ⟨(F.presheafHom y z).map c.op q⟩⟩

private def compositionFamily {x y z : F.obj (.mk (op U))} {T : (Over U)ᵒᵖ}
    (s : (b.extendedTorsor φ x y).sheaf.obj.obj T)
    (t : (b.extendedTorsor φ y z).sheaf.obj.obj T) :
    Presieve.FamilyOfElements (b.extendedTorsor φ x z).sheaf.obj
      (compositionCover (F := F) x y z T.unop).arrows :=
  fun _ f hf ↦ b.chartComp φ hf.1.some hf.2.some
    ((b.extendedTorsor φ x y).sheaf.obj.map f.op s)
    ((b.extendedTorsor φ y z).sheaf.obj.map f.op t)

private lemma compositionFamily_compatible {x y z : F.obj (.mk (op U))}
    {T : (Over U)ᵒᵖ} (s : (b.extendedTorsor φ x y).sheaf.obj.obj T)
    (t : (b.extendedTorsor φ y z).sheaf.obj.obj T) :
    (b.compositionFamily φ s t).Compatible := by
  rw [Presieve.compatible_iff_sieveCompatible]
  intro V W f g hf
  dsimp only [compositionFamily]
  erw [chartComp_map, ← Functor.map_comp_apply, ← Functor.map_comp_apply]
  exact b.chartComp_change φ _ _ _ _ _ _

private def compSection {x y z : F.obj (.mk (op U))} {T : (Over U)ᵒᵖ}
    (s : (b.extendedTorsor φ x y).sheaf.obj.obj T)
    (t : (b.extendedTorsor φ y z).sheaf.obj.obj T) :
    (b.extendedTorsor φ x z).sheaf.obj.obj T :=
  (((isSheaf_iff_isSheaf_of_type _ _).1 (b.extendedTorsor φ x z).sheaf.property)
    _ (compositionCover_mem (J := J) x y z T.unop)).amalgamate
      (b.compositionFamily φ s t) (b.compositionFamily_compatible φ s t)

private lemma compSection_restrict {x y z : F.obj (.mk (op U))} {T : (Over U)ᵒᵖ}
    (s : (b.extendedTorsor φ x y).sheaf.obj.obj T)
    (t : (b.extendedTorsor φ y z).sheaf.obj.obj T) {V : Over U} (f : V ⟶ T.unop)
    (hf : compositionCover (F := F) x y z T.unop f) :
    (b.extendedTorsor φ x z).sheaf.obj.map f.op (b.compSection φ s t) =
      b.chartComp φ hf.1.some hf.2.some
        ((b.extendedTorsor φ x y).sheaf.obj.map f.op s)
        ((b.extendedTorsor φ y z).sheaf.obj.map f.op t) :=
  Presieve.IsSheafFor.valid_glue _ (b.compositionFamily_compatible φ s t) f hf

private lemma compSection_chart {x y z : F.obj (.mk (op U))} {T : (Over U)ᵒᵖ}
    (p : (F.presheafHom x y).obj T) (q : (F.presheafHom y z).obj T)
    (s : (b.extendedTorsor φ x y).sheaf.obj.obj T)
    (t : (b.extendedTorsor φ y z).sheaf.obj.obj T) :
    b.compSection φ s t = b.chartComp φ p q s t := by
  apply (((isSheaf_iff_isSheaf_of_type _ _).1
    (b.extendedTorsor φ x z).sheaf.property).isSeparated _
      (compositionCover_mem (J := J) x y z T.unop)).ext
  intro V f hf
  erw [compSection_restrict, chartComp_map]
  · exact b.chartComp_change φ _ _ _ _ _ _
  · exact hf

private lemma compSection_map {x y z : F.obj (.mk (op U))} {T T' : (Over U)ᵒᵖ}
    (f : T ⟶ T') (s : (b.extendedTorsor φ x y).sheaf.obj.obj T)
    (t : (b.extendedTorsor φ y z).sheaf.obj.obj T) :
    (b.extendedTorsor φ x z).sheaf.obj.map f (b.compSection φ s t) =
      b.compSection φ ((b.extendedTorsor φ x y).sheaf.obj.map f s)
        ((b.extendedTorsor φ y z).sheaf.obj.map f t) := by
  apply (((isSheaf_iff_isSheaf_of_type _ _).1
    (b.extendedTorsor φ x z).sheaf.property).isSeparated _
      (compositionCover_mem (J := J) x y z T'.unop)).ext
  intro V g hg
  erw [← Functor.map_comp_apply, compSection_restrict, compSection_restrict]
  · congr 1 <;> exact Functor.map_comp_apply _ _ _ _
  · exact hg
  · exact hg

private lemma compSection_mk {x y z : F.obj (.mk (op U))} {T : (Over U)ᵒᵖ}
    (p : (F.presheafHom x y).obj T) (q : (F.presheafHom y z).obj T)
    (a c : coefficient (B := B) T) :
    b.compSection φ (b.chart φ p a) (b.chart φ q c) = b.chart φ (p ≫ q) (a * c) :=
  (b.compSection_chart φ p q _ _).trans (b.chartComp_chart φ p q a c)

private def idSection (x : F.obj (.mk (op U))) (T : (Over U)ᵒᵖ) :
    (b.extendedTorsor φ x x).sheaf.obj.obj T :=
  ((b.sourceTorsor x x).toMap (bandMap φ)).hom.app T (𝟙 _)

private lemma idSection_chart (x : F.obj (.mk (op U))) (T : (Over U)ᵒᵖ) :
    b.idSection φ x T = b.chart φ (𝟙 ((F.map T.unop.hom.op.toLoc).toFunctor.obj x)) 1 := by
  erw [chart_apply, one_smul]
  rfl

private lemma idSection_map (x : F.obj (.mk (op U))) {T T' : (Over U)ᵒᵖ}
    (f : T ⟶ T') :
    (b.extendedTorsor φ x x).sheaf.obj.map f (b.idSection φ x T) = b.idSection φ x T' := by
  unfold idSection
  erw [← NatTrans.naturality_apply]
  congr 1
  exact pullHom_id_self T.unop.hom f.unop.left T'.unop.hom (Over.w f.unop)

private lemma idSection_comp {x y : F.obj (.mk (op U))} {T : (Over U)ᵒᵖ}
    (s : (b.extendedTorsor φ x y).sheaf.obj.obj T) :
    b.compSection φ (b.idSection φ x T) s = s := by
  apply (((isSheaf_iff_isSheaf_of_type _ _).1
    (b.extendedTorsor φ x y).sheaf.property).isSeparated _
      (compositionCover_mem (J := J) x y y T.unop)).ext
  intro V f hf
  erw [compSection_map, idSection_map]
  obtain ⟨a, ha⟩ := (b.chart φ hf.1.some).surjective
    ((b.extendedTorsor φ x y).sheaf.obj.map f.op s)
  erw [← ha, idSection_chart, compSection_mk, Category.id_comp, one_mul]

private lemma compSection_id {x y : F.obj (.mk (op U))} {T : (Over U)ᵒᵖ}
    (s : (b.extendedTorsor φ x y).sheaf.obj.obj T) :
    b.compSection φ s (b.idSection φ y T) = s := by
  apply (((isSheaf_iff_isSheaf_of_type _ _).1
    (b.extendedTorsor φ x y).sheaf.property).isSeparated _
      (compositionCover_mem (J := J) x y y T.unop)).ext
  intro V f hf
  erw [compSection_map, idSection_map]
  obtain ⟨a, ha⟩ := (b.chart φ hf.1.some).surjective
    ((b.extendedTorsor φ x y).sheaf.obj.map f.op s)
  erw [← ha, idSection_chart, compSection_mk, Category.comp_id, mul_one]

private lemma compSection_assoc_charts {w x y z : F.obj (.mk (op U))}
    {T : (Over U)ᵒᵖ} (p : (F.presheafHom w x).obj T)
    (q : (F.presheafHom x y).obj T) (r : (F.presheafHom y z).obj T)
    (a c d : coefficient (B := B) T) :
    b.compSection φ (b.compSection φ (b.chart φ p a) (b.chart φ q c)) (b.chart φ r d) =
      b.compSection φ (b.chart φ p a) (b.compSection φ (b.chart φ q c) (b.chart φ r d)) := by
  calc
    _ = b.compSection φ (b.chart φ (p ≫ q) (a * c)) (b.chart φ r d) :=
      congrArg (fun h ↦ b.compSection φ h (b.chart φ r d)) (b.compSection_mk φ p q a c)
    _ = b.chart φ ((p ≫ q) ≫ r) ((a * c) * d) := b.compSection_mk φ (p ≫ q) r _ _
    _ = b.chart φ (p ≫ q ≫ r) (a * (c * d)) := by rw [Category.assoc, mul_assoc]
    _ = b.compSection φ (b.chart φ p a) (b.chart φ (q ≫ r) (c * d)) :=
      (b.compSection_mk φ p (q ≫ r) _ _).symm
    _ = _ := congrArg (b.compSection φ (b.chart φ p a)) (b.compSection_mk φ q r c d).symm

private lemma compSection_assoc_anchors {w x y z : F.obj (.mk (op U))}
    {T : (Over U)ᵒᵖ} (p : (F.presheafHom w x).obj T)
    (q : (F.presheafHom x y).obj T) (r : (F.presheafHom y z).obj T)
    (s : (b.extendedTorsor φ w x).sheaf.obj.obj T)
    (t : (b.extendedTorsor φ x y).sheaf.obj.obj T)
    (v : (b.extendedTorsor φ y z).sheaf.obj.obj T) :
    b.compSection φ (b.compSection φ s t) v = b.compSection φ s (b.compSection φ t v) := by
  obtain ⟨a, rfl⟩ := (b.chart φ p).surjective s
  obtain ⟨c, rfl⟩ := (b.chart φ q).surjective t
  obtain ⟨d, rfl⟩ := (b.chart φ r).surjective v
  exact b.compSection_assoc_charts φ p q r a c d

private lemma compSection_assoc {w x y z : F.obj (.mk (op U))} {T : (Over U)ᵒᵖ}
    (s : (b.extendedTorsor φ w x).sheaf.obj.obj T)
    (t : (b.extendedTorsor φ x y).sheaf.obj.obj T)
    (r : (b.extendedTorsor φ y z).sheaf.obj.obj T) :
    b.compSection φ (b.compSection φ s t) r = b.compSection φ s (b.compSection φ t r) := by
  apply (((isSheaf_iff_isSheaf_of_type _ _).1
    (b.extendedTorsor φ w z).sheaf.property).isSeparated _
      ((J.over U).intersection_covering
        (compositionCover_mem (J := J) w x y T.unop)
        (compositionCover_mem (J := J) x y z T.unop))).ext
  intro V f hf
  simp only [compSection_map]
  exact b.compSection_assoc_anchors φ hf.1.1.some hf.1.2.some hf.2.2.some _ _ _

private def chartInverse {x y : F.obj (.mk (op U))} {T : (Over U)ᵒᵖ}
    (p : (F.presheafHom x y).obj T) (s : (b.extendedTorsor φ x y).sheaf.obj.obj T) :
    (b.extendedTorsor φ y x).sheaf.obj.obj T :=
  have : IsGroupoid (F.obj (.mk (op T.unop.left))) := IsGerbe.isGroupoid (J := J) _
  let p' : (F.map T.unop.hom.op.toLoc).toFunctor.obj x ⟶
    (F.map T.unop.hom.op.toLoc).toFunctor.obj y := p
  b.chart φ (inv p') ((b.chart φ p).symm s)⁻¹

private lemma chartInverse_right {x y : F.obj (.mk (op U))} {T : (Over U)ᵒᵖ}
    (p : (F.presheafHom x y).obj T) (s : (b.extendedTorsor φ x y).sheaf.obj.obj T) :
    b.compSection φ s (b.chartInverse φ p s) = b.idSection φ x T := by
  have : IsGroupoid (F.obj (.mk (op T.unop.left))) := IsGerbe.isGroupoid (J := J) _
  let p' : (F.map T.unop.hom.op.toLoc).toFunctor.obj x ⟶
    (F.map T.unop.hom.op.toLoc).toFunctor.obj y := p
  obtain ⟨a, rfl⟩ := (b.chart φ p).surjective s
  dsimp only [chartInverse]
  rw [Equiv.symm_apply_apply]
  exact (b.compSection_mk φ p (inv p') a a⁻¹).trans
    ((congrArg₂ (fun p a ↦ b.chart φ p a) (IsIso.hom_inv_id p') (mul_inv_cancel a)).trans
      (b.idSection_chart φ x T).symm)

private lemma chartInverse_left {x y : F.obj (.mk (op U))} {T : (Over U)ᵒᵖ}
    (p : (F.presheafHom x y).obj T) (s : (b.extendedTorsor φ x y).sheaf.obj.obj T) :
    b.compSection φ (b.chartInverse φ p s) s = b.idSection φ y T := by
  have : IsGroupoid (F.obj (.mk (op T.unop.left))) := IsGerbe.isGroupoid (J := J) _
  let p' : (F.map T.unop.hom.op.toLoc).toFunctor.obj x ⟶
    (F.map T.unop.hom.op.toLoc).toFunctor.obj y := p
  obtain ⟨a, rfl⟩ := (b.chart φ p).surjective s
  dsimp only [chartInverse]
  rw [Equiv.symm_apply_apply]
  exact (b.compSection_mk φ (inv p') p a⁻¹ a).trans
    ((congrArg₂ (fun p a ↦ b.chart φ p a) (IsIso.inv_hom_id p') (inv_mul_cancel a)).trans
      (b.idSection_chart φ y T).symm)

private lemma inverse_unique {x y : F.obj (.mk (op U))} {T : (Over U)ᵒᵖ}
    (s : (b.extendedTorsor φ x y).sheaf.obj.obj T)
    (t v : (b.extendedTorsor φ y x).sheaf.obj.obj T)
    (ht : b.compSection φ s t = b.idSection φ x T)
    (hv : b.compSection φ v s = b.idSection φ y T) : t = v := by
  calc
    t = b.compSection φ (b.idSection φ y T) t := (b.idSection_comp φ t).symm
    _ = b.compSection φ (b.compSection φ v s) t := congrArg (b.compSection φ · t) hv.symm
    _ = b.compSection φ v (b.compSection φ s t) := b.compSection_assoc φ v s t
    _ = b.compSection φ v (b.idSection φ x T) := congrArg (b.compSection φ v) ht
    _ = v := b.compSection_id φ v

private lemma chartInverse_map {x y : F.obj (.mk (op U))} {T T' : (Over U)ᵒᵖ}
    (f : T ⟶ T') (p : (F.presheafHom x y).obj T) (p' : (F.presheafHom x y).obj T')
    (s : (b.extendedTorsor φ x y).sheaf.obj.obj T) :
    (b.extendedTorsor φ y x).sheaf.obj.map f (b.chartInverse φ p s) =
      b.chartInverse φ p' ((b.extendedTorsor φ x y).sheaf.obj.map f s) := by
  apply b.inverse_unique φ ((b.extendedTorsor φ x y).sheaf.obj.map f s)
  · erw [← compSection_map, chartInverse_right, idSection_map]
  · exact b.chartInverse_left φ p' _

private def inverseFamily {x y : F.obj (.mk (op U))} {T : (Over U)ᵒᵖ}
    (s : (b.extendedTorsor φ x y).sheaf.obj.obj T) :
    Presieve.FamilyOfElements (b.extendedTorsor φ y x).sheaf.obj
      (compositionCover (F := F) x y x T.unop).arrows :=
  fun _ f hf ↦ b.chartInverse φ hf.1.some
    ((b.extendedTorsor φ x y).sheaf.obj.map f.op s)

private lemma inverseFamily_compatible {x y : F.obj (.mk (op U))} {T : (Over U)ᵒᵖ}
    (s : (b.extendedTorsor φ x y).sheaf.obj.obj T) : (b.inverseFamily φ s).Compatible := by
  rw [Presieve.compatible_iff_sieveCompatible]
  intro V W f g hf
  dsimp only [inverseFamily]
  symm
  simpa only [op_comp, Functor.map_comp_apply] using
    b.chartInverse_map φ g.op hf.1.some
      (((compositionCover (F := F) x y x T.unop).downward_closed hf g).1.some)
      ((b.extendedTorsor φ x y).sheaf.obj.map f.op s)

private def invSection {x y : F.obj (.mk (op U))} {T : (Over U)ᵒᵖ}
    (s : (b.extendedTorsor φ x y).sheaf.obj.obj T) :
    (b.extendedTorsor φ y x).sheaf.obj.obj T :=
  (((isSheaf_iff_isSheaf_of_type _ _).1 (b.extendedTorsor φ y x).sheaf.property)
    _ (compositionCover_mem (J := J) x y x T.unop)).amalgamate
      (b.inverseFamily φ s) (b.inverseFamily_compatible φ s)

private lemma invSection_restrict {x y : F.obj (.mk (op U))} {T : (Over U)ᵒᵖ}
    (s : (b.extendedTorsor φ x y).sheaf.obj.obj T) {V : Over U} (f : V ⟶ T.unop)
    (hf : compositionCover (F := F) x y x T.unop f) :
    (b.extendedTorsor φ y x).sheaf.obj.map f.op (b.invSection φ s) =
      b.chartInverse φ hf.1.some ((b.extendedTorsor φ x y).sheaf.obj.map f.op s) :=
  Presieve.IsSheafFor.valid_glue _ (b.inverseFamily_compatible φ s) f hf

private lemma comp_invSection {x y : F.obj (.mk (op U))} {T : (Over U)ᵒᵖ}
    (s : (b.extendedTorsor φ x y).sheaf.obj.obj T) :
    b.compSection φ s (b.invSection φ s) = b.idSection φ x T := by
  apply (((isSheaf_iff_isSheaf_of_type _ _).1
    (b.extendedTorsor φ x x).sheaf.property).isSeparated _
      (compositionCover_mem (J := J) x y x T.unop)).ext
  intro V f hf
  erw [compSection_map, invSection_restrict _ _ _ _ hf, idSection_map]
  exact b.chartInverse_right φ _ _

private lemma invSection_comp {x y : F.obj (.mk (op U))} {T : (Over U)ᵒᵖ}
    (s : (b.extendedTorsor φ x y).sheaf.obj.obj T) :
    b.compSection φ (b.invSection φ s) s = b.idSection φ y T := by
  apply (((isSheaf_iff_isSheaf_of_type _ _).1
    (b.extendedTorsor φ y y).sheaf.property).isSeparated _
      (compositionCover_mem (J := J) x y x T.unop)).ext
  intro V f hf
  erw [compSection_map, invSection_restrict _ _ _ _ hf, idSection_map]
  exact b.chartInverse_left φ _ _

private lemma invSection_map {x y : F.obj (.mk (op U))} {T T' : (Over U)ᵒᵖ}
    (f : T ⟶ T') (s : (b.extendedTorsor φ x y).sheaf.obj.obj T) :
    (b.extendedTorsor φ y x).sheaf.obj.map f (b.invSection φ s) =
      b.invSection φ ((b.extendedTorsor φ x y).sheaf.obj.map f s) := by
  apply b.inverse_unique φ ((b.extendedTorsor φ x y).sheaf.obj.map f s)
  · erw [← compSection_map, comp_invSection, idSection_map]
  · exact b.invSection_comp φ _

private lemma invSection_mk {x y : F.obj (.mk (op U))} {T : (Over U)ᵒᵖ}
    (p : (F.map T.unop.hom.op.toLoc).toFunctor.obj x ≅
      (F.map T.unop.hom.op.toLoc).toFunctor.obj y) (a : coefficient (B := B) T) :
    b.invSection φ (b.chart φ p.hom a) = b.chart φ p.inv a⁻¹ := by
  apply b.inverse_unique φ (b.chart φ p.hom a)
  · exact b.comp_invSection φ _
  · exact (b.compSection_mk φ p.inv p.hom a⁻¹ a).trans
      ((congrArg₂ (fun p a ↦ b.chart φ p a) p.inv_hom_id (inv_mul_cancel a)).trans
        (b.idSection_chart φ y T).symm)

private lemma chart_mul {x y : F.obj (.mk (op U))} {T : (Over U)ᵒᵖ}
    (p : (F.presheafHom x y).obj T) (a c : coefficient (B := B) T) :
    a • b.chart φ p c = b.chart φ p (a * c) := by
  erw [chart_apply, chart_apply, mul_smul]

private lemma compSection_smul_charts {x y z : F.obj (.mk (op U))} {T : (Over U)ᵒᵖ}
    (p : (F.presheafHom x y).obj T) (q : (F.presheafHom y z).obj T)
    (a c d e : coefficient (B := B) T) :
    b.compSection φ (a • b.chart φ p d) (c • b.chart φ q e) =
      (a * c) • b.compSection φ (b.chart φ p d) (b.chart φ q e) := by
  erw [chart_mul, chart_mul, compSection_mk, compSection_mk, chart_mul]
  apply congrArg (b.chart φ (p ≫ q))
  apply (abelianSheafToGrpSheafObjEquiv ((J.overPullback AddCommGrpCat U).obj B) T).symm.injective
  simp only [map_mul]
  exact mul_mul_mul_comm _ _ _ _

private lemma compSection_smul {x y z : F.obj (.mk (op U))} {T : (Over U)ᵒᵖ}
    (s : (b.extendedTorsor φ x y).sheaf.obj.obj T)
    (t : (b.extendedTorsor φ y z).sheaf.obj.obj T) (a c : coefficient (B := B) T) :
    b.compSection φ (a • s) (c • t) = (a * c) • b.compSection φ s t := by
  apply (((isSheaf_iff_isSheaf_of_type _ _).1
    (b.extendedTorsor φ x z).sheaf.property).isSeparated _
      (compositionCover_mem (J := J) x y z T.unop)).ext
  intro V f hf
  simp only [compSection_map, Sheaf.Torsor.map_smul, map_mul]
  obtain ⟨d, hd⟩ := (b.chart φ hf.1.some).surjective
    ((b.extendedTorsor φ x y).sheaf.obj.map f.op s)
  obtain ⟨e, he⟩ := (b.chart φ hf.2.some).surjective
    ((b.extendedTorsor φ y z).sheaf.obj.map f.op t)
  erw [← hd, ← he]
  exact b.compSection_smul_charts φ _ _ _ _ d e

/-- Composition on the extended isomorphism sheaves on the fixed slice site.
In local trivializations it sends `([p, a], [q, c])` to `[p ≫ q, a * c]`. -/
def changeBandComp (x y z : F.obj (.mk (op U))) :
    let P := fun x y ↦ b.sheafHomTorsor x y (IsGerbe.exists_covering_iso (J := J) x y)
    let ψ := (abelianSheafToGrpSheaf (J.over U)).map
      ((J.overPullback AddCommGrpCat U).map φ)
    (P x y |>.map ψ).sheaf ⊗ (P y z |>.map ψ).sheaf ⟶ (P x z |>.map ψ).sheaf :=
  ObjectProperty.homMk
    { app T := TypeCat.ofHom fun p ↦ b.compSection φ p.1 p.2
      naturality T T' f := by
        ext p
        exact (b.compSection_map φ f p.1 p.2).symm }

/-- The identity section of an extended isomorphism sheaf, represented by `[𝟙, 1]`. -/
def changeBandId (x : F.obj (.mk (op U))) :
    let P := b.sheafHomTorsor x x (IsGerbe.exists_covering_iso (J := J) x x)
    let ψ := (abelianSheafToGrpSheaf (J.over U)).map
      ((J.overPullback AddCommGrpCat U).map φ)
    𝟙_ (Sheaf (J.over U) (Type v')) ⟶ (P.map ψ).sheaf :=
  ObjectProperty.homMk
    { app T := TypeCat.ofHom fun _ ↦ b.idSection φ x T
      naturality T T' f := by
        ext _
        exact (b.idSection_map φ x f).symm }

/-- Inversion on extended isomorphism sheaves, locally `[p, a] ↦ [p⁻¹, a⁻¹]`. -/
def changeBandInv (x y : F.obj (.mk (op U))) :
    let P := fun x y ↦ b.sheafHomTorsor x y (IsGerbe.exists_covering_iso (J := J) x y)
    let ψ := (abelianSheafToGrpSheaf (J.over U)).map
      ((J.overPullback AddCommGrpCat U).map φ)
    (P x y |>.map ψ).sheaf ⟶ (P y x |>.map ψ).sheaf :=
  ObjectProperty.homMk
    { app T := TypeCat.ofHom fun s ↦ b.invSection φ s
      naturality T T' f := by
        ext s
        exact (b.invSection_map φ f s).symm }

/-- The composition formula on local representatives, with multiplicative notation for
coefficients of the abelian sheaf. -/
lemma changeBandComp_toMap {x y z : F.obj (.mk (op U))} (T : (Over U)ᵒᵖ)
    (p : (F.presheafHom x y).obj T) (q : (F.presheafHom y z).obj T)
    (a c : ((abelianSheafToGrpSheaf (J.over U)).obj
      ((J.overPullback AddCommGrpCat U).obj B)).obj.obj T) :
    let P := fun x y ↦ b.sheafHomTorsor x y (IsGerbe.exists_covering_iso (J := J) x y)
    let ψ := (abelianSheafToGrpSheaf (J.over U)).map
      ((J.overPullback AddCommGrpCat U).map φ)
    (b.changeBandComp φ x y z).hom.app T
      (a • (P x y |>.toMap ψ).hom.app T p, c • (P y z |>.toMap ψ).hom.app T q) =
        (a * c) • (P x z |>.toMap ψ).hom.app T (p ≫ q) :=
  (congrArg₂ (b.compSection φ) (b.chart_apply φ p a).symm (b.chart_apply φ q c).symm).trans
    ((b.compSection_mk φ p q a c).trans (b.chart_apply φ (p ≫ q) (a * c)))

/-- The identity is the image of the original identity morphism. -/
lemma changeBandId_app (x : F.obj (.mk (op U))) (T : (Over U)ᵒᵖ) :
    let P := b.sheafHomTorsor x x (IsGerbe.exists_covering_iso (J := J) x x)
    let ψ := (abelianSheafToGrpSheaf (J.over U)).map
      ((J.overPullback AddCommGrpCat U).map φ)
    (b.changeBandId φ x).hom.app T PUnit.unit = (P.toMap ψ).hom.app T (𝟙 _) := (rfl)

/-- The inverse formula on local representatives. -/
@[simp]
lemma changeBandInv_toMap {x y : F.obj (.mk (op U))} (T : (Over U)ᵒᵖ)
    (p : (F.map T.unop.hom.op.toLoc).toFunctor.obj x ≅
      (F.map T.unop.hom.op.toLoc).toFunctor.obj y)
    (a : ((abelianSheafToGrpSheaf (J.over U)).obj
      ((J.overPullback AddCommGrpCat U).obj B)).obj.obj T) :
    let P := fun x y ↦ b.sheafHomTorsor x y (IsGerbe.exists_covering_iso (J := J) x y)
    let ψ := (abelianSheafToGrpSheaf (J.over U)).map
      ((J.overPullback AddCommGrpCat U).map φ)
    (b.changeBandInv φ x y).hom.app T (a • (P x y |>.toMap ψ).hom.app T p.hom) =
      a⁻¹ • (P y x |>.toMap ψ).hom.app T p.inv :=
  (congrArg (b.invSection φ) (b.chart_apply φ p.hom a).symm).trans
    ((b.invSection_mk φ p a).trans (b.chart_apply φ p.inv a⁻¹))

/-- Composition of the extended sheaves is associative on every object of the slice. -/
lemma changeBandComp_assoc (w x y z : F.obj (.mk (op U))) (T : (Over U)ᵒᵖ) :
    let P := fun x y ↦ b.sheafHomTorsor x y (IsGerbe.exists_covering_iso (J := J) x y)
    let ψ := (abelianSheafToGrpSheaf (J.over U)).map
      ((J.overPullback AddCommGrpCat U).map φ)
    ∀ (s : (P w x |>.map ψ).sheaf.obj.obj T) (t : (P x y |>.map ψ).sheaf.obj.obj T)
      (r : (P y z |>.map ψ).sheaf.obj.obj T),
      (b.changeBandComp φ w y z).hom.app T ((b.changeBandComp φ w x y).hom.app T (s, t), r) =
        (b.changeBandComp φ w x z).hom.app T (s, (b.changeBandComp φ x y z).hom.app T (t, r)) := by
  intro P ψ s t r
  exact b.compSection_assoc φ s t r

/-- The identity section is a left identity for composition of extended sheaves. -/
lemma changeBandId_comp (x y : F.obj (.mk (op U))) (T : (Over U)ᵒᵖ) :
    let P := fun x y ↦ b.sheafHomTorsor x y (IsGerbe.exists_covering_iso (J := J) x y)
    let ψ := (abelianSheafToGrpSheaf (J.over U)).map
      ((J.overPullback AddCommGrpCat U).map φ)
    ∀ s : (P x y |>.map ψ).sheaf.obj.obj T,
      (b.changeBandComp φ x x y).hom.app T ((b.changeBandId φ x).hom.app T PUnit.unit, s) = s := by
  intro P ψ s
  exact b.idSection_comp φ s

/-- The identity section is a right identity for composition of extended sheaves. -/
lemma changeBandComp_id (x y : F.obj (.mk (op U))) (T : (Over U)ᵒᵖ) :
    let P := fun x y ↦ b.sheafHomTorsor x y (IsGerbe.exists_covering_iso (J := J) x y)
    let ψ := (abelianSheafToGrpSheaf (J.over U)).map
      ((J.overPullback AddCommGrpCat U).map φ)
    ∀ s : (P x y |>.map ψ).sheaf.obj.obj T,
      (b.changeBandComp φ x y y).hom.app T (s, (b.changeBandId φ y).hom.app T PUnit.unit) = s := by
  intro P ψ s
  exact b.compSection_id φ s

/-- An extended arrow followed by its inverse is the identity section. -/
lemma changeBandComp_inv (x y : F.obj (.mk (op U))) (T : (Over U)ᵒᵖ) :
    let P := fun x y ↦ b.sheafHomTorsor x y (IsGerbe.exists_covering_iso (J := J) x y)
    let ψ := (abelianSheafToGrpSheaf (J.over U)).map
      ((J.overPullback AddCommGrpCat U).map φ)
    ∀ s : (P x y |>.map ψ).sheaf.obj.obj T,
      (b.changeBandComp φ x y x).hom.app T (s, (b.changeBandInv φ x y).hom.app T s) =
        (b.changeBandId φ x).hom.app T PUnit.unit := by
  intro P ψ s
  exact b.comp_invSection φ s

/-- The inverse of an extended arrow followed by that arrow is the identity section. -/
lemma changeBandInv_comp (x y : F.obj (.mk (op U))) (T : (Over U)ᵒᵖ) :
    let P := fun x y ↦ b.sheafHomTorsor x y (IsGerbe.exists_covering_iso (J := J) x y)
    let ψ := (abelianSheafToGrpSheaf (J.over U)).map
      ((J.overPullback AddCommGrpCat U).map φ)
    ∀ s : (P x y |>.map ψ).sheaf.obj.obj T,
      (b.changeBandComp φ y x y).hom.app T ((b.changeBandInv φ x y).hom.app T s, s) =
        (b.changeBandId φ y).hom.app T PUnit.unit := by
  intro P ψ s
  exact b.invSection_comp φ s

/-- Composition adds the two coefficient translations. In particular its action has the
positive sign on both factors. -/
lemma changeBandComp_smul (x y z : F.obj (.mk (op U))) (T : (Over U)ᵒᵖ)
    (a c : ((abelianSheafToGrpSheaf (J.over U)).obj
      ((J.overPullback AddCommGrpCat U).obj B)).obj.obj T) :
    let P := fun x y ↦ b.sheafHomTorsor x y (IsGerbe.exists_covering_iso (J := J) x y)
    let ψ := (abelianSheafToGrpSheaf (J.over U)).map
      ((J.overPullback AddCommGrpCat U).map φ)
    ∀ (s : (P x y |>.map ψ).sheaf.obj.obj T) (t : (P y z |>.map ψ).sheaf.obj.obj T),
      (b.changeBandComp φ x y z).hom.app T (a • s, c • t) =
        (a * c) • (b.changeBandComp φ x y z).hom.app T (s, t) := by
  intro P ψ s t
  exact b.compSection_smul φ s t a c

/-- The objects of the changed-band fibre over `U`. Morphisms are the sections over the
terminal slice object of the extended isomorphism torsors. -/
@[ext]
structure ChangeBandFiber (b : F.AbelianBanding J A) (φ : A ⟶ B) (U : C) where
  /-- The original fibre object. -/
  obj : F.obj (.mk (op U))

/-- The groupoid whose arrows are the extended isomorphism sheaves evaluated at the terminal
slice object. Its morphism types compute to these sections. -/
instance changeBandFiberGroupoid : Groupoid.{v'} (b.ChangeBandFiber φ U) where
  Hom x y :=
    let P := b.sheafHomTorsor x.obj y.obj (IsGerbe.exists_covering_iso (J := J) x.obj y.obj)
    let ψ := (abelianSheafToGrpSheaf (J.over U)).map
      ((J.overPullback AddCommGrpCat U).map φ)
    (P.map ψ).sheaf.obj.obj (op (Over.mk (𝟙 U)))
  id x := (b.changeBandId φ x.obj).hom.app _ PUnit.unit
  comp {x y z} s t := (b.changeBandComp φ x.obj y.obj z.obj).hom.app _ (s, t)
  inv {x y} s := (b.changeBandInv φ x.obj y.obj).hom.app _ s
  id_comp {x y} := b.changeBandId_comp φ x.obj y.obj _
  comp_id {x y} := b.changeBandComp_id φ x.obj y.obj _
  assoc {w x y z} := b.changeBandComp_assoc φ w.obj x.obj y.obj z.obj _
  inv_comp {x y} := b.changeBandInv_comp φ x.obj y.obj _
  comp_inv {x y} := b.changeBandComp_inv φ x.obj y.obj _

/-- The comparison from original arrows to arrows with the extended band. The body is exposed
so that its object map and the dependent arrow types compute to the original objects. -/
@[expose]
def toChangeBandFiber : F.obj (.mk (op U)) ⥤ b.ChangeBandFiber φ U where
  obj x := ⟨x⟩
  map {x y} p :=
    let P := b.sheafHomTorsor x y (IsGerbe.exists_covering_iso (J := J) x y)
    let ψ := (abelianSheafToGrpSheaf (J.over U)).map
      ((J.overPullback AddCommGrpCat U).map φ)
    (P.toMap ψ).hom.app _ (F.presheafHomObjHomEquiv p)
  map_id x := by
    erw [presheafHomObjHomEquiv_id]
    rfl
  map_comp {x y z} p q := by
    erw [presheafHomObjHomEquiv_comp]
    have h := b.changeBandComp_toMap φ (op (Over.mk (𝟙 U)))
      (F.presheafHomObjHomEquiv p) (F.presheafHomObjHomEquiv q) 1 1
    simp only [one_mul, one_smul] at h
    convert h.symm using 1

/-- The positive action of `B(U)` on the arrows of the changed-band fibre. -/
instance changeBandFiberMulAction (x y : b.ChangeBandFiber φ U) :
    MulAction (Multiplicative (B.obj.obj (op U))) (x ⟶ y) :=
  let P := b.sheafHomTorsor x.obj y.obj (IsGerbe.exists_covering_iso (J := J) x.obj y.obj)
  let ψ := (abelianSheafToGrpSheaf (J.over U)).map
    ((J.overPullback AddCommGrpCat U).map φ)
  let T := op (Over.mk (𝟙 U))
  let e := abelianSheafToGrpSheafObjEquiv ((J.overPullback AddCommGrpCat U).obj B) T
  letI : MulAction _ (x ⟶ y) := (P.map ψ).mulAction T
  MulAction.compHom _ e.toMonoidHom

/-- The two positive translations add under composition in the changed-band fibre. -/
lemma changeBandFiber_smul_comp_smul {x y z : b.ChangeBandFiber φ U}
    (s : x ⟶ y) (t : y ⟶ z) (a c : Multiplicative (B.obj.obj (op U))) :
    (a • s) ≫ (c • t) = (a * c) • (s ≫ t) := by
  let : MulAction (coefficient (B := B) (op (Over.mk (𝟙 U)))) (x ⟶ z) :=
    (b.extendedTorsor φ x.obj z.obj).mulAction _
  exact (b.changeBandComp_smul φ x.obj y.obj z.obj (op (Over.mk (𝟙 U)))
    (abelianSheafToGrpSheafObjEquiv _ _ a) (abelianSheafToGrpSheafObjEquiv _ _ c) s t).trans
      (congrArg (fun d ↦ d • (s ≫ t)) (map_mul _ a c).symm)

/-- The comparison functor keeps the original fibre object. -/
@[simp]
lemma toChangeBandFiber_obj_obj (x : F.obj (.mk (op U))) :
    ((b.toChangeBandFiber φ).obj x).obj = x := (rfl)

/-- The comparison on arrows is the torsor extension map at the terminal slice object. -/
@[simp]
lemma toChangeBandFiber_map {x y : F.obj (.mk (op U))} (p : x ⟶ y) :
    let P := b.sheafHomTorsor x y (IsGerbe.exists_covering_iso (J := J) x y)
    let ψ := (abelianSheafToGrpSheaf (J.over U)).map
      ((J.overPullback AddCommGrpCat U).map φ)
    (b.toChangeBandFiber φ).map p = (P.toMap ψ).hom.app (op (Over.mk (𝟙 U)))
      (F.presheafHomObjHomEquiv p) := (rfl)

/-- A coefficient translates a compared arrow by the same positive coefficient in its
extended isomorphism torsor. -/
lemma changeBandFiber_smul_toMap {x y : F.obj (.mk (op U))} (p : x ⟶ y)
    (a : Multiplicative (B.obj.obj (op U))) :
    let P := b.sheafHomTorsor x y (IsGerbe.exists_covering_iso (J := J) x y)
    let ψ := (abelianSheafToGrpSheaf (J.over U)).map
      ((J.overPullback AddCommGrpCat U).map φ)
    let T := op (Over.mk (𝟙 U))
    a • (b.toChangeBandFiber φ).map p =
      (abelianSheafToGrpSheafObjEquiv ((J.overPullback AddCommGrpCat U).obj B) T a) •
        (P.toMap ψ).hom.app T (F.presheafHomObjHomEquiv p) := (rfl)

end CategoryTheory.Pseudofunctor.AbelianBanding
