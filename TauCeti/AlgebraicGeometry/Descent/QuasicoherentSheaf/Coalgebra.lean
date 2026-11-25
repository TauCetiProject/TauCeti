/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monad.Adjunction
public import TauCeti.CategoryTheory.Sites.Descent.DescentData
public import TauCeti.AlgebraicGeometry.Descent.QuasicoherentSheaf.Basic
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.BaseChange
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.QuasiSeparated

/-!
# Descent data of quasi-coherent modules as coalgebras

Let `f : X ⟶ S` be a flat, quasi-compact and quasi-separated morphism of schemes, with projections
`p₁, p₂ : X ×_S X ⟶ X`. A descent datum `D` for quasi-coherent modules along `f` (Mathlib's
`Pseudofunctor.DescentData` for `qcohPseudofunctor` and the single morphism `f`) consists of a
quasi-coherent module `E` on `X` and gluing isomorphisms `u^* E ⟶ v^* E` for all `u v : Y ⟶ X` with
`u ≫ f = v ≫ f`, compatible with pullback and composition (`qcohDescentDataHom`, in
`TauCeti.AlgebraicGeometry.Descent.QuasicoherentSheaf.Basic`). By flat base change
`f^* f_* E ≅ p₂_* p₁^* E` (`Scheme.Modules.isIso_pushforwardBaseChange_app`), the adjunct
`E ⟶ p₂_* p₁^* E` of the gluing isomorphism `p₂^* E ⟶ p₁^* E` is a morphism `E ⟶ f^* f_* E`
(`qcohDescentDataCoaction`). It is a coalgebra structure for the comonad `f^* f_*`: the counit law
comes from the normalisation of `D` on the diagonal of `X ×_S X`, and coassociativity from the
cocycle condition on `X ×_S X ×_S X`. This is the object part of the Bénabou–Roubaud theorem: when
base change holds, descent data along `f` are coalgebras for `f^* f_*`. The functor is fully
faithful: a morphism of modules intertwines the coactions exactly when it commutes with the gluing
isomorphisms on `X ×_S X` (`qcohDescentDataCoaction_comp_map_iff`), and a morphism commuting with
the gluing isomorphisms on `X ×_S X` commutes with all gluing morphisms, which are pulled back from
them (`CategoryTheory.Pseudofunctor.DescentData.homMkOfIsPullback`).

For the descent datum of the pullback `f^* M` of a quasi-coherent module `M` on `S`, the coaction is
`f^*` of the unit `M ⟶ f_* f^* M` (`qcohDescentDataCoaction_ofObj`): the coalgebra that Beck's
comparison functor attaches to `M`. For faithfully flat `f` between affine schemes, pullback of
quasi-coherent modules is comonadic (`QuasicoherentSheaf.comonadicPullbackSpecMap`), so every such
coalgebra comes from a quasi-coherent module on `S`; with full faithfulness, this makes descent data
along such `f` effective (`TauCeti.AlgebraicGeometry.Descent.isEquivalence_toDescentData_specMap`).

## Main declarations

* `TauCeti.AlgebraicGeometry.Descent.qcohDescentDataCoaction`: the coaction `E ⟶ f^* f_* E`, with
  the counit law `qcohDescentDataCoaction_counit`, coassociativity
  `qcohDescentDataCoaction_coassoc` and naturality `qcohDescentDataCoaction_comp_map`;
* `TauCeti.AlgebraicGeometry.Descent.qcohDescentDataCoaction_comp_map_iff`: a morphism of modules
  intertwines the coactions iff it commutes with the gluing isomorphisms on `X ×_S X`;
* `TauCeti.AlgebraicGeometry.Descent.qcohDescentDataToCoalgebra`: the functor from descent data
  along `f` to coalgebras for the comonad `f^* f_*` on `X.Modules`, fully faithful by
  `fullyFaithfulQcohDescentDataToCoalgebra`;
* `TauCeti.AlgebraicGeometry.Descent.qcohDescentDataCoaction_ofObj`: on the descent datum of `f^* M`
  the coaction is `f^*` of the unit of `f^* ⊣ f_*`.

## References

* J. Bénabou, J. Roubaud, *Monades et descente*, C. R. Acad. Sci. Paris Sér. A-B 270 (1970),
  A96–A98.
* G. Janelidze, W. Tholen, *Facets of descent, I*, Appl. Categ. Structures 2 (1994), 245–281.
* The Stacks Project, Section 35.3 (descent for modules along faithfully flat ring maps) and
  Proposition 35.5.2 (023T), descent of quasi-coherent modules along fpqc coverings.
* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé VIII.
-/

public section

open CategoryTheory Limits Opposite

noncomputable section

universe u

namespace TauCeti.AlgebraicGeometry.Descent

open _root_.AlgebraicGeometry

variable {X S : Scheme.{u}} {f : X ⟶ S}
  {D : qcohPseudofunctor.DescentData (fun _ : PUnit ↦ f)}

section Aux

/-! The coalgebra laws are proved for an arbitrary module `E` with gluing morphisms `δ`
satisfying the axioms of descent data. Stated on `(D.obj PUnit.unit).obj` directly, the
morphisms of `X.Modules` involved are typed through `qcohPseudofunctor`, and `rw` cannot match
them. -/

variable {E : X.Modules}
  (δ : ∀ ⦃Y : Scheme.{u}⦄ (u v : Y ⟶ X), u ≫ f = v ≫ f →
    ((Scheme.Modules.pullback u).obj E ⟶ (Scheme.Modules.pullback v).obj E))

private lemma δ_congr {Y : Scheme.{u}} {u u' v v' : Y ⟶ X} (hu : u = u') (hv : v = v')
    (h : u ≫ f = v ≫ f) :
    δ u v h = (Scheme.Modules.pullbackCongr hu).hom.app _ ≫ δ u' v' (hu ▸ hv ▸ h) ≫
      (Scheme.Modules.pullbackCongr hv).inv.app _ := by
  subst hu hv
  simp [Scheme.Modules.pullbackCongr]

private lemma counit_aux (hself : ∀ ⦃Y : Scheme.{u}⦄ (u : Y ⟶ X), δ u u rfl = 𝟙 _)
    (hpull : ∀ ⦃Y Y' : Scheme.{u}⦄ (g : Y' ⟶ Y) (u v : Y ⟶ X) (h : u ≫ f = v ≫ f),
      (Scheme.Modules.pullbackComp g u).inv.app _ ≫ (Scheme.Modules.pullback g).map (δ u v h) ≫
        (Scheme.Modules.pullbackComp g v).hom.app _ = δ (g ≫ u) (g ≫ v) (by simp [h]))
    (a : E ⟶ (Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback f).obj E)
    (ha : a ≫
        (Scheme.Modules.pushforwardBaseChange (IsPullback.of_hasPullback f f).toCommSq).app E =
      (Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd f f)).unit.app _ ≫
        (Scheme.Modules.pushforward (pullback.snd f f)).map
          (δ (pullback.snd f f) (pullback.fst f f) pullback.condition.symm)) :
    a ≫ (Scheme.Modules.pullbackPushforwardAdjunction f).counit.app _ = 𝟙 _ := by
  have h₁ := pullback.diagonal_fst f
  have h₂ := pullback.diagonal_snd f
  have K := Scheme.Modules.pushforwardBaseChange_app_comp_pushforwardToPullback_app
    (IsPullback.of_hasPullback f f).toCommSq h₁ h₂ E
  have hσ := hpull (pullback.diagonal f) (pullback.snd f f) (pullback.fst f f)
    pullback.condition.symm
  rw [δ_congr δ h₂ h₁, hself] at hσ
  have hn := (Scheme.Modules.pushforwardToPullback h₂).naturality
    (δ (pullback.snd f f) (pullback.fst f f) pullback.condition.symm)
  have hu := Scheme.Modules.unit_comp_pushforwardToPullback_app h₂ E
  rw [← cancel_mono ((Scheme.Modules.pullbackId X).inv.app _ ≫
    (Scheme.Modules.pullbackCongr h₁.symm).hom.app _ ≫
      (Scheme.Modules.pullbackComp (pullback.diagonal f) (pullback.fst f f)).inv.app _),
    Category.id_comp, Category.assoc, ← K, reassoc_of% ha, hn, reassoc_of% hu]
  have hσ' : (Scheme.Modules.pullbackComp (pullback.diagonal f) (pullback.snd f f)).inv.app E ≫
      (Scheme.Modules.pullback (pullback.diagonal f)).map
        (δ (pullback.snd f f) (pullback.fst f f) pullback.condition.symm) =
      (Scheme.Modules.pullbackCongr h₂).hom.app E ≫ (Scheme.Modules.pullbackCongr h₁).inv.app E ≫
        (Scheme.Modules.pullbackComp (pullback.diagonal f) (pullback.fst f f)).inv.app E := by
    rw [← cancel_mono ((Scheme.Modules.pullbackComp (pullback.diagonal f)
      (pullback.fst f f)).hom.app E), Category.assoc, hσ]
    simp
  rw [hσ']
  simp [Scheme.Modules.pullbackCongr]

/-- The cocycle condition on `X ×_S X ×_S X`, written as `Z = (X ×_S X) ×_X (X ×_S X)` with its
two projections `g' f' : Z ⟶ X ×_S X` and the projection `p₁₃` to the outer factors. -/
private lemma cocycle_aux
    (hcomp : ∀ ⦃Y : Scheme.{u}⦄ (u v w : Y ⟶ X) (h : u ≫ f = v ≫ f) (h' : v ≫ f = w ≫ f),
      δ u v h ≫ δ v w h' = δ u w (h.trans h'))
    (hpull : ∀ ⦃Y Y' : Scheme.{u}⦄ (g : Y' ⟶ Y) (u v : Y ⟶ X) (h : u ≫ f = v ≫ f),
      (Scheme.Modules.pullbackComp g u).inv.app _ ≫ (Scheme.Modules.pullback g).map (δ u v h) ≫
        (Scheme.Modules.pullbackComp g v).hom.app _ = δ (g ≫ u) (g ≫ v) (by simp [h]))
    {Z : Scheme.{u}} (g' f' p₁₃ : Z ⟶ pullback f f)
    (hw : g' ≫ pullback.snd f f = f' ≫ pullback.fst f f)
    (h₁ : p₁₃ ≫ pullback.fst f f = g' ≫ pullback.fst f f)
    (h₂ : p₁₃ ≫ pullback.snd f f = f' ≫ pullback.snd f f) :
    (Scheme.Modules.pullback f').map
        (δ (pullback.snd f f) (pullback.fst f f) pullback.condition.symm) ≫
      ((Scheme.Modules.pullbackComp f' (pullback.fst f f)).hom.app E ≫
        (Scheme.Modules.pullbackCongr hw.symm).hom.app E ≫
          (Scheme.Modules.pullbackComp g' (pullback.snd f f)).inv.app E) ≫
      (Scheme.Modules.pullback g').map
        (δ (pullback.snd f f) (pullback.fst f f) pullback.condition.symm) =
    ((Scheme.Modules.pullbackComp f' (pullback.snd f f)).hom.app E ≫
        (Scheme.Modules.pullbackCongr h₂.symm).hom.app E ≫
          (Scheme.Modules.pullbackComp p₁₃ (pullback.snd f f)).inv.app E) ≫
      (Scheme.Modules.pullback p₁₃).map
        (δ (pullback.snd f f) (pullback.fst f f) pullback.condition.symm) ≫
      (Scheme.Modules.pullbackComp p₁₃ (pullback.fst f f)).hom.app E ≫
        (Scheme.Modules.pullbackCongr h₁).hom.app E ≫
          (Scheme.Modules.pullbackComp g' (pullback.fst f f)).inv.app E := by
  -- Each pulled-back gluing morphism is a gluing morphism of `δ` on `Z`.
  have hx (x : Z ⟶ pullback f f) :
      (Scheme.Modules.pullback x).map
          (δ (pullback.snd f f) (pullback.fst f f) pullback.condition.symm) =
        (Scheme.Modules.pullbackComp x (pullback.snd f f)).hom.app E ≫
          δ (x ≫ pullback.snd f f) (x ≫ pullback.fst f f)
            (by simp only [Category.assoc, pullback.condition]) ≫
            (Scheme.Modules.pullbackComp x (pullback.fst f f)).inv.app E := by
    rw [← hpull _ _ _ pullback.condition.symm]
    simp
  rw [hx f', hx g', hx p₁₃, δ_congr δ hw rfl, δ_congr δ h₂ h₁]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  simp [Scheme.Modules.pullbackCongr, reassoc_of% hcomp]

/-- Pulled back along either projection of `X ×_S X`, the base change morphism of `f` along `f`
composes with a further base change on `Z = X ×_S X ×_S X` to the same morphism: the two ways of
pasting squares over the outer square of `Z` agree. -/
private lemma paste_aux {Z : Scheme.{u}} {g' f' p₁₃ : Z ⟶ pullback f f}
    (w' : CommSq g' f' (pullback.snd f f) (pullback.fst f f))
    (h₁ : p₁₃ ≫ pullback.fst f f = g' ≫ pullback.fst f f)
    (h₂ : p₁₃ ≫ pullback.snd f f = f' ≫ pullback.snd f f) :
    (Scheme.Modules.pullbackComp (pullback.fst f f) f).inv.app _ ≫
      (Scheme.Modules.pullback (pullback.fst f f)).map
        ((Scheme.Modules.pushforwardBaseChange (IsPullback.of_hasPullback f f).toCommSq).app E) ≫
      (Scheme.Modules.pushforwardBaseChange w').app _ =
    (Scheme.Modules.pullbackCongr pullback.condition).hom.app _ ≫
      (Scheme.Modules.pullbackComp (pullback.snd f f) f).inv.app _ ≫
      (Scheme.Modules.pullback (pullback.snd f f)).map
        ((Scheme.Modules.pushforwardBaseChange (IsPullback.of_hasPullback f f).toCommSq).app E) ≫
      (Scheme.Modules.pushforwardBaseChange (⟨h₂⟩ : CommSq p₁₃ f' _ _)).app _ ≫
      (Scheme.Modules.pushforward f').map
        ((Scheme.Modules.pullbackComp p₁₃ (pullback.fst f f)).hom.app E ≫
          (Scheme.Modules.pullbackCongr h₁).hom.app E ≫
            (Scheme.Modules.pullbackComp g' (pullback.fst f f)).inv.app E) := by
  have P1 := Scheme.Modules.pushforwardBaseChange_horiz_comp
    (IsPullback.of_hasPullback f f).toCommSq w' E
  have P2 := Scheme.Modules.pushforwardBaseChange_horiz_comp
    (IsPullback.of_hasPullback f f).toCommSq (⟨h₂⟩ : CommSq p₁₃ f' _ _) E
  have C := Scheme.Modules.pushforwardBaseChange_congr
    (w'.horiz_comp (IsPullback.of_hasPullback f f).toCommSq)
    ((⟨h₂⟩ : CommSq p₁₃ f' _ _).horiz_comp (IsPullback.of_hasPullback f f).toCommSq)
    pullback.condition h₁.symm E
  rw [← cancel_mono ((Scheme.Modules.pushforward f').map
    ((Scheme.Modules.pullbackComp g' (pullback.fst f f)).hom.app E))]
  simp only [Category.assoc, Functor.map_comp]
  rw [← P1, ← reassoc_of% P2, reassoc_of% C, ← Functor.map_comp]
  simp [Scheme.Modules.pullbackCongr]

/-- The left side `σ ≫ p₁^* a` of `comp_pullback_map_aux`, followed by the base change morphisms
`p₁^* f^* f_* E ⟶ p₁^* p₂_* p₁^* E ⟶ q₂_* q₁^* p₁^* E` on `Z = (X ×_S X) ×_X (X ×_S X)`, is the
adjunct of the left side of the cocycle condition `cocycle_aux`. -/
private lemma comp_pullback_map_left_aux
    (a : E ⟶ (Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback f).obj E)
    (ha : a ≫
        (Scheme.Modules.pushforwardBaseChange (IsPullback.of_hasPullback f f).toCommSq).app E =
      (Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd f f)).unit.app _ ≫
        (Scheme.Modules.pushforward (pullback.snd f f)).map
          (δ (pullback.snd f f) (pullback.fst f f) pullback.condition.symm)) :
    (δ (pullback.snd f f) (pullback.fst f f) pullback.condition.symm ≫
        (Scheme.Modules.pullback (pullback.fst f f)).map a) ≫
      (Scheme.Modules.pullback (pullback.fst f f)).map
        ((Scheme.Modules.pushforwardBaseChange (IsPullback.of_hasPullback f f).toCommSq).app E) ≫
      (Scheme.Modules.pushforwardBaseChange
        (IsPullback.of_hasPullback (pullback.snd f f) (pullback.fst f f)).toCommSq).app _ =
    (Scheme.Modules.pullbackPushforwardAdjunction
        (pullback.snd (pullback.snd f f) (pullback.fst f f))).unit.app _ ≫
      (Scheme.Modules.pushforward (pullback.snd (pullback.snd f f) (pullback.fst f f))).map
        ((Scheme.Modules.pullback (pullback.snd (pullback.snd f f) (pullback.fst f f))).map
            (δ (pullback.snd f f) (pullback.fst f f) pullback.condition.symm) ≫
          ((Scheme.Modules.pullbackComp (pullback.snd (pullback.snd f f) (pullback.fst f f))
              (pullback.fst f f)).hom.app E ≫
            (Scheme.Modules.pullbackCongr
              (IsPullback.of_hasPullback (pullback.snd f f) (pullback.fst f f)).w.symm).hom.app E ≫
              (Scheme.Modules.pullbackComp (pullback.fst (pullback.snd f f) (pullback.fst f f))
                (pullback.snd f f)).inv.app E) ≫
          (Scheme.Modules.pullback (pullback.fst (pullback.snd f f) (pullback.fst f f))).map
            (δ (pullback.snd f f) (pullback.fst f f) pullback.condition.symm)) := by
  have H' := IsPullback.of_hasPullback (pullback.snd f f) (pullback.fst f f)
  have ha' := congrArg (Scheme.Modules.pullback (pullback.fst f f)).map ha
  have hn := (Scheme.Modules.pushforwardBaseChange H'.toCommSq).naturality
    (δ (pullback.snd f f) (pullback.fst f f) pullback.condition.symm)
  have hu := Scheme.Modules.pullback_map_unit_comp_pushforwardBaseChange_app H'.toCommSq E
  have hu' := (Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd (pullback.snd f f)
    (pullback.fst f f))).unit.naturality
      (δ (pullback.snd f f) (pullback.fst f f) pullback.condition.symm)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj, Functor.id_map] at hn hu hu'
  simp only [Functor.map_comp, Category.assoc] at ha' hu ⊢
  -- `p₁^*` of the defining equation of the coaction `a`.
  rw [reassoc_of% ha']
  -- Naturality of base change along `q₁, q₂ : Z ⟶ X ×_S X` in the gluing morphism.
  rw [hn]
  -- Base change turns the pulled-back unit of `p₂^* ⊣ p₂_*` into the unit of `q₂^* ⊣ q₂_*`.
  rw [reassoc_of% hu]
  -- Naturality of the unit of `q₂^* ⊣ q₂_*` in the gluing morphism.
  rw [reassoc_of% hu']

/-- The right side `p₂^* a ≫ c` of `comp_pullback_map_aux`, followed by the base change morphisms
as in `comp_pullback_map_left_aux`, is the adjunct of the right side of the cocycle condition
`cocycle_aux`, for `p₁₃ : Z ⟶ X ×_S X` the projection to the outer factors. -/
private lemma comp_pullback_map_right_aux
    {p₁₃ : pullback (pullback.snd f f) (pullback.fst f f) ⟶ pullback f f}
    (h₁ : p₁₃ ≫ pullback.fst f f = pullback.fst _ _ ≫ pullback.fst f f)
    (h₂ : p₁₃ ≫ pullback.snd f f = pullback.snd _ _ ≫ pullback.snd f f)
    (a : E ⟶ (Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback f).obj E)
    (ha : a ≫
        (Scheme.Modules.pushforwardBaseChange (IsPullback.of_hasPullback f f).toCommSq).app E =
      (Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd f f)).unit.app _ ≫
        (Scheme.Modules.pushforward (pullback.snd f f)).map
          (δ (pullback.snd f f) (pullback.fst f f) pullback.condition.symm)) :
    ((Scheme.Modules.pullback (pullback.snd f f)).map a ≫
        (Scheme.Modules.pullbackComp (pullback.snd f f) f).hom.app _ ≫
          (Scheme.Modules.pullbackCongr pullback.condition.symm).hom.app _ ≫
            (Scheme.Modules.pullbackComp (pullback.fst f f) f).inv.app _) ≫
      (Scheme.Modules.pullback (pullback.fst f f)).map
        ((Scheme.Modules.pushforwardBaseChange (IsPullback.of_hasPullback f f).toCommSq).app E) ≫
      (Scheme.Modules.pushforwardBaseChange
        (IsPullback.of_hasPullback (pullback.snd f f) (pullback.fst f f)).toCommSq).app _ =
    (Scheme.Modules.pullbackPushforwardAdjunction
        (pullback.snd (pullback.snd f f) (pullback.fst f f))).unit.app _ ≫
      (Scheme.Modules.pushforward (pullback.snd (pullback.snd f f) (pullback.fst f f))).map
        (((Scheme.Modules.pullbackComp (pullback.snd (pullback.snd f f) (pullback.fst f f))
              (pullback.snd f f)).hom.app E ≫
            (Scheme.Modules.pullbackCongr h₂.symm).hom.app E ≫
              (Scheme.Modules.pullbackComp p₁₃ (pullback.snd f f)).inv.app E) ≫
          (Scheme.Modules.pullback p₁₃).map
            (δ (pullback.snd f f) (pullback.fst f f) pullback.condition.symm) ≫
          (Scheme.Modules.pullbackComp p₁₃ (pullback.fst f f)).hom.app E ≫
            (Scheme.Modules.pullbackCongr h₁).hom.app E ≫
              (Scheme.Modules.pullbackComp (pullback.fst (pullback.snd f f) (pullback.fst f f))
                (pullback.fst f f)).inv.app E) := by
  have w : CommSq p₁₃ (pullback.snd _ _) (pullback.snd f f) (pullback.snd f f) := ⟨h₂⟩
  have hpaste := paste_aux (E := E)
    (IsPullback.of_hasPullback (pullback.snd f f) (pullback.fst f f)).toCommSq h₁ h₂
  have hcc : (Scheme.Modules.pullbackCongr (pullback.condition (f := f) (g := f)).symm).hom.app
      ((Scheme.Modules.pushforward f).obj E) ≫
      (Scheme.Modules.pullbackCongr (pullback.condition (f := f) (g := f))).hom.app _ = 𝟙 _ := by
    simp [Scheme.Modules.pullbackCongr]
  have ha' := congrArg (Scheme.Modules.pullback (pullback.snd f f)).map ha
  have hn := (Scheme.Modules.pushforwardBaseChange w).naturality
    (δ (pullback.snd f f) (pullback.fst f f) pullback.condition.symm)
  have hu := Scheme.Modules.pullback_map_unit_comp_pushforwardBaseChange_app w E
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn hu
  simp only [Functor.map_comp, Category.assoc] at hpaste ha' hu ⊢
  -- Paste the base change morphisms over the outer square of `Z` through `p₁₃` instead.
  rw [hpaste]
  -- The identifications `p₂^* f^* ≅ p₁^* f^*` and back cancel.
  rw [reassoc_of% hcc, Iso.hom_inv_id_app_assoc]
  -- `p₂^*` of the defining equation of the coaction `a`.
  rw [reassoc_of% ha']
  -- Naturality of base change along `p₁₃, q₂` in the gluing morphism.
  rw [reassoc_of% hn]
  -- Base change turns the pulled-back unit of `p₂^* ⊣ p₂_*` into the unit of `q₂^* ⊣ q₂_*`.
  rw [reassoc_of% hu]

/-- The coaction `a` is a morphism of descent data from `δ` to the canonical descent datum of
`f_* E`: `σ ≫ p₁^* a = p₂^* a ≫ c`, for `σ` the gluing isomorphism and `c` the identification
`p₂^* f^* ≅ p₁^* f^*`. -/
private lemma comp_pullback_map_aux [E.IsQuasicoherent] [QuasiCompact f] [QuasiSeparated f]
    [Flat f]
    (hcomp : ∀ ⦃Y : Scheme.{u}⦄ (u v w : Y ⟶ X) (h : u ≫ f = v ≫ f) (h' : v ≫ f = w ≫ f),
      δ u v h ≫ δ v w h' = δ u w (h.trans h'))
    (hpull : ∀ ⦃Y Y' : Scheme.{u}⦄ (g : Y' ⟶ Y) (u v : Y ⟶ X) (h : u ≫ f = v ≫ f),
      (Scheme.Modules.pullbackComp g u).inv.app _ ≫ (Scheme.Modules.pullback g).map (δ u v h) ≫
        (Scheme.Modules.pullbackComp g v).hom.app _ = δ (g ≫ u) (g ≫ v) (by simp [h]))
    (a : E ⟶ (Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback f).obj E)
    (ha : a ≫
        (Scheme.Modules.pushforwardBaseChange (IsPullback.of_hasPullback f f).toCommSq).app E =
      (Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd f f)).unit.app _ ≫
        (Scheme.Modules.pushforward (pullback.snd f f)).map
          (δ (pullback.snd f f) (pullback.fst f f) pullback.condition.symm)) :
    δ (pullback.snd f f) (pullback.fst f f) pullback.condition.symm ≫
        (Scheme.Modules.pullback (pullback.fst f f)).map a =
      (Scheme.Modules.pullback (pullback.snd f f)).map a ≫
        (Scheme.Modules.pullbackComp (pullback.snd f f) f).hom.app _ ≫
          (Scheme.Modules.pullbackCongr pullback.condition.symm).hom.app _ ≫
            (Scheme.Modules.pullbackComp (pullback.fst f f) f).inv.app _ := by
  have H' := IsPullback.of_hasPullback (pullback.snd f f) (pullback.fst f f)
  have := Scheme.Modules.isIso_pushforwardBaseChange_app H'
    ((Scheme.Modules.pullback (pullback.fst f f)).obj E)
  have := Scheme.Modules.isIso_pushforwardBaseChange_app (IsPullback.of_hasPullback f f) E
  -- The projection `p₁₃ : Z ⟶ X ×_S X` to the outer factors of `Z = X ×_S X ×_S X`.
  let p₁₃ : pullback (pullback.snd f f) (pullback.fst f f) ⟶ pullback f f :=
    pullback.lift (pullback.fst _ _ ≫ pullback.fst f f) (pullback.snd _ _ ≫ pullback.snd f f)
      (by simp only [Category.assoc, pullback.condition, pullback.condition_assoc])
  have h₁ : p₁₃ ≫ pullback.fst f f = pullback.fst _ _ ≫ pullback.fst f f := pullback.lift_fst _ _ _
  have h₂ : p₁₃ ≫ pullback.snd f f = pullback.snd _ _ ≫ pullback.snd f f :=
    pullback.lift_snd _ _ _
  -- After the base change isomorphisms, both sides are adjuncts of the two sides of the cocycle
  -- condition on `Z`.
  rw [← cancel_mono ((Scheme.Modules.pullback (pullback.fst f f)).map
    ((Scheme.Modules.pushforwardBaseChange (IsPullback.of_hasPullback f f).toCommSq).app E) ≫
      (Scheme.Modules.pushforwardBaseChange H'.toCommSq).app _),
    comp_pullback_map_left_aux δ a ha, comp_pullback_map_right_aux δ h₁ h₂ a ha,
    cocycle_aux δ hcomp hpull _ _ p₁₃ H'.w h₁ h₂]

private lemma coassoc_aux [E.IsQuasicoherent] [QuasiCompact f] [QuasiSeparated f] [Flat f]
    (hcomp : ∀ ⦃Y : Scheme.{u}⦄ (u v w : Y ⟶ X) (h : u ≫ f = v ≫ f) (h' : v ≫ f = w ≫ f),
      δ u v h ≫ δ v w h' = δ u w (h.trans h'))
    (hpull : ∀ ⦃Y Y' : Scheme.{u}⦄ (g : Y' ⟶ Y) (u v : Y ⟶ X) (h : u ≫ f = v ≫ f),
      (Scheme.Modules.pullbackComp g u).inv.app _ ≫ (Scheme.Modules.pullback g).map (δ u v h) ≫
        (Scheme.Modules.pullbackComp g v).hom.app _ = δ (g ≫ u) (g ≫ v) (by simp [h]))
    (a : E ⟶ (Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback f).obj E)
    (ha : a ≫
        (Scheme.Modules.pushforwardBaseChange (IsPullback.of_hasPullback f f).toCommSq).app E =
      (Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd f f)).unit.app _ ≫
        (Scheme.Modules.pushforward (pullback.snd f f)).map
          (δ (pullback.snd f f) (pullback.fst f f) pullback.condition.symm)) :
    a ≫ (Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback f).map a =
      a ≫ (Scheme.Modules.pullback f).map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
          ((Scheme.Modules.pushforward f).obj E)) := by
  have : ((Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback f).obj E).IsQuasicoherent :=
    inferInstanceAs
      ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pushforward f).obj E)).IsQuasicoherent
  have := Scheme.Modules.isIso_pushforwardBaseChange_app (IsPullback.of_hasPullback f f)
    ((Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback f).obj E)
  rw [← cancel_mono ((Scheme.Modules.pushforwardBaseChange
    (IsPullback.of_hasPullback f f).toCommSq).app
      ((Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback f).obj E))]
  have hn :=
    (Scheme.Modules.pushforwardBaseChange (IsPullback.of_hasPullback f f).toCommSq).naturality a
  have hu := Scheme.Modules.pullback_map_unit_comp_pushforwardBaseChange_app
    (IsPullback.of_hasPullback f f).toCommSq ((Scheme.Modules.pushforward f).obj E)
  have hu' := (Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd f f)).unit.naturality a
  have hc := congrArg (Scheme.Modules.pushforward (pullback.snd f f)).map
    (comp_pullback_map_aux δ hcomp hpull a ha)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj, Functor.id_map] at hn hu hu' ⊢
  simp only [Functor.map_comp, Category.assoc] at hu hc ⊢
  -- Naturality of base change in `a`, then the defining equation of `a`.
  rw [hn, reassoc_of% ha]
  -- `a` is a morphism of descent data (`comp_pullback_map_aux`), pushed forward along `p₂`.
  rw [hc]
  -- Naturality of the unit of `p₂^* ⊣ p₂_*` in `a`.
  rw [← reassoc_of% hu']
  -- Base change turns `f^*` of the unit of `f^* ⊣ f_*` into the unit of `p₂^* ⊣ p₂_*`.
  rw [hu]

private lemma comp_map_iff_aux [QuasiCompact f] [QuasiSeparated f] [Flat f] {E' : X.Modules}
    [E'.IsQuasicoherent]
    (δ' : ∀ ⦃Y : Scheme.{u}⦄ (u v : Y ⟶ X), u ≫ f = v ≫ f →
      ((Scheme.Modules.pullback u).obj E' ⟶ (Scheme.Modules.pullback v).obj E'))
    (φ : E ⟶ E')
    (a : E ⟶ (Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback f).obj E)
    (ha : a ≫
        (Scheme.Modules.pushforwardBaseChange (IsPullback.of_hasPullback f f).toCommSq).app E =
      (Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd f f)).unit.app _ ≫
        (Scheme.Modules.pushforward (pullback.snd f f)).map
          (δ (pullback.snd f f) (pullback.fst f f) pullback.condition.symm))
    (a' : E' ⟶ (Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback f).obj E')
    (ha' : a' ≫ (Scheme.Modules.pushforwardBaseChange
        (IsPullback.of_hasPullback f f).toCommSq).app E' =
      (Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd f f)).unit.app _ ≫
        (Scheme.Modules.pushforward (pullback.snd f f)).map
          (δ' (pullback.snd f f) (pullback.fst f f) pullback.condition.symm)) :
    a ≫ (Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback f).map φ = φ ≫ a' ↔
      (Scheme.Modules.pullback (pullback.snd f f)).map φ ≫
          δ' (pullback.snd f f) (pullback.fst f f) pullback.condition.symm =
        δ (pullback.snd f f) (pullback.fst f f) pullback.condition.symm ≫
          (Scheme.Modules.pullback (pullback.fst f f)).map φ := by
  have := Scheme.Modules.isIso_pushforwardBaseChange_app (IsPullback.of_hasPullback f f) E'
  -- After the base change isomorphism `f^* f_* E' ≅ p₂_* p₁^* E'`, the two sides of the coalgebra
  -- condition are the adjuncts under `p₂^* ⊣ p₂_*` of the two sides of the gluing condition.
  rw [← cancel_mono ((Scheme.Modules.pushforwardBaseChange
    (IsPullback.of_hasPullback f f).toCommSq).app E'), eq_comm,
    ← ((Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd f f)).homEquiv _
      _).apply_eq_iff_eq]
  have hn :=
    (Scheme.Modules.pushforwardBaseChange (IsPullback.of_hasPullback f f).toCommSq).naturality φ
  have hu := (Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd f f)).unit.naturality φ
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj, Functor.id_map] at hn hu ⊢
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  -- Naturality of base change in `φ`, then the defining equations of `a` and `a'`, and
  -- naturality of the unit of `p₂^* ⊣ p₂_*` in `φ`.
  rw [hn, reassoc_of% ha, ha', reassoc_of% hu]

omit δ in
private lemma eq_pullback_map_unit_aux [QuasiCompact f] [QuasiSeparated f] [Flat f]
    (N : S.Modules) [N.IsQuasicoherent]
    (a : (Scheme.Modules.pullback f).obj N ⟶
      (Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback f).obj
        ((Scheme.Modules.pullback f).obj N))
    (ha : a ≫ (Scheme.Modules.pushforwardBaseChange (IsPullback.of_hasPullback f f).toCommSq).app
        ((Scheme.Modules.pullback f).obj N) =
      (Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd f f)).unit.app _ ≫
        (Scheme.Modules.pushforward (pullback.snd f f)).map
          ((Scheme.Modules.pullbackComp (pullback.snd f f) f).hom.app N ≫
            (Scheme.Modules.pullbackCongr pullback.condition.symm).hom.app N ≫
              (Scheme.Modules.pullbackComp (pullback.fst f f) f).inv.app N)) :
    a = (Scheme.Modules.pullback f).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N) := by
  have := Scheme.Modules.isIso_pushforwardBaseChange_app (IsPullback.of_hasPullback f f)
    ((Scheme.Modules.pullback f).obj N)
  rw [← cancel_mono ((Scheme.Modules.pushforwardBaseChange
    (IsPullback.of_hasPullback f f).toCommSq).app ((Scheme.Modules.pullback f).obj N)), ha,
    Scheme.Modules.pullback_map_unit_comp_pushforwardBaseChange_app]

end Aux

variable (f D) in
/-- The **coaction** `E ⟶ f^* f_* E` of a descent datum `D` along a flat, quasi-compact and
quasi-separated morphism `f : X ⟶ S`, where `E` is the module of `D`: the adjunct
`E ⟶ p₂_* p₁^* E` of the gluing isomorphism `p₂^* E ⟶ p₁^* E` on `X ×_S X`, read through the flat
base change isomorphism `f^* f_* E ≅ p₂_* p₁^* E`. -/
def qcohDescentDataCoaction [QuasiCompact f] [QuasiSeparated f] [Flat f] :
    (D.obj PUnit.unit).obj ⟶
      (Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback f).obj (D.obj PUnit.unit).obj :=
  have : (D.obj PUnit.unit).obj.IsQuasicoherent := (D.obj PUnit.unit).property
  have hβ := Scheme.Modules.isIso_pushforwardBaseChange_app (IsPullback.of_hasPullback f f)
    (D.obj PUnit.unit).obj
  (Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd f f)).homEquiv _ _
      (qcohDescentDataHom f D (pullback.snd f f) (pullback.fst f f) pullback.condition.symm) ≫
    inv (I := hβ) ((Scheme.Modules.pushforwardBaseChange
      (IsPullback.of_hasPullback f f).toCommSq).app (D.obj PUnit.unit).obj)

variable [QuasiCompact f] [QuasiSeparated f] [Flat f]

/-- The coaction of a descent datum followed by the base change isomorphism
`f^* f_* E ≅ p₂_* p₁^* E` is the adjunct of the gluing isomorphism `p₂^* E ⟶ p₁^* E`. -/
@[reassoc]
lemma qcohDescentDataCoaction_comp_pushforwardBaseChange_app :
    qcohDescentDataCoaction f D ≫
        (Scheme.Modules.pushforwardBaseChange (IsPullback.of_hasPullback f f).toCommSq).app _ =
      (Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd f f)).unit.app _ ≫
        (Scheme.Modules.pushforward (pullback.snd f f)).map
          (qcohDescentDataHom f D (pullback.snd f f) (pullback.fst f f)
            pullback.condition.symm) := by
  have : (D.obj PUnit.unit).obj.IsQuasicoherent := (D.obj PUnit.unit).property
  have hβ := Scheme.Modules.isIso_pushforwardBaseChange_app (IsPullback.of_hasPullback f f)
    (D.obj PUnit.unit).obj
  exact (Category.assoc _ _ _).trans ((congrArg _ (@IsIso.inv_hom_id _ _ _ _ _ hβ)).trans
    ((Category.comp_id _).trans (Adjunction.homEquiv_unit _ _ _ _)))



/-- **Counit law.** The coaction of a descent datum followed by the counit `f^* f_* E ⟶ E` is the
identity: on the diagonal of `X ×_S X` the gluing isomorphism is the identity. -/
@[reassoc, simp]
theorem qcohDescentDataCoaction_counit :
    qcohDescentDataCoaction f D ≫
      (Scheme.Modules.pullbackPushforwardAdjunction f).counit.app _ = 𝟙 _ :=
  counit_aux (E := (D.obj PUnit.unit).obj) (fun _ u v h ↦ qcohDescentDataHom f D u v h)
    (fun _ u ↦ qcohDescentDataHom_self u)
    (fun _ _ g u v h ↦ pullbackComp_inv_app_comp_pullback_map_qcohDescentDataHom g u v h) _
    qcohDescentDataCoaction_comp_pushforwardBaseChange_app

/-- **Coassociativity.** The coaction `a` of a descent datum satisfies `a ≫ f^* f_* a = a ≫ f^* η`,
for `η` the unit of `f^* ⊣ f_*` at `f_* E`: this is the cocycle condition on `X ×_S X ×_S X`. -/
@[reassoc]
theorem qcohDescentDataCoaction_coassoc :
    qcohDescentDataCoaction f D ≫
        (Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback f).map
          (qcohDescentDataCoaction f D) =
      qcohDescentDataCoaction f D ≫ (Scheme.Modules.pullback f).map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
          ((Scheme.Modules.pushforward f).obj _)) :=
  have : (D.obj PUnit.unit).obj.IsQuasicoherent := (D.obj PUnit.unit).property
  coassoc_aux (E := (D.obj PUnit.unit).obj) (fun _ u v h ↦ qcohDescentDataHom f D u v h)
    (fun _ u v w h h' ↦ qcohDescentDataHom_comp u v w h h')
    (fun _ _ g u v h ↦ pullbackComp_inv_app_comp_pullback_map_qcohDescentDataHom g u v h) _
    qcohDescentDataCoaction_comp_pushforwardBaseChange_app

/-- A morphism `φ` between the modules of two descent data intertwines their coactions,
`a₁ ≫ f^* f_* φ = φ ≫ a₂`, exactly when it commutes with their gluing isomorphisms on `X ×_S X`:
`p₂^* φ ≫ σ₂ = σ₁ ≫ p₁^* φ`. -/
theorem qcohDescentDataCoaction_comp_map_iff
    {D₁ D₂ : qcohPseudofunctor.DescentData (fun _ : PUnit ↦ f)}
    (φ : (D₁.obj PUnit.unit).obj ⟶ (D₂.obj PUnit.unit).obj) :
    qcohDescentDataCoaction f D₁ ≫
        (Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback f).map φ =
      φ ≫ qcohDescentDataCoaction f D₂ ↔
    (Scheme.Modules.pullback (pullback.snd f f)).map φ ≫
        qcohDescentDataHom f D₂ (pullback.snd f f) (pullback.fst f f) pullback.condition.symm =
      qcohDescentDataHom f D₁ (pullback.snd f f) (pullback.fst f f) pullback.condition.symm ≫
        (Scheme.Modules.pullback (pullback.fst f f)).map φ :=
  have : (D₂.obj PUnit.unit).obj.IsQuasicoherent := (D₂.obj PUnit.unit).property
  comp_map_iff_aux (E := (D₁.obj PUnit.unit).obj) (fun _ u v h ↦ qcohDescentDataHom f D₁ u v h)
    (fun _ u v h ↦ qcohDescentDataHom f D₂ u v h) φ
    _ qcohDescentDataCoaction_comp_pushforwardBaseChange_app
    _ qcohDescentDataCoaction_comp_pushforwardBaseChange_app

/-- A morphism of descent data intertwines the coactions: `a₁ ≫ f^* f_* ψ = ψ ≫ a₂`. -/
@[reassoc]
theorem qcohDescentDataCoaction_comp_map
    {D₁ D₂ : qcohPseudofunctor.DescentData (fun _ : PUnit ↦ f)} (ψ : D₁ ⟶ D₂) :
    qcohDescentDataCoaction f D₁ ≫
        (Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback f).map (ψ.hom PUnit.unit).hom =
      (ψ.hom PUnit.unit).hom ≫ qcohDescentDataCoaction f D₂ := by
  rw [qcohDescentDataCoaction_comp_map_iff,
    qcohDescentDataHom_eq (pullback.snd f f ≫ f) _ _ rfl pullback.condition,
    qcohDescentDataHom_eq (pullback.snd f f ≫ f) _ _ rfl pullback.condition]
  exact congrArg InducedCategory.Hom.hom (ψ.comm (pullback.snd f f ≫ f) (i₁ := PUnit.unit)
    (i₂ := PUnit.unit) (pullback.snd f f) (pullback.fst f f) rfl pullback.condition)

variable (f) in
/-- **Descent data as coalgebras.** For a flat, quasi-compact and quasi-separated morphism
`f : X ⟶ S`, a descent datum for quasi-coherent modules along `f` is a coalgebra for the comonad
`f^* f_*` on `X.Modules`, with the coaction `qcohDescentDataCoaction`; a morphism of descent data
is a morphism of coalgebras. -/
@[expose, simps]
def qcohDescentDataToCoalgebra :
    qcohPseudofunctor.DescentData (fun _ : PUnit ↦ f) ⥤
      (Scheme.Modules.pullbackPushforwardAdjunction f).toComonad.Coalgebra where
  obj D :=
    { A := (D.obj PUnit.unit).obj
      a := qcohDescentDataCoaction f D
      counit := qcohDescentDataCoaction_counit
      coassoc := qcohDescentDataCoaction_coassoc.symm }
  map {D₁ D₂} ψ :=
    { f := (ψ.hom PUnit.unit).hom
      h := qcohDescentDataCoaction_comp_map ψ }

variable (f) in
/-- **Descent data embed fully faithfully into coalgebras.** For a flat, quasi-compact and
quasi-separated morphism `f : X ⟶ S`, the functor `qcohDescentDataToCoalgebra f` from descent data
for quasi-coherent modules along `f` to coalgebras for the comonad `f^* f_*` is fully faithful: a
morphism of modules intertwining the coactions commutes with the gluing isomorphisms on `X ×_S X`
(`qcohDescentDataCoaction_comp_map_iff`), hence with all gluing morphisms
(`Pseudofunctor.DescentData.homMkOfIsPullback`). -/
def fullyFaithfulQcohDescentDataToCoalgebra : (qcohDescentDataToCoalgebra f).FullyFaithful where
  preimage g := Pseudofunctor.DescentData.homMkOfIsPullback
    (fun _ ↦ ObjectProperty.homMk g.f) (fun _ _ ↦ (IsPullback.of_hasPullback f f).flip)
    fun _ _ ↦ ObjectProperty.hom_ext _ (by
      have h := (qcohDescentDataCoaction_comp_map_iff g.f).1 g.h
      rw [qcohDescentDataHom_eq (pullback.snd f f ≫ f) _ _ rfl pullback.condition,
        qcohDescentDataHom_eq (pullback.snd f f ≫ f) _ _ rfl pullback.condition] at h
      -- Composites and pullbacks of morphisms of quasi-coherent modules are, by definition, those
      -- of the underlying morphisms of modules.
      exact h)
  map_preimage g := Comonad.Coalgebra.Hom.ext <| congrArg InducedCategory.Hom.hom
    (Pseudofunctor.DescentData.homMkOfIsPullback_hom (fun _ ↦ ObjectProperty.homMk g.f) _ _ _)
  preimage_map _ := Pseudofunctor.DescentData.hom_ext fun _ ↦
    (Pseudofunctor.DescentData.homMkOfIsPullback_hom ..).trans rfl

/-- On the descent datum of the pullback `f^* M` of a quasi-coherent module `M` on `S`, the
coaction is `f^*` of the unit `M ⟶ f_* f^* M`: the coalgebra of Beck's comparison functor. -/
theorem qcohDescentDataCoaction_ofObj (M : QuasicoherentSheaf S) :
    qcohDescentDataCoaction f (.ofObj M) = (Scheme.Modules.pullback f).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M.obj) :=
  have : M.obj.IsQuasicoherent := M.property
  eq_pullback_map_unit_aux (f := f) M.obj _
    (qcohDescentDataCoaction_comp_pushforwardBaseChange_app.trans (by
      rw [qcohDescentDataHom_ofObj]
      -- The module of `ofObj M` is `f^* M` by definition.
      rfl))

end TauCeti.AlgebraicGeometry.Descent
