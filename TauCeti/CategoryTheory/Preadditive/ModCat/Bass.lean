/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import TauCeti.CategoryTheory.Functor.Factorizable
public import TauCeti.CategoryTheory.Preadditive.ModCat.Basic

import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.CategoryTheory.Limits.Constructions.Filtered
import TauCeti.Algebra.Category.ModuleCat.Colimits
import TauCeti.Algebra.Homology.ShortComplex.ShortExact

/-!
# Bass modules of sequences

The Bass module of a sequence in a preadditive category is the sequential colimit of its
contravariant representables. The colimit vanishes precisely when the composite out of each
stage eventually vanishes. If the colimit is projective, the composites out of each stage
eventually factor back through all subsequent composites. The telescope gives a short exact
presentation by coproducts of representables. Its pointwise exactness uses
`ModuleCat.shortExact_telescopeShortComplex` and the equivalence of abelian groups with
integer modules.

## References

* H. Bass, *Finitistic dimension and a homological generalization of semi-primary rings*,
  Trans. Amer. Math. Soc. 95 (1960), Lemmas 1.1–1.3.
* M. Harada, *Perfect categories I*, Osaka J. Math. 10 (1973), Remark 1, p. 339.
* D. Simson, *On pure global dimension of locally finitely presented Grothendieck categories*,
  Fund. Math. 96 (1977), Definition 3.1.
-/

public section

universe w v u

open CategoryTheory Category DirectSum Limits Opposite
open CoproductsFromFiniteFiltered

namespace TauCeti.ModCat

variable {C : Type u} [Category.{v} C] [Preadditive C]
  (c : ℕ → C) (f : ∀ i, c i ⟶ c (i + 1))

/-- The sequence of representable modules induced by a sequence in a preadditive category. -/
abbrev bassDiagram : ℕ ⥤ ModCat.{v} C :=
  Functor.ofSequence f ⋙ yoneda C

/-- The Bass module of a sequence is the colimit of its sequence of representable modules. -/
noncomputable abbrev bassModule : ModCat.{v} C :=
  colimit (bassDiagram c f)

/-- The telescope of the Bass diagram. Its first map subtracts the successor transition
from each summand inclusion, and its second map is induced by the colimit legs. -/
noncomputable def bassTelescope : ShortComplex (ModCat.{v} C) :=
  let F := bassDiagram c f
  ShortComplex.mk (X₃ := bassModule c f)
    (Sigma.desc fun i ↦ Sigma.ι F.obj i -
      F.map (homOfLE (i.le_add_right 1)) ≫ Sigma.ι F.obj (i + 1))
    (Sigma.desc (colimit.ι F)) (by
      apply Sigma.hom_ext
      intro i
      simp [Preadditive.sub_comp])

/-- The source of the telescope is the coproduct of the stages. -/
@[simp]
theorem bassTelescope_X₁ : (bassTelescope c f).X₁ = ∐ (bassDiagram c f).obj := (rfl)

/-- The middle object of the telescope is the coproduct of the stages. -/
@[simp]
theorem bassTelescope_X₂ : (bassTelescope c f).X₂ = ∐ (bassDiagram c f).obj := (rfl)

/-- The target of the telescope is the Bass module. -/
@[simp]
theorem bassTelescope_X₃ : (bassTelescope c f).X₃ = bassModule c f := (rfl)

/-- On each summand, the first telescope map subtracts the transition to its successor. -/
@[simp]
theorem ι_bassTelescope_f (i : ℕ) :
    Sigma.ι (bassDiagram c f).obj i ≫ eqToHom (bassTelescope_X₁ c f).symm ≫
      (bassTelescope c f).f ≫ eqToHom (bassTelescope_X₂ c f) =
      Sigma.ι (bassDiagram c f).obj i -
        (bassDiagram c f).map (homOfLE (i.le_add_right 1)) ≫
          Sigma.ι (bassDiagram c f).obj (i + 1) := by
  simp [bassTelescope]

/-- On each summand, the second telescope map is the corresponding colimit leg. -/
@[simp]
theorem ι_bassTelescope_g (i : ℕ) :
    Sigma.ι (bassDiagram c f).obj i ≫ eqToHom (bassTelescope_X₂ c f).symm ≫
      (bassTelescope c f).g ≫ eqToHom (bassTelescope_X₃ c f) = colimit.ι (bassDiagram c f) i := by
  simp [bassTelescope]

private theorem bassTelescope_map_g {R : Type w} [Ring R]
    (E : ModCat.{v} C ⥤ ModuleCat.{v} R)
    (e : ModuleCat.of R (⨁ i, E.obj ((bassDiagram c f).obj i)) ≅
      E.obj (∐ (bassDiagram c f).obj))
    (hι : ∀ i : ℕ, ModuleCat.ofHom (lof R ℕ (fun j ↦ E.obj ((bassDiagram c f).obj j)) i) ≫
      e.hom = E.map (Sigma.ι (bassDiagram c f).obj i)) :
    let t := E.mapCocone (colimit.cocone (bassDiagram c f))
    e.hom ≫ E.map (eqToHom (bassTelescope_X₂ c f).symm ≫
      (bassTelescope c f).g ≫ eqToHom (bassTelescope_X₃ c f)) =
      ModuleCat.ofHom (toModule R ℕ t.pt (fun j ↦ (t.ι.app j).hom)) := by
  intro t
  let F := bassDiagram c f
  let ag := eqToHom (bassTelescope_X₂ c f).symm ≫ (bassTelescope c f).g ≫
    eqToHom (bassTelescope_X₃ c f)
  apply Cofan.IsColimit.hom_ext (ModuleCat.coproductCoconeIsColimit fun i ↦ E.obj (F.obj i))
  intro i
  -- Display the concrete direct sum inclusions to apply `DirectSum.toModule_lof`.
  change ModuleCat.ofHom (lof R ℕ (fun j ↦ E.obj (F.obj j)) i) ≫ e.hom ≫ E.map ag =
    ModuleCat.ofHom (lof R ℕ (fun j ↦ E.obj (F.obj j)) i) ≫
      ModuleCat.ofHom (toModule R ℕ t.pt (fun j ↦ (t.ι.app j).hom))
  rw [← assoc, hι, ← E.map_comp]
  dsimp only [ag]
  rw [ι_bassTelescope_g]
  refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply,
    DirectSum.toModule_lof]
  simp only [t, Functor.mapCocone_ι_app, colimit.cocone_ι]

private theorem shortExact_map_bassTelescope {R : Type w} [Ring R]
    (E : ModCat.{v} C ⥤ ModuleCat.{v} R) [E.Additive] [PreservesColimitsOfShape ℕ E]
    [PreservesColimitsOfShape (Discrete ℕ) E] :
    ((bassTelescope c f).map E).ShortExact := by
  let F := bassDiagram c f
  let H := F ⋙ E
  let t := E.mapCocone (colimit.cocone F)
  let S := bassTelescope c f
  let P := ModuleCat.coproductCoconeIsColimit H.obj
  let Q := isColimitOfHasCoproductOfPreservesColimit E F.obj
  let e : ModuleCat.of R (⨁ i, H.obj i) ≅ E.obj (∐ F.obj) := P.coconePointUniqueUpToIso Q
  have hι (i : ℕ) :
      ModuleCat.ofHom (DirectSum.lof R ℕ (fun i ↦ H.obj i) i) ≫ e.hom =
        E.map (Sigma.ι F.obj i) :=
    P.comp_coconePointUniqueUpToIso_hom Q (Discrete.mk i)
  have hι_apply (i : ℕ) (x : H.obj i) :
      e.hom.hom (DirectSum.lof R ℕ (fun j ↦ H.obj j) i x) =
        (E.map (Sigma.ι F.obj i)).hom x :=
    congrArg (fun m : H.obj i ⟶ E.obj (∐ F.obj) ↦ m.hom x) (hι i)
  let af := eqToHom (bassTelescope_X₁ c f).symm ≫ S.f ≫ eqToHom (bassTelescope_X₂ c f)
  let ag := eqToHom (bassTelescope_X₂ c f).symm ≫ S.g ≫ eqToHom (bassTelescope_X₃ c f)
  have hf : e.hom ≫ E.map af = ModuleCat.ofHom (ModuleCat.telescopeDiff H) ≫ e.hom := by
    apply Cofan.IsColimit.hom_ext P
    intro i
    -- Display the concrete direct sum inclusions in the comparison square.
    change ModuleCat.ofHom (lof R ℕ (fun i ↦ H.obj i) i) ≫ e.hom ≫ E.map af =
      ModuleCat.ofHom (lof R ℕ (fun i ↦ H.obj i) i) ≫
        ModuleCat.ofHom (ModuleCat.telescopeDiff H) ≫ e.hom
    rw [← assoc, hι, ← E.map_comp]
    dsimp only [F, af, S]
    rw [ι_bassTelescope_f, E.map_sub, E.map_comp]
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
    simp only [ModuleCat.hom_sub, LinearMap.sub_apply, ModuleCat.hom_comp, LinearMap.coe_comp,
      Function.comp_apply, ModuleCat.hom_ofHom, ModuleCat.telescopeDiff_lof, map_sub, hι_apply]
    simp only [H, F, Functor.comp_map]
  have hg : e.hom ≫ E.map ag =
      ModuleCat.ofHom (toModule R ℕ t.pt (fun j ↦ (t.ι.app j).hom)) :=
    bassTelescope_map_g c f E e hι
  refine ShortComplex.shortExact_of_iso
    (ShortComplex.isoMk (S₁ := ModuleCat.telescopeShortComplex H t) (S₂ := S.map E)
      (eqToIso (ModuleCat.telescopeShortComplex_X₁ H t) ≪≫ e ≪≫
        eqToIso (congrArg E.obj (bassTelescope_X₁ c f).symm))
      (eqToIso (ModuleCat.telescopeShortComplex_X₂ H t) ≪≫ e ≪≫
        eqToIso (congrArg E.obj (bassTelescope_X₂ c f).symm))
      (eqToIso (ModuleCat.telescopeShortComplex_X₃ H t) ≪≫
        eqToIso (congrArg E.obj (bassTelescope_X₃ c f).symm)) ?_ ?_)
    (ModuleCat.shortExact_telescopeShortComplex H (isColimitOfPreserves E (colimit.isColimit F)))
  · rw [← cancel_mono (eqToHom (congrArg E.obj (bassTelescope_X₂ c f)))]
    simpa [ModuleCat.telescopeShortComplex_f, af, S, Functor.map_comp, eqToHom_map]
      using congrArg (eqToHom (ModuleCat.telescopeShortComplex_X₁ H t) ≫ ·) hf
  · rw [← cancel_mono (eqToHom (congrArg E.obj (bassTelescope_X₃ c f)))]
    simpa [ModuleCat.telescopeShortComplex_g, ag, S, Functor.map_comp, eqToHom_map]
      using congrArg (eqToHom (ModuleCat.telescopeShortComplex_X₂ H t) ≫ ·) hg

/-- The telescope is a short exact presentation of the Bass module by coproducts of
representables. -/
theorem shortExact_bassTelescope : (bassTelescope c f).ShortExact := by
  let U := (additiveFunctor Cᵒᵖ AddCommGrpCat.{v}).ι
  let A := (forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v}).asEquivalence.inverse
  refine ShortExact.reflects_shortExact_of_faithful U
    (ShortComplex.shortExact_of_forall_evaluation _ fun X ↦ ?_)
  let E := (evaluation Cᵒᵖ AddCommGrpCat.{v}).obj X
  have : A.Additive := Functor.additive_of_preserves_binary_products A
  apply ShortExact.reflects_shortExact_of_faithful A
  have : PreservesColimitsOfShape ℕ (U ⋙ E) := comp_preservesColimitsOfShape U E
  have : PreservesColimitsOfShape (Discrete ℕ) (U ⋙ E) := comp_preservesColimitsOfShape U E
  have : PreservesColimitsOfShape ℕ ((U ⋙ E) ⋙ A) := comp_preservesColimitsOfShape _ _
  have : PreservesColimitsOfShape (Discrete ℕ) ((U ⋙ E) ⋙ A) := comp_preservesColimitsOfShape _ _
  exact shortExact_map_bassTelescope c f ((U ⋙ E) ⋙ A)

/-- Evaluate a module at an object and take the underlying type. -/
private abbrev forgetEval (X : C) : ModCat.{v} C ⥤ Type v :=
  ((additiveFunctor Cᵒᵖ AddCommGrpCat.{v}).ι ⋙ (evaluation _ _).obj (op X)) ⋙
    forget AddCommGrpCat

@[simp]
private theorem forgetEval_map_apply (X : C) {M N : ModCat.{v} C}
    (m : M ⟶ N) (x : (forgetEval X).obj M) :
    (forgetEval X).map m x = m.hom.app (op X) x := rfl

private instance (X : C) {J : Type} [SmallCategory J] [IsFiltered J] :
    PreservesColimitsOfShape J (forgetEval X) := by
  have : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{v}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits (forget AddCommGrpCat.{v})
  infer_instance

private theorem bassDiagram_eventually_eq {X : C} {j : ℕ}
    (a b : (yoneda C).obj X ⟶ (bassDiagram c f).obj j)
    (h : a ≫ colimit.ι (bassDiagram c f) j = b ≫ colimit.ι (bassDiagram c f) j) :
    ∃ (k : ℕ) (g : j ⟶ k), a ≫ (bassDiagram c f).map g = b ≫ (bassDiagram c f).map g := by
  let F := bassDiagram c f
  let E := forgetEval X
  have hh := congrArg (fun m : (yoneda C).obj X ⟶ colimit F => E.map m (𝟙 X)) h
  simp only [Functor.map_comp] at hh
  obtain ⟨k, g, hg⟩ := (Types.FilteredColimit.isColimit_eq_iff'
    (isColimitOfPreserves E (colimit.isColimit F)) (E.map a (𝟙 X)) (E.map b (𝟙 X))).mp hh
  refine ⟨k, g, ObjectProperty.hom_ext _ (preadditiveYoneda_obj_hom_ext ?_)⟩
  have he : E.map (a ≫ F.map g) (𝟙 X) = E.map (b ≫ F.map g) (𝟙 X) := by
    simp only [Functor.map_comp]
    exact hg
  exact (forgetEval_map_apply X _ _).symm.trans (he.trans (forgetEval_map_apply X _ _))

/-- A colimit leg of the Bass diagram vanishes exactly when some transition out of its stage
vanishes in the original sequence. -/
theorem bassDiagram_ι_eq_zero_iff (i : ℕ) :
    colimit.ι (bassDiagram c f) i = 0 ↔
      ∃ (j : ℕ) (hij : i ≤ j), (Functor.ofSequence f).map (homOfLE hij) = 0 := by
  let F := bassDiagram c f
  constructor
  · intro hi
    obtain ⟨j, g, hg⟩ := bassDiagram_eventually_eq c f (𝟙 ((yoneda C).obj (c i))) 0
      (by simpa only [id_comp, zero_comp] using hi)
    refine ⟨j, leOfHom g, (yoneda C).map_injective ?_⟩
    have hg' : F.map g = 0 := by simpa only [id_comp, zero_comp] using hg
    rw [Subsingleton.elim (homOfLE (leOfHom g)) g]
    simpa only [F, Functor.comp_map, Functor.map_zero] using hg'
  · rintro ⟨j, hij, hj⟩
    rw [← colimit.w F (homOfLE hij), Functor.comp_map, hj, Functor.map_zero, zero_comp]

/-- The Bass module vanishes if and only if, for each stage, the composite to some later
stage is zero. -/
theorem isZero_bassModule_iff :
    IsZero (bassModule c f) ↔
      ∀ i : ℕ, ∃ (j : ℕ) (hij : i ≤ j), (Functor.ofSequence f).map (homOfLE hij) = 0 := by
  refine ⟨fun h i ↦ (bassDiagram_ι_eq_zero_iff c f i).1 (h.eq_of_tgt _ _), fun h ↦ ?_⟩
  dsimp only [bassModule]
  refine (IsZero.iff_id_eq_zero _).2 (colimit.hom_ext fun i ↦ ?_)
  simpa using (bassDiagram_ι_eq_zero_iff c f i).2 (h i)

private theorem bassDiagram_factors_at_stage {i : ℕ}
    (s : colimit (bassDiagram c f) ⟶ ∐ (bassDiagram c f).obj) :
    ∃ (j : ℕ) (_ : i ≤ j) (p : (∐ (bassDiagram c f).obj) ⟶ (bassDiagram c f).obj j),
      colimit.ι (bassDiagram c f) i ≫ s ≫ p ≫ colimit.ι (bassDiagram c f) j =
      colimit.ι (bassDiagram c f) i ≫ s ≫ Sigma.desc (colimit.ι (bassDiagram c f)) := by
  let F := bassDiagram c f
  let E := forgetEval (c i)
  let K := finiteSubcoproductsCocone F.obj
  let a := colimit.ι F i ≫ s
  let x : E.obj (F.obj i) := 𝟙 (c i)
  obtain ⟨S, y, hy⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves E (isColimitFiniteSubproductsCocone F.obj)) (E.map a x)
  let j := max i (S.sup Discrete.as)
  let p : (∐ F.obj) ⟶ F.obj j := Sigma.desc fun n ↦
    if hn : n ≤ j then F.map (homOfLE hn) else 0
  let q := Sigma.desc (colimit.ι F)
  let d : (liftToFinsetObj (Discrete.functor F.obj)).obj S ⟶ ∐ F.obj := K.ι.app S
  have hp : d ≫ p ≫ colimit.ι F j = d ≫ q := by
    -- Display the finite coproduct inclusion so that its components can be rewritten.
    change Sigma.desc (fun n : S ↦ Sigma.ι F.obj n.val.as) ≫ p ≫ colimit.ι F j =
      Sigma.desc (fun n : S ↦ Sigma.ι F.obj n.val.as) ≫ q
    apply Sigma.hom_ext
    intro n
    have hn : n.val.as ≤ j := (Finset.le_sup n.property).trans (le_max_right _ _)
    rw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc_assoc]
    simp [q, hn]
  refine ⟨j, le_max_left _ _, p, ObjectProperty.hom_ext _ (preadditiveYoneda_obj_hom_ext ?_)⟩
  have h : E.map (p ≫ colimit.ι F j) (E.map d y) = E.map q (E.map d y) := by
    have hh := congrArg (fun m => E.map m y) hp
    simp only [Functor.map_comp] at hh ⊢
    exact hh
  rw [Functor.mapCocone_ι_app] at hy
  -- Identify the mapped cocone leg as the image of the finite coproduct inclusion `d`.
  rw [show E.map d y = E.map a x from hy] at h
  have he : E.map (a ≫ p ≫ colimit.ι F j) x = E.map (a ≫ q) x := by
    simp only [Functor.map_comp]
    exact h
  exact (forgetEval_map_apply (c i) _ _).symm.trans (he.trans (forgetEval_map_apply (c i) _ _))

/-- If the Bass module is projective then the original sequence is factorizable. -/
theorem isFactorizable_of_projective_bassModule [Projective (bassModule c f)] :
    (Functor.ofSequence f).IsFactorizable := by
  let F := bassDiagram c f
  let q := eqToHom (bassTelescope_X₂ c f).symm ≫ (bassTelescope c f).g ≫
    eqToHom (bassTelescope_X₃ c f)
  have := (shortExact_bassTelescope c f).epi_g
  have : Epi q := by dsimp only [q]; infer_instance
  have : Projective (colimit F) := ‹Projective (bassModule c f)›
  let s := Projective.factorThru (𝟙 (colimit F)) q
  have hs : s ≫ q = 𝟙 (colimit F) := Projective.factorThru_comp _ _
  unfold Functor.IsFactorizable
  intro i
  -- Bound the finite support of the split leg and then compare the two maps at that stage.
  obtain ⟨j, hij, p, hp⟩ := bassDiagram_factors_at_stage c f (i := i) s
  have hq : Sigma.desc (colimit.ι (bassDiagram c f)) = q := by
    apply Sigma.hom_ext
    intro n
    simp only [q, Sigma.ι_comp_desc, ι_bassTelescope_g]
  rw [hq, hs, comp_id] at hp
  have he : (colimit.ι F i ≫ s ≫ p) ≫ colimit.ι F j =
      F.map (homOfLE hij) ≫ colimit.ι F j := by
    rw [colimit.w]
    simpa only [Category.assoc] using hp
  obtain ⟨l, g, hg⟩ := bassDiagram_eventually_eq c f _ _ he
  have hjl := leOfHom g
  refine ⟨l, hij.trans hjl, fun k hlk ↦ ?_⟩
  obtain ⟨t, ht⟩ := (yoneda C).map_surjective (colimit.ι F k ≫ s ≫ p ≫ F.map g)
  refine ⟨t, (yoneda C).map_injective ?_⟩
  rw [Functor.map_comp, ht]
  have hmap : F.map (homOfLE (hij.trans hjl)) = F.map (homOfLE hij) ≫ F.map g := by
    rw [← Functor.map_comp]
    congr
  calc
    F.map (homOfLE ((hij.trans hjl).trans hlk)) ≫ (colimit.ι F k ≫ s ≫ p ≫ F.map g) =
        (colimit.ι F i ≫ s ≫ p) ≫ F.map g := by rw [← Category.assoc, colimit.w, Category.assoc,
          Category.assoc]
    _ = F.map (homOfLE hij) ≫ F.map g := hg
    _ = F.map (homOfLE (hij.trans hjl)) := hmap.symm

end TauCeti.ModCat
