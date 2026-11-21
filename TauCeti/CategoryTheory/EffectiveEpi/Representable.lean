/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.EffectiveEpi.Basic
public import Mathlib.CategoryTheory.Sites.IsSheafFor
public import TauCeti.CategoryTheory.Comma.Over
public import TauCeti.CategoryTheory.Limits.Shapes.Pullback.DescentDatum

/-!
# Representability of a presheaf which is representable after a base change

Let `p : S' ⟶ S` be a morphism in a category with pullbacks and let `F` be a presheaf of types
on `Over S`. Suppose that the restriction `(Over.map p).op ⋙ F` of `F` to `Over S'` is
represented by an object `X` over `S'`, through `e : ((Over.map p).op ⋙ F).RepresentableBy X`.

Over an object `Z` of `Over S` with a lift `a : Z ⟶ S'` of its structure morphism, `e`
identifies the sections of `F` over `Z` with the morphisms `(Z, a) ⟶ X` over `S'`
(`CategoryTheory.Functor.RepresentableBy.sectionsEquiv`). Since `F(Z)` does not depend on the
lift, two lifts `a`, `b` of `Z ⟶ S` give a bijection between the morphisms over `a` and those
over `b`. Applied to the two lifts `s` and `π x` of a point `(s, x)` of `S' ×_S X`, this is a
descent datum on `X` relative to `p`, in the action form of `TauCeti.DescentDatum`
(`CategoryTheory.Functor.RepresentableBy.descentDatum`).

If this descent datum is effective, with model `X₀` over `S`, if `F` satisfies the sheaf
condition for the base changes `T ×_S S' ⟶ T` of `p`, and if these base changes are effective
epimorphisms, then `F` is represented by `X₀`
(`CategoryTheory.Functor.RepresentableBy.descend`). Together with an effectivity theorem for
descent data, such as effective descent of schemes affine over the cover, this shows that a sheaf
which becomes representable after a covering base change is representable.

## Main definitions

* `CategoryTheory.Functor.RepresentableBy.sectionsEquiv e a ha`: the sections of `F` over `Z`
  as morphisms `(Z, a) ⟶ X` over `S'`, natural in `Z`
  (`CategoryTheory.Functor.RepresentableBy.sectionsEquiv_map`).
* `CategoryTheory.Functor.RepresentableBy.descentDatum e`: the descent datum on `X` induced by
  `e`, characterized by `CategoryTheory.Functor.RepresentableBy.lift_act_descentDatum`.
* `CategoryTheory.Functor.RepresentableBy.descend e hF f`: for a morphism of descent data
  `f` from the canonical descent datum on `X₀ ×_S S'` to `e.descentDatum` which is an isomorphism
  over `S'`, the representation of `F` by `X₀`. After base change to `S'` it is base change
  followed by `f` (`CategoryTheory.Functor.RepresentableBy.sectionsEquiv_descend_homEquiv`).

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé VIII, §1.
* J. S. Milne, *Étale cohomology*, Chapter III, Theorem 4.3, for the application to the
  representability of torsors under affine group schemes.
-/

public section

namespace CategoryTheory.Functor.RepresentableBy

open TauCeti Limits Opposite

universe w v u

variable {C : Type u} [Category.{v} C] {S S' : C} {p : S' ⟶ S}
  {F : (Over S)ᵒᵖ ⥤ Type w} {X : Over S'}

section Sections

variable (e : ((Over.map p).op ⋙ F).RepresentableBy X)

/-- For an object `Z` over `S` and a lift `a : Z ⟶ S'` of its structure morphism through `p`,
the representation `e` identifies the sections of `F` over `Z` with the morphisms `(Z, a) ⟶ X`
over `S'`. -/
noncomputable def sectionsEquiv {Z : Over S} (a : Z.left ⟶ S') (ha : a ≫ p = Z.hom) :
    F.obj (op Z) ≃ (Over.mk a ⟶ X) :=
  (F.mapIso (Over.mapMkIso a ha).op).toEquiv.trans e.homEquiv.symm

variable {e}

/-- The identification `sectionsEquiv` is natural: restricting a section along
`g : Z' ⟶ Z` corresponds to precomposition with `g`, for the lift `g ≫ a` of `Z' ⟶ S`. -/
theorem sectionsEquiv_map {Z Z' : Over S} (g : Z' ⟶ Z) (a : Z.left ⟶ S')
    (ha : a ≫ p = Z.hom) (ζ : F.obj (op Z)) :
    sectionsEquiv e (g.left ≫ a) (by simp [ha]) (F.map g.op ζ) =
      (Over.homMk g.left : Over.mk (g.left ≫ a) ⟶ Over.mk a) ≫ sectionsEquiv e a ha ζ := by
  have hsq : (Over.mapMkIso (g.left ≫ a) (by simp [ha])).hom ≫ g =
      (Over.map p).map (Over.homMk g.left : Over.mk (g.left ≫ a) ⟶ Over.mk a) ≫
        (Over.mapMkIso a ha).hom := by
    ext
    simp
  simp only [sectionsEquiv, Equiv.trans_apply, Iso.toEquiv_fun, Functor.mapIso_hom,
    Iso.op_hom, e.comp_homEquiv_symm]
  rw [← Functor.map_comp_apply, ← op_comp, hsq, op_comp, Functor.map_comp_apply]
  -- `((Over.map p).op ⋙ F).map g.op` is `F.map ((Over.map p).map g).op` by definition.
  rfl

/-- `sectionsEquiv` depends on the lift only through its value. -/
theorem sectionsEquiv_left_congr {Z : Over S} {a b : Z.left ⟶ S'} (hab : a = b)
    (ha : a ≫ p = Z.hom) (hb : b ≫ p = Z.hom) (ζ : F.obj (op Z)) :
    (sectionsEquiv e a ha ζ).left = (sectionsEquiv e b hb ζ).left := by
  subst hab
  rfl

/-- Sections of `F` over `Z` are determined by the underlying morphisms of their images under
`sectionsEquiv`. -/
theorem sectionsEquiv_left_injective {Z : Over S} (a : Z.left ⟶ S') (ha : a ≫ p = Z.hom) :
    Function.Injective fun ζ : F.obj (op Z) ↦ (sectionsEquiv e a ha ζ).left :=
  fun _ _ h ↦ (sectionsEquiv e a ha).injective (Over.OverMorphism.ext h)

/-- The image of a section under `sectionsEquiv` lies over the lift. -/
@[reassoc]
theorem sectionsEquiv_left_hom {Z : Over S} (a : Z.left ⟶ S') (ha : a ≫ p = Z.hom)
    (ζ : F.obj (op Z)) : (sectionsEquiv e a ha ζ).left ≫ X.hom = a := by
  simp

end Sections

section Datum

variable [HasPullbacks C] (e : ((Over.map p).op ⋙ F).RepresentableBy X)

/-- The space `S' ×_S X` of the action, as an object over `S`. -/
private noncomputable abbrev actionSpace (p : S' ⟶ S) (X : Over S') : Over S :=
  Over.mk (pullback.fst p (X.hom ≫ p) ≫ p)

private lemma snd_hom_comp (X : Over S') :
    (pullback.snd p (X.hom ≫ p) ≫ X.hom) ≫ p = (actionSpace p X).hom := by
  simp [pullback.condition]

/-- The section of `F` over `S' ×_S X` corresponding to the second projection to `X`. -/
private noncomputable def actionSection : F.obj (op (actionSpace p X)) :=
  (sectionsEquiv e _ (snd_hom_comp X)).symm (Over.homMk (pullback.snd _ _))

private lemma sectionsEquiv_actionSection :
    (sectionsEquiv e _ (snd_hom_comp X) (actionSection e)).left = pullback.snd _ _ := by
  simp [actionSection]

/-- The action `S' ×_S X ⟶ X` of the descent datum induced by `e`. -/
private noncomputable def descentAct : pullback p (X.hom ≫ p) ⟶ X.left :=
  (sectionsEquiv e (pullback.fst p (X.hom ≫ p)) rfl (actionSection e)).left

/-- The characteristic property of `descentAct`, before the descent datum is assembled. -/
private lemma lift_descentAct {Z : Over S} (a b : Z.left ⟶ S') (ha : a ≫ p = Z.hom)
    (hb : b ≫ p = Z.hom) (ζ : F.obj (op Z)) (y : Z.left ⟶ X.left)
    (hy : (sectionsEquiv e b hb ζ).left = y) (h : a ≫ p = y ≫ X.hom ≫ p) :
    pullback.lift a y h ≫ descentAct e = (sectionsEquiv e a ha ζ).left := by
  subst hy
  let g : Z ⟶ actionSpace p X := Over.homMk (pullback.lift a _ h) (by simp [ha])
  have hg : g.left = pullback.lift a _ h := Over.homMk_left _ _
  have h₁ := congrArg Over.Hom.left
    (sectionsEquiv_map (e := e) g _ rfl (actionSection e))
  have h₂ := congrArg Over.Hom.left
    (sectionsEquiv_map (e := e) g _ (snd_hom_comp X) (actionSection e))
  simp only [Over.comp_left, Over.homMk_left] at h₁ h₂
  rw [sectionsEquiv_actionSection] at h₂
  have hb' : b = g.left ≫ pullback.snd p (X.hom ≫ p) ≫ X.hom := by
    rw [hg, pullback.lift_snd_assoc, sectionsEquiv_left_hom]
  have hζ : F.map g.op (actionSection e) = ζ := by
    refine sectionsEquiv_left_injective (e := e) b hb ?_
    refine (sectionsEquiv_left_congr hb' hb _ _).trans (h₂.trans ?_)
    rw [hg, pullback.lift_snd]
  have ha' : g.left ≫ pullback.fst p (X.hom ≫ p) = a := by rw [hg, pullback.lift_fst]
  rw [descentAct, ← hg, ← h₁, hζ]
  exact sectionsEquiv_left_congr ha' _ ha _

/-- The descent datum on `X` relative to `p` induced by a representation `e` by `X` of the
restriction of `F` to `Over S'`. A point
`s` of `S'` sends `x` to the point of `X` over `s` corresponding to the same section of `F` as
`x`; see `lift_act_descentDatum`. -/
noncomputable def descentDatum : DescentDatum p X where
  act := descentAct e
  act_hom := sectionsEquiv_left_hom _ _ _
  lift_act := by
    let ζ := (sectionsEquiv e (Z := Over.mk (X.hom ≫ p)) X.hom rfl).symm
      (Over.homMk (𝟙 X.left) : Over.mk X.hom ⟶ X)
    refine (lift_descentAct e X.hom X.hom rfl rfl ζ (𝟙 X.left) (by simp [ζ]) (by simp)).trans
      ?_
    simp [ζ]
  act_assoc := by
    let g : Over.mk (pullback.fst p (pullback.fst p (X.hom ≫ p) ≫ p) ≫ p) ⟶
        actionSpace p X :=
      Over.homMk (pullback.snd _ _) pullback.condition.symm
    let ζ := F.map g.op (actionSection e)
    have h₁ := congrArg Over.Hom.left
      (sectionsEquiv_map (e := e) g _ rfl (actionSection e))
    have h₂ := congrArg Over.Hom.left
      (sectionsEquiv_map (e := e) g _ (snd_hom_comp X) (actionSection e))
    simp only [Over.comp_left, Over.homMk_left] at h₁ h₂
    rw [sectionsEquiv_actionSection] at h₂
    have hg : g.left = pullback.snd p (pullback.fst p (X.hom ≫ p) ≫ p) := Over.homMk_left _ _
    have hb₁ : (g.left ≫ pullback.fst p (X.hom ≫ p)) ≫ p =
        (Over.mk (pullback.fst p (pullback.fst p (X.hom ≫ p) ≫ p) ≫ p)).hom := by
      simp [hg, ← pullback.condition]
    have hb₂ : (g.left ≫ pullback.snd p (X.hom ≫ p) ≫ X.hom) ≫ p =
        (Over.mk (pullback.fst p (pullback.fst p (X.hom ≫ p) ≫ p) ≫ p)).hom := by
      rw [← hb₁]
      simp [pullback.condition]
    rw [lift_descentAct e _ _ rfl hb₁ ζ _ (h₁.trans (by rw [hg]; rfl)),
      lift_descentAct e _ _ rfl hb₂ ζ _ (h₂.trans (by rw [hg]))]

/-- The characteristic property of the descent datum `descentDatum e`. For a section `ζ` of
`F` over `Z` and two lifts `a`, `b` of `Z ⟶ S` to `S'`, the point `a` acts on the morphism
`Z ⟶ X` over `b` corresponding to `ζ`, giving the morphism over `a` corresponding to `ζ`. -/
theorem lift_act_descentDatum {Z : Over S} (a b : Z.left ⟶ S') (ha : a ≫ p = Z.hom)
    (hb : b ≫ p = Z.hom) (ζ : F.obj (op Z)) :
    pullback.lift a (sectionsEquiv e b hb ζ).left (by simp [ha, hb]) ≫
      (descentDatum e).act = (sectionsEquiv e a ha ζ).left :=
  lift_descentAct e a b ha hb ζ _ rfl _

end Datum

section Representable

variable [HasPullbacks C] {e : ((Over.map p).op ⋙ F).RepresentableBy X} {X₀ : Over S}

/-- The section of `F` over `X₀ ×_S S'` corresponding, under `e`, to the isomorphism
`f : X₀ ×_S S' ⟶ X`. -/
private noncomputable def baseChangeSection
    (f : (DescentDatum.baseChange p X₀).Hom e.descentDatum) :
    F.obj (op ((Over.map p).obj ((Over.pullback p).obj X₀))) :=
  (sectionsEquiv e (pullback.snd X₀.hom p) rfl).symm (Over.homMk f.hom.left (by simp))

private lemma sectionsEquiv_baseChangeSection
    (f : (DescentDatum.baseChange p X₀).Hom e.descentDatum) :
    (sectionsEquiv e (pullback.snd X₀.hom p) rfl (baseChangeSection f)).left = f.hom.left := by
  simp [baseChangeSection]

/-- The section `baseChangeSection f` is compatible with descent along `X₀ ×_S S' ⟶ X₀`. -/
private lemma baseChangeSection_compatible
    (f : (DescentDatum.baseChange p X₀).Hom e.descentDatum) {Z : Over S}
    (g₁ g₂ : Z ⟶ (Over.map p).obj ((Over.pullback p).obj X₀))
    (hg : g₁ ≫ (Over.mapPullbackAdj p).counit.app X₀ =
      g₂ ≫ (Over.mapPullbackAdj p).counit.app X₀) :
    F.map g₁.op (baseChangeSection f) = F.map g₂.op (baseChangeSection f) := by
  have hc₁ : (g₁.left ≫ pullback.snd X₀.hom p) ≫ p = Z.hom := by simpa using Over.w g₁
  have hc₂ : (g₂.left ≫ pullback.snd X₀.hom p) ≫ p = Z.hom := by simpa using Over.w g₂
  have hfst : g₁.left ≫ pullback.fst X₀.hom p = g₂.left ≫ pullback.fst X₀.hom p := by
    simpa using congrArg Over.Hom.left hg
  have h₁ := congrArg Over.Hom.left
    (sectionsEquiv_map (e := e) g₁ (pullback.snd X₀.hom p) rfl (baseChangeSection f))
  have h₂ := congrArg Over.Hom.left
    (sectionsEquiv_map (e := e) g₂ (pullback.snd X₀.hom p) rfl (baseChangeSection f))
  simp only [Over.comp_left, Over.homMk_left, sectionsEquiv_baseChangeSection] at h₁ h₂
  refine sectionsEquiv_left_injective (e := e) _ hc₁ ?_
  dsimp only
  rw [h₁, ← lift_descentAct e _ _ hc₁ hc₂ _ _ h₂ (by rw [hc₁, ← hc₂]; simp)]
  refine Eq.trans ?_ (f.lift_comp_act _ _ _).symm
  congr 1
  apply pullback.hom_ext <;> simp [hfst]

variable (hF : ∀ T : Over S,
  Presieve.IsSheafFor F (.singleton ((Over.mapPullbackAdj p).counit.app T)))

/-- The section of `F` over `X₀` descended from `baseChangeSection f`. -/
private noncomputable def descendedSection
    (f : (DescentDatum.baseChange p X₀).Hom e.descentDatum) :
    F.obj (op X₀) :=
  (Presieve.isSheafFor_singleton.1 (hF X₀) (baseChangeSection f)
    fun g₁ g₂ hg ↦ baseChangeSection_compatible f g₁ g₂ hg).exists.choose

private lemma map_descendedSection
    (f : (DescentDatum.baseChange p X₀).Hom e.descentDatum) :
    F.map ((Over.mapPullbackAdj p).counit.app X₀).op (descendedSection hF f) =
      baseChangeSection f :=
  (Presieve.isSheafFor_singleton.1 (hF X₀) (baseChangeSection f)
    fun g₁ g₂ hg ↦ baseChangeSection_compatible f g₁ g₂ hg).exists.choose_spec

/-- After base change to `S'`, the section `x^* (descendedSection f)` of `F` over `T`
corresponds under `e` to the base change of `x` followed by `f`. -/
private lemma sectionsEquiv_map_descendedSection
    (f : (DescentDatum.baseChange p X₀).Hom e.descentDatum) {T : Over S} (x : T ⟶ X₀) :
    (sectionsEquiv e (pullback.snd T.hom p) rfl
        (F.map ((Over.mapPullbackAdj p).counit.app T).op
          (F.map x.op (descendedSection hF f)))).left =
      ((Over.pullback p).map x).left ≫ f.hom.left := by
  have hnat := (Over.mapPullbackAdj p).counit_naturality x
  rw [← Functor.map_comp_apply, ← op_comp, ← hnat, op_comp, Functor.map_comp_apply,
    map_descendedSection]
  have h := congrArg Over.Hom.left (sectionsEquiv_map (e := e)
    ((Over.map p).map ((Over.pullback p).map x)) (pullback.snd X₀.hom p) rfl
    (baseChangeSection f))
  simp only [Over.comp_left, Over.homMk_left, sectionsEquiv_baseChangeSection] at h
  have hl : Over.Hom.left ((Over.map p).map ((Over.pullback p).map x)) ≫
      pullback.snd X₀.hom p = pullback.snd T.hom p := by
    simp
  have h3 := sectionsEquiv_left_congr (e := e) hl.symm rfl (by simp)
    (F.map ((Over.map p).map ((Over.pullback p).map x)).op (baseChangeSection f))
  exact (h3.trans h).trans (by rw [Over.map_map_left])

omit hF in
/-- The morphism `T ×_S S' ⟶ X` corresponding to a section `η` of `F` over `T`, followed by a
morphism of descent data to a canonical descent datum and the projection to `X₀`, satisfies the
descent condition along `T ×_S S' ⟶ T`. -/
private lemma descent_condition (f : e.descentDatum.Hom (DescentDatum.baseChange p X₀))
    {T : Over S} (η : F.obj (op T)) {Z : C} (g₁ g₂ : Z ⟶ pullback T.hom p)
    (hg : g₁ ≫ pullback.fst T.hom p = g₂ ≫ pullback.fst T.hom p) :
    g₁ ≫ (sectionsEquiv e (pullback.snd T.hom p) rfl
        (F.map ((Over.mapPullbackAdj p).counit.app T).op η)).left ≫ f.hom.left ≫
        pullback.fst X₀.hom p =
      g₂ ≫ (sectionsEquiv e (pullback.snd T.hom p) rfl
        (F.map ((Over.mapPullbackAdj p).counit.app T).op η)).left ≫ f.hom.left ≫
        pullback.fst X₀.hom p := by
  let φ := (sectionsEquiv e (pullback.snd T.hom p) rfl
    (F.map ((Over.mapPullbackAdj p).counit.app T).op η)).left
  let Z' : Over S := Over.mk (g₁ ≫ pullback.fst T.hom p ≫ T.hom)
  let h₁ : Z' ⟶ (Over.map p).obj ((Over.pullback p).obj T) :=
    Over.homMk g₁ (by simp [Z', pullback.condition])
  let h₂ : Z' ⟶ (Over.map p).obj ((Over.pullback p).obj T) :=
    Over.homMk g₂ (by simp [Z', ← pullback.condition, reassoc_of% hg])
  have hh : h₁ ≫ (Over.mapPullbackAdj p).counit.app T =
      h₂ ≫ (Over.mapPullbackAdj p).counit.app T := by
    ext
    simp [h₁, h₂, hg]
  have n₁ := congrArg Over.Hom.left (sectionsEquiv_map (e := e) h₁ (pullback.snd T.hom p)
    rfl (F.map ((Over.mapPullbackAdj p).counit.app T).op η))
  have n₂ := congrArg Over.Hom.left (sectionsEquiv_map (e := e) h₂ (pullback.snd T.hom p)
    rfl (F.map ((Over.mapPullbackAdj p).counit.app T).op η))
  rw [← Functor.map_comp_apply, ← op_comp, Over.comp_left] at n₁ n₂
  rw [hh] at n₁
  have key : g₁ ≫ φ = pullback.lift (h₁.left ≫ pullback.snd T.hom p) (g₂ ≫ φ)
      (by simp [φ, h₁, Z', ← pullback.condition, reassoc_of% hg]) ≫
      (descentDatum e).act :=
    n₁.symm.trans (lift_descentAct e _ _ _ _ _ _ n₂ _).symm
  rw [← Category.assoc, key, Category.assoc, f.lift_act_comp_fst, Category.assoc]

variable [∀ T : Over S, EffectiveEpi (pullback.fst T.hom p)]

private lemma injective_map_descendedSection
    (f : (DescentDatum.baseChange p X₀).Hom e.descentDatum) [IsIso f.hom] (T : Over S) :
    Function.Injective fun x : T ⟶ X₀ ↦ F.map x.op (descendedSection hF f) := by
  intro x y hxy
  have h := (sectionsEquiv_map_descendedSection hF f x).symm.trans
    ((congrArg (fun ζ ↦ (sectionsEquiv e (pullback.snd T.hom p) rfl
      (F.map ((Over.mapPullbackAdj p).counit.app T).op ζ)).left) hxy).trans
    (sectionsEquiv_map_descendedSection hF f y))
  rw [cancel_mono] at h
  have h' := congrArg (· ≫ pullback.fst X₀.hom p) h
  simp only [Over.pullback_map_left, pullback.lift_fst, cancel_epi] at h'
  exact Over.OverMorphism.ext h'

private lemma surjective_map_descendedSection
    (f : (DescentDatum.baseChange p X₀).Hom e.descentDatum) [IsIso f.hom] (T : Over S) :
    Function.Surjective fun x : T ⟶ X₀ ↦ F.map x.op (descendedSection hF f) := by
  intro η
  let φ := (sectionsEquiv e (pullback.snd T.hom p) rfl
    (F.map ((Over.mapPullbackAdj p).counit.app T).op η)).left
  have hφ : φ ≫ X.hom = pullback.snd T.hom p := sectionsEquiv_left_hom _ _ _
  have hinv : (CategoryTheory.inv f.hom).left ≫ pullback.snd X₀.hom p = X.hom := by
    simpa using Over.w (CategoryTheory.inv f.hom)
  -- Descend `T ×_S S' ⟶ X ≅ X₀ ×_S S' ⟶ X₀` along the effective epimorphism
  -- `T ×_S S' ⟶ T`.
  let ψ := φ ≫ (CategoryTheory.inv f.hom).left ≫ pullback.fst X₀.hom p
  let x₀ := EffectiveEpi.desc (pullback.fst T.hom p) ψ fun g₁ g₂ hg ↦ by
    simpa only [DescentDatum.Hom.inv_hom] using descent_condition f.inv η g₁ g₂ hg
  have hx₀ : pullback.fst T.hom p ≫ x₀ = ψ := EffectiveEpi.fac _ _ _
  have hx₀' : x₀ ≫ X₀.hom = T.hom := by
    rw [← cancel_epi (pullback.fst T.hom p), reassoc_of% hx₀, Category.assoc, Category.assoc,
      pullback.condition,
      reassoc_of% hinv, reassoc_of% hφ, pullback.condition]
  refine ⟨Over.homMk x₀ hx₀', Presieve.isSeparatedFor_singleton.1 (hF T).isSeparatedFor ?_⟩
  refine sectionsEquiv_left_injective (e := e) (pullback.snd T.hom p) rfl ?_
  dsimp only
  rw [sectionsEquiv_map_descendedSection]
  have : ((Over.pullback p).map (Over.homMk x₀ hx₀')).left =
      φ ≫ (CategoryTheory.inv f.hom).left := by
    apply pullback.hom_ext
    · simp [hx₀, ψ]
    · simp [hinv, hφ]
  rw [this, Category.assoc, ← Over.comp_left, IsIso.inv_hom_id, Over.id_left, Category.comp_id]

variable (e) in
/-- **Representability by effective descent.** Let `F` be a presheaf on `Over S` satisfying the
sheaf condition for the base changes `T ×_S S' ⟶ T` of `p`, which are effective epimorphisms.
If the restriction of `F` to `Over S'` is represented by `X`, and the induced descent datum on
`X` is effective, with a morphism `f` from the canonical descent datum on `X₀ ×_S S'` which is
an isomorphism over `S'`, then `F` is represented by `X₀`. The representation is characterized
by `sectionsEquiv_descend_homEquiv`. -/
noncomputable def descend (f : (DescentDatum.baseChange p X₀).Hom e.descentDatum)
    [IsIso f.hom] : F.RepresentableBy X₀ where
  homEquiv {T} := Equiv.ofBijective (fun x : T ⟶ X₀ ↦ F.map x.op (descendedSection hF f))
    ⟨injective_map_descendedSection hF f T, surjective_map_descendedSection hF f T⟩
  -- `Equiv.ofBijective φ _` applies `φ`, and `(g ≫ x).op = x.op ≫ g.op`.
  homEquiv_comp g x := Functor.map_comp_apply F x.op g.op _

variable (e) in
/-- After base change to `S'`, the representation `e.descend hF f` sends a morphism
`x : T ⟶ X₀` to the section of `F` corresponding under `e` to the base change of `x` followed by
`f`. -/
theorem sectionsEquiv_descend_homEquiv
    (f : (DescentDatum.baseChange p X₀).Hom e.descentDatum) [IsIso f.hom] {T : Over S}
    (x : T ⟶ X₀) :
    (sectionsEquiv e (pullback.snd T.hom p) rfl
        (F.map ((Over.mapPullbackAdj p).counit.app T).op
          ((e.descend hF f).homEquiv x))).left =
      ((Over.pullback p).map x).left ≫ f.hom.left :=
  sectionsEquiv_map_descendedSection hF f x

end Representable

end CategoryTheory.Functor.RepresentableBy
