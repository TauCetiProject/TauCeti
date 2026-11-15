/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AlgebraicSpace.Pullback
public import TauCeti.AlgebraicGeometry.Sites.Etale.MorphismProperty

/-!
# Étale-local properties of morphisms of algebraic spaces

Given a property `P` of morphisms of schemes, a morphism `f : F ⟶ G` of algebraic spaces satisfies
`Spaces.EtaleLocal P` if there is a commutative diagram
```
  h_U ---h_h---> h_V
   |              |
   a              b
   v              v
   F ----f----->  G
```
where `a : h_U ⟶ F` is an étale atlas, `b : h_V ⟶ G` is representable by étale morphisms of
schemes, and `h : U ⟶ V` satisfies `P` (Stacks, Definition 66.16.1 (04RD) and
Definition 67.22.2 (04RD)).

Stability under base change in `AlgSpace` (`EtaleLocal.of_isPullback`, `EtaleLocal.baseChange`)
requires only `[P.IsStableUnderBaseChange]`: given an étale atlas `c : h_W ⟶ G'` of the base-change
target, pulling `b` back along `c ≫ g` and then pulling `h` back to `U ×_V (V ×_G G')` produces a
base-changed scheme morphism satisfying `P`, while `EtaleAtlas.lift_isPullback` shows that the
induced morphism into `F ×_G G'` is an étale atlas.

When `P` is étale-local on source and target in the sense of Stacks, Definition 35.32.3 (04QZ) —
expressed via Mathlib's `[P.IsLocalAtSource Scheme.etalePrecoverage]`,
`[P.IsLocalAtTarget Scheme.etalePrecoverage]`, and `[P.RespectsRight @IsOpenImmersion]` using
`CategoryTheory.MorphismProperty.iff_of_etale_surjective_commSq` (Stacks, Lemma 35.32.6 (04R2)) —
`EtaleLocal P f` holds on one étale chart square if and only if it holds on *every* commutative
square with étale vertical maps (`EtaleLocal.iff_forall_square`, Stacks, Lemma 67.22.1 (03MJ)).
From this chart-independence we deduce:

* `EtaleLocal.ofScheme_iff`: `AlgSpace.ofScheme.map f` satisfies `EtaleLocal P` iff `P f`;
* `EtaleLocal.comp`, `EtaleLocal.isStableUnderComposition`, and `EtaleLocal.isMultiplicative`;
* `EtaleLocal.iff_presheaf`: for a morphism `f` representable by schemes, `EtaleLocal P f` agrees
  with `MorphismProperty.presheaf P f.hom` whenever `P` is also stable under base change.

## References

* [Stacks Project, Lemma 35.32.6](https://stacks.math.columbia.edu/tag/04R2)
* [Stacks Project, Definition 66.16.1](https://stacks.math.columbia.edu/tag/04RD)
* [Stacks Project, Lemma 67.22.1](https://stacks.math.columbia.edu/tag/03MJ)
-/

public section

open CategoryTheory Limits Opposite

namespace TauCeti.AlgebraicGeometry.Spaces

open _root_.AlgebraicGeometry

universe u

/-- Precomposing a presheaf-étale morphism `b : h_V ⟶ G` with `h_v` for an étale scheme morphism
`v : V' ⟶ V` preserves `MorphismProperty.presheaf @Etale`. -/
private lemma presheaf_etale_yoneda_map_comp {G : SchemePresheaf.{u}} {V' V : Scheme.{u}}
    (v : V' ⟶ V) [Etale v] {b : yoneda.obj V ⟶ G}
    (hb : MorphismProperty.presheaf @Etale b) :
    MorphismProperty.presheaf @Etale (yoneda.map v ≫ b) := by
  have : MorphismProperty.IsStableUnderComposition @Etale.{u} :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  have : (MorphismProperty.presheaf @Etale.{u}).IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition (F := yoneda) (P := @Etale.{u})
  exact MorphismProperty.comp_mem _ _ _
    (MorphismProperty.relative_map (inferInstance : Etale v)) hb

namespace AlgSpace

/-- Given a morphism `f : F ⟶ G` of algebraic spaces and an étale atlas `b : h_V ⟶ G`, there exist
an étale atlas `a : h_U ⟶ F` and a morphism of schemes `h : U ⟶ V` forming a commutative square
`a ≫ f.hom = h_h ≫ b`. -/
theorem exists_etaleAtlas_over {F G : AlgSpace.{u}} (f : F ⟶ G)
    {V : Scheme.{u}} {b : yoneda.obj V ⟶ G.obj} (hb : EtaleAtlas b) :
    ∃ (U : Scheme.{u}) (a : yoneda.obj U ⟶ F.obj) (h : U ⟶ V),
      EtaleAtlas a ∧ a ≫ f.hom = yoneda.map h ≫ b := by
  have : MorphismProperty.RespectsIso @Etale.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : (MorphismProperty.presheaf @Etale.{u}).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) (P := @Etale.{u})
  have : (MorphismProperty.presheaf @Surjective.{u}).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) (P := @Surjective.{u})
  have hM : IsAlgebraicSpace (Limits.pullback f.hom b) :=
    isAlgebraicSpace_pullback f.hom b F.property (.yoneda_obj V) G.property
  obtain ⟨U, m, hm⟩ := hM.exists_etaleAtlas
  refine ⟨U, m ≫ Limits.pullback.fst f.hom b,
    yoneda.preimage (m ≫ Limits.pullback.snd f.hom b),
    hm.comp_of_presheaf (MorphismProperty.pullback_fst f.hom b hb.etale)
      (MorphismProperty.pullback_fst f.hom b hb.surjective), ?_⟩
  simp [Limits.pullback.condition]

/-- Every morphism `f : F ⟶ G` of algebraic spaces fits into a commutative square
`a ≫ f.hom = h_h ≫ b` where both `a : h_U ⟶ F` and `b : h_V ⟶ G` are étale atlases and `h : U ⟶ V`
is a morphism of schemes. -/
theorem exists_etaleAtlas_commSq {F G : AlgSpace.{u}} (f : F ⟶ G) :
    ∃ (U V : Scheme.{u}) (a : yoneda.obj U ⟶ F.obj) (b : yoneda.obj V ⟶ G.obj) (h : U ⟶ V),
      EtaleAtlas a ∧ EtaleAtlas b ∧ a ≫ f.hom = yoneda.map h ≫ b := by
  obtain ⟨V, b, hb⟩ := G.property.exists_etaleAtlas
  obtain ⟨U, a, h, ha, w⟩ := exists_etaleAtlas_over f hb
  exact ⟨U, V, a, b, h, ha, hb, w⟩

end AlgSpace

/-- A property `P` of morphisms of schemes extends to a property `EtaleLocal P` of morphisms of
algebraic spaces: `f : F ⟶ G` satisfies `EtaleLocal P` if there exist an étale atlas
`a : h_U ⟶ F`, a morphism `b : h_V ⟶ G` representable by étale morphisms of schemes, and a
morphism of schemes `h : U ⟶ V` satisfying `P h` such that `a ≫ f.hom = h_h ≫ b`
(Stacks, Definition 66.16.1 (04RD)).

When `P` is local at the source and at the target for `Scheme.etalePrecoverage` and respects
postcomposition with open immersions, `EtaleLocal P f` is independent of the choice of étale
square (`EtaleLocal.iff_forall_square`, Stacks, Lemma 67.22.1 (03MJ)). -/
@[stacks 04RD]
def EtaleLocal (P : MorphismProperty Scheme.{u}) ⦃F G : AlgSpace.{u}⦄ (f : F ⟶ G) : Prop :=
  ∃ (U V : Scheme.{u}) (a : yoneda.obj U ⟶ F.obj) (b : yoneda.obj V ⟶ G.obj) (h : U ⟶ V),
    EtaleAtlas a ∧ MorphismProperty.presheaf @Etale b ∧ a ≫ f.hom = yoneda.map h ≫ b ∧ P h

/-- Unfolds `EtaleLocal P f` to its existential chart presentation. -/
theorem etaleLocal_iff {P : MorphismProperty Scheme.{u}} {F G : AlgSpace.{u}} (f : F ⟶ G) :
    EtaleLocal P f ↔
      ∃ (U V : Scheme.{u}) (a : yoneda.obj U ⟶ F.obj) (b : yoneda.obj V ⟶ G.obj) (h : U ⟶ V),
        EtaleAtlas a ∧ MorphismProperty.presheaf @Etale b ∧ a ≫ f.hom = yoneda.map h ≫ b ∧ P h :=
  Iff.rfl

namespace EtaleLocal

section Basic

/-- `EtaleLocal` is monotone in the scheme morphism property `P`. -/
theorem mono {P Q : MorphismProperty Scheme.{u}} {F G : AlgSpace.{u}} {f : F ⟶ G}
    (hf : EtaleLocal P f) (hPQ : P ≤ Q) : EtaleLocal Q f := by
  obtain ⟨U, V, a, b, h, ha, hb, w, hh⟩ := hf
  exact ⟨U, V, a, b, h, ha, hb, w, hPQ h hh⟩

/-- `EtaleLocal` as a monotone map from scheme morphism properties to algebraic-space morphism
properties. -/
theorem monotone : Monotone EtaleLocal.{u} :=
  fun _ _ hPQ _ _ _ hf ↦ hf.mono hPQ

/-- If a morphism of schemes `f : X ⟶ Y` satisfies `P`, then `AlgSpace.ofScheme.map f` satisfies
`EtaleLocal P`. -/
theorem ofScheme {P : MorphismProperty Scheme.{u}} {X Y : Scheme.{u}} {f : X ⟶ Y} (hf : P f) :
    EtaleLocal P (AlgSpace.ofScheme.map f) :=
  ⟨X, Y, 𝟙 (yoneda.obj X), 𝟙 (yoneda.obj Y), f, .of_isIso (𝟙 (yoneda.obj X)),
    (EtaleAtlas.of_isIso (𝟙 (yoneda.obj Y))).etale,
    (Category.id_comp (yoneda.map f)).trans (Category.comp_id (yoneda.map f)).symm, hf⟩

/-- Any morphism `f : F ⟶ G` of algebraic spaces whose underlying presheaf map satisfies
`MorphismProperty.presheaf P` satisfies `EtaleLocal P`. -/
theorem of_presheaf {P : MorphismProperty Scheme.{u}} {F G : AlgSpace.{u}} {f : F ⟶ G}
    (hf : MorphismProperty.presheaf P f.hom) : EtaleLocal P f := by
  obtain ⟨V, b, hb⟩ := G.property.exists_etaleAtlas
  exact ⟨hf.rep.pullback b, V, hf.rep.fst b, b, hf.rep.snd b,
    hb.of_isPullback (hf.rep.isPullback b).flip, hb.etale, hf.rep.w b, hf.property_snd b⟩

/-- `EtaleLocal P` respects isomorphisms in `AlgSpace` for any scheme morphism property `P`. -/
instance respectsIso (P : MorphismProperty Scheme.{u}) :
    MorphismProperty.RespectsIso (EtaleLocal P) where
  precomp {F' F G} e _ f := by
    rintro ⟨U, V, a, b, h, ha, hb, w, hh⟩
    let eIso : F.obj ≅ F'.obj := AlgSpace.toPresheaf.mapIso (asIso e).symm
    refine ⟨U, V, a ≫ eIso.hom, b, h, ha.comp_iso eIso, hb, ?_, hh⟩
    have he : eIso.hom ≫ e.hom = 𝟙 F.obj := by simp [eIso]
    calc
      (a ≫ eIso.hom) ≫ (e ≫ f).hom = a ≫ (eIso.hom ≫ e.hom) ≫ f.hom := by simp [Category.assoc]
      _ = a ≫ f.hom := by simp [he]
      _ = yoneda.map h ≫ b := w
  postcomp {F G G'} e _ f := by
    rintro ⟨U, V, a, b, h, ha, hb, w, hh⟩
    have : MorphismProperty.RespectsIso @Etale.{u} :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    have : IsIso e.hom := inferInstanceAs (IsIso (AlgSpace.toPresheaf.map e))
    refine ⟨U, V, a, b ≫ e.hom, h, ha,
      (MorphismProperty.relative_respectsIso @Etale.{u}).postcomp _ e.hom _ hb, ?_, hh⟩
    simpa [Category.assoc] using w =≫ e.hom

/-- If `P` contains identities of schemes, then `EtaleLocal P` contains identities of algebraic
spaces. -/
instance containsIdentities (P : MorphismProperty Scheme.{u}) [P.ContainsIdentities] :
    MorphismProperty.ContainsIdentities (EtaleLocal P) where
  id_mem F := by
    obtain ⟨U, a, ha⟩ := F.property.exists_etaleAtlas
    exact ⟨U, U, a, a, 𝟙 U, ha, ha.etale, by simp, P.id_mem U⟩

/-- If `P` contains identities, the identity morphism of any algebraic space satisfies
`EtaleLocal P`. -/
theorem id {P : MorphismProperty Scheme.{u}} [P.ContainsIdentities] {F : AlgSpace.{u}} :
    EtaleLocal P (𝟙 F) :=
  MorphismProperty.id_mem (EtaleLocal P) F

end Basic

section BaseChange

variable {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]

/-- If `P` is stable under base change of schemes, then `EtaleLocal P` is preserved along any
pullback square in `AlgSpace`. -/
theorem of_isPullback {W F G H : AlgSpace.{u}} {fst : W ⟶ F} {snd : W ⟶ G}
    {f : F ⟶ H} {g : G ⟶ H} (hf : EtaleLocal P f) (sq : IsPullback fst snd f g) :
    EtaleLocal P snd := by
  obtain ⟨U, V, a, b, h, ha, hb, w, hh⟩ := hf
  obtain ⟨Z, c, hc⟩ := G.property.exists_etaleAtlas
  let v₁ : hb.rep.pullback (c ≫ g.hom) ⟶ V := hb.rep.fst' (c ≫ g.hom)
  let v₂ : hb.rep.pullback (c ≫ g.hom) ⟶ Z := hb.rep.snd (c ≫ g.hom)
  have hv₂ : Etale v₂ := hb.property_snd (c ≫ g.hom)
  let u₁ : pullback h v₁ ⟶ U := pullback.fst h v₁
  let h' : pullback h v₁ ⟶ hb.rep.pullback (c ≫ g.hom) := pullback.snd h v₁
  have sqU' : IsPullback (yoneda.map u₁) (yoneda.map (h' ≫ v₂)) (a ≫ f.hom) (c ≫ g.hom) := by
    have sq₀ := ((IsPullback.of_hasPullback h v₁).map yoneda).paste_vert
      (hb.rep.isPullback' (c ≫ g.hom))
    rwa [← yoneda.map_comp, ← w] at sq₀
  have sqP : IsPullback fst.hom snd.hom f.hom g.hom := sq.map AlgSpace.toPresheaf
  refine ⟨pullback h v₁, hb.rep.pullback (c ≫ g.hom),
    sqP.lift (yoneda.map u₁ ≫ a) (yoneda.map (h' ≫ v₂) ≫ c)
      (by simpa only [Category.assoc] using sqU'.w),
    yoneda.map v₂ ≫ c, h', ha.lift_isPullback hc sqP sqU',
    presheaf_etale_yoneda_map_comp v₂ hc.etale, ?_, P.pullback_snd h v₁ hh⟩
  simp [sqP.lift_snd]

instance isStableUnderBaseChange (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange] :
    MorphismProperty.IsStableUnderBaseChange (EtaleLocal P) where
  of_isPullback sq hf := hf.of_isPullback sq

/-- If `P` is stable under base change of schemes and `f : F ⟶ H` satisfies `EtaleLocal P`, then
the second projection `AlgSpace.pullbackSnd f g : AlgSpace.pullbackObj f g ⟶ G` satisfies
`EtaleLocal P` (Stacks, Section 67.22 (03MJ, 04RD)). -/
theorem baseChange {F G H : AlgSpace.{u}} {f : F ⟶ H} (hf : EtaleLocal P f) (g : G ⟶ H) :
    EtaleLocal P (AlgSpace.pullbackSnd f g) :=
  hf.of_isPullback (AlgSpace.isPullback f g)

/-- First-projection counterpart of `EtaleLocal.baseChange`: if `g : G ⟶ H` satisfies
`EtaleLocal P`, then `AlgSpace.pullbackFst f g : AlgSpace.pullbackObj f g ⟶ F` satisfies
`EtaleLocal P`. -/
theorem baseChange_fst {F G H : AlgSpace.{u}} {g : G ⟶ H} (hg : EtaleLocal P g) (f : F ⟶ H) :
    EtaleLocal P (AlgSpace.pullbackFst f g) :=
  hg.of_isPullback (AlgSpace.isPullback f g).flip

end BaseChange

section Comparison

variable {P : MorphismProperty Scheme.{u}}
  [P.IsLocalAtSource Scheme.etalePrecoverage] [P.IsLocalAtTarget Scheme.etalePrecoverage]
  [P.RespectsRight @IsOpenImmersion]

/-- **Independence of the étale square** (Stacks, Lemma 67.22.1 (03MJ)). If `f : F ⟶ G` satisfies
`EtaleLocal P`, then on *every* commutative square `a' ≫ f.hom = h_{h'} ≫ b'` with `a'` and `b'`
representable by étale morphisms of schemes, the top scheme morphism `h'` satisfies `P`. -/
@[stacks 03MJ]
theorem of_commSq {F G : AlgSpace.{u}} {f : F ⟶ G} (hf : EtaleLocal P f)
    {U' V' : Scheme.{u}} {a' : yoneda.obj U' ⟶ F.obj} {b' : yoneda.obj V' ⟶ G.obj}
    {h' : U' ⟶ V'} (ha' : MorphismProperty.presheaf @Etale a')
    (hb' : MorphismProperty.presheaf @Etale b') (w' : a' ≫ f.hom = yoneda.map h' ≫ b') :
    P h' := by
  obtain ⟨U, V, a, b, h, ha, hb, w, hh⟩ := hf
  let v₁ : hb.rep.pullback b' ⟶ V := hb.rep.fst' b'
  let v₂ : hb.rep.pullback b' ⟶ V' := hb.rep.snd b'
  have sqV : IsPullback (yoneda.map v₁) (yoneda.map v₂) b b' := hb.rep.isPullback' b'
  have hv₁ : Etale v₁ := hb'.property b _ _ sqV.flip
  have hv₂ : Etale v₂ := hb.property_snd b'
  let u₁ : ha.relativelyRepresentable.pullback a' ⟶ U := ha.relativelyRepresentable.fst' a'
  let u₂ : ha.relativelyRepresentable.pullback a' ⟶ U' := ha.relativelyRepresentable.snd a'
  have sqU : IsPullback (yoneda.map u₁) (yoneda.map u₂) a a' :=
    ha.relativelyRepresentable.isPullback' a'
  have hu₁ : Etale u₁ := ha'.property a _ _ sqU.flip
  have hu₂_et : Etale u₂ := ha.etale_snd a'
  have hu₂_surj : Surjective u₂ := ha.surjective_snd a'
  have hcompat : yoneda.map (u₁ ≫ h) ≫ b = yoneda.map (u₂ ≫ h') ≫ b' := by
    calc
      yoneda.map (u₁ ≫ h) ≫ b = yoneda.map u₁ ≫ yoneda.map h ≫ b := by simp
      _ = (yoneda.map u₁ ≫ a) ≫ f.hom := by rw [← w, Category.assoc]
      _ = (yoneda.map u₂ ≫ a') ≫ f.hom := by rw [sqU.w]
      _ = yoneda.map u₂ ≫ yoneda.map h' ≫ b' := by rw [Category.assoc, w']
      _ = yoneda.map (u₂ ≫ h') ≫ b' := by simp
  let h'' : ha.relativelyRepresentable.pullback a' ⟶ hb.rep.pullback b' :=
    yoneda.preimage (sqV.lift (yoneda.map (u₁ ≫ h)) (yoneda.map (u₂ ≫ h')) hcompat)
  have w₁ : u₁ ≫ h = h'' ≫ v₁ := yoneda.map_injective (by simp [h''])
  have w₂ : u₂ ≫ h' = h'' ≫ v₂ := yoneda.map_injective (by simp [h''])
  exact MorphismProperty.of_etale_surjective_commSq u₂ v₂ w₂
    (MorphismProperty.of_etale_commSq u₁ v₁ w₁ hh)

/-- For `P` étale-local on source and target and respecting postcomposition with open immersions,
`EtaleLocal P f` holds if and only if `P h` holds on *every* commutative square
`a ≫ f.hom = h_h ≫ b` with `a` and `b` representable by étale morphisms of schemes
(Stacks, Lemma 67.22.1 (03MJ)). -/
@[stacks 03MJ]
theorem iff_forall_square {F G : AlgSpace.{u}} (f : F ⟶ G) :
    EtaleLocal P f ↔
      ∀ ⦃U V : Scheme.{u}⦄ (a : yoneda.obj U ⟶ F.obj) (b : yoneda.obj V ⟶ G.obj) (h : U ⟶ V),
        MorphismProperty.presheaf @Etale a → MorphismProperty.presheaf @Etale b →
          a ≫ f.hom = yoneda.map h ≫ b → P h := by
  refine ⟨fun hf _ _ a b h ha hb w ↦ hf.of_commSq ha hb w, fun H ↦ ?_⟩
  obtain ⟨U, V, a, b, h, ha, hb, w⟩ := AlgSpace.exists_etaleAtlas_commSq f
  exact ⟨U, V, a, b, h, ha, hb.etale, w, H a b h ha.etale hb.etale w⟩

/-- On morphisms of schemes embedded via `AlgSpace.ofScheme`, `EtaleLocal P` agrees with `P`. -/
@[simp]
theorem ofScheme_iff {X Y : Scheme.{u}} (f : X ⟶ Y) :
    EtaleLocal P (AlgSpace.ofScheme.map f) ↔ P f :=
  ⟨fun hf ↦ hf.of_commSq (EtaleAtlas.of_isIso (𝟙 (yoneda.obj X))).etale
    (EtaleAtlas.of_isIso (𝟙 (yoneda.obj Y))).etale
    ((Category.id_comp (yoneda.map f)).trans (Category.comp_id (yoneda.map f)).symm), ofScheme⟩

/-- If `P` is also stable under composition, then `EtaleLocal P` is closed under composition of
morphisms of algebraic spaces. -/
theorem comp [P.IsStableUnderComposition] {F G H : AlgSpace.{u}} {f : F ⟶ G} {g : G ⟶ H}
    (hf : EtaleLocal P f) (hg : EtaleLocal P g) : EtaleLocal P (f ≫ g) := by
  obtain ⟨W, c, hc⟩ := H.property.exists_etaleAtlas
  obtain ⟨V, b, h₂, hb, w₂⟩ := AlgSpace.exists_etaleAtlas_over g hc
  obtain ⟨U, a, h₁, ha, w₁⟩ := AlgSpace.exists_etaleAtlas_over f hb
  refine ⟨U, W, a, c, h₁ ≫ h₂, ha, hc.etale, ?_,
    P.comp_mem h₁ h₂ (hf.of_commSq ha.etale hb.etale w₁) (hg.of_commSq hb.etale hc.etale w₂)⟩
  calc
    a ≫ (f ≫ g).hom = (a ≫ f.hom) ≫ g.hom := by simp [Category.assoc]
    _ = yoneda.map h₁ ≫ b ≫ g.hom := by rw [w₁, Category.assoc]
    _ = yoneda.map (h₁ ≫ h₂) ≫ c := by simp [w₂]

instance isStableUnderComposition (P : MorphismProperty Scheme.{u})
    [P.IsLocalAtSource Scheme.etalePrecoverage] [P.IsLocalAtTarget Scheme.etalePrecoverage]
    [P.RespectsRight @IsOpenImmersion] [P.IsStableUnderComposition] :
    MorphismProperty.IsStableUnderComposition (EtaleLocal P) where
  comp_mem _ _ hf hg := hf.comp hg

instance isMultiplicative (P : MorphismProperty Scheme.{u})
    [P.IsLocalAtSource Scheme.etalePrecoverage] [P.IsLocalAtTarget Scheme.etalePrecoverage]
    [P.RespectsRight @IsOpenImmersion] [P.IsMultiplicative] :
    MorphismProperty.IsMultiplicative (EtaleLocal P) where

/-- For a morphism `f : F ⟶ G` of algebraic spaces whose underlying presheaf morphism is
representable by schemes, `EtaleLocal P f` agrees with `MorphismProperty.presheaf P f.hom`
(Stacks, Lemma 67.22.1 (03MJ)). -/
@[stacks 03MJ]
theorem iff_presheaf [P.IsStableUnderBaseChange] {F G : AlgSpace.{u}} {f : F ⟶ G}
    (hr : yoneda.relativelyRepresentable f.hom) :
    EtaleLocal P f ↔ MorphismProperty.presheaf P f.hom := by
  refine ⟨fun hf ↦ MorphismProperty.relative_of_snd hr fun T y ↦ ?_, of_presheaf⟩
  have sq : IsPullback (ObjectProperty.homMk (hr.fst y) : AlgSpace.ofScheme.obj _ ⟶ F)
      (AlgSpace.ofScheme.map (hr.snd y)) f (ObjectProperty.homMk y) := by
    apply IsPullback.of_map_of_faithful AlgSpace.toPresheaf.{u}
    exact hr.isPullback y
  exact (ofScheme_iff (hr.snd y)).1 (hf.of_isPullback sq)

/-- Any morphism from an embedded scheme to an algebraic space is representable by schemes, so
`EtaleLocal P` on it agrees with `MorphismProperty.presheaf P`. -/
theorem iff_presheaf_of_ofScheme [P.IsStableUnderBaseChange] {U : Scheme.{u}} {G : AlgSpace.{u}}
    (f : AlgSpace.ofScheme.obj U ⟶ G) :
    EtaleLocal P f ↔ MorphismProperty.presheaf P f.hom :=
  iff_presheaf (AlgSpace.ofScheme_relativelyRepresentable f)

end Comparison

end EtaleLocal

/-- Any morphism `f : AlgSpace.ofScheme.obj U ⟶ F` whose underlying presheaf map is an étale atlas
is étale as a morphism of algebraic spaces (`EtaleLocal @Etale f`). -/
theorem EtaleAtlas.etaleLocal {U : Scheme.{u}} {F : AlgSpace.{u}}
    {f : AlgSpace.ofScheme.obj U ⟶ F} (hf : EtaleAtlas f.hom) :
    EtaleLocal @Etale f :=
  EtaleLocal.of_presheaf hf.etale

end TauCeti.AlgebraicGeometry.Spaces
