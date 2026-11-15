/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import TauCeti.AlgebraicGeometry.Morphisms.Etale.Basic
public import TauCeti.CategoryTheory.MorphismProperty.CommaSites
public import TauCeti.CategoryTheory.MorphismProperty.Over.Pullback

/-!
# The base-change functor and pseudofunctor of small étale sites

For a morphism of schemes `f : X ⟶ Y`, pulling back along `f` defines the base-change functor
`f.smallEtaleBaseChange : Y.Etale ⥤ X.Etale` sending an étale `Y`-scheme `V ⟶ Y` to `V ×_Y X ⟶ X`.

This file develops the geometric, site-theoretic, and 2-categorical properties of
`f.smallEtaleBaseChange`:

* **Pointwise covering sieves**: `AlgebraicGeometry.Scheme.mem_smallEtaleTopology_iff_forall_exists`
  characterizes covering sieves in `smallEtaleTopology X` as sieves whose arrows are jointly
  surjective on underlying points (using automatic étaleness of morphisms in `X.Etale`).
* **General small-site base change**:
  `AlgebraicGeometry.Scheme.Hom.coverPreserving_smallGrothendieckTopology` and
  `AlgebraicGeometry.Scheme.Hom.isContinuous_smallGrothendieckTopology` prove that for morphism
  properties `P ≤ Q` on `Scheme`, base change on `Q.Over ⊤` is cover-preserving and continuous for
  the `P`-small Grothendieck topologies.
* **Pullback squares, surjectivity, and morphism of sites**: `f.smallEtaleBaseChange` sends objects
  and morphisms of `Y.Etale` to cartesian squares over `Y`, preserves emptiness over an empty base
  and joint surjectivity of covering families, preserves finite limits, is representably flat, is
  cover-preserving (`AlgebraicGeometry.Scheme.Hom.coverPreserving_smallEtaleBaseChange`), and is
  continuous for `smallEtaleTopology` (hence defines a morphism of sites `(X_ét) → (Y_ét)` in the
  sense of SGA 4 IV 4.9 / `Mathlib.CategoryTheory.Sites.Pullback`).
* **Functoriality, coherence, and pseudofunctor**: we provide the identity, congruence, composition,
  and commutative-square comparison isomorphisms (`AlgebraicGeometry.Scheme.smallEtaleBaseChangeId`,
  `AlgebraicGeometry.Scheme.Hom.smallEtaleBaseChangeCongr`,
  `AlgebraicGeometry.Scheme.Hom.smallEtaleBaseChangeComp`,
  `AlgebraicGeometry.Scheme.Hom.smallEtaleBaseChangeCommSqIso`, and
  `AlgebraicGeometry.Scheme.Hom.smallEtaleBaseChangeConditionIso`), their associativity and unit
  coherence theorems, and the contravariant pseudofunctor
  `AlgebraicGeometry.Scheme.smallEtalePseudofunctor`
  (`LocallyDiscrete Scheme.{u}ᵒᵖ ⥤ᵖ Cat.{u, u + 1}`) sending `X` to `X.Etale` and `f` to
  `f.smallEtaleBaseChange`.

## References

* The Stacks Project, [Tag 021I](https://stacks.math.columbia.edu/tag/021I) (the base-change
  functor of small étale sites defines a morphism of sites) and
  [Tag 021J](https://stacks.math.columbia.edu/tag/021J) (2-functoriality of small-étale base
  change).
-/

public section

universe u

open CategoryTheory Bicategory Category Limits MorphismProperty

namespace AlgebraicGeometry.Scheme

/-- A sieve `R` on `U : X.Etale` belongs to `smallEtaleTopology X` if and only if every point of
`U` lies in the image of some arrow in `R`. -/
lemma mem_smallEtaleTopology_iff_forall_exists {X : Scheme.{u}} {U : X.Etale} (R : Sieve U) :
    R ∈ smallEtaleTopology X U ↔
      ∀ x : U.left, ∃ (V : X.Etale) (g : V ⟶ U) (v : V.left), R g ∧ g.left v = x := by
  let ι := Σ V : X.Etale, {g : V ⟶ U // R g}
  have hR : Sieve.ofArrows (fun s : ι ↦ s.1) (fun s : ι ↦ s.2.1) = R := by
    ext V g
    constructor
    · rintro ⟨_, u, _, ⟨s⟩, fac⟩
      exact fac ▸ R.downward_closed s.2.2 u
    · intro hg
      let s : ι := ⟨V, ⟨g, hg⟩⟩
      exact ⟨s.1, 𝟙 s.1, s.2.1, Presieve.ofArrows.mk s, id_comp g⟩
  constructor
  · intro h x
    have hx : x ∈ ⋃ s : ι, Set.range s.2.1.left := by
      rw [(ofArrows_mem_smallEtaleTopology_iff _).mp (hR.symm ▸ h)]
      exact Set.mem_univ x
    rcases Set.mem_iUnion.mp hx with ⟨⟨V, g, hg⟩, v, hv⟩
    exact ⟨V, g, v, hg, hv⟩
  · intro h
    rw [← hR, ofArrows_mem_smallEtaleTopology_iff]
    refine Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.mpr ?_
    rcases h x with ⟨V, g, v, hg, hv⟩
    exact ⟨⟨V, g, hg⟩, v, hv⟩

namespace Hom

section SmallSite

/-- For morphism properties `P ≤ Q` on `Scheme`, base change along `f : X ⟶ Y` is cover-preserving
for the `P`-small Grothendieck topologies on `Q.Over ⊤ Y` and `Q.Over ⊤ X`. -/
theorem coverPreserving_smallGrothendieckTopology
    {P Q : MorphismProperty Scheme.{u}} [P.IsMultiplicative] [P.IsStableUnderBaseChange]
    [Q.IsStableUnderComposition] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Q.HasPullbacksAlong f] [Q.IsStableUnderBaseChangeAlong f] (hPQ : P ≤ Q) :
    CoverPreserving (Y.smallGrothendieckTopology P) (X.smallGrothendieckTopology P)
      (MorphismProperty.Over.pullback Q ⊤ f) :=
  have := Y.locallyCoverDense_of_le hPQ
  MorphismProperty.Over.coverPreserving_pullback_restrictedTopology Q
    (Scheme.grothendieckTopology P) f

/-- For morphism properties `P ≤ Q` on `Scheme`, base change along `f : X ⟶ Y` is continuous for
the `P`-small Grothendieck topologies on `Q.Over ⊤ Y` and `Q.Over ⊤ X`. -/
theorem isContinuous_smallGrothendieckTopology
    {P Q : MorphismProperty Scheme.{u}} [P.IsMultiplicative] [P.IsStableUnderBaseChange]
    [Q.IsMultiplicative] [Q.IsStableUnderBaseChange] [Q.HasOfPostcompProperty Q]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hPQ : P ≤ Q) :
    (MorphismProperty.Over.pullback Q ⊤ f).IsContinuous
      (Y.smallGrothendieckTopology P) (X.smallGrothendieckTopology P) :=
  have := Y.locallyCoverDense_of_le hPQ
  MorphismProperty.Over.isContinuous_pullback_restrictedTopology Q
    (Scheme.grothendieckTopology P) f

instance isContinuous_smallGrothendieckTopology_self
    {P : MorphismProperty Scheme.{u}} [P.IsMultiplicative] [P.IsStableUnderBaseChange]
    [P.HasOfPostcompProperty P] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (MorphismProperty.Over.pullback P ⊤ f).IsContinuous
      (Y.smallGrothendieckTopology P) (X.smallGrothendieckTopology P) :=
  isContinuous_smallGrothendieckTopology f le_rfl

end SmallSite

section BaseChange

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Base change along `f : X ⟶ Y`, from schemes étale over `Y` to schemes étale over `X`: an étale
`V ⟶ Y` is sent to `V ×_Y X ⟶ X`. -/
@[expose]
noncomputable def smallEtaleBaseChange : Y.Etale ⥤ X.Etale :=
  MorphismProperty.Over.pullback @Etale ⊤ f

/-- On underlying schemes over `X`, `f.smallEtaleBaseChange` is base change along `f`. -/
@[expose]
noncomputable def smallEtaleBaseChangeCompForgetIso :
    f.smallEtaleBaseChange ⋙ Etale.forget X ≅ Etale.forget Y ⋙ CategoryTheory.Over.pullback f :=
  MorphismProperty.Over.pullbackCompForgetIso (P := @Etale) (Q := ⊤) f

@[simp]
lemma smallEtaleBaseChange_obj_left (V : Y.Etale) :
    (f.smallEtaleBaseChange.obj V).left = Limits.pullback V.hom f :=
  (rfl)

@[simp]
lemma smallEtaleBaseChange_obj_hom (V : Y.Etale) :
    (f.smallEtaleBaseChange.obj V).hom = Limits.pullback.snd V.hom f :=
  (rfl)

@[simp]
lemma smallEtaleBaseChange_obj_mk {Z : Scheme.{u}} (g : Z ⟶ Y) [Etale g] :
    f.smallEtaleBaseChange.obj (Etale.mk g) = Etale.mk (Limits.pullback.snd g f) :=
  (rfl)

@[simp, reassoc]
lemma smallEtaleBaseChange_map_left_fst {V W : Y.Etale} (g : V ⟶ W) :
    (f.smallEtaleBaseChange.map g).left ≫ Limits.pullback.fst W.hom f =
      Limits.pullback.fst V.hom f ≫ g.left :=
  MorphismProperty.Over.pullback_map_left_fst f g

@[simp, reassoc]
lemma smallEtaleBaseChange_map_left_snd {V W : Y.Etale} (g : V ⟶ W) :
    (f.smallEtaleBaseChange.map g).left ≫ Limits.pullback.snd W.hom f =
      Limits.pullback.snd V.hom f :=
  MorphismProperty.Over.pullback_map_left_snd f g

/-- Two morphisms in `X.Etale` into `f.smallEtaleBaseChange.obj V` are equal as soon as their
compositions with the first projection `pullback.fst V.hom f` agree. -/
lemma smallEtaleBaseChange_hom_ext {f : X ⟶ Y} {U : X.Etale} {V : Y.Etale}
    {u v : U ⟶ f.smallEtaleBaseChange.obj V}
    (h : u.left ≫ Limits.pullback.fst V.hom f = v.left ≫ Limits.pullback.fst V.hom f) :
    u = v :=
  MorphismProperty.Over.pullback_hom_ext h

/-- For `V : Y.Etale`, `f.smallEtaleBaseChange.obj V` fits into a cartesian square over `f : X ⟶ Y`
with top morphism `pullback.fst V.hom f`. -/
lemma isPullback_smallEtaleBaseChange_obj (V : Y.Etale) :
    IsPullback (Limits.pullback.fst V.hom f) (f.smallEtaleBaseChange.obj V).hom V.hom f :=
  MorphismProperty.Over.isPullback_pullback_obj f V

/-- For a morphism `g : V ⟶ W` in `Y.Etale`, `f.smallEtaleBaseChange.map g` fits into a cartesian
square with `g.left` along the first projections. -/
lemma isPullback_smallEtaleBaseChange_map {V W : Y.Etale} (g : V ⟶ W) :
    IsPullback (Limits.pullback.fst V.hom f) (f.smallEtaleBaseChange.map g).left
      g.left (Limits.pullback.fst W.hom f) :=
  MorphismProperty.Over.isPullback_pullback_map f g

/-- Over an empty scheme `X`, every object in the essential image of `f.smallEtaleBaseChange` has
empty underlying scheme. -/
instance isEmpty_smallEtaleBaseChange_obj_left [IsEmpty X] (V : Y.Etale) :
    IsEmpty (f.smallEtaleBaseChange.obj V).left :=
  Function.isEmpty (Limits.pullback.snd V.hom f)

/-- Base change along `f` sends an empty étale `Y`-scheme to an empty étale `X`-scheme. -/
instance isEmpty_smallEtaleBaseChange_obj_left_of_left (V : Y.Etale) [IsEmpty V.left] :
    IsEmpty (f.smallEtaleBaseChange.obj V).left :=
  @Function.isEmpty _ V.left ‹IsEmpty V.left› (Limits.pullback.fst V.hom f)

/-- Base change along `f` preserves surjectivity of morphisms in `Y.Etale`. -/
instance surjective_smallEtaleBaseChange_map {V W : Y.Etale} (g : V ⟶ W) [Surjective g.left] :
    Surjective (f.smallEtaleBaseChange.map g).left :=
  MorphismProperty.of_isPullback (f.isPullback_smallEtaleBaseChange_map g) ‹Surjective g.left›

/-- Base change along `f` preserves joint surjectivity of families of morphisms in `Y.Etale`. -/
lemma iUnion_range_smallEtaleBaseChange_map_eq_univ {W : Y.Etale} {ι : Type*} {Z : ι → Y.Etale}
    (g : ∀ i, Z i ⟶ W) (hg : ⋃ i, Set.range (g i).left = Set.univ) :
    ⋃ i, Set.range (f.smallEtaleBaseChange.map (g i)).left = Set.univ := by
  refine Set.eq_univ_of_forall fun w' ↦ Set.mem_iUnion.mpr ?_
  have hw : Limits.pullback.fst W.hom f w' ∈ ⋃ i, Set.range (g i).left :=
    hg.symm ▸ Set.mem_univ _
  rcases Set.mem_iUnion.mp hw with ⟨i, z, hz⟩
  obtain ⟨p, _, hp⟩ :=
    Scheme.exists_preimage_of_isPullback (f.isPullback_smallEtaleBaseChange_map (g i)) z w' hz
  exact ⟨i, p, hp⟩

/-- Base change along `f` sends jointly covering families in `smallEtaleTopology Y` to jointly
covering families in `smallEtaleTopology X`. -/
lemma ofArrows_smallEtaleBaseChange_mem_smallEtaleTopology {W : Y.Etale} {ι : Type*}
    {Z : ι → Y.Etale} {g : ∀ i, Z i ⟶ W}
    (hg : Sieve.ofArrows Z g ∈ smallEtaleTopology Y W) :
    Sieve.ofArrows (fun i ↦ f.smallEtaleBaseChange.obj (Z i))
      (fun i ↦ f.smallEtaleBaseChange.map (g i)) ∈
        smallEtaleTopology X (f.smallEtaleBaseChange.obj W) :=
  (ofArrows_mem_smallEtaleTopology_iff _).mpr <|
    f.iUnion_range_smallEtaleBaseChange_map_eq_univ g <|
      (ofArrows_mem_smallEtaleTopology_iff g).mp hg

/-- Base change along `f : X ⟶ Y` preserves finite limits on small étale sites. -/
noncomputable instance preservesFiniteLimits_smallEtaleBaseChange :
    PreservesFiniteLimits f.smallEtaleBaseChange :=
  have := preservesFiniteLimits_of_natIso f.smallEtaleBaseChangeCompForgetIso.symm
  preservesFiniteLimits_of_reflects_of_preserves f.smallEtaleBaseChange (Etale.forget X)

/-- Base change along `f : X ⟶ Y` is representably flat on small étale sites. -/
instance representablyFlat_smallEtaleBaseChange :
    RepresentablyFlat f.smallEtaleBaseChange :=
  flat_of_preservesFiniteLimits f.smallEtaleBaseChange

/-- Base change along `f : X ⟶ Y` preserves covering sieves for the small étale topologies
(Stacks, Tag 021I). -/
theorem coverPreserving_smallEtaleBaseChange :
    CoverPreserving (smallEtaleTopology Y) (smallEtaleTopology X) f.smallEtaleBaseChange :=
  coverPreserving_smallGrothendieckTopology (P := @Etale) (Q := @Etale) f le_rfl

/-- Base change along `f : X ⟶ Y` is continuous for the small étale topologies, so together with
`representablyFlat_smallEtaleBaseChange` it defines a morphism of small étale sites
(Stacks, Tag 021I). -/
instance isContinuous_smallEtaleBaseChange :
    f.smallEtaleBaseChange.IsContinuous (smallEtaleTopology Y) (smallEtaleTopology X) :=
  Functor.isContinuous_of_coverPreserving
    (compatiblePreservingOfFlat _ _)
    f.coverPreserving_smallEtaleBaseChange

end BaseChange

end Hom

section Functoriality

/-- Base change of small étale sites along `𝟙 X` is naturally isomorphic to the identity functor,
with forward component `pullback.fst V.hom (𝟙 X)` (Stacks, Tag 021J). -/
@[expose]
noncomputable def smallEtaleBaseChangeId (X : Scheme.{u}) :
    Hom.smallEtaleBaseChange (𝟙 X) ≅ 𝟭 X.Etale :=
  MorphismProperty.Over.pullbackId @Etale ⊤ X

@[simp]
lemma smallEtaleBaseChangeId_hom_app_left (X : Scheme.{u}) (V : X.Etale) :
    ((smallEtaleBaseChangeId X).hom.app V).left = Limits.pullback.fst V.hom (𝟙 X) :=
  MorphismProperty.Over.pullbackId_hom_app_left rfl V

@[simp, reassoc]
lemma smallEtaleBaseChangeId_inv_app_left_fst (X : Scheme.{u}) (V : X.Etale) :
    ((smallEtaleBaseChangeId X).inv.app V).left ≫ Limits.pullback.fst V.hom (𝟙 X) = 𝟙 V.left :=
  MorphismProperty.Over.pullbackId_inv_app_left_fst rfl V

@[simp, reassoc]
lemma smallEtaleBaseChangeId_inv_app_left_snd (X : Scheme.{u}) (V : X.Etale) :
    ((smallEtaleBaseChangeId X).inv.app V).left ≫ Limits.pullback.snd V.hom (𝟙 X) = V.hom :=
  MorphismProperty.Over.pullbackId_inv_app_left_snd rfl V

namespace Hom

/-- Equal morphisms `f = g` induce naturally isomorphic base-change functors on small étale
sites. -/
@[expose]
noncomputable def smallEtaleBaseChangeCongr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    f.smallEtaleBaseChange ≅ g.smallEtaleBaseChange :=
  MorphismProperty.Over.pullbackCongr h

@[simp, reassoc]
lemma smallEtaleBaseChangeCongr_hom_app_left_fst {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (V : Y.Etale) :
    ((smallEtaleBaseChangeCongr h).hom.app V).left ≫ Limits.pullback.fst V.hom g =
      Limits.pullback.fst V.hom f :=
  MorphismProperty.Over.pullbackCongr_hom_app_left_fst h V

@[simp, reassoc]
lemma smallEtaleBaseChangeCongr_hom_app_left_snd {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (V : Y.Etale) :
    ((smallEtaleBaseChangeCongr h).hom.app V).left ≫ Limits.pullback.snd V.hom g =
      Limits.pullback.snd V.hom f :=
  MorphismProperty.Over.pullbackCongr_hom_app_left_snd h V

@[simp]
lemma smallEtaleBaseChangeCongr_rfl {X Y : Scheme.{u}} (f : X ⟶ Y) :
    smallEtaleBaseChangeCongr (rfl : f = f) = Iso.refl f.smallEtaleBaseChange :=
  MorphismProperty.Over.pullbackCongr_rfl (P := @Etale) (Q := ⊤) f

@[simp, reassoc]
lemma smallEtaleBaseChangeCongr_inv_app_left_fst {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (V : Y.Etale) :
    ((smallEtaleBaseChangeCongr h).inv.app V).left ≫ Limits.pullback.fst V.hom f =
      Limits.pullback.fst V.hom g :=
  MorphismProperty.Over.pullbackCongr_inv_app_left_fst h V

@[simp, reassoc]
lemma smallEtaleBaseChangeCongr_inv_app_left_snd {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (V : Y.Etale) :
    ((smallEtaleBaseChangeCongr h).inv.app V).left ≫ Limits.pullback.snd V.hom f =
      Limits.pullback.snd V.hom g :=
  MorphismProperty.Over.pullbackCongr_inv_app_left_snd h V

/-- Base change of small étale sites along a composite `fg = f ≫ g` is naturally isomorphic to
pulling back along `g` followed by pulling back along `f` (Stacks, Tag 021J). -/
@[expose]
noncomputable def smallEtaleBaseChangeComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z := f ≫ g) (hfg : fg = f ≫ g := by cat_disch) :
    fg.smallEtaleBaseChange ≅ g.smallEtaleBaseChange ⋙ f.smallEtaleBaseChange :=
  MorphismProperty.Over.pullbackComp f g fg hfg

@[reassoc]
lemma smallEtaleBaseChangeComp_hom_app_left_fst_fst {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) (V : Z.Etale) :
    ((smallEtaleBaseChangeComp f g fg hfg).hom.app V).left ≫
        Limits.pullback.fst (Limits.pullback.snd V.hom g) f ≫ Limits.pullback.fst V.hom g =
      Limits.pullback.fst V.hom fg :=
  MorphismProperty.Over.pullbackComp_hom_app_left_fst_fst f g fg hfg V

@[simp, reassoc]
lemma smallEtaleBaseChangeComp_hom_app_left_snd {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) (V : Z.Etale) :
    ((smallEtaleBaseChangeComp f g fg hfg).hom.app V).left ≫
        Limits.pullback.snd (Limits.pullback.snd V.hom g) f =
      Limits.pullback.snd V.hom fg :=
  MorphismProperty.Over.pullbackComp_hom_app_left_snd f g fg hfg V

@[simp, reassoc]
lemma smallEtaleBaseChangeComp_inv_app_left_fst {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) (V : Z.Etale) :
    ((smallEtaleBaseChangeComp f g fg hfg).inv.app V).left ≫ Limits.pullback.fst V.hom fg =
      Limits.pullback.fst (Limits.pullback.snd V.hom g) f ≫ Limits.pullback.fst V.hom g :=
  MorphismProperty.Over.pullbackComp_inv_app_left_fst f g fg hfg V

@[simp, reassoc]
lemma smallEtaleBaseChangeComp_inv_app_left_snd {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) (V : Z.Etale) :
    ((smallEtaleBaseChangeComp f g fg hfg).inv.app V).left ≫ Limits.pullback.snd V.hom fg =
      Limits.pullback.snd (Limits.pullback.snd V.hom g) f :=
  MorphismProperty.Over.pullbackComp_inv_app_left_snd f g fg hfg V

/-- A commutative square `f ≫ g = h ≫ i` of schemes induces a canonical natural isomorphism
between the two iterated base-change functors on small étale sites (Stacks, Tag 021J). -/
@[expose]
noncomputable def smallEtaleBaseChangeCommSqIso {W X Y Z : Scheme.{u}} {f : W ⟶ X} {g : X ⟶ Z}
    {h : W ⟶ Y} {i : Y ⟶ Z} (w : f ≫ g = h ≫ i) :
    g.smallEtaleBaseChange ⋙ f.smallEtaleBaseChange ≅
      i.smallEtaleBaseChange ⋙ h.smallEtaleBaseChange :=
  MorphismProperty.Over.pullbackCommSqIso w

@[reassoc]
lemma smallEtaleBaseChangeCommSqIso_hom_app_left_fst_fst {W X Y Z : Scheme.{u}} {f : W ⟶ X}
    {g : X ⟶ Z} {h : W ⟶ Y} {i : Y ⟶ Z} (w : f ≫ g = h ≫ i) (V : Z.Etale) :
    ((smallEtaleBaseChangeCommSqIso w).hom.app V).left ≫
        Limits.pullback.fst (Limits.pullback.snd V.hom i) h ≫ Limits.pullback.fst V.hom i =
      Limits.pullback.fst (Limits.pullback.snd V.hom g) f ≫ Limits.pullback.fst V.hom g :=
  MorphismProperty.Over.pullbackCommSqIso_hom_app_left_fst_fst w V

@[simp, reassoc]
lemma smallEtaleBaseChangeCommSqIso_hom_app_left_snd {W X Y Z : Scheme.{u}} {f : W ⟶ X}
    {g : X ⟶ Z} {h : W ⟶ Y} {i : Y ⟶ Z} (w : f ≫ g = h ≫ i) (V : Z.Etale) :
    ((smallEtaleBaseChangeCommSqIso w).hom.app V).left ≫
        Limits.pullback.snd (Limits.pullback.snd V.hom i) h =
      Limits.pullback.snd (Limits.pullback.snd V.hom g) f :=
  MorphismProperty.Over.pullbackCommSqIso_hom_app_left_snd w V

@[simp]
lemma smallEtaleBaseChangeCommSqIso_symm {W X Y Z : Scheme.{u}} {f : W ⟶ X} {g : X ⟶ Z}
    {h : W ⟶ Y} {i : Y ⟶ Z} (w : f ≫ g = h ≫ i) :
    (smallEtaleBaseChangeCommSqIso w).symm = smallEtaleBaseChangeCommSqIso w.symm :=
  MorphismProperty.Over.pullbackCommSqIso_symm (P := @Etale) (Q := ⊤) w

@[reassoc]
lemma smallEtaleBaseChangeCommSqIso_inv_app_left_fst_fst {W X Y Z : Scheme.{u}} {f : W ⟶ X}
    {g : X ⟶ Z} {h : W ⟶ Y} {i : Y ⟶ Z} (w : f ≫ g = h ≫ i) (V : Z.Etale) :
    ((smallEtaleBaseChangeCommSqIso w).inv.app V).left ≫
        Limits.pullback.fst (Limits.pullback.snd V.hom g) f ≫ Limits.pullback.fst V.hom g =
      Limits.pullback.fst (Limits.pullback.snd V.hom i) h ≫ Limits.pullback.fst V.hom i :=
  MorphismProperty.Over.pullbackCommSqIso_inv_app_left_fst_fst w V

@[simp, reassoc]
lemma smallEtaleBaseChangeCommSqIso_inv_app_left_snd {W X Y Z : Scheme.{u}} {f : W ⟶ X}
    {g : X ⟶ Z} {h : W ⟶ Y} {i : Y ⟶ Z} (w : f ≫ g = h ≫ i) (V : Z.Etale) :
    ((smallEtaleBaseChangeCommSqIso w).inv.app V).left ≫
        Limits.pullback.snd (Limits.pullback.snd V.hom g) f =
      Limits.pullback.snd (Limits.pullback.snd V.hom i) h :=
  MorphismProperty.Over.pullbackCommSqIso_inv_app_left_snd w V

/-- For `f : X ⟶ Z` and `g : Y ⟶ Z`, the natural isomorphism between the two iterated small-étale
base-change functors around the cartesian square of `pullback f g`. -/
noncomputable abbrev smallEtaleBaseChangeConditionIso {X Y Z : Scheme.{u}} (f : X ⟶ Z)
    (g : Y ⟶ Z) :
    f.smallEtaleBaseChange ⋙ (Limits.pullback.fst f g).smallEtaleBaseChange ≅
      g.smallEtaleBaseChange ⋙ (Limits.pullback.snd f g).smallEtaleBaseChange :=
  smallEtaleBaseChangeCommSqIso Limits.pullback.condition

/-- Associativity coherence of `smallEtaleBaseChangeComp` as an equality of natural isomorphisms. -/
theorem smallEtaleBaseChangeComp_assoc {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y)
    (h : Y ⟶ Z) :
    smallEtaleBaseChangeCongr (Category.assoc f g h) ≪≫
        smallEtaleBaseChangeComp f (g ≫ h) ≪≫
        Functor.isoWhiskerRight (smallEtaleBaseChangeComp g h) f.smallEtaleBaseChange ≪≫
        Functor.associator _ _ _ =
      smallEtaleBaseChangeComp (f ≫ g) h ≪≫
        Functor.isoWhiskerLeft h.smallEtaleBaseChange (smallEtaleBaseChangeComp f g) :=
  MorphismProperty.Over.pullbackComp_assoc (P := @Etale) (Q := ⊤) f g h

/-- Right unitality coherence of `smallEtaleBaseChangeComp` and `smallEtaleBaseChangeId`. -/
theorem smallEtaleBaseChangeComp_id {X Y : Scheme.{u}} (f : X ⟶ Y) :
    smallEtaleBaseChangeComp f (𝟙 Y) ≪≫
        Functor.isoWhiskerRight (smallEtaleBaseChangeId Y) f.smallEtaleBaseChange ≪≫
        Functor.leftUnitor f.smallEtaleBaseChange =
      smallEtaleBaseChangeCongr (Category.comp_id f) :=
  MorphismProperty.Over.pullbackComp_id (P := @Etale) (Q := ⊤) f

/-- Left unitality coherence of `smallEtaleBaseChangeComp` and `smallEtaleBaseChangeId`. -/
theorem id_smallEtaleBaseChangeComp {X Y : Scheme.{u}} (f : X ⟶ Y) :
    smallEtaleBaseChangeComp (𝟙 X) f ≪≫
        Functor.isoWhiskerLeft f.smallEtaleBaseChange (smallEtaleBaseChangeId X) ≪≫
        Functor.rightUnitor f.smallEtaleBaseChange =
      smallEtaleBaseChangeCongr (Category.id_comp f) :=
  MorphismProperty.Over.id_pullbackComp (P := @Etale) (Q := ⊤) f

end Hom

/-- The contravariant pseudofunctor sending a scheme `X` to its small étale category `X.Etale` and
a morphism `f : X ⟶ Y` to `f.smallEtaleBaseChange : Y.Etale ⥤ X.Etale`, with unit and composition
comparisons given by `smallEtaleBaseChangeId` and `smallEtaleBaseChangeComp` (Stacks, Tag 021J). -/
@[expose]
noncomputable def smallEtalePseudofunctor : LocallyDiscrete Scheme.{u}ᵒᵖ ⥤ᵖ Cat.{u, u + 1} :=
  LocallyDiscrete.mkCatPseudofunctor
    (obj := fun X ↦ Cat.of X.unop.Etale)
    (fun f ↦ f.unop.smallEtaleBaseChange)
    (fun X ↦ smallEtaleBaseChangeId X.unop)
    (fun f g fg hfg ↦
      Hom.smallEtaleBaseChangeComp g.unop f.unop fg.unop (congrArg Quiver.Hom.unop hfg.symm))
    (fun f g h fg gh fgh hfg hgh hfgh hfgh' V ↦
      MorphismProperty.Over.pullbackComp_assoc' (P := @Etale) (Q := ⊤)
        h.unop g.unop f.unop gh.unop fg.unop fgh.unop
        (congrArg Quiver.Hom.unop hgh.symm) (congrArg Quiver.Hom.unop hfg.symm)
        (congrArg Quiver.Hom.unop hfgh'.symm) (congrArg Quiver.Hom.unop hfgh.symm) V)
    (fun f hf V ↦
      MorphismProperty.Over.pullbackComp_id' (P := @Etale) (Q := ⊤)
        f.unop (𝟙 _) rfl (congrArg Quiver.Hom.unop hf.symm) V)
    (fun f hf V ↦
      MorphismProperty.Over.id_pullbackComp' (P := @Etale) (Q := ⊤)
        (𝟙 _) rfl f.unop (congrArg Quiver.Hom.unop hf.symm) V)

@[simp]
lemma smallEtalePseudofunctor_obj (X : LocallyDiscrete Scheme.{u}ᵒᵖ) :
    smallEtalePseudofunctor.obj X = Cat.of X.as.unop.Etale :=
  rfl

@[simp]
lemma smallEtalePseudofunctor_map_toFunctor {X Y : LocallyDiscrete Scheme.{u}ᵒᵖ} (f : X ⟶ Y) :
    (smallEtalePseudofunctor.map f).toFunctor = f.as.unop.smallEtaleBaseChange :=
  rfl

@[simp]
lemma smallEtalePseudofunctor_mapId_hom_toNatTrans_app (X : LocallyDiscrete Scheme.{u}ᵒᵖ)
    (V : X.as.unop.Etale) :
    (smallEtalePseudofunctor.mapId X).hom.toNatTrans.app V =
      (smallEtaleBaseChangeId X.as.unop).hom.app V :=
  rfl

@[simp]
lemma smallEtalePseudofunctor_mapId_inv_toNatTrans_app (X : LocallyDiscrete Scheme.{u}ᵒᵖ)
    (V : X.as.unop.Etale) :
    (smallEtalePseudofunctor.mapId X).inv.toNatTrans.app V =
      (smallEtaleBaseChangeId X.as.unop).inv.app V :=
  rfl

@[simp]
lemma smallEtalePseudofunctor_mapComp_hom_toNatTrans_app {X Y Z : LocallyDiscrete Scheme.{u}ᵒᵖ}
    (f : X ⟶ Y) (g : Y ⟶ Z) (V : X.as.unop.Etale) :
    (smallEtalePseudofunctor.mapComp f g).hom.toNatTrans.app V =
      (Hom.smallEtaleBaseChangeComp g.as.unop f.as.unop (g.as.unop ≫ f.as.unop) rfl).hom.app V :=
  rfl

@[simp]
lemma smallEtalePseudofunctor_mapComp_inv_toNatTrans_app {X Y Z : LocallyDiscrete Scheme.{u}ᵒᵖ}
    (f : X ⟶ Y) (g : Y ⟶ Z) (V : X.as.unop.Etale) :
    (smallEtalePseudofunctor.mapComp f g).inv.toNatTrans.app V =
      (Hom.smallEtaleBaseChangeComp g.as.unop f.as.unop (g.as.unop ≫ f.as.unop) rfl).inv.app V :=
  rfl

end Functoriality

end AlgebraicGeometry.Scheme
