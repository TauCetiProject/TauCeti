/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Representability
public import TauCeti.CategoryTheory.Sites.Over.Basic

/-!
# Representability from open charts on affine tests

A Zariski sheaf on schemes over a base is representable if it is covered by representable
open subfunctors. Injectivity, open inverse images and coverage can all be checked on affine
test schemes.

The relative criterion follows from the absolute open-chart criterion by applying the native
presheaf of pairs consisting of a structure morphism and a relative section.

## References

* The Stacks Project, Tag 01JJ.
-/

public section

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.LocalRepresentability

variable {S : Scheme.{u}} (P : (Over S)ᵒᵖ ⥤ Type u)

/-- Pull a relative section back along a morphism of underlying schemes. -/
private def chartElement {T : Scheme.{u}} {Y : Over S} (a : T ⟶ Y.left)
    (y : P.obj (op Y)) : (Over.sigmaPresheaf P).obj (op T) :=
  (Over.sigmaPresheaf P).map a.op ⟨Y.hom, y⟩

private lemma chartElement_comp {T T' : Scheme.{u}} {Y : Over S} (b : T' ⟶ T)
    (a : T ⟶ Y.left) (y : P.obj (op Y)) :
    (Over.sigmaPresheaf P).map b.op (chartElement P a y) =
      chartElement P (b ≫ a) y := by
  exact ((Over.sigmaPresheaf P).map_comp_apply a.op b.op
    (⟨Y.hom, y⟩ : (Over.sigmaPresheaf P).obj (op Y.left))).symm

private lemma chartElement_sigma {T W : Scheme.{u}} (a : W ⟶ T)
    (x : (Over.sigmaPresheaf P).obj (op T)) :
    chartElement P (Y := Over.mk x.1) a x.2 = (Over.sigmaPresheaf P).map a.op x := by
  rcases x with ⟨h, s⟩
  rfl

private lemma chartElement_eq_iff {W Y Y' : Over S} (a : W ⟶ Y) (b : W ⟶ Y')
    (y : P.obj (op Y)) (y' : P.obj (op Y')) :
    chartElement P a.left y = chartElement P b.left y' ↔
      P.map a.op y = P.map b.op y' := by
  rw [chartElement, chartElement, Over.sigmaPresheaf_map_left_mk,
    Over.sigmaPresheaf_map_left_mk]
  exact ⟨fun h ↦ sigma_mk_injective (β := fun h : W.left ⟶ S ↦ P.obj (op (Over.mk h))) h,
    fun h ↦ congrArg (Sigma.mk _) h⟩

private lemma isSheaf_sigma (hP : Presheaf.IsSheaf (zariskiTopology.over S) P) :
    Presheaf.IsSheaf zariskiTopology (Over.sigmaPresheaf P) := by
  rw [isSheaf_iff_isSheaf_of_type] at hP ⊢
  exact (Over.isSheaf_over_iff_isSheaf_sigmaPresheaf zariskiTopology
    ((isSheaf_iff_isSheaf_of_type _ _).1 (zariskiTopology.yoneda.obj S).property)).mp hP

section

variable {P} {ι : Type u} (X : ι → Over S) (ξ : ∀ i, P.obj (op (X i)))

private noncomputable def chartMap (i : ι) : yoneda.obj (X i).left ⟶ Over.sigmaPresheaf P :=
  yonedaEquiv.symm (chartElement P (𝟙 (X i).left) (ξ i))

private lemma chartMap_app {V : Scheme.{u}} (i : ι) (e : V ⟶ (X i).left) :
    (chartMap X ξ i).app (op V) e = chartElement P e (ξ i) := by
  -- Yoneda evaluation is the action of the total presheaf on the universal chart element.
  change (Over.sigmaPresheaf P).map e.op (chartElement P (𝟙 (X i).left) (ξ i)) = _
  rw [chartElement_comp, Category.comp_id]

variable {X ξ}

private lemma exists_isPullback_chartMap
    {i : ι}
    (hinj : ∀ {T : Over S} (a b : T ⟶ X i), P.map a.op (ξ i) = P.map b.op (ξ i) → a = b)
    {T : Over S} {y : P.obj (op T)} {U : T.left.Opens}
    (hU : ∀ (W : Over S) (a : W ⟶ T),
      (∃ b : W ⟶ X i, P.map a.op y = P.map b.op (ξ i)) ↔ Set.range a.left ⊆ U) :
    ∃ c : (U : Scheme.{u}) ⟶ (X i).left, ∀ (V : Scheme.{u}) (e : V ⟶ (X i).left)
      (a : V ⟶ T.left), chartElement P e (ξ i) = chartElement P a y ↔
        ∃ d : V ⟶ U, d ≫ c = e ∧ d ≫ U.ι = a := by
  obtain ⟨b₀, hb₀⟩ := (hU (Over.mk (U.ι ≫ T.hom)) (Over.homMk U.ι rfl)).2
    (by simp [Scheme.Opens.range_ι])
  refine ⟨b₀.left, fun V e a ↦ ?_⟩
  have key (W : Over S) (d : W.left ⟶ U) (hd : d ≫ U.ι ≫ T.hom = W.hom) :
      P.map (Over.homMk (d ≫ b₀.left) (by simp [Over.w b₀, hd]) : W ⟶ X i).op (ξ i) =
        P.map (Over.homMk (d ≫ U.ι) (by simp [hd]) : W ⟶ T).op y := by
    have e₁ : (Over.homMk (d ≫ b₀.left) (by simp [Over.w b₀, hd]) : W ⟶ X i) =
        (Over.homMk d (by simp [hd]) : W ⟶ Over.mk (U.ι ≫ T.hom)) ≫ b₀ := by ext; simp
    have e₂ : (Over.homMk (d ≫ U.ι) (by simp [hd]) : W ⟶ T) =
        (Over.homMk d (by simp [hd]) : W ⟶ Over.mk (U.ι ≫ T.hom)) ≫
          Over.homMk U.ι rfl := by ext; simp
    rw [e₁, e₂, op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, hb₀]
  constructor
  · intro h
    have h₁ : e ≫ (X i).hom = a ≫ T.hom := congr_arg Sigma.fst h
    have hrelative := chartElement_eq_iff P
      (Over.homMk e h₁ : Over.mk (a ≫ T.hom) ⟶ X i)
      (Over.homMk a rfl : Over.mk (a ≫ T.hom) ⟶ T) (ξ i) y
    simp only [Over.homMk_left] at hrelative
    rw [hrelative] at h
    have hr : Set.range a ⊆ U := (hU (Over.mk (a ≫ T.hom)) (Over.homMk a rfl)).1 ⟨_, h.symm⟩
    let d := IsOpenImmersion.lift U.ι a (by rwa [Scheme.Opens.range_ι])
    have hd : d ≫ U.ι = a := IsOpenImmersion.lift_fac _ _ _
    refine ⟨d, ?_, hd⟩
    have := key (Over.mk (a ≫ T.hom)) d (by simp [← hd])
    have e₃ : (Over.homMk (d ≫ U.ι) (by simp [hd]) : Over.mk (a ≫ T.hom) ⟶ T) =
        Over.homMk a rfl := by ext; simp [hd]
    rw [e₃, ← h] at this
    exact congr_arg CommaMorphism.left (hinj _ _ this)
  · rintro ⟨d, rfl, rfl⟩
    have hrelative := chartElement_eq_iff P
      (Over.homMk (d ≫ b₀.left) (by simp [Over.w b₀]) :
        Over.mk (d ≫ U.ι ≫ T.hom) ⟶ X i)
      (Over.homMk (d ≫ U.ι) (by simp) : Over.mk (d ≫ U.ι ≫ T.hom) ⟶ T) (ξ i) y
    simp only [Over.homMk_left] at hrelative
    rw [hrelative]
    exact key (Over.mk (d ≫ U.ι ≫ T.hom)) d rfl

end

private lemma exists_open_pullback_chartMap
    {ι : Type u} (X : ι → Over S) (ξ : ∀ i, P.obj (op (X i)))
    (hinj : ∀ i {T : Over S} (a b : T ⟶ X i), P.map a.op (ξ i) = P.map b.op (ξ i) → a = b)
    (hopen : ∀ i (T : Over S) (x : P.obj (op T)), ∃ U : T.left.Opens,
      ∀ (W : Over S) (a : W ⟶ T),
        (∃ b : W ⟶ X i, P.map a.op x = P.map b.op (ξ i)) ↔ Set.range a.left ⊆ U)
    (i : ι) (T : Scheme.{u}) (x : (Over.sigmaPresheaf P).obj (op T)) :
    ∃ (U : T.Opens) (c : (U : Scheme.{u}) ⟶ (X i).left),
      (∀ (V : Scheme.{u}) (e : V ⟶ (X i).left) (a : V ⟶ T),
        (chartMap X ξ i).app (op V) e = (Over.sigmaPresheaf P).map a.op x ↔
          ∃ d : V ⟶ U, d ≫ c = e ∧ d ≫ U.ι = a) ∧
      ∀ t : T, (∃ (W : Over S) (a : W ⟶ Over.mk x.1) (b : W ⟶ X i),
        t ∈ Set.range a.left ∧ P.map a.op x.2 = P.map b.op (ξ i)) →
          t ∈ U := by
  obtain ⟨U, hU⟩ := hopen i (Over.mk x.1) x.2
  obtain ⟨c, hc⟩ := exists_isPullback_chartMap (hinj i) hU
  refine ⟨U, c, fun V e a ↦ ?_, fun t ⟨W, a, b, ht, h⟩ ↦ (hU W a).1 ⟨b, h⟩ ht⟩
  rw [chartMap_app, ← hc V e a, chartElement_sigma]

/-- A Zariski sheaf over a base, locally covered by representable open subfunctors,
is representable. -/
theorem isRepresentable_of_isSheaf_over (hP : Presheaf.IsSheaf (zariskiTopology.over S) P)
    {ι : Type u} (X : ι → Over S) (ξ : ∀ i, P.obj (op (X i)))
    (hinj : ∀ i {T : Over S} (a b : T ⟶ X i), P.map a.op (ξ i) = P.map b.op (ξ i) → a = b)
    (hopen : ∀ i (T : Over S) (x : P.obj (op T)), ∃ U : T.left.Opens,
      ∀ (W : Over S) (a : W ⟶ T),
        (∃ b : W ⟶ X i, P.map a.op x = P.map b.op (ξ i)) ↔ Set.range a.left ⊆ U)
    (hcov : ∀ (T : Over S) (x : P.obj (op T)) (t : T.left),
      ∃ (i : ι) (W : Over S) (a : W ⟶ T) (b : W ⟶ X i),
        t ∈ Set.range a.left ∧ P.map a.op x = P.map b.op (ξ i)) :
    P.IsRepresentable := by
  let F : Sheaf zariskiTopology (Type u) := ⟨Over.sigmaPresheaf P, isSheaf_sigma P hP⟩
  let f : (i : ι) → yoneda.obj (X i).left ⟶ F.obj := chartMap X ξ
  have hpb := exists_open_pullback_chartMap P X ξ hinj hopen
  have hf (i : ι) : IsOpenImmersion.presheaf (f i) := by
    refine MorphismProperty.relative.of_exists (fun T g ↦ ?_)
    obtain ⟨U, c, hc, -⟩ := hpb i T (yonedaEquiv g)
    refine ⟨U, yoneda.map c, U.ι, IsPullback.of_forall_isPullback_app (fun V ↦ ?_),
      inferInstance⟩
    rw [Types.isPullback_iff]
    refine ⟨?_, fun d d' ⟨_, h⟩ ↦ (cancel_mono U.ι).1 h, fun e a h ↦ ?_⟩
    · apply ConcreteCategory.hom_ext
      intro d
      simp only [types_comp_apply, yoneda_map_app]
      rw [← map_yonedaEquiv g]
      exact (hc V.unop _ _).2 ⟨d, rfl, rfl⟩
    · replace h : (f i).app V e = g.app V a := h
      rw [← map_yonedaEquiv g] at h
      exact (hc V.unop e a).1 h
  have : Presheaf.IsLocallySurjective zariskiTopology (Sigma.desc f) := by
    refine ⟨fun {T} x ↦ ?_⟩
    have H (t : T) : ∃ (i : ι) (U : T.Opens) (c : (U : Scheme.{u}) ⟶ (X i).left),
        t ∈ U ∧ (f i).app (op U) c = (Over.sigmaPresheaf P).map U.ι.op x := by
      obtain ⟨i, W, a, b, ht, h⟩ := hcov (Over.mk x.1) x.2 t
      obtain ⟨U, c, hc, hU⟩ := hpb i T x
      exact ⟨i, U, c, hU t ⟨W, a, b, ht, h⟩, (hc _ _ _).2 ⟨𝟙 _, by simp, by simp⟩⟩
    choose i U c ht hc using H
    rw [mem_grothendieckTopology_iff]
    refine ⟨Scheme.Cover.mkOfCovers T (fun t ↦ (U t : Scheme.{u})) (fun t ↦ (U t).ι)
      (fun t ↦ ⟨t, by
        have h : t ∈ Set.range (U t).ι := by rw [Scheme.Opens.range_ι]; exact ht t
        exact h⟩), ?_⟩
    rintro V g ⟨t⟩
    refine ⟨(Sigma.ι (fun i ↦ yoneda.obj (X i).left) (i t)).app _ (c t), ?_⟩
    refine (congr_arg
      (fun φ : yoneda.obj (X (i t)).left ⟶ F.obj ↦ φ.app (op (U t : Scheme)) (c t))
      (Sigma.ι_comp_desc f (i t))).trans (hc t)
  have := Scheme.LocalRepresentability.isRepresentable (F := F) hf
  exact Over.isRepresentable_of_isRepresentable_sigmaPresheaf

section Affine

variable {P} {ι : Type u} {X : ι → Over S} {ξ : ∀ i, P.obj (op (X i))}

private lemma exists_map_eq_iff_exists_chartElement_eq {W T : Over S} (a : W ⟶ T) (x : P.obj (op T))
    (i : ι) : (∃ b : W ⟶ X i, P.map a.op x = P.map b.op (ξ i)) ↔
      ∃ c : W.left ⟶ (X i).left, chartElement P a.left x = chartElement P c (ξ i) := by
  constructor
  · rintro ⟨b, h⟩
    exact ⟨b.left, (chartElement_eq_iff P a b _ _).2 h⟩
  · rintro ⟨c, h⟩
    have hc : c ≫ (X i).hom = W.hom := by
      rw [← Over.w a]
      exact (congr_arg Sigma.fst h).symm
    exact ⟨Over.homMk c hc, (chartElement_eq_iff P a (Over.homMk c hc) _ _).1 h⟩

private lemma eq_of_chartElement_eq {i : ι}
    (hinj : ∀ {T : Over S} [IsAffine T.left] (a b : T ⟶ X i),
      P.map a.op (ξ i) = P.map b.op (ξ i) → a = b)
    {T : Scheme.{u}} {c c' : T ⟶ (X i).left}
    (h : chartElement P c (ξ i) = chartElement P c' (ξ i)) : c = c' := by
  refine T.affineCover.hom_ext _ _ fun j ↦ ?_
  have h' := congr_arg ((Over.sigmaPresheaf P).map (T.affineCover.f j).op) h
  rw [chartElement_comp, chartElement_comp] at h'
  have h₁ : (T.affineCover.f j ≫ c') ≫ (X i).hom = (T.affineCover.f j ≫ c) ≫ (X i).hom :=
    (congr_arg Sigma.fst h').symm
  have hrelative := chartElement_eq_iff P
    (Over.homMk (T.affineCover.f j ≫ c) rfl :
      Over.mk ((T.affineCover.f j ≫ c) ≫ (X i).hom) ⟶ X i)
    (Over.homMk (T.affineCover.f j ≫ c') h₁ :
      Over.mk ((T.affineCover.f j ≫ c) ≫ (X i).hom) ⟶ X i) (ξ i) (ξ i)
  simp only [Over.homMk_left] at hrelative
  rw [hrelative] at h'
  have : IsAffine (Over.mk ((T.affineCover.f j ≫ c) ≫ (X i).hom)).left := by
    dsimp
    infer_instance
  exact congr_arg CommaMorphism.left (hinj _ _ h')

private lemma exists_chartElement_eq_of_openCover {i : ι}
    (hP : Presheaf.IsSheaf (zariskiTopology.over S) P)
    (hinj : ∀ {T : Scheme.{u}} (c c' : T ⟶ (X i).left),
      chartElement P c (ξ i) = chartElement P c' (ξ i) → c = c')
    {T : Scheme.{u}} (s : (Over.sigmaPresheaf P).obj (op T))
    (𝒰 : Scheme.OpenCover.{u} T)
    (h : ∀ j, ∃ c : 𝒰.X j ⟶ (X i).left,
      (Over.sigmaPresheaf P).map (𝒰.f j).op s = chartElement P c (ξ i)) :
    ∃ c : T ⟶ (X i).left, s = chartElement P c (ξ i) := by
  choose c hc using h
  have hglue (j k : 𝒰.I₀) : pullback.fst (𝒰.f j) (𝒰.f k) ≫ c j = pullback.snd _ _ ≫ c k := by
    refine hinj _ _ ?_
    rw [← chartElement_comp, ← chartElement_comp, ← hc, ← hc,
      ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
      pullback.condition]
  refine ⟨𝒰.glueMorphisms c hglue, ?_⟩
  have hF := (isSheaf_iff_isSheaf_of_type _ _).1 (isSheaf_sigma P hP)
  refine (hF.isSeparated (Sieve.generate (Presieve.ofArrows 𝒰.X 𝒰.f))
    (mem_grothendieckTopology_iff.2 ⟨𝒰, Sieve.le_generate _⟩)).ext ?_
  rintro V _ ⟨Z, g, _, ⟨j⟩, rfl⟩
  rw [op_comp, Functor.map_comp_apply, Functor.map_comp_apply, hc, chartElement_comp,
    chartElement_comp, chartElement_comp, 𝒰.ι_glueMorphisms]

private lemma exists_chartElement_eq_of_forall_mem {i : ι}
    (hP : Presheaf.IsSheaf (zariskiTopology.over S) P)
    (hinj : ∀ {T : Scheme.{u}} (c c' : T ⟶ (X i).left),
      chartElement P c (ξ i) = chartElement P c' (ξ i) → c = c')
    {T : Scheme.{u}} (s : (Over.sigmaPresheaf P).obj (op T))
    (h : ∀ t : T, ∃ U : T.Opens, t ∈ U ∧ ∃ c : (U : Scheme.{u}) ⟶ (X i).left,
      (Over.sigmaPresheaf P).map U.ι.op s = chartElement P c (ξ i)) :
    ∃ c : T ⟶ (X i).left, s = chartElement P c (ξ i) := by
  choose U hU c hc using h
  let 𝒰 : Scheme.OpenCover.{u} T := {
    I₀ := T, X t := U t, f t := (U t).ι,
    mem₀ := by
      rw [presieve₀_mem_precoverage_iff]
      exact ⟨fun t ↦ ⟨t, by simpa using hU t⟩, inferInstance⟩ }
  exact exists_chartElement_eq_of_openCover hP hinj s 𝒰 fun t ↦ ⟨c t, hc t⟩

private lemma exists_opens_chartElement {i : ι}
    (hP : Presheaf.IsSheaf (zariskiTopology.over S) P)
    (hinj : ∀ {T : Scheme.{u}} (c c' : T ⟶ (X i).left),
      chartElement P c (ξ i) = chartElement P c' (ξ i) → c = c')
    (hopen : ∀ (T : Scheme.{u}) [IsAffine T] (s : (Over.sigmaPresheaf P).obj (op T)), ∃ U : T.Opens,
      ∀ (W : Scheme.{u}) [IsAffine W] (a : W ⟶ T),
        (∃ c : W ⟶ (X i).left, (Over.sigmaPresheaf P).map a.op s = chartElement P c (ξ i)) ↔
          Set.range a ⊆ U)
    {T : Scheme.{u}} (s : (Over.sigmaPresheaf P).obj (op T)) : ∃ U : T.Opens,
      ∀ (W : Scheme.{u}) (a : W ⟶ T),
        (∃ c : W ⟶ (X i).left, (Over.sigmaPresheaf P).map a.op s = chartElement P c (ξ i)) ↔
          Set.range a ⊆ U := by
  let L (V : T.Opens) : Prop :=
    ∃ c : (V : Scheme.{u}) ⟶ (X i).left,
      (Over.sigmaPresheaf P).map V.ι.op s = chartElement P c (ξ i)
  refine ⟨sSup {V | L V}, fun W a ↦ ⟨?_, fun ha ↦ ?_⟩⟩
  · rintro ⟨c, hc⟩ _ ⟨w, rfl⟩
    obtain ⟨V₀ : T.Opens, hV₀, hw, -⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.1 T.isBasis_affineOpens
        (show a w ∈ (⊤ : T.Opens) from trivial)
    have : IsAffine V₀ := hV₀
    obtain ⟨U₀, hU₀⟩ := hopen V₀ ((Over.sigmaPresheaf P).map V₀.ι.op s)
    refine (TopologicalSpace.Opens.mem_sSup).2 ⟨V₀.ι ''ᵁ U₀, ?_, ?_⟩
    · obtain ⟨c', hc'⟩ : ∃ c' : (U₀ : Scheme.{u}) ⟶ (X i).left,
          (Over.sigmaPresheaf P).map (U₀.ι ≫ V₀.ι).op s = chartElement P c' (ξ i) := by
        refine exists_chartElement_eq_of_openCover hP hinj _ (U₀ : Scheme.{u}).affineCover
          fun j ↦ ?_
        rw [← Functor.map_comp_apply, ← op_comp, ← Category.assoc, op_comp,
          Functor.map_comp_apply]
        refine (hU₀ _ _).2 ?_
        rw [Scheme.Hom.comp_base, TopCat.coe_comp, ← Scheme.Opens.range_ι U₀]
        exact Set.range_comp_subset_range _ _
      refine ⟨(V₀.ι.isoImage U₀).inv ≫ c', ?_⟩
      rw [← Scheme.Hom.isoImage_inv_ι, op_comp, Functor.map_comp_apply, hc',
        chartElement_comp]
    · obtain ⟨W' : W.Opens, hW', hwW', hW'le⟩ :=
        TopologicalSpace.Opens.isBasis_iff_nbhd.1 W.isBasis_affineOpens
        (show w ∈ a ⁻¹ᵁ V₀ from hw)
      have : IsAffine W' := hW'
      have hr : Set.range (a.resLE V₀ W' hW'le) ⊆ U₀ := by
        refine (hU₀ _ _).1 ⟨W'.ι ≫ c, ?_⟩
        rw [← Functor.map_comp_apply, ← op_comp, Scheme.Hom.resLE_comp_ι, op_comp,
          Functor.map_comp_apply, hc, chartElement_comp]
      refine ⟨a.resLE V₀ W' hW'le ⟨w, hwW'⟩, hr ⟨_, rfl⟩, ?_⟩
      exact Scheme.Hom.coe_resLE_apply a hW'le ⟨w, hwW'⟩
  · refine exists_chartElement_eq_of_forall_mem hP hinj _ fun w ↦ ?_
    obtain ⟨V, ⟨c, hc⟩, hV⟩ := (TopologicalSpace.Opens.mem_sSup).1 (ha ⟨w, rfl⟩)
    refine ⟨a ⁻¹ᵁ V, hV, a.resLE V (a ⁻¹ᵁ V) le_rfl ≫ c, ?_⟩
    rw [← Functor.map_comp_apply, ← op_comp, ← Scheme.Hom.resLE_comp_ι, op_comp,
      Functor.map_comp_apply, hc, chartElement_comp]

end Affine

/-- Representability by open charts can be checked on affine test schemes. -/
theorem isRepresentable_of_isSheaf_over_of_isAffine
    (hP : Presheaf.IsSheaf (zariskiTopology.over S) P)
    {ι : Type u} (X : ι → Over S) (ξ : ∀ i, P.obj (op (X i)))
    (hinj : ∀ i {T : Over S} [IsAffine T.left] (a b : T ⟶ X i),
      P.map a.op (ξ i) = P.map b.op (ξ i) → a = b)
    (hopen : ∀ i (T : Over S) [IsAffine T.left] (x : P.obj (op T)), ∃ U : T.left.Opens,
      ∀ (W : Over S) [IsAffine W.left] (a : W ⟶ T),
        (∃ b : W ⟶ X i, P.map a.op x = P.map b.op (ξ i)) ↔ Set.range a.left ⊆ U)
    (hcov : ∀ (T : Over S) [IsAffine T.left] (x : P.obj (op T)) (t : T.left),
      ∃ (i : ι) (W : Over S) (a : W ⟶ T) (b : W ⟶ X i),
        t ∈ Set.range a.left ∧ P.map a.op x = P.map b.op (ξ i)) :
    P.IsRepresentable := by
  have hinj' (i : ι) {T : Scheme.{u}} (c c' : T ⟶ (X i).left)
      (h : chartElement P c (ξ i) = chartElement P c' (ξ i)) : c = c' :=
    eq_of_chartElement_eq (hinj i) h
  have hmap {T : Scheme.{u}} (s : (Over.sigmaPresheaf P).obj (op T)) {W : Scheme.{u}} (a : W ⟶ T) :
      (Over.sigmaPresheaf P).map a.op s = chartElement P (Y := Over.mk s.1) a s.2 := by
    exact (chartElement_sigma P a s).symm
  refine isRepresentable_of_isSheaf_over P hP X ξ (fun i T a b h ↦ ?_) (fun i T x ↦ ?_)
    (fun T x t ↦ ?_)
  · exact Over.OverMorphism.ext (hinj' i _ _
      ((chartElement_eq_iff P a b _ _).2 h))
  · obtain ⟨U, hU⟩ := exists_opens_chartElement hP (hinj' i) (i := i) (fun T hT s ↦ by
      obtain ⟨U, hU⟩ := @hopen i (Over.mk s.1) hT s.2
      refine ⟨U, fun W hW a ↦ ?_⟩
      rw [hmap]
      exact (exists_map_eq_iff_exists_chartElement_eq _ _ i).symm.trans
        (@hU (Over.mk (a ≫ s.1)) hW (Over.homMk a rfl))) (chartElement P (𝟙 T.left) x)
    refine ⟨U, fun W a ↦ ?_⟩
    rw [exists_map_eq_iff_exists_chartElement_eq, ← hU, chartElement_comp,
      Category.comp_id]
  · obtain ⟨V : T.left.Opens, hV, ht, -⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.1 T.left.isBasis_affineOpens
        (show t ∈ (⊤ : T.left.Opens) from trivial)
    have : IsAffine (Over.mk (V.ι ≫ T.hom)).left := hV
    let x' := P.map (Over.homMk V.ι rfl : Over.mk (V.ι ≫ T.hom) ⟶ T).op x
    obtain ⟨i, W, a, b, ⟨w, hw⟩, h⟩ := hcov (Over.mk (V.ι ≫ T.hom)) x' ⟨t, ht⟩
    refine ⟨i, W, a ≫ Over.homMk V.ι rfl, b, ⟨w, ?_⟩, ?_⟩
    · simp only [Over.comp_left, Over.homMk_left, Scheme.Hom.comp_apply]
      exact (congrArg (fun z : V ↦ V.ι z) hw).trans (Scheme.Opens.ι_apply _ _)
    · rw [op_comp, Functor.map_comp_apply, h]

end AlgebraicGeometry.Scheme.LocalRepresentability
