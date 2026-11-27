/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.Limits.BaseChange
public import TauCeti.AlgebraicGeometry.Morphisms.FinitePresentation.Basic
public import TauCeti.CategoryTheory.Comma.Over.Pullback

/-!
# Descent of morphisms and their properties along cofiltered limits

For a cofiltered diagram of quasi-compact quasi-separated schemes with affine transition
maps, morphisms of finitely presented stage models descend from the limit to a finite stage.

Isomorphism and monomorphism inheritance require no finiteness assumptions on the members
of the base diagram. A locally finitely presented morphism from a quasi-compact source to a
quasi-compact quasi-separated target that is an isomorphism over the limit is eventually an
isomorphism. A quasi-compact locally finite type morphism from a quasi-compact quasi-separated
source that is monic over the limit is eventually monic. Base change along the target reduces
isomorphism inheritance to a diagram of quasi-compact quasi-separated schemes. Monomorphism
inheritance follows by applying isomorphism inheritance to the diagonal.

The descent of morphisms and of equalities of morphisms is also stated for the base change
functors `Over.pullback` between the over categories of the members and of the limit, through which
structures such as group laws are transported: a morphism between base changes to the limit is,
up to the identification `Over.pullbackCompIsoOfEq`, the base change of a morphism over some
member, and two morphisms over a member which agree over the limit agree over some later member.

## Main declarations

* `CategoryTheory.Limits.IsLimit.exists_pullbackMap_comp_eq`: morphism descent for finitely
  presented stage models over a quasi-compact quasi-separated affine-transition diagram.
* `CategoryTheory.Limits.IsLimit.exists_isIso_pullbackMap`: isomorphism inheritance for a
  locally finitely presented morphism between suitable quasi-compact stage models.
* `CategoryTheory.Limits.IsLimit.exists_iso_pullback_of_iso`: isomorphism descent for finitely
  presented quasi-compact quasi-separated stage models.
* `CategoryTheory.Limits.IsLimit.exists_mono_pullbackMap`: monomorphism inheritance for a
  quasi-compact locally finite type morphism from a quasi-compact quasi-separated stage source.
* `CategoryTheory.Limits.IsLimit.exists_overPullback_map_comp_eq`: morphism descent for the base
  change functors of over categories, stated through `CategoryTheory.Limits.Cone.LiftsAlong`.
* `CategoryTheory.Limits.IsLimit.exists_overPullback_map_eq_map`: descent of equalities of
  morphisms for the base change functors of over categories.

## References

* The Stacks Project, [Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM).
* The Stacks Project, [Tag 081E](https://stacks.math.columbia.edu/tag/081E).
* The Stacks Project, [Tag 01ZP](https://stacks.math.columbia.edu/tag/01ZP).
* The Stacks Project, [Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC).
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace CategoryTheory.Limits.IsLimit

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ Scheme.{u}}
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] {c : Cone D} (hc : IsLimit c)

include hc in
/-- Let `S = lim Dⱼ` be a cofiltered limit of quasi-compact quasi-separated schemes with affine
transition maps, and let `X` and `Y` be schemes over a member `Dᵢ`, with `X` quasi-compact and
quasi-separated over `Dᵢ` and `Y` locally of finite presentation over `Dᵢ`. Every morphism
`X ×_{Dᵢ} S ⟶ Y ×_{Dᵢ} S` over `S` is the base change of a morphism `X ×_{Dᵢ} Dⱼ ⟶ Y ×_{Dᵢ} Dⱼ`
over some `Dⱼ`. Stacks, Lemma 32.10.1 (01ZM), descent of morphisms. -/
theorem exists_pullbackMap_comp_eq [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] {i : I} {X Y : Scheme.{u}} {p : X ⟶ D.obj i}
    {q : Y ⟶ D.obj i} [QuasiCompact p] [QuasiSeparated p] [LocallyOfFinitePresentation q]
    (a : pullback (c.π.app i) p ⟶ pullback (c.π.app i) q)
    (ha : a ≫ pullback.fst _ _ = pullback.fst _ _) :
    ∃ (j : I) (hji : j ⟶ i) (b : pullback (D.map hji) p ⟶ pullback (D.map hji) q),
      b ≫ pullback.fst _ _ = pullback.fst _ _ ∧
        pullback.map (c.π.app i) p (D.map hji) p (c.π.app j) (𝟙 X) (𝟙 _) (by simp) (by simp) ≫ b =
          a ≫ pullback.map (c.π.app i) q (D.map hji) q (c.π.app j) (𝟙 Y) (𝟙 _) (by simp)
            (by simp) := by
  let t : D.pullbackOver p ⟶ (Functor.const (Over i)).obj (D.obj i) :=
    { app j := pullback.snd _ _ ≫ p
      naturality j k f := by simp [D.pullbackOver_map_snd_assoc p f] }
  -- The composite of `a` with the projection to `Y` descends to some member.
  obtain ⟨j, g', hg'₁, hg'₂⟩ :=
    AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
      (D.pullbackOver p) t q _ (hc.pullbackOver p)
      (a ≫ pullback.snd _ _ : pullback (c.π.app i) p ⟶ Y) (by
        ext j
        simp only [t, NatTrans.comp_app, Functor.const_obj_obj, Functor.const_map_app,
          Category.assoc]
        rw [Cone.pullbackOver_π_app_snd_assoc, ← pullback.condition, ← pullback.condition,
          reassoc_of% ha])
  refine ⟨j.left, j.hom, pullback.lift (pullback.fst _ _) g' (by rw [hg'₂]; exact
    pullback.condition), by simp, ?_⟩
  apply pullback.hom_ext
  · simp [reassoc_of% ha]
  · rw [Category.assoc, pullback.lift_snd]
    exact hg'₁.trans (by simp)

include hc in
/-- Let `S = lim Dⱼ` be a cofiltered limit of quasi-compact quasi-separated schemes with affine
transition maps, and `g : X ⟶ Y` a morphism of schemes over a member `Dᵢ`, with `X` locally of
finite presentation and quasi-compact over `Dᵢ`, and `Y` locally of finite type, quasi-compact and
quasi-separated over `Dᵢ`. If the base change of `g` to `S` is an isomorphism, then so is its base
change to some `Dⱼ`. Stacks, Lemma 32.8.11 (081E). -/
private theorem exists_isIso_pullbackMap_of_structure [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] {i : I} {X Y : Scheme.{u}} {p : X ⟶ D.obj i}
    {q : Y ⟶ D.obj i} [LocallyOfFinitePresentation p] [QuasiCompact p] [LocallyOfFiniteType q]
    [QuasiCompact q] [QuasiSeparated q] (g : X ⟶ Y) (hg : g ≫ q = p)
    [IsIso (pullback.map (c.π.app i) p (c.π.app i) q (𝟙 _) g (𝟙 _) (by simp) (by simp [hg]))] :
    ∃ (j : I) (hji : j ⟶ i),
      IsIso (pullback.map (D.map hji) p (D.map hji) q (𝟙 _) g (𝟙 _) (by simp) (by simp [hg])) := by
  -- The members of `D` over `i` base changed to `X` and to `Y`, and their limits.
  let DX := D.pullbackOver p
  let DY := D.pullbackOver q
  have hcX := hc.pullbackOver p
  have hcY := hc.pullbackOver q
  let t {Z : Scheme.{u}} (r : Z ⟶ D.obj i) :
      D.pullbackOver r ⟶ (Functor.const (Over i)).obj (D.obj i) :=
    { app j := pullback.snd _ _ ≫ r
      naturality j k f := by simp [D.pullbackOver_map_snd_assoc r f] }
  -- The base change `φ` of `g` to the limit, and its base changes `φB j` to the members.
  let φ := pullback.map (c.π.app i) p (c.π.app i) q (𝟙 _) g (𝟙 _) (by simp) (by simp [hg])
  have : IsIso φ := ‹_›
  let φB (j : Over i) : DX.obj j ⟶ DY.obj j :=
    pullback.map (D.map j.hom) p (D.map j.hom) q (𝟙 _) g (𝟙 _) (by simp) (by simp [hg])
  have φB_snd (j : Over i) : φB j ≫ pullback.snd _ _ = pullback.snd _ _ ≫ g := by simp [φB]
  have π_φB (j : Over i) :
      (c.pullbackOver p).π.app j ≫ φB j = φ ≫ (c.pullbackOver q).π.app j := by
    apply pullback.hom_ext <;> simp [φB, φ]
  have map_φB {j k : Over i} (f : j ⟶ k) : DX.map f ≫ φB k = φB j ≫ DY.map f := by
    apply pullback.hom_ext <;> simp [DX, DY, φB]
  have inv_fst : inv φ ≫ pullback.fst (c.π.app i) p = pullback.fst (c.π.app i) q := by
    rw [IsIso.inv_comp_eq]; simp [φ]
  have inv_snd : inv φ ≫ pullback.snd (c.π.app i) p ≫ g = pullback.snd (c.π.app i) q := by
    rw [IsIso.inv_comp_eq]; simp [φ]
  -- The inverse of `φ` followed by the projection to `X` descends to some member.
  obtain ⟨j, g', hg'₁, hg'₂⟩ :=
    AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation DY (t q) p _ hcY
      (inv φ ≫ pullback.snd _ _ : pullback (c.π.app i) q ⟶ X) (by
        ext j
        simp only [t, NatTrans.comp_app, Functor.const_obj_obj, Functor.const_map_app,
          Category.assoc]
        rw [Cone.pullbackOver_π_app_snd_assoc, ← pullback.condition, ← pullback.condition,
          reassoc_of% inv_fst])
  -- Both composites of `φB j` with this descent are the identity on the limit, hence on some
  -- later member.
  obtain ⟨k, hkj, hk⟩ :=
    AlgebraicGeometry.Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType DY (t q) q _ hcY
      (g' ≫ g) (pullback.snd _ _) (by simp [hg, hg'₂]) rfl (by
        rw [reassoc_of% hg'₁, Cone.pullbackOver_π_app_snd, inv_snd])
  obtain ⟨k', hk'j, hk'⟩ :=
    AlgebraicGeometry.Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType DX (t p) p _ hcX
      (φB j ≫ g') (pullback.snd _ _) (by simp [hg'₂, t, reassoc_of% φB_snd, hg]) rfl (by
        rw [reassoc_of% π_φB, hg'₁, IsIso.hom_inv_id_assoc, Cone.pullbackOver_π_app_snd])
  obtain ⟨l, hlk, hlk', hl⟩ := IsCofiltered.cospan hkj hk'j
  refine ⟨l.left, l.hom,
    ⟨pullback.lift (pullback.fst _ _) (DY.map (hlk ≫ hkj) ≫ g') ?_, ?_, ?_⟩⟩
  · rw [Category.assoc, hg'₂]
    simp [t, DY, pullback.condition]
  · apply pullback.hom_ext
    · simp
    · -- The base change of `g` to `Dₗ` in the goal is `φB l` by definition.
      change φB l ≫ _ ≫ _ = _
      rw [pullback.lift_snd, ← reassoc_of% map_φB, hl, Functor.map_comp_assoc, hk']
      simp [DX]
  · apply pullback.hom_ext
    · simp
    · -- The base change of `g` to `Dₗ` in the goal is `φB l` by definition.
      change _ ≫ φB l ≫ _ = _
      rw [φB_snd, pullback.lift_snd_assoc, Category.assoc, Functor.map_comp_assoc, hk]
      simp [DY]

include hc in
private theorem exists_isIso_pullback_snd [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] {i : I} {X : Scheme.{u}} (q : X ⟶ D.obj i)
    [LocallyOfFinitePresentation q] [QuasiCompact q]
    [IsIso (pullback.snd q (c.π.app i))] :
    ∃ (j : I) (a : j ⟶ i), IsIso (pullback.snd q (D.map a)) := by
  let m (s : Scheme.{u}) (t : s ⟶ D.obj i) :=
    pullback.map t q t (𝟙 (D.obj i)) (𝟙 s) q (𝟙 (D.obj i)) (by simp) (by simp)
  have hcomp (s : Scheme.{u}) (t : s ⟶ D.obj i) :
      m s t ≫ pullback.fst t (𝟙 (D.obj i)) = pullback.fst t q := by
    simp [m]
  have : IsIso (pullback.fst (c.π.app i) q) := by
    have h : (pullbackSymmetry (c.π.app i) q).hom ≫
        pullback.snd q (c.π.app i) = pullback.fst (c.π.app i) q := by simp
    rw [← h]
    infer_instance
  have : IsIso (m c.pt (c.π.app i)) := by
    have : IsIso (m c.pt (c.π.app i) ≫
        pullback.fst (c.π.app i) (𝟙 (D.obj i))) := by
      rw [hcomp c.pt (c.π.app i)]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (pullback.fst (c.π.app i) (𝟙 (D.obj i)))
  have : IsIso (pullback.map (c.π.app i) q (c.π.app i) (𝟙 (D.obj i))
      (𝟙 c.pt) q (𝟙 (D.obj i)) (by simp) (by simp)) :=
    ‹IsIso (m c.pt (c.π.app i))›
  obtain ⟨j, a, ha⟩ := @exists_isIso_pullbackMap_of_structure
    I _ _ D _ c hc _ _ i X (D.obj i) q (𝟙 _) _ _ _ _ _ q (by simp)
    ‹IsIso (pullback.map (c.π.app i) q (c.π.app i) (𝟙 (D.obj i))
      (𝟙 c.pt) q (𝟙 (D.obj i)) (by simp) (by simp))›
  have : IsIso (m (D.obj j) (D.map a)) := ha
  have : IsIso (pullback.fst (D.map a) q) := by
    rw [← hcomp (D.obj j) (D.map a)]
    infer_instance
  have h : (pullbackSymmetry q (D.map a)).hom ≫ pullback.fst (D.map a) q =
      pullback.snd q (D.map a) := by simp
  refine ⟨j, a, ?_⟩
  rw [← h]
  infer_instance

include hc in
/-- A locally finitely presented morphism from a quasi-compact scheme to a quasi-compact
quasi-separated scheme becomes an isomorphism at a finite stage if it is one over the limit.
The members of the affine-transition base diagram need not be quasi-compact or quasi-separated.
Stacks, Lemma 32.8.11 (081E). -/
theorem exists_isIso_pullbackMap
    {i : I} {X Y : Scheme.{u}} {p : X ⟶ D.obj i} {q : Y ⟶ D.obj i}
    [CompactSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (g : X ⟶ Y) (hg : g ≫ q = p) [LocallyOfFinitePresentation g]
    [IsIso (pullback.map (c.π.app i) p (c.π.app i) q (𝟙 _) g (𝟙 _)
      (by simp) (by simp [hg]))] :
    ∃ (j : I) (a : j ⟶ i),
      IsIso (pullback.map (D.map a) p (D.map a) q (𝟙 _) g (𝟙 _)
        (by simp) (by simp [hg])) := by
  have : QuasiCompact g := inferInstance
  refine (MorphismProperty.isomorphisms Scheme.{u}).exists_pullbackMap_of_pullbackOver
    c g hg ?_ ‹_›
  intro b hb
  have : ∀ j, CompactSpace ((D.pullbackOver q).obj j) := fun j ↦
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd (D.map j.hom) q)
  have : ∀ j, QuasiSeparatedSpace ((D.pullbackOver q).obj j) := fun j ↦
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd (D.map j.hom) q)
  have : IsIso (pullback.snd (g ≫ b.inv)
      ((c.pullbackOver q).π.app (Over.mk (𝟙 i)))) := hb
  exact (hc.pullbackOver q).exists_isIso_pullback_snd (g ≫ b.inv)

include hc in
/-- Let `S = lim Dⱼ` be a cofiltered limit of quasi-compact quasi-separated schemes with affine
transition maps, and let `X` and `Y` be quasi-compact, quasi-separated and locally of finite
presentation over a member `Dᵢ`. Every isomorphism `S ×_{Dᵢ} X ≅ S ×_{Dᵢ} Y` over `S` is the base
change of an isomorphism `Dⱼ ×_{Dᵢ} X ≅ Dⱼ ×_{Dᵢ} Y` over some `Dⱼ`. Stacks, Lemmas 32.10.1
(01ZM) and 32.8.11 (081E). -/
theorem exists_iso_pullback_of_iso [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] {i : I} {X Y : Scheme.{u}} {p : X ⟶ D.obj i}
    {q : Y ⟶ D.obj i} [QuasiCompact p] [QuasiSeparated p] [LocallyOfFinitePresentation p]
    [QuasiCompact q] [QuasiSeparated q] [LocallyOfFinitePresentation q]
    (a : pullback (c.π.app i) p ≅ pullback (c.π.app i) q)
    (ha : a.hom ≫ pullback.fst _ _ = pullback.fst _ _) :
    ∃ (j : I) (t : j ⟶ i) (e : pullback (D.map t) p ≅ pullback (D.map t) q),
      e.hom ≫ pullback.fst _ _ = pullback.fst _ _ ∧
        pullback.map (c.π.app i) p (D.map t) p (c.π.app j) (𝟙 X) (𝟙 _) (by simp) (by simp) ≫
          e.hom = a.hom ≫ pullback.map (c.π.app i) q (D.map t) q (c.π.app j) (𝟙 Y) (𝟙 _)
            (by simp) (by simp) := by
  -- `a` is the base change of a morphism `b` over some `Dⱼ`, which is an isomorphism over `S`.
  obtain ⟨j, hji, b, hb₁, hb₂⟩ := hc.exists_pullbackMap_comp_eq a.hom ha
  have : IsIso (pullback.map (c.π.app j) (pullback.fst (D.map hji) p) (c.π.app j)
      (pullback.fst (D.map hji) q) (𝟙 _) b (𝟙 _) (by simp) (by exact hb₁.symm)) :=
    (MorphismProperty.pullbackMap_iff_of_pullbackMap_comp_eq
      (.isomorphisms Scheme) hji ha hb₁ hb₂).mpr (inferInstance : IsIso a.hom)
  have := QuasiCompact.compactSpace_of_compactSpace (pullback.fst (D.map hji) p)
  have := QuasiCompact.compactSpace_of_compactSpace (pullback.fst (D.map hji) q)
  have := quasiSeparatedSpace_of_quasiSeparated (pullback.fst (D.map hji) q)
  have : LocallyOfFinitePresentation b := by
    have : LocallyOfFinitePresentation (b ≫ pullback.fst (D.map hji) q) := by
      rw [hb₁]
      infer_instance
    exact locallyOfFinitePresentation_of_comp b (pullback.fst (D.map hji) q)
  -- Hence `b` is an isomorphism over some later stage `Dₖ`.
  obtain ⟨k, hkj, hk⟩ := hc.exists_isIso_pullbackMap b hb₁
  -- `Dₖ ×_{Dⱼ} (Dⱼ ×_{Dᵢ} Z) ≅ Dₖ ×_{Dᵢ} Z`.
  let ψ {Z : Scheme.{u}} (r : Z ⟶ D.obj i) :
      pullback (D.map hkj) (pullback.fst (D.map hji) r) ≅ pullback (D.map (hkj ≫ hji)) r :=
    pullbackRightPullbackFstIso (D.map hji) r (D.map hkj) ≪≫
      pullback.congrHom (D.map_comp hkj hji).symm rfl
  let bK := pullback.map (D.map hkj) (pullback.fst (D.map hji) p) (D.map hkj)
    (pullback.fst (D.map hji) q) (𝟙 _) b (𝟙 _) (by simp) (by exact hb₁.symm)
  have : IsIso bK := hk
  let e := (ψ p).symm ≪≫ asIso bK ≪≫ ψ q
  refine ⟨k, hkj ≫ hji, e, by simp [e, ψ, bK], ?_⟩
  apply pullback.hom_ext
  · simpa [e, ψ, bK] using ((reassoc_of% ha) (c.π.app k)).symm
  · have h := congrArg (· ≫ pullback.snd (D.map hji) q) hb₂
    simp only [Category.assoc] at h
    have key : pullback.map (c.π.app i) p (D.map (hkj ≫ hji)) p (c.π.app k) (𝟙 _) (𝟙 _)
        (by simp) (by simp) ≫ (ψ p).inv ≫ pullback.snd (D.map hkj) (pullback.fst (D.map hji) p) =
        pullback.map (c.π.app i) p (D.map hji) p (c.π.app j) (𝟙 _) (𝟙 _) (by simp) (by simp) := by
      apply pullback.hom_ext <;> simp [ψ]
    have h' := congrArg (· ≫ b ≫ pullback.snd (D.map hji) q) key
    simpa [e, ψ, bK] using h'.trans h

include hc in
private theorem exists_isIso_overPullback
    {i : I} {X Y : Over (D.obj i)}
    [CompactSpace X.left] [CompactSpace Y.left] [QuasiSeparatedSpace Y.left]
    (g : X ⟶ Y) [LocallyOfFinitePresentation g.left]
    [IsIso ((Over.pullback (c.π.app i)).map g).left] :
    ∃ (j : I) (a : j ⟶ i), IsIso ((Over.pullback (D.map a)).map g).left := by
  let m {T : Scheme.{u}} (t : T ⟶ D.obj i) :=
    pullback.map t X.hom t Y.hom (𝟙 T) g.left (𝟙 _) (by simp) (by simp)
  have h {T : Scheme.{u}} (t : T ⟶ D.obj i) :
      (pullbackSymmetry t X.hom).hom ≫ ((Over.pullback t).map g).left =
        m t ≫ (pullbackSymmetry t Y.hom).hom := by
    apply pullback.hom_ext <;> simp [m]
  have : IsIso (m (c.π.app i)) := by
    have : IsIso (m (c.π.app i) ≫ (pullbackSymmetry (c.π.app i) Y.hom).hom) := by
      rw [← h]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (pullbackSymmetry (c.π.app i) Y.hom).hom
  obtain ⟨j, a, ha⟩ := hc.exists_isIso_pullbackMap
    g.left (Over.w g)
  have : IsIso (m (D.map a)) := ha
  have : IsIso ((pullbackSymmetry (D.map a) X.hom).hom ≫
      ((Over.pullback (D.map a)).map g).left) := by
    rw [h]
    infer_instance
  exact ⟨j, a, IsIso.of_isIso_comp_left (pullbackSymmetry (D.map a) X.hom).hom _⟩

include hc in
private theorem exists_mono_pullback_snd {i : I}
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] (p : X ⟶ D.obj i)
    [LocallyOfFiniteType p] [QuasiCompact p]
    [Mono (pullback.snd p (c.π.app i))] :
    ∃ (j : I) (a : j ⟶ i), Mono (pullback.snd p (D.map a)) := by
  let g : Over.mk p ⟶ Over.mk (pullback.snd p p ≫ p) :=
    Over.homMk (pullback.diagonal p) (by simp)
  have : LocallyOfFinitePresentation (pullback.diagonal p ≫ pullback.fst p p) := by
    rw [pullback.diagonal_fst]
    infer_instance
  have : LocallyOfFinitePresentation g.left :=
    locallyOfFinitePresentation_of_comp (pullback.diagonal p) (pullback.fst p p)
  have : Mono (pullback.fst (c.π.app i) p) := by
    rw [← pullbackSymmetry_hom_comp_snd (c.π.app i) p]
    infer_instance
  have hd : IsIso (pullback.diagonal (pullback.fst (c.π.app i) p)) := inferInstance
  rw [diagonal_pullback_fst] at hd
  have : IsIso ((Over.pullback (c.π.app i)).map g).left :=
    (MorphismProperty.cancel_right_of_respectsIso (MorphismProperty.isomorphisms Scheme.{u})
      _ _).mp ((MorphismProperty.cancel_left_of_respectsIso
        (MorphismProperty.isomorphisms Scheme.{u}) _ _).mp hd)
  have : CompactSpace (Over.mk p : Over (D.obj i)).left := ‹CompactSpace X›
  have : CompactSpace (Over.mk (pullback.snd p p ≫ p) : Over (D.obj i)).left :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd p p)
  have : QuasiSeparatedSpace
      (Over.mk (pullback.snd p p ≫ p) : Over (D.obj i)).left :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd p p)
  obtain ⟨j, a, ha⟩ := exists_isIso_overPullback hc g
  have hd : IsIso (pullback.diagonal (pullback.fst (D.map a) p)) := by
    rw [diagonal_pullback_fst]
    exact (MorphismProperty.cancel_left_of_respectsIso (MorphismProperty.isomorphisms Scheme.{u})
      _ _).mpr ((MorphismProperty.cancel_right_of_respectsIso
        (MorphismProperty.isomorphisms Scheme.{u}) _ _).mpr ha)
  have : Mono (pullback.fst (D.map a) p) := (pullback.isIso_diagonal_iff _).mp hd
  refine ⟨j, a, ?_⟩
  rw [← pullbackSymmetry_hom_comp_fst p (D.map a)]
  infer_instance

include hc in
/-- A quasi-compact locally finite type morphism from a quasi-compact quasi-separated scheme
becomes a monomorphism at a finite stage if it is one over the limit.
The affine-transition base diagram need not consist of quasi-compact or quasi-separated schemes.
Stacks, Tag 01ZP. -/
theorem exists_mono_pullbackMap
    {i : I} {X Y : Scheme.{u}} {p : X ⟶ D.obj i} {q : Y ⟶ D.obj i}
    [CompactSpace X] [QuasiSeparatedSpace X]
    (g : X ⟶ Y) (hg : g ≫ q = p) [QuasiCompact g] [LocallyOfFiniteType g]
    [Mono (pullback.map (c.π.app i) p (c.π.app i) q (𝟙 _) g (𝟙 _)
      (by simp) (by simp [hg]))] :
    ∃ (j : I) (a : j ⟶ i),
      Mono (pullback.map (D.map a) p (D.map a) q (𝟙 _) g (𝟙 _)
        (by simp) (by simp [hg])) := by
  refine (MorphismProperty.monomorphisms Scheme.{u}).exists_pullbackMap_of_pullbackOver
    c g hg ?_ ‹_›
  intro b hb
  have : Mono (pullback.snd (g ≫ b.inv)
      ((c.pullbackOver q).π.app (Over.mk (𝟙 i)))) := hb
  exact exists_mono_pullback_snd (hc.pullbackOver q) (g ≫ b.inv)

include hc in
/-- Let `S = lim Dⱼ` be a cofiltered limit of quasi-compact quasi-separated schemes with affine
transition maps, and let `A` and `B` be schemes over a member `Dᵢ`, with `A` quasi-compact and
quasi-separated over `Dᵢ` and `B` locally of finite presentation over `Dᵢ`. Every morphism
`u : A ×_{Dᵢ} S ⟶ B ×_{Dᵢ} S` over `S` is the base change of a morphism
`v : A ×_{Dᵢ} Dⱼ ⟶ B ×_{Dᵢ} Dⱼ` over some `Dⱼ`, up to the identifications of
`(A ×_{Dᵢ} Dⱼ) ×_{Dⱼ} S` with `A ×_{Dᵢ} S` given by `Over.pullbackCompIsoOfEq`. Stacks,
Lemma 32.10.1 (01ZM), descent of morphisms. -/
theorem exists_overPullback_map_comp_eq [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] {i : I} {A B : Over (D.obj i)} [QuasiCompact A.hom]
    [QuasiSeparated A.hom] [LocallyOfFinitePresentation B.hom]
    (u : (Over.pullback (c.π.app i)).obj A ⟶ (Over.pullback (c.π.app i)).obj B) :
    ∃ (j : I) (f : j ⟶ i), c.LiftsAlong u f := by
  have hu : u.left ≫ pullback.snd B.hom (c.π.app i) = pullback.snd A.hom (c.π.app i) := Over.w u
  -- Descend `u`, written with the base as the first factor of the pullbacks.
  obtain ⟨j, f, b, hb₁, hb₂⟩ := hc.exists_pullbackMap_comp_eq (p := A.hom) (q := B.hom)
    ((pullbackSymmetry _ _).hom ≫ u.left ≫ (pullbackSymmetry _ _).inv) (by simp [hu])
  refine ⟨j, f, (Cone.liftsAlong_iff u f).mpr
    ⟨Over.homMk ((pullbackSymmetry _ _).hom ≫ b ≫ (pullbackSymmetry _ _).inv) (by simp [hb₁]), ?_⟩⟩
  have hb := congrArg (· ≫ pullback.snd _ _) hb₂
  simp only [Category.assoc, pullback.lift_snd, Category.comp_id, pullbackSymmetry_inv_comp_snd]
    at hb
  -- The identity is checked on the two projections out of `B ×_{Dᵢ} S`.
  ext1
  apply pullback.hom_ext
  · have key : pullback.fst (pullback.snd A.hom (D.map f)) (c.π.app j) ≫
        (pullbackSymmetry A.hom (D.map f)).hom =
        ((Over.pullbackCompIsoOfEq (c.w f)).hom.app A).left ≫
          (pullbackSymmetry (c.π.app i) A.hom).inv ≫
            pullback.map (c.π.app i) A.hom (D.map f) A.hom (c.π.app j) (𝟙 _) (𝟙 _) (by simp)
              (by simp) := by
      apply pullback.hom_ext
      · simp [pullback.condition]
      · simp
    simp [reassoc_of% key, hb]
  · simp [hu]

include hc in
/-- Let `S = lim Dⱼ` be a cofiltered limit of quasi-compact schemes with affine transition maps,
and let `u v : A ⟶ B` be morphisms of schemes over a member `Dⱼ`, with `A` quasi-compact and `B`
locally of finite type over `Dⱼ`. If the base changes of `u` and `v` to `S` agree, then so do their
base changes to some `Dₖ`. This is Mathlib's
`AlgebraicGeometry.Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType` (Stacks, Tag 01ZC) for
the base change functors of over categories. -/
theorem exists_overPullback_map_eq_map [∀ i, CompactSpace (D.obj i)] {j : I}
    {A B : Over (D.obj j)} [QuasiCompact A.hom] [LocallyOfFiniteType B.hom] (u v : A ⟶ B)
    (huv : (Over.pullback (c.π.app j)).map u = (Over.pullback (c.π.app j)).map v) :
    ∃ (k : I) (g : k ⟶ j),
      (Over.pullback (D.map g)).map u = (Over.pullback (D.map g)).map v := by
  let t : D.pullbackOver A.hom ⟶ (Functor.const (Over j)).obj (D.obj j) :=
    { app k := pullback.snd _ _ ≫ A.hom
      naturality k l f := by simp [D.pullbackOver_map_snd_assoc A.hom f] }
  have hlim := (Over.pullback_map_eq_map_iff _ u v).mp huv
  obtain ⟨k, _, e⟩ := AlgebraicGeometry.Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    (D.pullbackOver A.hom) t B.hom _ (hc.pullbackOver A.hom) (i := Over.mk (𝟙 j))
    (pullback.snd _ _ ≫ u.left) (pullback.snd _ _ ≫ v.left) (by simp [t]) (by simp [t])
    (by simpa [Cone.pullbackOver_π_app_snd_assoc] using
      congrArg ((pullbackSymmetry (c.π.app j) A.hom).hom ≫ ·) hlim)
  refine ⟨k.left, k.hom, (Over.pullback_map_eq_map_iff _ u v).mpr ?_⟩
  simpa [D.pullbackOver_map_snd_assoc] using
    congrArg ((pullbackSymmetry A.hom (D.map k.hom)).hom ≫ ·) e

end CategoryTheory.Limits.IsLimit
