/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Limits.BaseChange
public import TauCeti.CategoryTheory.Comma.Over.Pullback

/-!
# Descent of morphisms of finitely presented schemes along cofiltered limits

Let `D : I ⥤ Scheme` be a cofiltered diagram of quasi-compact quasi-separated schemes with affine
transition maps and limit cone `c`, so that `S = lim Dⱼ`. Mathlib proves that for a scheme `X`
locally of finite presentation over a base, morphisms from `S` to `X` over the base are the
filtered colimit of the morphisms from the `Dⱼ` (Stacks, Proposition 32.6.1 (01ZC)). Applied to the
base changes `Dⱼ ×_{Dᵢ} X` of `CategoryTheory.Functor.pullbackOver`, which have limit
`S ×_{Dᵢ} X`, this shows that morphisms over the limit between base changes of schemes over a
member `Dᵢ` descend to some `Dⱼ` (Stacks, Lemma 32.10.1 (01ZM)), and that a morphism of schemes
of finite presentation over `Dᵢ` is an isomorphism over some `Dⱼ` as soon as it is one over the
limit (Stacks, Lemma 32.8.11 (081E)): the inverse over the limit descends, and the two composites,
being the identity over the limit, are the identity at some later stage.

## Main declarations

* `CategoryTheory.Limits.IsLimit.exists_pullbackMap_comp_eq`: a morphism over the limit between
  base changes of schemes over `Dᵢ`, the target of finite presentation, descends to some `Dⱼ`; by
  `CategoryTheory.MorphismProperty.pullbackMap_iff_of_pullbackMap_comp_eq`, the base change to the
  limit of the descended morphism is the original morphism, up to isomorphism.
* `CategoryTheory.Limits.IsLimit.exists_isIso_pullbackMap`: a morphism of schemes of finite
  presentation over `Dᵢ` whose base change to the limit is an isomorphism is an isomorphism over
  some `Dⱼ`.
* `CategoryTheory.Limits.IsLimit.exists_hom_overPullback_of_isLimit`,
  `CategoryTheory.Limits.IsLimit.exists_overPullback_map_eq_of_isLimit`, and
  `CategoryTheory.Limits.IsLimit.exists_iso_overPullback_of_isLimit`: the bundled `Over.pullback`
  forms of morphism descent, eventual equality, and isomorphism descent.
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
theorem exists_isIso_pullbackMap [∀ i, CompactSpace (D.obj i)]
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
private theorem exists_hom_overPullback_of_isLimit_aux [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] {i₀ : I} (Y₁ Y₂ : Over (D.obj i₀))
    [QuasiCompact Y₁.hom] [QuasiSeparated Y₁.hom] [LocallyOfFinitePresentation Y₂.hom]
    (α : (Over.pullback (c.π.app i₀)).obj Y₁ ⟶ (Over.pullback (c.π.app i₀)).obj Y₂) :
    ∃ (j : I) (fj : j ⟶ i₀)
      (b : pullback (D.map fj) Y₁.hom ⟶ pullback (D.map fj) Y₂.hom)
      (hb₁ : b ≫ pullback.fst _ _ = pullback.fst _ _),
      let β : (Over.pullback (D.map fj)).obj Y₁ ⟶ (Over.pullback (D.map fj)).obj Y₂ :=
        Over.pullbackHomOfFstEq (D.map fj) b hb₁
      Over.pullbackTransport (c.w fj) (c.w fj) β = α ∧
      pullback.map (c.π.app i₀) Y₁.hom (D.map fj) Y₁.hom (c.π.app j) (𝟙 _) (𝟙 _)
          (by simp) (by simp) ≫ b =
        Over.pullbackLeftSymm (c.π.app i₀) α ≫
          pullback.map (c.π.app i₀) Y₂.hom (D.map fj) Y₂.hom (c.π.app j)
            (𝟙 _) (𝟙 _) (by simp) (by simp) := by
  let a := Over.pullbackLeftSymm (c.π.app i₀) α
  have ha : a ≫ pullback.fst (c.π.app i₀) Y₂.hom = pullback.fst (c.π.app i₀) Y₁.hom :=
    Over.pullbackLeftSymm_fst (c.π.app i₀) α
  obtain ⟨j, fj, b, hb₁, hb₂⟩ := hc.exists_pullbackMap_comp_eq a ha
  refine ⟨j, fj, b, hb₁, ?_, hb₂⟩
  rw [Over.pullbackTransport_def]
  exact (Over.pullbackCompIsoOfEq_conj_hom_of_fstEq (c.w fj) hb₁ ha hb₂).trans
    (Over.pullbackHomOfFstEq_pullbackLeftSymm (c.π.app i₀) α)

include hc in
/-- Bundled `Over.pullback` form of `exists_pullbackMap_comp_eq`: along a cofiltered limit of
quasi-compact quasi-separated schemes with affine transition morphisms, any morphism between the
`Over.pullback`s of `Y₁, Y₂ : Over (D.obj i₀)` to the limit descends to a morphism over some stage
`j` mapping to `i₀`. Stacks, Lemma 32.10.1 (01ZM), descent of morphisms. -/
theorem exists_hom_overPullback_of_isLimit [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] {i₀ : I} (Y₁ Y₂ : Over (D.obj i₀))
    [QuasiCompact Y₁.hom] [QuasiSeparated Y₁.hom] [LocallyOfFinitePresentation Y₂.hom]
    (α : (Over.pullback (c.π.app i₀)).obj Y₁ ⟶ (Over.pullback (c.π.app i₀)).obj Y₂) :
    ∃ (j : I) (fj : j ⟶ i₀)
      (β : (Over.pullback (D.map fj)).obj Y₁ ⟶ (Over.pullback (D.map fj)).obj Y₂),
      Over.pullbackTransport (c.w fj) (c.w fj) β = α :=
  let ⟨j, fj, _, _, hβ, _⟩ := hc.exists_hom_overPullback_of_isLimit_aux Y₁ Y₂ α
  ⟨j, fj, _, hβ⟩

include hc in
/-- Along a cofiltered limit of quasi-compact schemes with affine transition morphisms, two
morphisms in `Over (D.obj i₀)` (with source quasi-compact and target locally of finite type) whose
`Over.pullback`s to the limit agree already have equal `Over.pullback`s at some stage `k` mapping
to `i₀`. Stacks, Lemma 32.10.1 (01ZM), eventual equality of morphisms. -/
theorem exists_overPullback_map_eq_of_isLimit [∀ i, CompactSpace (D.obj i)] {i₀ : I}
    {Y₁ Y₂ : Over (D.obj i₀)} [QuasiCompact Y₁.hom] [LocallyOfFiniteType Y₂.hom] (β₁ β₂ : Y₁ ⟶ Y₂)
    (h : (Over.pullback (c.π.app i₀)).map β₁ = (Over.pullback (c.π.app i₀)).map β₂) :
    ∃ (k : I) (fk : k ⟶ i₀),
      (Over.pullback (D.map fk)).map β₁ = (Over.pullback (D.map fk)).map β₂ := by
  let t : D.pullbackOver Y₁.hom ⟶ (Functor.const (Over i₀)).obj (D.obj i₀) :=
    { app j := pullback.snd _ _ ≫ Y₁.hom
      naturality j k f := by simp [D.pullbackOver_map_snd_assoc Y₁.hom f] }
  have hlim : (c.pullbackOver Y₁.hom).π.app (Over.mk (𝟙 i₀)) ≫
        pullback.snd (D.map (Over.mk (𝟙 i₀)).hom) Y₁.hom ≫ β₁.left =
      (c.pullbackOver Y₁.hom).π.app (Over.mk (𝟙 i₀)) ≫
        pullback.snd (D.map (Over.mk (𝟙 i₀)).hom) Y₁.hom ≫ β₂.left := by
    rw [Cone.pullbackOver_π_app_snd_assoc, Cone.pullbackOver_π_app_snd_assoc]
    have hfst : pullback.fst Y₁.hom (c.π.app i₀) ≫ β₁.left =
        pullback.fst Y₁.hom (c.π.app i₀) ≫ β₂.left :=
      (Over.pullback_map_left_fst (c.π.app i₀) β₁).symm.trans ((congrArg (fun u ↦ u.left ≫
        pullback.fst Y₂.hom (c.π.app i₀)) h).trans
        (Over.pullback_map_left_fst (c.π.app i₀) β₂))
    have hfst' := congrArg ((pullbackSymmetry (c.π.app i₀) Y₁.hom).hom ≫ ·) hfst
    simpa only [pullbackSymmetry_hom_comp_fst_assoc] using hfst'
  obtain ⟨k, hkj, hk⟩ := AlgebraicGeometry.Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    (D.pullbackOver Y₁.hom) t Y₂.hom (c.pullbackOver Y₁.hom)
    (hc.pullbackOver Y₁.hom) (i := Over.mk (𝟙 i₀))
    (pullback.snd _ _ ≫ β₁.left) (pullback.snd _ _ ≫ β₂.left)
    (by simp [t, Over.w β₁]) (by simp [t, Over.w β₂]) hlim
  refine ⟨k.left, k.hom, Over.pullback_hom_ext ?_⟩
  rw [D.pullbackOver_map_snd_assoc Y₁.hom hkj, D.pullbackOver_map_snd_assoc Y₁.hom hkj] at hk
  have hsymm := congrArg ((pullbackSymmetry Y₁.hom (D.map k.hom)).hom ≫ ·) hk
  simp only [pullbackSymmetry_hom_comp_snd_assoc] at hsymm
  exact (Over.pullback_map_left_fst (D.map k.hom) β₁).trans
    (hsymm.trans (Over.pullback_map_left_fst (D.map k.hom) β₂).symm)

include hc in
/-- Bundled `Over.pullback` isomorphism descent: along a cofiltered limit of quasi-compact
quasi-separated schemes with affine transition morphisms, an isomorphism `e` on the limit between
the `Over.pullback`s of `Y₁, Y₂ : Over (D.obj i₀)` descends to an isomorphism `ek` at some stage
`k` mapping to `i₀` whose transport to the limit recovers `e.hom`.
Stacks, Lemma 32.10.1 (01ZM), descent of isomorphisms. -/
theorem exists_iso_overPullback_of_isLimit [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] {i₀ : I} (Y₁ Y₂ : Over (D.obj i₀))
    [QuasiCompact Y₁.hom] [QuasiSeparated Y₁.hom] [LocallyOfFinitePresentation Y₁.hom]
    [QuasiCompact Y₂.hom] [QuasiSeparated Y₂.hom] [LocallyOfFinitePresentation Y₂.hom]
    (e : (Over.pullback (c.π.app i₀)).obj Y₁ ≅ (Over.pullback (c.π.app i₀)).obj Y₂) :
    ∃ (k : I) (fk : k ⟶ i₀)
      (ek : (Over.pullback (D.map fk)).obj Y₁ ≅ (Over.pullback (D.map fk)).obj Y₂),
      Over.pullbackTransport (c.w fk) (c.w fk) ek.hom = e.hom := by
  obtain ⟨j, fj, b, hb₁, hβ, hb₂⟩ := hc.exists_hom_overPullback_of_isLimit_aux Y₁ Y₂ e.hom
  let eSymm := Over.pullbackLeftSymmIso (c.π.app i₀) e
  have ha_iso : IsIso (Over.pullbackLeftSymm (c.π.app i₀) e.hom) := by
    rw [← Over.pullbackLeftSymmIso_hom (c.π.app i₀) e]
    exact eSymm.isIso_hom
  have : IsIso (pullback.map (c.π.app j) (pullback.fst (D.map fj) Y₁.hom)
      (c.π.app j) (pullback.fst (D.map fj) Y₂.hom) (𝟙 _) b (𝟙 _) (by simp)
      (by exact hb₁.symm)) :=
    (MorphismProperty.pullbackMap_iff_of_pullbackMap_comp_eq
      (.isomorphisms Scheme) fj (Over.pullbackLeftSymm_fst (c.π.app i₀) e.hom) hb₁ hb₂).mpr
      ha_iso
  obtain ⟨k, hkj, hk⟩ := hc.exists_isIso_pullbackMap b hb₁
  let β : (Over.pullback (D.map fj)).obj Y₁ ⟶ (Over.pullback (D.map fj)).obj Y₂ :=
    Over.pullbackHomOfFstEq (D.map fj) b hb₁
  let βK := Over.pullbackTransport (D.map_comp hkj fj).symm (D.map_comp hkj fj).symm β
  let bK := pullback.map (D.map hkj) (pullback.fst (D.map fj) Y₁.hom)
    (D.map hkj) (pullback.fst (D.map fj) Y₂.hom) (𝟙 _) b (𝟙 _) (by simp)
    (by exact hb₁.symm)
  have : IsIso bK := hk
  let eIso := pullbackSymmetry Y₁.hom (D.map (hkj ≫ fj)) ≪≫
    (pullbackRightPullbackFstIsoOfEq (D.map hkj) (D.map fj) (D.map (hkj ≫ fj))
      (D.map_comp hkj fj).symm Y₁.hom).symm ≪≫
    asIso bK ≪≫
    pullbackRightPullbackFstIsoOfEq (D.map hkj) (D.map fj) (D.map (hkj ≫ fj))
      (D.map_comp hkj fj).symm Y₂.hom ≪≫
    pullbackSymmetry (D.map (hkj ≫ fj)) Y₂.hom
  have hbK : (Over.forget (D.obj k)).map βK = eIso.hom := by
    simpa [βK, β, eIso, bK, Over.pullbackTransport_def] using
      Over.pullbackCompIsoOfEq_conj_left_eq_pullbackMap (D.map_comp hkj fj).symm b hb₁
  have : IsIso ((Over.forget (D.obj k)).map βK) := by rw [hbK]; exact eIso.isIso_hom
  have : IsIso βK := isIso_of_reflects_iso βK (Over.forget (D.obj k))
  refine ⟨k, hkj ≫ fj, asIso βK, ?_⟩
  rw [asIso_hom, Over.pullbackTransport_comp (c.w hkj) (D.map_comp _ _).symm
    (D.map_comp _ _).symm (c.w (hkj ≫ fj)) (c.w (hkj ≫ fj)) (c.w fj) (c.w fj) β, hβ]

end CategoryTheory.Limits.IsLimit
