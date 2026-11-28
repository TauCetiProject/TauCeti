/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Limits.Finite.Presentation
public import TauCeti.CategoryTheory.Limits.Shapes.Pullback.Map

/-!
# Open immersions of finitely presented schemes descend along cofiltered limits

Let `D : I ⥤ Scheme` be a cofiltered diagram of schemes with affine transition maps and limit
`S = lim Dⱼ`, and let `g : X ⟶ Y` be a locally finitely presented morphism of schemes over a member
`Dᵢ`, with `X` quasi-compact and `Y` quasi-separated. If the base change `g_S` of `g` to `S` is an
open immersion, then so is the base change of `g` to some `Dⱼ` (Stacks, Lemma 32.8.12 (0EUU)).

The image of `g_S` is a quasi-compact open of `S ×_{Dᵢ} Y`, which is the limit of the base changes
`Dₗ ×_{Dᵢ} Y`. Quasi-compact opens of such a limit come from a member (Stacks, Tag 01Z4,
Mathlib's `AlgebraicGeometry.exists_preimage_eq`), so the image is the preimage of a
quasi-compact open `V ⊆ Dₗ ×_{Dᵢ} Y`; after enlarging `l`, the base change of `g` to `Dₗ` lands
in `V` (Mathlib's `AlgebraicGeometry.exists_map_eq_top`). The corestriction to `V` becomes an
isomorphism over the limit, hence is an isomorphism at a later stage by
`CategoryTheory.Limits.IsLimit.exists_isIso_pullbackMap` (Stacks, Lemma 32.8.11 (081E)), and
the base change of `g` is this isomorphism followed by the inclusion of `V`.

## Main declarations

* `CategoryTheory.Limits.IsLimit.exists_isOpenImmersion_pullbackMap`: a morphism over `Dᵢ` whose
  base change to the limit is an open immersion is an open immersion over some `Dⱼ`.
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace CategoryTheory.Limits.IsLimit

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ Scheme.{u}}
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] {c : Cone D} (hc : IsLimit c)

include hc in
/-- The case of `exists_isOpenImmersion_pullbackMap` in which some quasi-compact open `V` of `Y`
contains the image of `g`, and its preimage in `S ×_{Dᵢ} Y` lies in the image of the base change
of `g` to `S`. -/
private lemma exists_isOpenImmersion_pullbackMap_of_le_opensRange {i : I}
    {X Y : Scheme.{u}} {p : X ⟶ D.obj i} {q : Y ⟶ D.obj i} [CompactSpace X]
    [QuasiSeparatedSpace Y] (g : X ⟶ Y) (hg : g ≫ q = p) [LocallyOfFinitePresentation g]
    [IsOpenImmersion
      (pullback.map (c.π.app i) p (c.π.app i) q (𝟙 _) g (𝟙 _) (by simp) (by simp [hg]))]
    (V : Y.Opens) (hVc : IsCompact (V : Set Y)) (hgV : g ⁻¹ᵁ V = ⊤)
    (hV : pullback.snd (c.π.app i) q ⁻¹ᵁ V ≤
      (pullback.map (c.π.app i) p (c.π.app i) q (𝟙 _) g (𝟙 _) _ _).opensRange) :
    ∃ (j : I) (hji : j ⟶ i), IsOpenImmersion
      (pullback.map (D.map hji) p (D.map hji) q (𝟙 _) g (𝟙 _) (by simp) (by simp [hg])) := by
  have : CompactSpace V := isCompact_iff_compactSpace.mp hVc
  -- `g` factors as `ψ : X ⟶ V` followed by the inclusion of `V`.
  let ψ : X ⟶ V := IsOpenImmersion.lift V.ι g (by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hgV.ge trivial)
  have hψ : ψ ≫ V.ι = g := IsOpenImmersion.lift_fac _ _ _
  have hψq : ψ ≫ V.ι ≫ q = p := by rw [reassoc_of% hψ, hg]
  -- Over every base, the base change of `g` is that of `ψ` followed by that of `V.ι`, which is an
  -- open immersion.
  have fac {T : Scheme.{u}} (t : T ⟶ D.obj i) :
      pullback.map t p t (V.ι ≫ q) (𝟙 _) ψ (𝟙 _) (by simp) (by simp [hψq]) ≫
        pullback.map t (V.ι ≫ q) t q (𝟙 _) V.ι (𝟙 _) (by simp) (by simp) =
      pullback.map t p t q (𝟙 _) g (𝟙 _) (by simp) (by simp [hg]) := by
    apply pullback.hom_ext <;> simp [hψ]
  have hι {T : Scheme.{u}} (t : T ⟶ D.obj i) :
      IsOpenImmersion (pullback.map t (V.ι ≫ q) t q (𝟙 _) V.ι (𝟙 _) (by simp) (by simp)) :=
    MorphismProperty.pullbackMap (P := @IsOpenImmersion)
      (inferInstanceAs (IsOpenImmersion (𝟙 T))) inferInstance (by simp) rfl
  -- Over the limit, the base change `Ψ` of `ψ` is an open immersion, and it is surjective since
  -- the image of the base change of `g` contains the preimage of `V`.
  let Ψ := pullback.map (c.π.app i) p (c.π.app i) (V.ι ≫ q) (𝟙 _) ψ (𝟙 _) (by simp)
    (by simp [hψq])
  let ι := pullback.map (c.π.app i) (V.ι ≫ q) (c.π.app i) q (𝟙 _) V.ι (𝟙 _) (by simp) (by simp)
  have := hι (c.π.app i)
  have : IsOpenImmersion (Ψ ≫ ι) := by rw [fac]; infer_instance
  have : IsOpenImmersion Ψ := .of_comp _ ι
  have : IsIso Ψ := by
    refine (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, ⟨fun z ↦ ?_⟩⟩
    obtain ⟨x, hx⟩ := hV (show ι z ∈ pullback.snd (c.π.app i) q ⁻¹ᵁ V by
      rw [Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, pullback.lift_snd,
        Scheme.Hom.comp_apply]
      exact (pullback.snd (c.π.app i) (V.ι ≫ q) z).property)
    refine ⟨x, ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, fac]
    exact hx
  -- Hence some finite-stage base change of `ψ` is an isomorphism, and that of `g` is the
  -- composite of this isomorphism with the open immersion base changed from `V.ι`.
  have : QuasiSeparatedSpace V := quasiSeparatedSpace_of_quasiSeparated V.ι
  have : LocallyOfFinitePresentation (ψ ≫ V.ι) := hψ ▸ inferInstance
  have : LocallyOfFinitePresentation ψ := locallyOfFinitePresentation_of_comp ψ V.ι
  obtain ⟨j, hji, hj⟩ := hc.exists_isIso_pullbackMap ψ hψq
  refine ⟨j, hji, ?_⟩
  have := hι (D.map hji)
  rw [← fac]
  infer_instance

include hc in
/-- If the base change of `g` to the limit is an open immersion, its image is the preimage of a
quasi-compact open `V` of the base change of `Y` to some `Dₗ` over `Dᵢ` which contains the image
of the base change of `g` to `Dₗ`. -/
private lemma exists_opens_preimage_eq_opensRange {i : I}
    {X Y : Scheme.{u}} {p : X ⟶ D.obj i} {q : Y ⟶ D.obj i} [CompactSpace X] (g : X ⟶ Y)
    (hg : g ≫ q = p)
    [IsOpenImmersion
      (pullback.map (c.π.app i) p (c.π.app i) q (𝟙 _) g (𝟙 _) (by simp) (by simp [hg]))] :
    ∃ (l : Over i) (V : (pullback (D.map l.hom) q).Opens),
      IsCompact (V : Set ↑(pullback (D.map l.hom) q)) ∧
      pullback.map (D.map l.hom) p (D.map l.hom) q (𝟙 _) g (𝟙 _) (by simp) (by simp [hg]) ⁻¹ᵁ V =
        ⊤ ∧
      pullback.map (c.π.app i) q (D.map l.hom) q (c.π.app l.left) (𝟙 _) (𝟙 _) (by simp)
          (by simp) ⁻¹ᵁ V =
        (pullback.map (c.π.app i) p (c.π.app i) q (𝟙 _) g (𝟙 _) _ _).opensRange := by
  let φ := pullback.map (c.π.app i) p (c.π.app i) q (𝟙 _) g (𝟙 _) (by simp) (by simp [hg])
  let φB (j : Over i) : (D.pullbackOver p).obj j ⟶ (D.pullbackOver q).obj j :=
    pullback.map (D.map j.hom) p (D.map j.hom) q (𝟙 _) g (𝟙 _) (by simp) (by simp [hg])
  have π_φB (j : Over i) :
      (c.pullbackOver p).π.app j ≫ φB j = φ ≫ (c.pullbackOver q).π.app j := by
    apply pullback.hom_ext <;> simp [φB, φ]
  have map_φB {j k : Over i} (f : j ⟶ k) :
      (D.pullbackOver p).map f ≫ φB k = φB j ≫ (D.pullbackOver q).map f := by
    apply pullback.hom_ext <;> simp [φB]
  -- The base changes of `X` are quasi-compact, since the projections to `X` are affine.
  have := isAffineHom_π_app D c hc i
  have : CompactSpace ↑(pullback (c.π.app i) p) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd (c.π.app i) p)
  have (j : Over i) : CompactSpace ((D.pullbackOver p).obj j) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd (D.map j.hom) p)
  -- The image of `φ` is a quasi-compact open of the limit of the base changes of `Y`, hence the
  -- preimage of a quasi-compact open `V` of some member.
  obtain ⟨k, V, hVc, hVφ⟩ := exists_preimage_eq _ _ (hc.pullbackOver q) φ.opensRange
    (isCompact_range φ.continuous)
  -- The preimage of `V` in the corresponding member for `X` pulls back to everything in the
  -- limit, so it is everything at some later member.
  obtain ⟨l, f, hl⟩ := exists_map_eq_top _ _ (hc.pullbackOver p) (φB k ⁻¹ᵁ V) (by
    rw [← Scheme.Hom.comp_preimage, π_φB, Scheme.Hom.comp_preimage, hVφ]
    exact φ.preimage_opensRange)
  refine ⟨l, (D.pullbackOver q).map f ⁻¹ᵁ V, ?_, ?_, ?_⟩
  · exact QuasiCompact.isCompact_preimage _ V.isOpen hVc
  · rw [← Scheme.Hom.comp_preimage, ← map_φB, Scheme.Hom.comp_preimage, hl]
  · rw [← Scheme.Hom.comp_preimage, ← hVφ]
    exact congrArg (· ⁻¹ᵁ V) ((c.pullbackOver q).w f)

include hc in
/-- Let `S = lim Dⱼ` be a cofiltered limit of schemes with affine transition maps, and
`g : X ⟶ Y` a locally finitely presented morphism of schemes over a member `Dᵢ`, from a
quasi-compact scheme to a quasi-separated scheme. If the base change of `g` to `S` is an open
immersion, then so is its base change to some `Dⱼ`. The members of the base diagram need not be
quasi-compact or quasi-separated. Stacks, Lemma 32.8.12 (0EUU). -/
theorem exists_isOpenImmersion_pullbackMap {i : I} {X Y : Scheme.{u}} {p : X ⟶ D.obj i}
    {q : Y ⟶ D.obj i} [CompactSpace X] [QuasiSeparatedSpace Y] (g : X ⟶ Y) (hg : g ≫ q = p)
    [LocallyOfFinitePresentation g]
    [IsOpenImmersion
      (pullback.map (c.π.app i) p (c.π.app i) q (𝟙 _) g (𝟙 _) (by simp) (by simp [hg]))] :
    ∃ (j : I) (hji : j ⟶ i), IsOpenImmersion
      (pullback.map (D.map hji) p (D.map hji) q (𝟙 _) g (𝟙 _) (by simp) (by simp [hg])) := by
  -- The image of the base change `φ` of `g` to the limit descends to an open `V` at some `Dₗ`.
  obtain ⟨l, V, hVc, hgV, hVφ⟩ := hc.exists_opens_preimage_eq_opensRange g hg
  let φ := pullback.map (c.π.app i) p (c.π.app i) q (𝟙 _) g (𝟙 _) (by simp) (by simp [hg])
  let gl := pullback.map (D.map l.hom) p (D.map l.hom) q (𝟙 _) g (𝟙 _) (by simp) (by simp [hg])
  have hgl : gl ≫ pullback.fst _ _ = pullback.fst _ _ := by simp [gl]
  -- The hypotheses on `g` pass to its base change `gl`, since the projections are affine.
  have : CompactSpace ↑(pullback (D.map l.hom) p) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd (D.map l.hom) p)
  have : QuasiSeparatedSpace ↑(pullback (D.map l.hom) q) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd (D.map l.hom) q)
  have : LocallyOfFinitePresentation gl :=
    MorphismProperty.pullbackMap (P := @LocallyOfFinitePresentation)
      (inferInstanceAs (LocallyOfFinitePresentation (𝟙 _))) ‹_› (by simp) hg.symm
  -- These isomorphisms `e` identify the second projection with the projection to `Dₗ ×_{Dᵢ} Y`.
  let e {Z : Scheme.{u}} (s : Z ⟶ D.obj i) := c.pullbackOverIso l.hom s
  have hcompat :
      pullback.map (c.π.app i) p (D.map l.hom) p (c.π.app l.left) (𝟙 _) (𝟙 _)
          (by simp) (by simp) ≫ gl =
        φ ≫ pullback.map (c.π.app i) q (D.map l.hom) q (c.π.app l.left) (𝟙 _) (𝟙 _)
          (by simp) (by simp) := by
    apply pullback.hom_ext <;> simp [gl, φ]
  have hφ := c.pullbackMap_eq_of_pullbackMap_comp_eq l.hom (a := φ) (by simp [φ]) hgl hcompat
  have : IsOpenImmersion (pullback.map (c.π.app l.left) (pullback.fst (D.map l.hom) p)
      (c.π.app l.left) (pullback.fst (D.map l.hom) q) (𝟙 _) gl (𝟙 _) (by simp)
      (by simp [hgl])) :=
    (MorphismProperty.pullbackMap_iff_of_pullbackMap_comp_eq @IsOpenImmersion l.hom
      (a := φ) (by simp [φ]) hgl hcompat).mpr inferInstance
  have hsnd := c.pullbackOverIso_hom_pullbackMap l.hom q
  obtain ⟨j, hjl, hj⟩ := hc.exists_isOpenImmersion_pullbackMap_of_le_opensRange gl hgl V hVc hgV
    (by
      intro z hz
      obtain ⟨x, hx⟩ : (e q).hom z ∈ φ.opensRange := by
        rw [← hVφ, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, hsnd]
        exact hz
      refine ⟨(e p).inv x, ?_⟩
      rw [← Scheme.Hom.comp_apply, hφ, Iso.inv_hom_id_assoc, Scheme.Hom.comp_apply]
      exact (congrArg (e q).inv hx).trans (by simp))
  -- Transport the open immersion at `Dⱼ ×_{Dₗ} (Dₗ ×_{Dᵢ} -)` back to `Dⱼ ×_{Dᵢ} -`.
  refine ⟨j, hjl ≫ l.hom, ?_⟩
  have key (w : D.obj j ⟶ D.obj i) (hw : D.map hjl ≫ D.map l.hom = w) :
      IsOpenImmersion (pullback.map w p w q (𝟙 _) g (𝟙 _) (by simp) (by simp [hg])) := by
    subst hw
    rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsOpenImmersion)
      (pullbackRightPullbackFstIso (D.map l.hom) p (D.map hjl)).hom,
      ← pullbackRightPullbackFstIso_hom_naturality p q (D.map l.hom) (D.map hjl) g hg,
      MorphismProperty.cancel_right_of_respectsIso (P := @IsOpenImmersion)]
    exact hj
  exact key _ (D.map_comp hjl l.hom).symm

end CategoryTheory.Limits.IsLimit
