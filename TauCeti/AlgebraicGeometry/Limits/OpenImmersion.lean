/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Limits.FinitePresentation

/-!
# Open immersions of finitely presented schemes descend along cofiltered limits

Let `D : I ⥤ Scheme` be a cofiltered diagram of quasi-compact quasi-separated schemes with affine
transition maps and limit `S = lim Dⱼ`, and let `g : X ⟶ Y` be a morphism of schemes over a member
`Dᵢ`, with `X` locally of finite presentation and quasi-compact over `Dᵢ` and `Y` locally of finite
type and quasi-separated over `Dᵢ`. If the base change `g_S` of `g` to `S` is an open immersion,
then so is the base change of `g` to some `Dⱼ` (Stacks, Lemma 32.8.12 (0EUU)).

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

/-- Base change in two stages, along `v` and then along `u`, is base change along `u ≫ v`, up to
canonical isomorphisms which are compatible with the base changes of a morphism `g` and with the
second projections. -/
private lemma exists_iso_pullback_map_pullback_map {C : Type*} [Category* C] [HasPullbacks C]
    {A B T X Y : C} (u : A ⟶ B) (v : B ⟶ T) (w : A ⟶ T) (huv : u ≫ v = w) {p : X ⟶ T}
    {q : Y ⟶ T} (g : X ⟶ Y) (hg : g ≫ q = p) :
    ∃ (eX : pullback u (pullback.fst v p) ≅ pullback w p)
      (eY : pullback u (pullback.fst v q) ≅ pullback w q),
      pullback.map u (pullback.fst v p) u (pullback.fst v q) (𝟙 _)
          (pullback.map v p v q (𝟙 _) g (𝟙 _) (by simp) (by simp [hg])) (𝟙 _) (by simp)
          (by simp) =
        eX.hom ≫ pullback.map w p w q (𝟙 _) g (𝟙 _) (by simp) (by simp [hg]) ≫ eY.inv ∧
      eY.hom ≫ pullback.map w q v q u (𝟙 _) (𝟙 _) (by simp [huv]) (by simp) =
        pullback.snd _ _ := by
  subst huv
  refine ⟨pullbackRightPullbackFstIso v p u, pullbackRightPullbackFstIso v q u, ?_, ?_⟩
  · rw [← Category.assoc, Iso.eq_comp_inv]
    apply pullback.hom_ext <;> simp
  · apply pullback.hom_ext <;> simp [pullback.condition]

namespace CategoryTheory.Limits.IsLimit

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ Scheme.{u}}
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] {c : Cone D} (hc : IsLimit c)

include hc in
/-- The case of `exists_isOpenImmersion_pullbackMap` in which some quasi-compact open `V` of `Y`
contains the image of `g`, and its preimage in `S ×_{Dᵢ} Y` lies in the image of the base change
of `g` to `S`. -/
private lemma exists_isOpenImmersion_pullbackMap_of_le_opensRange
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] {i : I}
    {X Y : Scheme.{u}} {p : X ⟶ D.obj i} {q : Y ⟶ D.obj i} [LocallyOfFinitePresentation p]
    [QuasiCompact p] [LocallyOfFiniteType q] [QuasiSeparated q] (g : X ⟶ Y) (hg : g ≫ q = p)
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
  obtain ⟨j, hji, hj⟩ := hc.exists_isIso_pullbackMap ψ hψq
  refine ⟨j, hji, ?_⟩
  have := hι (D.map hji)
  rw [← fac]
  infer_instance

include hc in
/-- If the base change of `g` to the limit is an open immersion, its image is the preimage of a
quasi-compact open `V` of the base change of `Y` to some `Dₗ` over `Dᵢ` which contains the image
of the base change of `g` to `Dₗ`. -/
private lemma exists_opens_preimage_eq_opensRange [∀ i, CompactSpace (D.obj i)] {i : I}
    {X Y : Scheme.{u}} {p : X ⟶ D.obj i} {q : Y ⟶ D.obj i} [QuasiCompact p] (g : X ⟶ Y)
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
  -- The image of `φ` is a quasi-compact open of the limit of the base changes of `Y`, hence the
  -- preimage of a quasi-compact open `V` of some member.
  have : CompactSpace (((Functor.const I).obj c.pt).obj i) :=
    Scheme.compactSpace_of_isLimit D c hc
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
/-- Let `S = lim Dⱼ` be a cofiltered limit of quasi-compact quasi-separated schemes with affine
transition maps, and `g : X ⟶ Y` a morphism of schemes over a member `Dᵢ`, with `X` locally of
finite presentation and quasi-compact over `Dᵢ`, and `Y` locally of finite type and
quasi-separated over `Dᵢ`. If the base change of `g` to `S` is an open immersion, then so is its
base change to some `Dⱼ`. Stacks, Lemma 32.8.12 (0EUU). -/
theorem exists_isOpenImmersion_pullbackMap [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] {i : I} {X Y : Scheme.{u}} {p : X ⟶ D.obj i}
    {q : Y ⟶ D.obj i} [LocallyOfFinitePresentation p] [QuasiCompact p] [LocallyOfFiniteType q]
    [QuasiSeparated q] (g : X ⟶ Y) (hg : g ≫ q = p)
    [IsOpenImmersion
      (pullback.map (c.π.app i) p (c.π.app i) q (𝟙 _) g (𝟙 _) (by simp) (by simp [hg]))] :
    ∃ (j : I) (hji : j ⟶ i), IsOpenImmersion
      (pullback.map (D.map hji) p (D.map hji) q (𝟙 _) g (𝟙 _) (by simp) (by simp [hg])) := by
  -- The image of the base change `φ` of `g` to the limit descends to an open `V` at some `Dₗ`.
  obtain ⟨l, V, hVc, hgV, hVφ⟩ := hc.exists_opens_preimage_eq_opensRange g hg
  let φ := pullback.map (c.π.app i) p (c.π.app i) q (𝟙 _) g (𝟙 _) (by simp) (by simp [hg])
  let gl := pullback.map (D.map l.hom) p (D.map l.hom) q (𝟙 _) g (𝟙 _) (by simp) (by simp [hg])
  have hgl : gl ≫ pullback.fst _ _ = pullback.fst _ _ := by simp [gl]
  -- Base changing `gl` to the limit gives `φ` up to the canonical isomorphisms, under which the
  -- second projection corresponds to the projection to `Dₗ ×_{Dᵢ} Y`.
  obtain ⟨eX, eY, hφ, hsnd⟩ := exists_iso_pullback_map_pullback_map (c.π.app l.left)
    (D.map l.hom) (c.π.app i) (c.w l.hom) g hg
  have : IsOpenImmersion (pullback.map (c.π.app l.left) (pullback.fst (D.map l.hom) p)
      (c.π.app l.left) (pullback.fst (D.map l.hom) q) (𝟙 _) gl (𝟙 _) (by simp)
      (by simp [hgl])) := by
    rw [hφ, MorphismProperty.cancel_left_of_respectsIso (P := @IsOpenImmersion),
      MorphismProperty.cancel_right_of_respectsIso (P := @IsOpenImmersion)]
    exact inferInstanceAs (IsOpenImmersion φ)
  obtain ⟨j, hjl, hj⟩ := hc.exists_isOpenImmersion_pullbackMap_of_le_opensRange gl hgl V hVc hgV
    (by
      intro z hz
      obtain ⟨x, hx⟩ : eY.hom z ∈ φ.opensRange := by
        rw [← hVφ, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, hsnd]
        exact hz
      refine ⟨eX.inv x, ?_⟩
      rw [← Scheme.Hom.comp_apply, hφ, Iso.inv_hom_id_assoc, Scheme.Hom.comp_apply]
      exact (congrArg eY.inv hx).trans (by simp))
  -- Transport the open immersion at `Dⱼ ×_{Dₗ} (Dₗ ×_{Dᵢ} -)` back to `Dⱼ ×_{Dᵢ} -`.
  obtain ⟨eX', eY', hφ', -⟩ := exists_iso_pullback_map_pullback_map (D.map hjl) (D.map l.hom)
    (D.map (hjl ≫ l.hom)) (D.map_comp hjl l.hom).symm g hg
  refine ⟨j, hjl ≫ l.hom, ?_⟩
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsOpenImmersion) eX'.hom,
    ← MorphismProperty.cancel_right_of_respectsIso (P := @IsOpenImmersion) _ eY'.inv,
    Category.assoc, ← hφ']
  exact hj

end CategoryTheory.Limits.IsLimit
