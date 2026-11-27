/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.Limits.Separated
public import TauCeti.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Presentable.Directed
import TauCeti.AlgebraicGeometry.Chow
import TauCeti.CategoryTheory.MorphismProperty.Limits

/-!
# Proper families at a finite stage

For an inverse system of affine Noetherian schemes with affine transition maps, a finite
type quasi-compact family that becomes proper over the limit is proper at
a finite stage. Chow's lemma supplies a proper surjective modification with a projective
immersion. That immersion is closed over the limit, hence closed at a finite stage.

References: The Stacks Project, Tags 081F and 01ZA.
-/

public section

noncomputable section

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry MvPolynomial TopologicalSpace

attribute [local instance] MvPolynomial.gradedAlgebra

namespace CategoryTheory.Functor

private theorem exists_isProper_pullback_snd_of_isSeparated
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I) [IsAffine (D.obj (op i₀))]
    [IsNoetherian (D.obj (op i₀))] {X : Scheme.{u}} [CompactSpace X]
    (p : X ⟶ D.obj (op i₀)) [LocallyOfFiniteType p] [IsSeparated p]
    [IsProper (pullback.snd p (c.π.app (op i₀)))] :
    ∃ (i : I) (hi : i₀ ≤ i), IsProper (pullback.snd p (D.map (homOfLE hi).op)) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : IsNoetherian X := ⟨⟩
  have : QuasiCompact p := quasiCompact_of_compactSpace p
  let e := (D.obj (op i₀)).isoSpec
  let p' := p ≫ e.hom
  have : IsSeparated p' := by dsimp [p']; infer_instance
  have : LocallyOfFiniteType p' := by dsimp [p']; infer_instance
  have : QuasiCompact p' := by dsimp [p']; infer_instance
  obtain ⟨Z, π, σ, hσ, j, h, hπ, hsurj, hj, _⟩ :=
    TauCeti.AlgebraicGeometry.exists_chowModification_of_finite_irreducibleComponents p'
      NoetherianSpace.finite_irreducibleComponents
  have := hσ
  have := hπ
  have := hsurj
  have := hj
  let q := Proj.toSpecCoeff (homogeneousSubmodule σ Γ(D.obj (op i₀), ⊤))
  -- The projective-space instance uses the same coefficient map as the Proj structure map.
  have hq : IsProper (Proj (homogeneousSubmodule σ Γ(D.obj (op i₀), ⊤)) ↘
      Spec (.of Γ(D.obj (op i₀), ⊤))) := inferInstance
  have : IsProper q := hq
  let P := Over.mk (q ≫ e.inv)
  let W := Over.mk (π ≫ p)
  let a : W ⟶ Over.mk p := Over.homMk π
  let b : W ⟶ P := Over.homMk j (by
    simp only [P, W, q, Over.mk_hom, ← Category.assoc, ← h]
    simp [p', Category.assoc])
  have : IsImmersion b.left := hj
  have : LocallyOfFiniteType b.left := inferInstanceAs (LocallyOfFiniteType j)
  have : IsProper P.hom := by simp only [P, Over.mk_hom]; infer_instance
  have : CompactSpace W.left := QuasiCompact.compactSpace_of_compactSpace π
  have : QuasiSeparatedSpace W.left := quasiSeparatedSpace_of_quasiSeparated π
  have : CompactSpace P.left := QuasiCompact.compactSpace_of_compactSpace P.hom
  have : QuasiSeparatedSpace P.left := quasiSeparatedSpace_of_quasiSeparated P.hom
  have : IsProper (pullback.snd W.hom (c.π.app (op i₀))) := by
    simp only [W, Over.mk_hom]
    exact MorphismProperty.pullback_snd_comp_left (P := @IsProper) p _ π inferInstance
      inferInstance
  have hclosed := isClosedImmersion_overPullback_of_proper (c.π.app (op i₀)) b
  obtain ⟨i, hi, hstage⟩ := exists_isClosedImmersion_baseChange_of_isLimit D c hc i₀ W P b hclosed
  let B := Over.pullback (D.map (homOfLE hi).op)
  have : IsClosedImmersion (B.map b).left := hstage
  have : IsProper (B.obj P).hom := by simp only [B, Over.pullback_obj_hom]; infer_instance
  have : Surjective (B.map a).left := MorphismProperty.overPullbackMap _ a hsurj
  have hP : IsProper (B.obj W).hom := by rw [← Over.w (B.map b)]; infer_instance
  have : UniversallyClosed ((B.map a).left ≫ (B.obj (Over.mk p)).hom) := by
    rw [Over.w]
    exact hP.toUniversallyClosed
  have : IsSeparated (B.obj (Over.mk p)).hom := by
    simp only [B, Over.pullback_obj_hom, Over.mk_hom]
    infer_instance
  have : LocallyOfFiniteType (B.obj (Over.mk p)).hom := by
    simp only [B, Over.pullback_obj_hom, Over.mk_hom]
    infer_instance
  refine ⟨i, hi, ?_⟩
  simpa only [B, Over.pullback_obj_hom, Over.mk_hom] using
    (IsProper.of_comp_surjective (B.map a).left (B.obj (Over.mk p)).hom)

private theorem exists_isProper_pullback_snd_of_isLimit_directed
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    [∀ i, IsAffine (D.obj i)] [∀ i, IsNoetherian (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I) {X : Scheme.{u}} [CompactSpace X]
    (p : X ⟶ D.obj (op i₀)) [LocallyOfFiniteType p]
    [IsProper (pullback.snd p (c.π.app (op i₀)))] :
    ∃ (i : I) (hi : i₀ ≤ i), IsProper (pullback.snd p (D.map (homOfLE hi).op)) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : QuasiCompact p := quasiCompact_of_compactSpace p
  obtain ⟨i₁, h₁, hsep⟩ := hc.exists_isSeparated_pullback_snd p
  let t := D.map (homOfLE h₁).op
  let p₁ := pullback.snd p t
  have : IsSeparated p₁ := hsep
  have hp₁ : IsProper (pullback.snd p₁ (c.π.app (op i₁))) :=
    MorphismProperty.pullback_snd_pullback_snd (P := @IsProper) p t _ _ (𝟙 _)
      (by simpa only [Category.id_comp] using c.w (homOfLE h₁).op) inferInstance
  let J := {i : I // i₁ ≤ i}
  have : IsDirected J (· ≤ ·) := ⟨by
    intro a b
    obtain ⟨k, ha, hb⟩ := exists_ge_ge a.val b.val
    exact ⟨⟨k, a.property.trans ha⟩, ha, hb⟩⟩
  let F : J ⥤ I := (Subtype.mono_coe _).functor
  have : F.Final := by
    apply (Subtype.mono_coe _).final_functor_iff.mpr
    intro i
    obtain ⟨k, hi, h₁k⟩ := exists_ge_ge i i₁
    exact ⟨⟨k, h₁k⟩, hi⟩
  let D' := F.op ⋙ D
  let c' : Cone D' := c.whisker F.op
  have hc' : IsLimit c' := (Functor.Initial.isLimitWhiskerEquiv F.op c).symm hc
  let k₁ : J := ⟨i₁, le_rfl⟩
  have {i j : Jᵒᵖ} (a : i ⟶ j) : IsAffineHom (D'.map a) := by
    rw [Functor.comp_map]
    infer_instance
  have hπ : (c'.π.app (op k₁) : c.pt ⟶ D.obj (op i₁)) = c.π.app (op i₁) := by
    simp only [c', Cone.whisker_π, Functor.whiskerLeft_app]
    rfl
  have : IsProper (pullback.snd p₁ (c'.π.app (op k₁))) := by
    rw [hπ]
    exact hp₁
  obtain ⟨k, _, hp⟩ := exists_isProper_pullback_snd_of_isSeparated D' c' hc' k₁ p₁
  let t' := D.map (homOfLE k.property).op
  have : IsProper (pullback.snd p₁ t') := hp
  have ht : t' ≫ t = D.map (homOfLE (h₁.trans k.property)).op := by
    rw [← D.map_comp]
    rfl
  refine ⟨k.val, h₁.trans k.property, ?_⟩
  rw [← ht, ← pullbackLeftPullbackSndIso_inv_snd_snd p t t']
  infer_instance

/-- A quasi-compact finite type family over an affine Noetherian stage that becomes proper over
the inverse limit becomes proper after base change to a later stage. -/
theorem exists_isProper_pullback_snd_of_isLimit
    {I : Type u} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
    [∀ {i j} (a : i ⟶ j), IsAffineHom (D.map a)]
    [∀ i, IsAffine (D.obj i)] [∀ i, IsNoetherian (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    {X : Scheme.{u}} [CompactSpace X] (p : X ⟶ D.obj i₀) [LocallyOfFiniteType p]
    [IsProper (pullback.snd p (c.π.app i₀))] :
    ∃ (j : I) (a : j ⟶ i₀), IsProper (pullback.snd p (D.map a)) := by
  obtain ⟨J, hJ, hdir, _, G, hG⟩ := IsFiltered.exists_directed Iᵒᵖ
  let := hJ
  let := hdir
  let := hG
  let F := G.leftOp
  let k := Functor.Initial.lift F i₀
  let a := Functor.Initial.homToLift F i₀
  let p₁ := pullback.snd p (D.map a)
  have : CompactSpace (↑(pullback p (D.map a) : Scheme.{u})) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst p (D.map a))
  have : IsProper (pullback.snd p₁ ((c.whisker F).π.app k)) := by
    simp only [Cone.whisker_π, Functor.whiskerLeft_app]
    exact MorphismProperty.pullback_snd_pullback_snd (P := @IsProper)
      p (D.map a) _ _ (𝟙 _) (by simpa only [Category.id_comp] using c.w a) inferInstance
  have {i j : Jᵒᵖ} (g : i ⟶ j) : IsAffineHom ((F ⋙ D).map g) := by
    rw [Functor.comp_map]
    infer_instance
  have (i : Jᵒᵖ) : IsAffine ((F ⋙ D).obj i) := by rw [Functor.comp_obj]; infer_instance
  have (i : Jᵒᵖ) : IsNoetherian ((F ⋙ D).obj i) := by rw [Functor.comp_obj]; infer_instance
  have hc' := (Functor.Initial.isLimitWhiskerEquiv F c).symm hc
  obtain ⟨j, hj, hp⟩ := exists_isProper_pullback_snd_of_isLimit_directed
    (F ⋙ D) (c.whisker F) hc' k.unop p₁
  let b := F.map (homOfLE hj).op
  have : IsProper (pullback.snd p₁ (D.map b)) := hp
  refine ⟨F.obj (op j), b ≫ a, ?_⟩
  rw [D.map_comp, ← pullbackLeftPullbackSndIso_inv_snd_snd p (D.map a) (D.map b)]
  infer_instance

end CategoryTheory.Functor
