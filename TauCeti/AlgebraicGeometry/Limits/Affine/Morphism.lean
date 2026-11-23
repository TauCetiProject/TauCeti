/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import TauCeti.AlgebraicGeometry.Morphisms.Affine.BaseChange
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Affine morphisms at a finite stage

An affine map from an affine-transition inverse limit to a fixed qcqs target
is affine at every sufficiently late stage.
-/

public section

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry

attribute [local instance] IsCofiltered.isConnected

namespace AlgebraicGeometry.Scheme

/-- Affineness of the limit map to a fixed target holds eventually on the stages. -/
theorem eventually_isAffineHom_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T]
    (D : I ⥤ Scheme.{u})
    (b : I) [CompactSpace (D.obj b)] [QuasiSeparatedSpace (D.obj b)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    (h : D ⟶ (Functor.const I).obj T)
    (c : Cone D) (hc : IsLimit c) (f : c.pt ⟶ T)
    (hf : ∀ i : I, c.π.app i ≫ h.app i = f) [IsAffineHom f] :
    ∃ i : I, ∀ j : I, (j ⟶ i) → IsAffineHom (h.app j) := by
  classical
  let 𝒰 := T.affineCover.finiteSubcover
  have (a : 𝒰.I₀) : IsAffine (𝒰.X a) := inferInstanceAs (IsAffine (Spec _))
  let V (a : 𝒰.I₀) : T.affineOpens := ⟨(𝒰.f a).opensRange,
    isAffineOpen_opensRange (𝒰.f a)⟩
  have H (a : 𝒰.I₀) : ∃ k : Over b, IsAffineOpen (h.app k.left ⁻¹ᵁ (V a).val) := by
    let U := h.app b ⁻¹ᵁ (V a).val
    have : QuasiCompact (h.app b) := by
      -- Expose the constant target so the qcqs instance applies.
      change QuasiCompact (show D.obj b ⟶ T from h.app b)
      infer_instance
    have hU : IsCompact (U : Set (D.obj b)) :=
      QuasiCompact.isCompact_preimage (f := h.app b) _ (V a).val.isOpen (V a).property.isCompact
    have (k : Over b) : CompactSpace ((opensDiagram D b U).obj k) :=
      isCompact_iff_compactSpace.mp
        (QuasiCompact.isCompact_preimage (f := D.map k.hom) _ U.isOpen hU)
    have (k : Over b) : QuasiSeparatedSpace (D.obj k.left) :=
      quasiSeparatedSpace_of_quasiSeparated (D.map k.hom)
    have (k : Over b) : QuasiSeparatedSpace ((opensDiagram D b U).obj k) :=
      (isQuasiSeparated_iff_quasiSeparatedSpace _ (D.map k.hom ⁻¹ᵁ U).isOpen).mp
        (.of_quasiSeparatedSpace _)
    have : IsAffine (opensCone D c b U).pt := by
      -- Expose the open defining the limit of the restricted diagram.
      change IsAffineOpen (c.π.app b ⁻¹ᵁ U)
      simpa [U, ← Scheme.Hom.comp_preimage, hf b] using (V a).property.preimage f
    obtain ⟨k, hk⟩ := Scheme.exists_isAffine_of_isLimit
      (opensDiagram D b U) (opensCone D c b U) (isLimitOpensCone D c hc b U)
    refine ⟨k, ?_⟩
    -- Expose the restricted stage before rewriting its preimage.
    change IsAffineOpen (D.map k.hom ⁻¹ᵁ U) at hk
    simpa [U, ← Scheme.Hom.comp_preimage, h.naturality k.hom] using hk
  choose k hk using H
  obtain ⟨i, hi⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image (fun a ↦ (k a).left))
  have gi (a : 𝒰.I₀) : i ⟶ (k a).left := (hi (by simp)).some
  refine ⟨i, fun j g ↦ ?_⟩
  apply isAffineHom_of_forall_exists_isAffineOpen
  intro x
  let a := 𝒰.idx x
  obtain ⟨y, hy⟩ := 𝒰.covers x
  refine ⟨(V a).val, ⟨y, hy⟩, (V a).property, ?_⟩
  have ha := (hk a).preimage (D.map (g ≫ gi a))
  simpa [← Scheme.Hom.comp_preimage, h.naturality (g ≫ gi a)] using ha

end AlgebraicGeometry.Scheme

namespace CategoryTheory.Functor

/-- An existing qcqs stage morphism that is affine over the inverse limit is affine at a
later stage. No finiteness hypothesis on the stage morphism is needed. -/
theorem exists_isAffineHom_baseChange_of_isLimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (X Y : Over (D.obj (op i₀)))
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    [CompactSpace Y.left] [QuasiSeparatedSpace Y.left]
    (f : X ⟶ Y)
    (hf : IsAffineHom (((Over.pullback (c.π.app (op i₀))).map f).left)) :
    ∃ (i : I) (hi : i₀ ≤ i),
      IsAffineHom (((Over.pullback (D.map (homOfLE hi).op)).map f).left) := by
  classical
  have : Nonempty I := ⟨i₀⟩
  let E := Over.post D ⋙ Over.pullback X.hom ⋙ Over.forget X.left
  let cE : Cone E :=
    (Over.pullback X.hom ⋙ Over.forget X.left).mapCone ((Over.conePost D (op i₀)).obj c)
  have hE : IsLimit cE :=
    isLimitOfPreserves (Over.pullback X.hom ⋙ Over.forget X.left)
      (Over.isLimitConePost (op i₀) hc)
  have transitions {j k : Over (op i₀)} (a : j ⟶ k) : IsAffineHom (E.map a) :=
    MorphismProperty.overPullbackMap (P := @IsAffineHom) X.hom
      ((Over.post D).map a) (show IsAffineHom (D.map a.left) from inferInstance)
  have (j : Over (op i₀)) :
      IsAffineHom (pullback.snd (D.map j.hom) X.hom) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom)
      (IsPullback.of_hasPullback (D.map j.hom) X.hom) inferInstance
  have (j : Over (op i₀)) : CompactSpace (E.obj j) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd (D.map j.hom) X.hom)
  have (j : Over (op i₀)) : QuasiSeparatedSpace (E.obj j) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd (D.map j.hom) X.hom)
  let t : E ⟶ (Functor.const (Over (op i₀))).obj Y.left :=
    { app := fun j ↦ pullback.snd (D.map j.hom) X.hom ≫ f.left
      naturality := by intro j k a; simp [E, Over.pullback_map_left] }
  let fE : cE.pt ⟶ Y.left := pullback.snd (c.π.app (op i₀)) X.hom ≫ f.left
  have : IsAffineHom (c.π.app (op i₀)) := isAffineHom_π_app D c hc _
  have : IsAffineHom fE := by
    -- Expose the native pullback projection hidden by fE.
    change IsAffineHom (pullback.snd (c.π.app (op i₀)) X.hom ≫ f.left)
    exact Scheme.Hom.snd_comp_of_overPullbackMap _ X Y f hf
  have factor (j : Over (op i₀)) : cE.π.app j ≫ t.app j = fE := by
    -- Expose mapCone's defining lift for the projection computation.
    change (pullback.lift (pullback.fst (c.π.app (op i₀)) X.hom ≫ c.π.app j.left)
      (pullback.snd (c.π.app (op i₀)) X.hom) (by simp [pullback.condition])) ≫
      pullback.snd (D.map j.hom) X.hom ≫ f.left =
      pullback.snd (c.π.app (op i₀)) X.hom ≫ f.left
    simp only [pullback.lift_snd_assoc]
  obtain ⟨j, hj⟩ := Y.left.eventually_isAffineHom_of_isLimit E (Over.mk (𝟙 (op i₀)))
    t cE hE fE factor
  have : IsAffineHom (t.app j) := hj j (𝟙 j)
  -- Give the native projection type hidden by the natural transformation.
  have affine := Scheme.Hom.overPullbackMap_of_snd_comp (D.map j.hom) X Y f
    (show IsAffineHom (pullback.snd (D.map j.hom) X.hom ≫ f.left) from inferInstance)
  refine ⟨j.left.unop, leOfHom j.hom.unop, ?_⟩
  have eq : (homOfLE (leOfHom j.hom.unop)).op = j.hom := Subsingleton.elim _ _
  -- Expose the preorder morphism before identifying its proof witness.
  change IsAffineHom (((Over.pullback (D.map (homOfLE (leOfHom j.hom.unop)).op)).map f).left)
  rw [eq]
  exact affine

end CategoryTheory.Functor
