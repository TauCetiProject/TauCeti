/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.KFlat.Tensor
public import TauCeti.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Product

/-!
# Left derived tensor bifunctors from K-flat derivability structures

Let `C` be an abelian braided monoidal preadditive category satisfying the graded-tensor hypotheses
of `HomologicalComplex.monoidalCategory`. Whenever `(CochainComplex.kFlatLocalizerMorphism C)` is a
left derivability structure on `CochainComplex C ℤ` with respect to quasi-isomorphisms, combining it
with `CategoryTheory.LocalizerMorphism.prod` produces product left derivability structures on
`CochainComplex C ℤ × CochainComplex C ℤ` that resolve either the first or the second factor by
K-flat complexes.

Consequently, for any functor `F : CochainComplex C ℤ ⥤ H` inverting quasi-isomorphisms, the
postcomposed total tensor bifunctor
`curriedTensor (CochainComplex C ℤ) ⋙ (whiskeringRight _ _ _).obj F`
satisfies `CategoryTheory.Functor.HasLeftDerivedFunctor₂` with respect to quasi-isomorphisms in both
variables (`TauCeti.hasLeftDerivedFunctor₂_tensor_of_inverts`). Moreover:
* any left derived bifunctor `(LF, α)` is computed on the nose whenever either factor is K-flat
  (`TauCeti.isIso_app_app_of_isLeftDerivedFunctor₂_tensor_of_isKFlat_left` and
  `TauCeti.isIso_app_app_of_isLeftDerivedFunctor₂_tensor_of_isKFlat_right`);
* fixing either variable yields a one-variable left derived functor via
  `CategoryTheory.Functor.bifunctorCounit₁` and `CategoryTheory.Functor.bifunctorCounit₂`
  (`TauCeti.isLeftDerivedFunctor_bifunctorCounit₁_of_isLeftDerivedFunctor₂_tensor` and
  `TauCeti.isLeftDerivedFunctor_bifunctorCounit₂_of_isLeftDerivedFunctor₂_tensor`);
* `(LF, α)` is absolute, remaining a left derived bifunctor after postcomposition with any functor
  `G : H ⥤ E` (`TauCeti.isLeftDerivedFunctor₂_comp_of_isLeftDerivedFunctor₂_tensor`).

## References

* N. Spaltenstein, *Resolutions of unbounded complexes*, Compositio Math. 65 (1988), 121–154.
* B. Kahn and G. Maltsiniotis, *Structures de dérivabilité*, Adv. Math. 218 (2008), 1286–1318.
* J. Riou, *Formalization of derived categories in Lean/mathlib*, Ann. Formaliz. Math. 1 (2025),
  1–42, §5.3.4.
* [Stacks Project, Tag 06Y4](https://stacks.math.columbia.edu/tag/06Y4),
  [Stacks Project, Tag 064L](https://stacks.math.columbia.edu/tag/064L), and
  [Stacks Project, Tag 064M](https://stacks.math.columbia.edu/tag/064M).
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory

namespace TauCeti

variable {C : Type*} [Category* C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [∀ (X₁ X₂ : GradedObject ℤ C), GradedObject.HasTensor X₁ X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((MonoidalCategory.curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((MonoidalCategory.curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [BraidedCategory C]
  {H : Type*} [Category* H]
  (F : CochainComplex C ℤ ⥤ H)
  (hF : (quasiIso C (.up ℤ)).IsInvertedBy F)

section HasLeftResolutions

variable [(CochainComplex.kFlatLocalizerMorphism C).HasLeftResolutions]

include hF in
/-- Resolving the first factor by K-flat complexes derives the postcomposition
`curriedTensor (CochainComplex C ℤ) ⋙ (whiskeringRight _ _ _).obj F` with any functor `F` that
inverts quasi-isomorphisms. -/
theorem derives_tensor_left_of_inverts :
    ((CochainComplex.kFlatLocalizerMorphism C).prod
      (LocalizerMorphism.id (quasiIso C (.up ℤ)))).Derives
      (uncurry.obj (MonoidalCategory.curriedTensor (CochainComplex C ℤ) ⋙
        (whiskeringRight _ _ _).obj F)) := by
  rintro ⟨P₁, L₁⟩ ⟨P₂, L₂⟩ ⟨f₁, f₂⟩ ⟨hf₁, hf₂⟩
  have : QuasiIso f₁.hom := (mem_quasiIso_iff _).1 hf₁
  have : QuasiIso f₂ := (mem_quasiIso_iff _).1 hf₂
  have : IsIso (F.map (f₁.hom ▷ L₁)) := hF _ ((mem_quasiIso_iff _).2 inferInstance)
  have : IsIso (F.map (P₂.obj ◁ f₂)) := hF _ ((mem_quasiIso_iff _).2 inferInstance)
  dsimp [uncurry, LocalizerMorphism.prod, LocalizerMorphism.id]
  rw [CochainComplex.kFlatLocalizerMorphism_functor]
  simp only [ObjectProperty.ι_map, ObjectProperty.ι_obj]
  infer_instance

include hF in
/-- Resolving the second factor by K-flat complexes derives the postcomposition
`curriedTensor (CochainComplex C ℤ) ⋙ (whiskeringRight _ _ _).obj F` with any functor `F` that
inverts quasi-isomorphisms. -/
theorem derives_tensor_right_of_inverts :
    ((LocalizerMorphism.id (quasiIso C (.up ℤ))).prod
      (CochainComplex.kFlatLocalizerMorphism C)).Derives
      (uncurry.obj (MonoidalCategory.curriedTensor (CochainComplex C ℤ) ⋙
        (whiskeringRight _ _ _).obj F)) := by
  rintro ⟨K₁, Q₁⟩ ⟨K₂, Q₂⟩ ⟨f₁, f₂⟩ ⟨hf₁, hf₂⟩
  have : QuasiIso f₁ := (mem_quasiIso_iff _).1 hf₁
  have : QuasiIso f₂.hom := (mem_quasiIso_iff _).1 hf₂
  have : IsIso (F.map (f₁ ▷ Q₁.obj)) := hF _ ((mem_quasiIso_iff _).2 inferInstance)
  have : IsIso (F.map (K₂ ◁ f₂.hom)) := hF _ ((mem_quasiIso_iff _).2 inferInstance)
  dsimp [uncurry, LocalizerMorphism.prod, LocalizerMorphism.id]
  rw [CochainComplex.kFlatLocalizerMorphism_functor]
  simp only [ObjectProperty.ι_map, ObjectProperty.ι_obj]
  infer_instance

include hF in
/-- For a fixed left complex `K`, resolving the right factor by K-flat complexes derives
`(curriedTensor (CochainComplex C ℤ) ⋙ (whiskeringRight _ _ _).obj F).obj K` whenever `F` inverts
quasi-isomorphisms. -/
theorem derives_tensor_obj_of_inverts (K : CochainComplex C ℤ) :
    (CochainComplex.kFlatLocalizerMorphism C).Derives
      ((MonoidalCategory.curriedTensor (CochainComplex C ℤ) ⋙
        (whiskeringRight _ _ _).obj F).obj K) := by
  intro Q₁ Q₂ f hf
  have : QuasiIso f.hom := (mem_quasiIso_iff _).1 hf
  have : IsIso (F.map (K ◁ f.hom)) := hF _ ((mem_quasiIso_iff _).2 inferInstance)
  dsimp
  rw [CochainComplex.kFlatLocalizerMorphism_functor]
  simp only [ObjectProperty.ι_map]
  infer_instance

include hF in
/-- For a fixed right complex `L`, resolving the left factor by K-flat complexes derives
`(curriedTensor (CochainComplex C ℤ) ⋙ (whiskeringRight _ _ _).obj F).flip.obj L` whenever `F`
inverts quasi-isomorphisms. -/
theorem derives_tensor_flip_obj_of_inverts (L : CochainComplex C ℤ) :
    (CochainComplex.kFlatLocalizerMorphism C).Derives
      ((MonoidalCategory.curriedTensor (CochainComplex C ℤ) ⋙
        (whiskeringRight _ _ _).obj F).flip.obj L) := by
  intro P₁ P₂ f hf
  have : QuasiIso f.hom := (mem_quasiIso_iff _).1 hf
  have : IsIso (F.map (f.hom ▷ L)) := hF _ ((mem_quasiIso_iff _).2 inferInstance)
  dsimp
  rw [CochainComplex.kFlatLocalizerMorphism_functor]
  simp only [ObjectProperty.ι_map]
  infer_instance

end HasLeftResolutions

section DerivabilityStructure

variable [(CochainComplex.kFlatLocalizerMorphism C).IsLeftDerivabilityStructure]

include hF in
/-- Postcomposing the total tensor product on `CochainComplex C ℤ` with any functor `F` that
inverts quasi-isomorphisms yields a bifunctor admitting a left derived bifunctor with respect to
quasi-isomorphisms in both variables. -/
theorem hasLeftDerivedFunctor₂_tensor_of_inverts :
    (MonoidalCategory.curriedTensor (CochainComplex C ℤ) ⋙
      (whiskeringRight _ _ _).obj F).HasLeftDerivedFunctor₂
      (quasiIso C (.up ℤ)) (quasiIso C (.up ℤ)) := by
  have := (derives_tensor_left_of_inverts F hF).hasPointwiseLeftDerivedFunctor
  infer_instance

section Characterization

variable {D₁ D₂ : Type*} [Category* D₁] [Category* D₂]
  {L₁ : CochainComplex C ℤ ⥤ D₁} {L₂ : CochainComplex C ℤ ⥤ D₂}
  [L₁.IsLocalization (quasiIso C (.up ℤ))] [L₂.IsLocalization (quasiIso C (.up ℤ))]
  {LF : D₁ ⥤ D₂ ⥤ H}
  (α : (((whiskeringLeft₂ H).obj L₁).obj L₂).obj LF ⟶
    MonoidalCategory.curriedTensor (CochainComplex C ℤ) ⋙ (whiskeringRight _ _ _).obj F)

include hF in
/-- When `F` inverts quasi-isomorphisms, a bifunctor `(LF, α)` is a left derived bifunctor of
`curriedTensor (CochainComplex C ℤ) ⋙ (whiskeringRight _ _ _).obj F` if and only if
`(α.app P).app L` is an isomorphism whenever `P` is K-flat. -/
theorem isLeftDerivedFunctor₂_tensor_iff_isIso_left :
    LF.IsLeftDerivedFunctor₂ α (quasiIso C (.up ℤ)) (quasiIso C (.up ℤ)) ↔
      ∀ (P : CochainComplex C ℤ) [P.IsKFlat] (L : CochainComplex C ℤ),
        IsIso ((α.app P).app L) := by
  rw [Functor.IsLeftDerivedFunctor₂,
    (derives_tensor_left_of_inverts F hF).isLeftDerivedFunctor_iff_isIso]
  refine ⟨fun h P hP L ↦ ?_, fun h ⟨⟨P, hP⟩, L⟩ ↦ ?_⟩
  · have h' := h (⟨P, hP⟩, L)
    dsimp [whiskeringLeft₂HomEquiv, LocalizerMorphism.prod, LocalizerMorphism.id] at h'
    rwa [CochainComplex.kFlatLocalizerMorphism_functor] at h'
  · dsimp [whiskeringLeft₂HomEquiv, LocalizerMorphism.prod, LocalizerMorphism.id]
    rw [CochainComplex.kFlatLocalizerMorphism_functor]
    exact @h P hP L

include hF in
/-- When `F` inverts quasi-isomorphisms, a bifunctor `(LF, α)` is a left derived bifunctor of
`curriedTensor (CochainComplex C ℤ) ⋙ (whiskeringRight _ _ _).obj F` if and only if
`(α.app K).app Q` is an isomorphism whenever `Q` is K-flat. -/
theorem isLeftDerivedFunctor₂_tensor_iff_isIso_right :
    LF.IsLeftDerivedFunctor₂ α (quasiIso C (.up ℤ)) (quasiIso C (.up ℤ)) ↔
      ∀ (K : CochainComplex C ℤ) (Q : CochainComplex C ℤ) [Q.IsKFlat],
        IsIso ((α.app K).app Q) := by
  rw [Functor.IsLeftDerivedFunctor₂,
    (derives_tensor_right_of_inverts F hF).isLeftDerivedFunctor_iff_isIso]
  refine ⟨fun h K Q hQ ↦ ?_, fun h ⟨K, ⟨Q, hQ⟩⟩ ↦ ?_⟩
  · have h' := h (K, ⟨Q, hQ⟩)
    dsimp [whiskeringLeft₂HomEquiv, LocalizerMorphism.prod, LocalizerMorphism.id] at h'
    rwa [CochainComplex.kFlatLocalizerMorphism_functor] at h'
  · dsimp [whiskeringLeft₂HomEquiv, LocalizerMorphism.prod, LocalizerMorphism.id]
    rw [CochainComplex.kFlatLocalizerMorphism_functor]
    exact @h K Q hQ

include hF in
/-- When `F` inverts quasi-isomorphisms, any left derived bifunctor `(LF, α)` of
`curriedTensor (CochainComplex C ℤ) ⋙ (whiskeringRight _ _ _).obj F` has invertible comparison
component `(α.app P).app L` whenever the left factor `P` is K-flat. -/
theorem isIso_app_app_of_isLeftDerivedFunctor₂_tensor_of_isKFlat_left
    [LF.IsLeftDerivedFunctor₂ α (quasiIso C (.up ℤ)) (quasiIso C (.up ℤ))]
    (P : CochainComplex C ℤ) [P.IsKFlat] (L : CochainComplex C ℤ) :
    IsIso ((α.app P).app L) :=
  (isLeftDerivedFunctor₂_tensor_iff_isIso_left F hF α).1 inferInstance P L

include hF in
/-- When `F` inverts quasi-isomorphisms, any left derived bifunctor `(LF, α)` of
`curriedTensor (CochainComplex C ℤ) ⋙ (whiskeringRight _ _ _).obj F` has invertible comparison
component `(α.app K).app Q` whenever the right factor `Q` is K-flat. -/
theorem isIso_app_app_of_isLeftDerivedFunctor₂_tensor_of_isKFlat_right
    [LF.IsLeftDerivedFunctor₂ α (quasiIso C (.up ℤ)) (quasiIso C (.up ℤ))]
    (K : CochainComplex C ℤ) (Q : CochainComplex C ℤ) [Q.IsKFlat] :
    IsIso ((α.app K).app Q) :=
  (isLeftDerivedFunctor₂_tensor_iff_isIso_right F hF α).1 inferInstance K Q

include hF in
/-- When `F` inverts quasi-isomorphisms and `(LF, α)` is a left derived bifunctor of
`curriedTensor (CochainComplex C ℤ) ⋙ (whiskeringRight _ _ _).obj F`, evaluating at `L₁.obj K`
exhibits `LF.obj (L₁.obj K)` as a left derived functor of
`(curriedTensor ⋙ whiskeringRight F).obj K` via `Functor.bifunctorCounit₁ α K`. -/
theorem isLeftDerivedFunctor_bifunctorCounit₁_of_isLeftDerivedFunctor₂_tensor
    [LF.IsLeftDerivedFunctor₂ α (quasiIso C (.up ℤ)) (quasiIso C (.up ℤ))]
    (K : CochainComplex C ℤ) :
    (LF.obj (L₁.obj K)).IsLeftDerivedFunctor
      (Functor.bifunctorCounit₁ α K) (quasiIso C (.up ℤ)) := by
  rw [(derives_tensor_obj_of_inverts F hF K).isLeftDerivedFunctor_iff_isIso]
  intro Q
  dsimp [Functor.bifunctorCounit₁]
  rw [CochainComplex.kFlatLocalizerMorphism_functor]
  exact isIso_app_app_of_isLeftDerivedFunctor₂_tensor_of_isKFlat_right F hF α K Q.obj

include hF in
/-- When `F` inverts quasi-isomorphisms and `(LF, α)` is a left derived bifunctor of
`curriedTensor (CochainComplex C ℤ) ⋙ (whiskeringRight _ _ _).obj F`, evaluating the flipped
bifunctor at `L₂.obj L` exhibits `LF.flip.obj (L₂.obj L)` as a left derived functor of
`(curriedTensor ⋙ whiskeringRight F).flip.obj L` via `Functor.bifunctorCounit₂ α L`. -/
theorem isLeftDerivedFunctor_bifunctorCounit₂_of_isLeftDerivedFunctor₂_tensor
    [LF.IsLeftDerivedFunctor₂ α (quasiIso C (.up ℤ)) (quasiIso C (.up ℤ))]
    (L : CochainComplex C ℤ) :
    (LF.flip.obj (L₂.obj L)).IsLeftDerivedFunctor
      (Functor.bifunctorCounit₂ α L) (quasiIso C (.up ℤ)) := by
  rw [(derives_tensor_flip_obj_of_inverts F hF L).isLeftDerivedFunctor_iff_isIso]
  intro P
  dsimp [Functor.bifunctorCounit₂]
  rw [CochainComplex.kFlatLocalizerMorphism_functor]
  exact isIso_app_app_of_isLeftDerivedFunctor₂_tensor_of_isKFlat_left F hF α P.obj L

include hF in
/-- **The left derived tensor bifunctor is absolute.** When `F` inverts quasi-isomorphisms,
postcomposing any left derived bifunctor `(LF, α)` of
`curriedTensor (CochainComplex C ℤ) ⋙ (whiskeringRight _ _ _).obj F` with an arbitrary functor
`G : H ⥤ E` yields a left derived bifunctor of
`curriedTensor (CochainComplex C ℤ) ⋙ (whiskeringRight _ _ _).obj (F ⋙ G)`. -/
theorem isLeftDerivedFunctor₂_comp_of_isLeftDerivedFunctor₂_tensor
    {E : Type*} [Category* E] (G : H ⥤ E)
    [LF.IsLeftDerivedFunctor₂ α (quasiIso C (.up ℤ)) (quasiIso C (.up ℤ))] :
    (LF ⋙ (whiskeringRight D₂ H E).obj G).IsLeftDerivedFunctor₂
      (Functor.whiskerRight α ((whiskeringRight _ _ _).obj G))
      (quasiIso C (.up ℤ)) (quasiIso C (.up ℤ)) :=
  (derives_tensor_left_of_inverts F hF).isLeftDerivedFunctor₂_comp α G

end Characterization

end DerivabilityStructure

end TauCeti
