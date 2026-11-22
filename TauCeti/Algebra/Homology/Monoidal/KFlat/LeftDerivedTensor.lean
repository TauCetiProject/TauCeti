/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.KFlat.Tensor
public import TauCeti.CategoryTheory.Localization.DerivabilityStructure.Derives
public import TauCeti.CategoryTheory.Functor.Derived.LeftDerivedTwo
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Product

/-!
# Left derived tensor bifunctors from K-flat derivability structures

Let `C` be an abelian braided monoidal preadditive category satisfying the graded-tensor hypotheses
of `HomologicalComplex.monoidalCategory`. Whenever `(CochainComplex.KFlat.localizerMorphism C)` is a
left derivability structure on `CochainComplex C ℤ` with respect to quasi-isomorphisms, combining it
with `CategoryTheory.LocalizerMorphism.prod` produces product left derivability structures on
`CochainComplex C ℤ × CochainComplex C ℤ` that resolve either the first or the second factor by
K-flat complexes.

Consequently, for any functor `F : CochainComplex C ℤ ⥤ H` inverting quasi-isomorphisms, the
postcomposed total tensor bifunctor
`curriedTensor (CochainComplex C ℤ) ⋙ (whiskeringRight _ _ _).obj F`
satisfies `CategoryTheory.Functor.HasLeftDerivedFunctor₂` with respect to quasi-isomorphisms in both
variables (`CategoryTheory.Functor.hasLeftDerivedFunctor₂_tensor_of_inverts`). Moreover:
* any left derived bifunctor `(LF, α)` is computed on the nose whenever either factor is K-flat
  (`CategoryTheory.Functor.isIso_app_app_of_isLeftDerivedFunctor₂_tensor_of_isKFlat_left` and
  `CategoryTheory.Functor.isIso_app_app_of_isLeftDerivedFunctor₂_tensor_of_isKFlat_right`);
* fixing either variable yields a one-variable left derived functor via
  `CategoryTheory.Functor.bifunctorCounit₁` and `CategoryTheory.Functor.bifunctorCounit₂`
  (`CategoryTheory.Functor.isLeftDerivedFunctor_bifunctorCounit₁_of_isLeftDerivedFunctor₂_tensor`
  and
  `CategoryTheory.Functor.isLeftDerivedFunctor_bifunctorCounit₂_of_isLeftDerivedFunctor₂_tensor`);
* `(LF, α)` is absolute, remaining a left derived bifunctor after postcomposition with any functor
  `G : H ⥤ E`
  (`CategoryTheory.Functor.isLeftDerivedFunctor₂_comp_of_isLeftDerivedFunctor₂_tensor`);
* when `HasDerivedCategory C` holds, `TauCeti.hasLeftDerivedFunctor₂_tensor` and
  `TauCeti.derivedTensor C` provide the canonical left derived tensor bifunctor `⊗^L` on
  `DerivedCategory C`, together with its universal counit `TauCeti.derivedTensorCounit C`,
  one-variable `IsLeftDerivedFunctor` instances, and K-flat object isomorphisms
  `CochainComplex.derivedTensorKFlatLeftIso` and `CochainComplex.derivedTensorKFlatRightIso`;
* for any left derived bifunctor `(LF, α)` of the tensor product on `DerivedCategory C`, the partial
  counits `Functor.bifunctorCounit₁ α P` and `Functor.bifunctorCounit₂ α Q` are isomorphisms when
  `P` or `Q` is K-flat, in particular a bounded-above complex of flat objects
  (`TauCeti.isIso_bifunctorCounit₁_of_boundedAbove_flat_of_isLeftDerivedFunctor₂_tensor`), for
  K-flat `P` the functor `LF.obj (DerivedCategory.Q.obj P)` is naturally isomorphic to
  `P.kFlatTensor` compatibly with morphisms of K-flat models
  (`TauCeti.leftDerivedTensorObjIsoKFlatTensor`,
  `TauCeti.leftDerivedTensorObjIsoKFlatTensor_naturality`), and derived tensoring with the unit
  complex `𝟙_ (CochainComplex C ℤ)` on either side is naturally isomorphic to the identity
  (`TauCeti.leftDerivedTensorLeftUnitor`, `TauCeti.leftDerivedTensorRightUnitor`), and the
  Koszul braiding (`TauCeti.koszulDerivedFlipIso`) induces a natural symmetry isomorphism
  `LF.flip ≅ LF` (`TauCeti.leftDerivedTensorFlipIso`) compatible with the counit
  (`TauCeti.leftDerivedTensorFlipIso_hom_fac`, `TauCeti.leftDerivedTensorFlipIso_inv_fac`, and
  `TauCeti.leftDerivedTensorFlipIso_app_app_Q`) and the derived unitors
  (`TauCeti.leftDerivedTensorFlipIso_hom_app_comp_leftUnitor`,
  `TauCeti.flip_leftDerivedTensorFlipIso_hom_app_comp_rightUnitor`,
  `TauCeti.leftDerivedTensorFlipIso_inv_app_comp_rightUnitor`,
  `TauCeti.flip_leftDerivedTensorFlipIso_inv_app_comp_leftUnitor`,
  `TauCeti.leftDerivedTensorRightUnitor_inv_comp_leftDerivedTensorFlipIso_hom_app`,
  `TauCeti.leftDerivedTensorLeftUnitor_inv_comp_flip_leftDerivedTensorFlipIso_hom_app`,
  `TauCeti.leftDerivedTensorLeftUnitor_inv_comp_leftDerivedTensorFlipIso_inv_app`,
  `TauCeti.leftDerivedTensorRightUnitor_inv_comp_flip_leftDerivedTensorFlipIso_inv_app`, and their
  `derivedTensor` specializations), which is involutive over symmetric coefficients
  (`TauCeti.Q_map_braiding_inv`, `TauCeti.Q_map_braiding_comp`,
  `TauCeti.flip_leftDerivedTensorFlipIso_hom_comp`, `TauCeti.leftDerivedTensorFlipIso_inv_app_app`,
  `TauCeti.leftDerivedTensorFlipIso_hom_app_app_comp`).

Bounded-above complexes of flat objects are K-flat, so on either side they compute the derived
tensor product on complex models as the ordinary totalized tensor product followed by
`DerivedCategory.Q` (`TauCeti.leftDerivedTensorObjModelIsoOfIsStrictlyLEFlat`,
`TauCeti.leftDerivedTensorFlipObjModelIsoOfIsStrictlyLEFlat`, and, for any target `F`,
`CategoryTheory.Functor.isIso_app_app_of_isLeftDerivedFunctor₂_tensor_of_boundedAbove_flat_left`
and
`CategoryTheory.Functor.isIso_app_app_of_isLeftDerivedFunctor₂_tensor_of_boundedAbove_flat_right`).

For the canonical bifunctor `TauCeti.derivedTensor C`, the unit `𝟙_ C` placed in degree `0` is a
unit on both sides (`TauCeti.derivedTensorLeftUnitor`, `TauCeti.derivedTensorRightUnitor`).
Modules over a commutative ring and sheaves of modules over a sheaf of commutative rings on a small
site are the main examples.

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

variable {C : Type*} [Category* C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [∀ (X₁ X₂ : GradedObject ℤ C), GradedObject.HasTensor X₁ X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((MonoidalCategory.curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((MonoidalCategory.curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

section

variable [BraidedCategory C]

namespace CategoryTheory.Functor

section GeneralTarget

variable {H : Type*} [Category* H]
  (F : CochainComplex C ℤ ⥤ H)
  (hF : (quasiIso C (.up ℤ)).IsInvertedBy F)

section HasLeftResolutions

variable [(CochainComplex.KFlat.localizerMorphism C).HasLeftResolutions]

include hF in
/-- Resolving the first factor by K-flat complexes derives the postcomposition
`curriedTensor (CochainComplex C ℤ) ⋙ (whiskeringRight _ _ _).obj F` with any functor `F` that
inverts quasi-isomorphisms. -/
theorem derives_tensor_left_of_inverts :
    ((CochainComplex.KFlat.localizerMorphism C).prod
      (LocalizerMorphism.id (quasiIso C (.up ℤ)))).Derives
      (uncurry.obj (MonoidalCategory.curriedTensor (CochainComplex C ℤ) ⋙
        (whiskeringRight _ _ _).obj F)) := by
  rintro ⟨P₁, L₁⟩ ⟨P₂, L₂⟩ ⟨f₁, f₂⟩ ⟨hf₁, hf₂⟩
  have : QuasiIso f₁.hom := (CochainComplex.KFlat.quasiIso_iff _).1 hf₁
  have : QuasiIso f₂ := (mem_quasiIso_iff _).1 hf₂
  have : IsIso (F.map (f₁.hom ▷ L₁)) := hF _ ((mem_quasiIso_iff _).2 inferInstance)
  have : IsIso (F.map (P₂.obj ◁ f₂)) := hF _ ((mem_quasiIso_iff _).2 inferInstance)
  dsimp [uncurry, LocalizerMorphism.prod, LocalizerMorphism.id]
  rw [CochainComplex.KFlat.localizerMorphism_functor]
  simp only [ObjectProperty.ι_map, ObjectProperty.ι_obj]
  infer_instance

include hF in
/-- Resolving the second factor by K-flat complexes derives the postcomposition
`curriedTensor (CochainComplex C ℤ) ⋙ (whiskeringRight _ _ _).obj F` with any functor `F` that
inverts quasi-isomorphisms. -/
theorem derives_tensor_right_of_inverts :
    ((LocalizerMorphism.id (quasiIso C (.up ℤ))).prod
      (CochainComplex.KFlat.localizerMorphism C)).Derives
      (uncurry.obj (MonoidalCategory.curriedTensor (CochainComplex C ℤ) ⋙
        (whiskeringRight _ _ _).obj F)) := by
  rintro ⟨K₁, Q₁⟩ ⟨K₂, Q₂⟩ ⟨f₁, f₂⟩ ⟨hf₁, hf₂⟩
  have : QuasiIso f₁ := (mem_quasiIso_iff _).1 hf₁
  have : QuasiIso f₂.hom := (CochainComplex.KFlat.quasiIso_iff _).1 hf₂
  have : IsIso (F.map (f₁ ▷ Q₁.obj)) := hF _ ((mem_quasiIso_iff _).2 inferInstance)
  have : IsIso (F.map (K₂ ◁ f₂.hom)) := hF _ ((mem_quasiIso_iff _).2 inferInstance)
  dsimp [uncurry, LocalizerMorphism.prod, LocalizerMorphism.id]
  rw [CochainComplex.KFlat.localizerMorphism_functor]
  simp only [ObjectProperty.ι_map, ObjectProperty.ι_obj]
  infer_instance

include hF in
/-- For a fixed left complex `K`, resolving the right factor by K-flat complexes derives
`(curriedTensor (CochainComplex C ℤ) ⋙ (whiskeringRight _ _ _).obj F).obj K` whenever `F` inverts
quasi-isomorphisms. -/
theorem derives_tensor_obj_of_inverts (K : CochainComplex C ℤ) :
    (CochainComplex.KFlat.localizerMorphism C).Derives
      ((MonoidalCategory.curriedTensor (CochainComplex C ℤ) ⋙
        (whiskeringRight _ _ _).obj F).obj K) :=
  (derives_tensor_right_of_inverts F hF).obj K

include hF in
/-- For a fixed right complex `L`, resolving the left factor by K-flat complexes derives
`(curriedTensor (CochainComplex C ℤ) ⋙ (whiskeringRight _ _ _).obj F).flip.obj L` whenever `F`
inverts quasi-isomorphisms. -/
theorem derives_tensor_flip_obj_of_inverts (L : CochainComplex C ℤ) :
    (CochainComplex.KFlat.localizerMorphism C).Derives
      ((MonoidalCategory.curriedTensor (CochainComplex C ℤ) ⋙
        (whiskeringRight _ _ _).obj F).flip.obj L) :=
  (derives_tensor_left_of_inverts F hF).flip_obj L

end HasLeftResolutions

section DerivabilityStructure

variable [(CochainComplex.KFlat.localizerMorphism C).IsLeftDerivabilityStructure]

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
  dsimp [whiskeringLeft₂HomEquiv, LocalizerMorphism.prod, LocalizerMorphism.id]
  rw [CochainComplex.KFlat.localizerMorphism_functor]
  exact ⟨fun h P hP L ↦ h (⟨P, (CochainComplex.kFlat_iff P).2 hP⟩, L),
    fun h ⟨⟨P, hP⟩, L⟩ ↦ @h P ((CochainComplex.kFlat_iff P).1 hP) L⟩

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
  dsimp [whiskeringLeft₂HomEquiv, LocalizerMorphism.prod, LocalizerMorphism.id]
  rw [CochainComplex.KFlat.localizerMorphism_functor]
  exact ⟨fun h K Q hQ ↦ h (K, ⟨Q, (CochainComplex.kFlat_iff Q).2 hQ⟩),
    fun h ⟨K, ⟨Q, hQ⟩⟩ ↦ @h K Q ((CochainComplex.kFlat_iff Q).1 hQ)⟩

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
/-- **Flat-model comparison on the left.** When `F` inverts quasi-isomorphisms and sequential
colimits in `C` are exact and commute with tensoring, any left derived bifunctor `(LF, α)` of
`curriedTensor (CochainComplex C ℤ) ⋙ (whiskeringRight _ _ _).obj F` has invertible comparison
component `(α.app P).app L` whenever `P` is a bounded-above complex of flat objects. -/
theorem isIso_app_app_of_isLeftDerivedFunctor₂_tensor_of_boundedAbove_flat_left
    [HasColimitsOfShape ℕ C] [HasExactColimitsOfShape ℕ C]
    [∀ X : C, PreservesColimitsOfShape ℕ (MonoidalCategory.tensorRight X)]
    [∀ X : C, PreservesFiniteColimits (MonoidalCategory.tensorLeft X)]
    [LF.IsLeftDerivedFunctor₂ α (quasiIso C (.up ℤ)) (quasiIso C (.up ℤ))]
    (P : CochainComplex C ℤ) (b : ℤ) [P.IsStrictlyLE b]
    [∀ n, PreservesFiniteLimits (MonoidalCategory.tensorLeft (P.X n))]
    (L : CochainComplex C ℤ) : IsIso ((α.app P).app L) :=
  have := P.isKFlat_of_boundedAbove_flat b
  isIso_app_app_of_isLeftDerivedFunctor₂_tensor_of_isKFlat_left F hF α P L

include hF in
/-- **Flat-model comparison on the right.** When `F` inverts quasi-isomorphisms and sequential
colimits in `C` are exact and commute with tensoring, any left derived bifunctor `(LF, α)` of
`curriedTensor (CochainComplex C ℤ) ⋙ (whiskeringRight _ _ _).obj F` has invertible comparison
component `(α.app K).app Q` whenever `Q` is a bounded-above complex of flat objects. -/
theorem isIso_app_app_of_isLeftDerivedFunctor₂_tensor_of_boundedAbove_flat_right
    [HasColimitsOfShape ℕ C] [HasExactColimitsOfShape ℕ C]
    [∀ X : C, PreservesColimitsOfShape ℕ (MonoidalCategory.tensorRight X)]
    [∀ X : C, PreservesFiniteColimits (MonoidalCategory.tensorLeft X)]
    [LF.IsLeftDerivedFunctor₂ α (quasiIso C (.up ℤ)) (quasiIso C (.up ℤ))]
    (K Q : CochainComplex C ℤ) (b : ℤ) [Q.IsStrictlyLE b]
    [∀ n, PreservesFiniteLimits (MonoidalCategory.tensorLeft (Q.X n))] :
    IsIso ((α.app K).app Q) :=
  have := Q.isKFlat_of_boundedAbove_flat b
  isIso_app_app_of_isLeftDerivedFunctor₂_tensor_of_isKFlat_right F hF α K Q

include hF in
/-- When `F` inverts quasi-isomorphisms and `(LF, α)` is a left derived bifunctor of
`curriedTensor (CochainComplex C ℤ) ⋙ (whiskeringRight _ _ _).obj F`, evaluating at `L₁.obj K`
exhibits `LF.obj (L₁.obj K)` as a left derived functor of
`(curriedTensor ⋙ whiskeringRight F).obj K` via `Functor.bifunctorCounit₁ α K`. -/
theorem isLeftDerivedFunctor_bifunctorCounit₁_of_isLeftDerivedFunctor₂_tensor
    [LF.IsLeftDerivedFunctor₂ α (quasiIso C (.up ℤ)) (quasiIso C (.up ℤ))]
    (K : CochainComplex C ℤ) :
    (LF.obj (L₁.obj K)).IsLeftDerivedFunctor
      (Functor.bifunctorCounit₁ α K) (quasiIso C (.up ℤ)) :=
  (derives_tensor_right_of_inverts F hF).isLeftDerivedFunctor_bifunctorCounit₁ α K

include hF in
/-- When `F` inverts quasi-isomorphisms and `(LF, α)` is a left derived bifunctor of
`curriedTensor (CochainComplex C ℤ) ⋙ (whiskeringRight _ _ _).obj F`, evaluating the flipped
bifunctor at `L₂.obj L` exhibits `LF.flip.obj (L₂.obj L)` as a left derived functor of
`(curriedTensor ⋙ whiskeringRight F).flip.obj L` via `Functor.bifunctorCounit₂ α L`. -/
theorem isLeftDerivedFunctor_bifunctorCounit₂_of_isLeftDerivedFunctor₂_tensor
    [LF.IsLeftDerivedFunctor₂ α (quasiIso C (.up ℤ)) (quasiIso C (.up ℤ))]
    (L : CochainComplex C ℤ) :
    (LF.flip.obj (L₂.obj L)).IsLeftDerivedFunctor
      (Functor.bifunctorCounit₂ α L) (quasiIso C (.up ℤ)) :=
  (derives_tensor_left_of_inverts F hF).isLeftDerivedFunctor_bifunctorCounit₂ α L

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

end GeneralTarget

end CategoryTheory.Functor

namespace CochainComplex.KFlat

variable [(localizerMorphism C).HasLeftResolutions]

/-- The product of the K-flat localizer morphism with itself derives the uncurried tensor product
of complexes followed by `DerivedCategory.Q`. -/
theorem prod_localizerMorphism_derives_tensor [HasDerivedCategory C] :
    ((localizerMorphism C).prod (localizerMorphism C)).Derives
      (Functor.uncurry.obj
        (MonoidalCategory.curriedTensor (CochainComplex C ℤ) ⋙
          (Functor.whiskeringRight _ _ _).obj (DerivedCategory.Q (C := C)))) := by
  rw [LocalizerMorphism.Derives, LocalizerMorphism.prod_functor, localizerMorphism_functor]
  rintro ⟨K₁, L₁⟩ ⟨K₂, L₂⟩ f ⟨hf₁, hf₂⟩
  have : QuasiIso f.1.hom := (quasiIso_iff f.1).1 hf₁
  have : QuasiIso f.2.hom := (quasiIso_iff f.2).1 hf₂
  simp only [Functor.comp_map, Functor.prod_map, Functor.prod_obj, ObjectProperty.ι_map,
    Functor.uncurry_obj_map, Functor.comp_obj, Functor.whiskeringRight_obj_obj,
    Functor.whiskeringRight_obj_map, whiskerRight_app, MonoidalCategory.curriedTensor_obj_obj,
    MonoidalCategory.curriedTensor_map_app, MonoidalCategory.curriedTensor_obj_map,
    ObjectProperty.ι_obj]
  infer_instance

end CochainComplex.KFlat

section DerivedCategory

variable [(CochainComplex.KFlat.localizerMorphism C).IsLeftDerivabilityStructure]
  [HasDerivedCategory C]

namespace TauCeti

variable (C)

/-- **Existence of the derived tensor product.** For an abelian braided monoidal preadditive
category `C` satisfying the graded-tensor hypotheses and admitting a K-flat left derivability
structure, the total tensor product of cochain complexes followed by localization to
`DerivedCategory C` admits a left derived bifunctor `⊗^L` with respect to quasi-isomorphisms in
both variables. -/
instance hasLeftDerivedFunctor₂_tensor :
    (MonoidalCategory.curriedTensor (CochainComplex C ℤ) ⋙
      (Functor.whiskeringRight _ _ _).obj (DerivedCategory.Q (C := C))).HasLeftDerivedFunctor₂
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) :=
  hasLeftDerivedFunctor₂_tensor_of_inverts (DerivedCategory.Q (C := C))
    (Localization.inverts DerivedCategory.Q (quasiIso C (.up ℤ)))

/-- The canonical left derived tensor bifunctor `⊗^L` on the unbounded derived category
`DerivedCategory C`. -/
def derivedTensor : DerivedCategory C ⥤ DerivedCategory C ⥤ DerivedCategory C :=
  Functor.leftDerived₂
    (MonoidalCategory.curriedTensor (CochainComplex C ℤ) ⋙
      (whiskeringRight _ _ _).obj (DerivedCategory.Q (C := C)))
    DerivedCategory.Q DerivedCategory.Q (quasiIso C (.up ℤ)) (quasiIso C (.up ℤ))

/-- The universal counit comparing `derivedTensor C` on localized complexes with the ordinary
total tensor product of cochain complexes. -/
def derivedTensorCounit :
    (((whiskeringLeft₂ (DerivedCategory C)).obj DerivedCategory.Q).obj
      DerivedCategory.Q).obj (derivedTensor C) ⟶
      MonoidalCategory.curriedTensor (CochainComplex C ℤ) ⋙
        (whiskeringRight _ _ _).obj (DerivedCategory.Q (C := C)) :=
  Functor.leftDerivedCounit₂
    (MonoidalCategory.curriedTensor (CochainComplex C ℤ) ⋙
      (whiskeringRight _ _ _).obj (DerivedCategory.Q (C := C)))
    DerivedCategory.Q DerivedCategory.Q (quasiIso C (.up ℤ)) (quasiIso C (.up ℤ))

instance : (derivedTensor C).IsLeftDerivedFunctor₂ (derivedTensorCounit C)
    (quasiIso C (.up ℤ)) (quasiIso C (.up ℤ)) := by
  dsimp [derivedTensor, derivedTensorCounit]; infer_instance

variable {C}

instance (K : CochainComplex C ℤ) :
    ((derivedTensor C).obj (DerivedCategory.Q.obj K)).IsLeftDerivedFunctor
      (Functor.bifunctorCounit₁ (derivedTensorCounit C) K) (quasiIso C (.up ℤ)) :=
  isLeftDerivedFunctor_bifunctorCounit₁_of_isLeftDerivedFunctor₂_tensor DerivedCategory.Q
    (Localization.inverts _ _) (derivedTensorCounit C) K

instance (L : CochainComplex C ℤ) :
    ((derivedTensor C).flip.obj (DerivedCategory.Q.obj L)).IsLeftDerivedFunctor
      (Functor.bifunctorCounit₂ (derivedTensorCounit C) L) (quasiIso C (.up ℤ)) :=
  isLeftDerivedFunctor_bifunctorCounit₂_of_isLeftDerivedFunctor₂_tensor DerivedCategory.Q
    (Localization.inverts _ _) (derivedTensorCounit C) L

instance (P L : CochainComplex C ℤ) [P.IsKFlat] :
    IsIso (((derivedTensorCounit C).app P).app L) :=
  isIso_app_app_of_isLeftDerivedFunctor₂_tensor_of_isKFlat_left DerivedCategory.Q
    (Localization.inverts _ _) (derivedTensorCounit C) P L

instance (K P : CochainComplex C ℤ) [P.IsKFlat] :
    IsIso (((derivedTensorCounit C).app K).app P) :=
  isIso_app_app_of_isLeftDerivedFunctor₂_tensor_of_isKFlat_right DerivedCategory.Q
    (Localization.inverts _ _) (derivedTensorCounit C) K P

end TauCeti

namespace CochainComplex

/-- The object isomorphism `((TauCeti.derivedTensor C).obj (DerivedCategory.Q.obj P)).obj
(DerivedCategory.Q.obj L) ≅ DerivedCategory.Q.obj (P ⊗ L)` induced by
`TauCeti.derivedTensorCounit C` when the left complex `P` is K-flat. -/
def derivedTensorKFlatLeftIso (P L : CochainComplex C ℤ) [P.IsKFlat] :
    ((TauCeti.derivedTensor C).obj (DerivedCategory.Q.obj P)).obj (DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj (P ⊗ L) :=
  asIso (((TauCeti.derivedTensorCounit C).app P).app L)

/-- The forward morphism of `derivedTensorKFlatLeftIso` is the counit component. -/
@[simp]
lemma derivedTensorKFlatLeftIso_hom (P L : CochainComplex C ℤ) [P.IsKFlat] :
    (derivedTensorKFlatLeftIso P L).hom = ((TauCeti.derivedTensorCounit C).app P).app L := (rfl)

/-- The inverse morphism of `derivedTensorKFlatLeftIso` is the inverse of the counit component. -/
@[simp]
lemma derivedTensorKFlatLeftIso_inv (P L : CochainComplex C ℤ) [P.IsKFlat] :
    (derivedTensorKFlatLeftIso P L).inv = inv (((TauCeti.derivedTensorCounit C).app P).app L) :=
  (rfl)

/-- The object isomorphism `((TauCeti.derivedTensor C).obj (DerivedCategory.Q.obj K)).obj
(DerivedCategory.Q.obj P) ≅ DerivedCategory.Q.obj (K ⊗ P)` induced by
`TauCeti.derivedTensorCounit C` when the right complex `P` is K-flat. -/
def derivedTensorKFlatRightIso (K P : CochainComplex C ℤ) [P.IsKFlat] :
    ((TauCeti.derivedTensor C).obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj (K ⊗ P) :=
  asIso (((TauCeti.derivedTensorCounit C).app K).app P)

/-- The forward morphism of `derivedTensorKFlatRightIso` is the counit component. -/
@[simp]
lemma derivedTensorKFlatRightIso_hom (K P : CochainComplex C ℤ) [P.IsKFlat] :
    (derivedTensorKFlatRightIso K P).hom = ((TauCeti.derivedTensorCounit C).app K).app P := (rfl)

/-- The inverse morphism of `derivedTensorKFlatRightIso` is the inverse of the counit component. -/
@[simp]
lemma derivedTensorKFlatRightIso_inv (K P : CochainComplex C ℤ) [P.IsKFlat] :
    (derivedTensorKFlatRightIso K P).inv = inv (((TauCeti.derivedTensorCounit C).app K).app P) :=
  (rfl)

end CochainComplex

end DerivedCategory

section ModelComparison

variable [(CochainComplex.KFlat.localizerMorphism C).IsLeftDerivabilityStructure]
  [HasDerivedCategory C]
  (LF : DerivedCategory C ⥤ DerivedCategory C ⥤ DerivedCategory C)
  (α : (((whiskeringLeft₂ (DerivedCategory C)).obj DerivedCategory.Q).obj
    DerivedCategory.Q).obj LF ⟶
      MonoidalCategory.curriedTensor (CochainComplex C ℤ) ⋙
        (whiskeringRight _ _ _).obj (DerivedCategory.Q (C := C)))
  [LF.IsLeftDerivedFunctor₂ α (quasiIso C (.up ℤ)) (quasiIso C (.up ℤ))]

namespace TauCeti

/-- For any left derived bifunctor `(LF, α)` of the tensor product on `DerivedCategory C`,
`(α.app P).app L` is an isomorphism whenever `P` is K-flat, for every (possibly unbounded)
complex `L`. -/
instance isIso_app_app_of_isKFlat_left_of_isLeftDerivedFunctor₂_tensor
    (P L : CochainComplex C ℤ) [P.IsKFlat] :
    IsIso ((α.app P).app L) :=
  isIso_app_app_of_isLeftDerivedFunctor₂_tensor_of_isKFlat_left DerivedCategory.Q
    (Localization.inverts _ _) α P L

/-- For any left derived bifunctor `(LF, α)` of the tensor product on `DerivedCategory C`,
`(α.app K).app Q` is an isomorphism whenever `Q` is K-flat, for every (possibly unbounded)
complex `K`. -/
instance isIso_app_app_of_isKFlat_right_of_isLeftDerivedFunctor₂_tensor
    (K Q : CochainComplex C ℤ) [Q.IsKFlat] :
    IsIso ((α.app K).app Q) :=
  isIso_app_app_of_isLeftDerivedFunctor₂_tensor_of_isKFlat_right DerivedCategory.Q
    (Localization.inverts _ _) α K Q

/-- For any complex `K` (without any K-flatness assumption), `LF.obj (Q.obj K)` is a left derived
functor of `K ⊗ - ⋙ Q` via `Functor.bifunctorCounit₁ α K`. -/
instance isLeftDerivedFunctor_bifunctorCounit₁_of_isLeftDerivedFunctor₂_tensor
    (K : CochainComplex C ℤ) :
    (LF.obj (DerivedCategory.Q.obj K)).IsLeftDerivedFunctor (Functor.bifunctorCounit₁ α K)
      (quasiIso C (.up ℤ)) :=
  Functor.isLeftDerivedFunctor_bifunctorCounit₁_of_isLeftDerivedFunctor₂_tensor DerivedCategory.Q
    (Localization.inverts _ _) α K

/-- For any complex `L` (without any K-flatness assumption), `LF.flip.obj (Q.obj L)` is a left
derived functor of `- ⊗ L ⋙ Q` via `Functor.bifunctorCounit₂ α L`. -/
instance isLeftDerivedFunctor_bifunctorCounit₂_of_isLeftDerivedFunctor₂_tensor
    (L : CochainComplex C ℤ) :
    (LF.flip.obj (DerivedCategory.Q.obj L)).IsLeftDerivedFunctor (Functor.bifunctorCounit₂ α L)
      (quasiIso C (.up ℤ)) :=
  Functor.isLeftDerivedFunctor_bifunctorCounit₂_of_isLeftDerivedFunctor₂_tensor DerivedCategory.Q
    (Localization.inverts _ _) α L

/-- When `P` is K-flat, the partial counit `Functor.bifunctorCounit₁ α P` is a natural isomorphism
`DerivedCategory.Q ⋙ LF.obj (DerivedCategory.Q.obj P) ≅ tensorLeft P ⋙ DerivedCategory.Q`. -/
instance isIso_bifunctorCounit₁_of_isKFlat_of_isLeftDerivedFunctor₂_tensor
    (P : CochainComplex C ℤ) [P.IsKFlat] :
    IsIso (Functor.bifunctorCounit₁ α P) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro L
  rw [Functor.bifunctorCounit₁_app]
  infer_instance

/-- When `Q` is K-flat, the partial counit `Functor.bifunctorCounit₂ α Q` is a natural isomorphism
`DerivedCategory.Q ⋙ LF.flip.obj (DerivedCategory.Q.obj Q) ≅ tensorRight Q ⋙ DerivedCategory.Q`. -/
instance isIso_bifunctorCounit₂_of_isKFlat_of_isLeftDerivedFunctor₂_tensor
    (Q : CochainComplex C ℤ) [Q.IsKFlat] :
    IsIso (Functor.bifunctorCounit₂ α Q) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  rw [Functor.bifunctorCounit₂_app]
  infer_instance

section BoundedAbove

variable [∀ M : C, PreservesFiniteColimits (MonoidalCategory.tensorLeft M)]
  [HasColimitsOfShape ℕ C] [HasExactColimitsOfShape ℕ C]
  [∀ X : C, PreservesColimitsOfShape ℕ (MonoidalCategory.tensorRight X)]

/-- When `P` is bounded above with flat terms and sequential colimits in `C` are exact and commute
with tensoring, `Functor.bifunctorCounit₁ α P` is a natural isomorphism. -/
theorem isIso_bifunctorCounit₁_of_boundedAbove_flat_of_isLeftDerivedFunctor₂_tensor
    (P : CochainComplex C ℤ) (b : ℤ)
    [P.IsStrictlyLE b] [∀ i, PreservesFiniteLimits (MonoidalCategory.tensorLeft (P.X i))] :
    IsIso (Functor.bifunctorCounit₁ α P) :=
  have := P.isKFlat_of_boundedAbove_flat b
  inferInstance

/-- When `Q` is bounded above with flat terms and sequential colimits in `C` are exact and commute
with tensoring, `Functor.bifunctorCounit₂ α Q` is a natural isomorphism. -/
theorem isIso_bifunctorCounit₂_of_boundedAbove_flat_of_isLeftDerivedFunctor₂_tensor
    (Q : CochainComplex C ℤ) (b : ℤ)
    [Q.IsStrictlyLE b] [∀ i, PreservesFiniteLimits (MonoidalCategory.tensorLeft (Q.X i))] :
    IsIso (Functor.bifunctorCounit₂ α Q) :=
  have := Q.isKFlat_of_boundedAbove_flat b
  inferInstance

/-- **Bounded-above flat models compute derived tensor products in the left variable.** If `P` is a
bounded-above complex of flat objects, then
`DerivedCategory.Q ⋙ LF.obj (DerivedCategory.Q.obj P)` is naturally isomorphic to the ordinary
totalized tensor functor `P ⊗ -` followed by `DerivedCategory.Q`. -/
def leftDerivedTensorObjModelIsoOfIsStrictlyLEFlat
    (P : CochainComplex C ℤ) (b : ℤ)
    [P.IsStrictlyLE b] [∀ i, PreservesFiniteLimits (MonoidalCategory.tensorLeft (P.X i))] :
    DerivedCategory.Q ⋙ LF.obj (DerivedCategory.Q.obj P) ≅
      (MonoidalCategory.curriedTensor (CochainComplex C ℤ)).obj P ⋙
        DerivedCategory.Q := by
  have : P.IsKFlat := P.isKFlat_of_boundedAbove_flat b
  exact asIso (Functor.bifunctorCounit₁ α P)

/-- The forward natural transformation of `leftDerivedTensorObjModelIsoOfIsStrictlyLEFlat` is
`Functor.bifunctorCounit₁ α P`. -/
@[simp]
theorem leftDerivedTensorObjModelIsoOfIsStrictlyLEFlat_hom
    (P : CochainComplex C ℤ) (b : ℤ)
    [P.IsStrictlyLE b] [∀ i, PreservesFiniteLimits (MonoidalCategory.tensorLeft (P.X i))] :
    (leftDerivedTensorObjModelIsoOfIsStrictlyLEFlat LF α P b).hom =
      Functor.bifunctorCounit₁ α P := by
  have : P.IsKFlat := P.isKFlat_of_boundedAbove_flat b
  simp [leftDerivedTensorObjModelIsoOfIsStrictlyLEFlat]

/-- **Bounded-above flat models compute derived tensor products in the right variable.** If `Q` is
a bounded-above complex of flat objects, then
`DerivedCategory.Q ⋙ LF.flip.obj (DerivedCategory.Q.obj Q)` is naturally isomorphic to the ordinary
totalized tensor functor `- ⊗ Q` followed by `DerivedCategory.Q`. -/
def leftDerivedTensorFlipObjModelIsoOfIsStrictlyLEFlat
    (Q : CochainComplex C ℤ) (b : ℤ)
    [Q.IsStrictlyLE b] [∀ i, PreservesFiniteLimits (MonoidalCategory.tensorLeft (Q.X i))] :
    DerivedCategory.Q ⋙ LF.flip.obj (DerivedCategory.Q.obj Q) ≅
      (MonoidalCategory.curriedTensor (CochainComplex C ℤ)).flip.obj Q ⋙
        DerivedCategory.Q := by
  have : Q.IsKFlat := Q.isKFlat_of_boundedAbove_flat b
  exact asIso (Functor.bifunctorCounit₂ α Q)

/-- The forward natural transformation of `leftDerivedTensorFlipObjModelIsoOfIsStrictlyLEFlat` is
`Functor.bifunctorCounit₂ α Q`. -/
@[simp]
theorem leftDerivedTensorFlipObjModelIsoOfIsStrictlyLEFlat_hom
    (Q : CochainComplex C ℤ) (b : ℤ)
    [Q.IsStrictlyLE b] [∀ i, PreservesFiniteLimits (MonoidalCategory.tensorLeft (Q.X i))] :
    (leftDerivedTensorFlipObjModelIsoOfIsStrictlyLEFlat LF α Q b).hom =
      Functor.bifunctorCounit₂ α Q := by
  have : Q.IsKFlat := Q.isKFlat_of_boundedAbove_flat b
  simp [leftDerivedTensorFlipObjModelIsoOfIsStrictlyLEFlat]

end BoundedAbove

/-- For a K-flat complex `P`, evaluating any left derived tensor bifunctor `(LF, α)` at
`DerivedCategory.Q.obj P` is naturally isomorphic to `P.kFlatTensor`. -/
def leftDerivedTensorObjIsoKFlatTensor (P : CochainComplex C ℤ) [P.IsKFlat] :
    LF.obj (DerivedCategory.Q.obj P) ≅ P.kFlatTensor :=
  letI : Localization.Lifting DerivedCategory.Q (quasiIso C (.up ℤ))
      ((MonoidalCategory.curriedTensor (CochainComplex C ℤ)).obj P ⋙ DerivedCategory.Q)
      (LF.obj (DerivedCategory.Q.obj P)) :=
    ⟨asIso (Functor.bifunctorCounit₁ α P)⟩
  Localization.liftNatIso DerivedCategory.Q (quasiIso C (.up ℤ))
    ((MonoidalCategory.curriedTensor (CochainComplex C ℤ)).obj P ⋙ DerivedCategory.Q)
    (((MonoidalCategory.curriedTensor C).map₂CochainComplex.obj P) ⋙ DerivedCategory.Q)
    (LF.obj (DerivedCategory.Q.obj P)) P.kFlatTensor
    (Functor.isoWhiskerRight ((CochainComplex.curriedTensorIsoMap₂CochainComplex C).app P)
      DerivedCategory.Q)

/-- On a complex model `L`, `leftDerivedTensorObjIsoKFlatTensor LF α P` intertwines
`P.kFlatTensorModelIso` with `(α.app P).app L`. -/
@[reassoc (attr := simp)]
theorem leftDerivedTensorObjIsoKFlatTensor_hom_app_Q_comp
    (P L : CochainComplex C ℤ) [P.IsKFlat] :
    (leftDerivedTensorObjIsoKFlatTensor LF α P).hom.app (DerivedCategory.Q.obj L) ≫
      P.kFlatTensorModelIso.hom.app L = (α.app P).app L := by
  let : Localization.Lifting DerivedCategory.Q (quasiIso C (.up ℤ))
      ((MonoidalCategory.curriedTensor (CochainComplex C ℤ)).obj P ⋙ DerivedCategory.Q)
      (LF.obj (DerivedCategory.Q.obj P)) :=
    ⟨asIso (Functor.bifunctorCounit₁ α P)⟩
  have h := Localization.liftNatTrans_app DerivedCategory.Q (quasiIso C (.up ℤ))
    ((MonoidalCategory.curriedTensor (CochainComplex C ℤ)).obj P ⋙ DerivedCategory.Q)
    (((MonoidalCategory.curriedTensor C).map₂CochainComplex.obj P) ⋙ DerivedCategory.Q)
    (LF.obj (DerivedCategory.Q.obj P)) P.kFlatTensor
    (Functor.isoWhiskerRight ((CochainComplex.curriedTensorIsoMap₂CochainComplex C).app P)
      DerivedCategory.Q).hom L
  rw [← CochainComplex.kFlatTensorModelIso_eq_liftingIso P] at h
  have h' := h =≫ P.kFlatTensorModelIso.hom.app L
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at h'
  exact h'.trans (by dsimp [Functor.bifunctorCounit₁]; simp; rfl)

/-- Compatibility of `leftDerivedTensorObjIsoKFlatTensor` with morphisms `f : P₁ ⟶ P₂` between
K-flat models: `LF.map (DerivedCategory.Q.map f)` corresponds to `CochainComplex.kFlatTensorMap f`.
-/
@[reassoc]
theorem leftDerivedTensorObjIsoKFlatTensor_naturality
    {P₁ P₂ : CochainComplex C ℤ} [P₁.IsKFlat] [P₂.IsKFlat] (f : P₁ ⟶ P₂) :
    LF.map (DerivedCategory.Q.map f) ≫ (leftDerivedTensorObjIsoKFlatTensor LF α P₂).hom =
      (leftDerivedTensorObjIsoKFlatTensor LF α P₁).hom ≫ CochainComplex.kFlatTensorMap f := by
  refine Localization.natTrans_ext DerivedCategory.Q (quasiIso C (.up ℤ)) fun L ↦ ?_
  rw [← cancel_mono (P₂.kFlatTensorModelIso.hom.app L)]
  simp only [NatTrans.comp_app, Category.assoc, leftDerivedTensorObjIsoKFlatTensor_hom_app_Q_comp,
    CochainComplex.kFlatTensorMap_app_Q_comp,
    leftDerivedTensorObjIsoKFlatTensor_hom_app_Q_comp_assoc]
  have hnat := NatTrans.congr_app (α.naturality f) L
  dsimp at hnat
  rw [whiskerRight_eq_mapBifunctorMap] at hnat
  exact hnat

/-- **Left unitor.** Left derived tensoring with the monoidal unit complex `𝟙_ (CochainComplex C ℤ)`
(the unit of `C` in degree `0`) is naturally isomorphic to the identity of `DerivedCategory C`, for
any left derived tensor bifunctor `(LF, α)`. -/
def leftDerivedTensorLeftUnitor :
    LF.obj (DerivedCategory.Q.obj (𝟙_ (CochainComplex C ℤ))) ≅ 𝟭 (DerivedCategory C) :=
  Localization.liftNatIso DerivedCategory.Q (quasiIso C (.up ℤ))
    (DerivedCategory.Q ⋙ LF.obj (DerivedCategory.Q.obj (𝟙_ (CochainComplex C ℤ))))
    (DerivedCategory.Q ⋙ 𝟭 (DerivedCategory C))
    (LF.obj (DerivedCategory.Q.obj (𝟙_ (CochainComplex C ℤ)))) (𝟭 (DerivedCategory C))
    (asIso (Functor.bifunctorCounit₁ α (𝟙_ (CochainComplex C ℤ))) ≪≫
      Functor.isoWhiskerRight (MonoidalCategory.leftUnitorNatIso _) DerivedCategory.Q ≪≫
      DerivedCategory.Q.leftUnitor ≪≫ DerivedCategory.Q.rightUnitor.symm)

/-- On complex models, `leftDerivedTensorLeftUnitor` is the derived tensor counit followed by the
left unitor of `CochainComplex C ℤ`. -/
@[simp]
theorem leftDerivedTensorLeftUnitor_hom_app_Q (L : CochainComplex C ℤ) :
    (leftDerivedTensorLeftUnitor LF α).hom.app (DerivedCategory.Q.obj L) =
      (α.app (𝟙_ (CochainComplex C ℤ))).app L ≫ DerivedCategory.Q.map (λ_ L).hom := by
  simp [leftDerivedTensorLeftUnitor]

/-- **Right unitor.** Right derived tensoring with the monoidal unit complex
`𝟙_ (CochainComplex C ℤ)` is naturally isomorphic to the identity of `DerivedCategory C`, for any
left derived tensor bifunctor `(LF, α)`. -/
def leftDerivedTensorRightUnitor :
    LF.flip.obj (DerivedCategory.Q.obj (𝟙_ (CochainComplex C ℤ))) ≅ 𝟭 (DerivedCategory C) :=
  Localization.liftNatIso DerivedCategory.Q (quasiIso C (.up ℤ))
    (DerivedCategory.Q ⋙ LF.flip.obj (DerivedCategory.Q.obj (𝟙_ (CochainComplex C ℤ))))
    (DerivedCategory.Q ⋙ 𝟭 (DerivedCategory C))
    (LF.flip.obj (DerivedCategory.Q.obj (𝟙_ (CochainComplex C ℤ)))) (𝟭 (DerivedCategory C))
    (asIso (Functor.bifunctorCounit₂ α (𝟙_ (CochainComplex C ℤ))) ≪≫
      Functor.isoWhiskerRight (MonoidalCategory.rightUnitorNatIso _) DerivedCategory.Q ≪≫
      DerivedCategory.Q.leftUnitor ≪≫ DerivedCategory.Q.rightUnitor.symm)

/-- On complex models, `leftDerivedTensorRightUnitor` is the derived tensor counit followed by the
right unitor of `CochainComplex C ℤ`. -/
@[simp]
theorem leftDerivedTensorRightUnitor_hom_app_Q (K : CochainComplex C ℤ) :
    (leftDerivedTensorRightUnitor LF α).hom.app (DerivedCategory.Q.obj K) =
      (α.app K).app (𝟙_ (CochainComplex C ℤ)) ≫ DerivedCategory.Q.map (ρ_ K).hom := by
  simp [leftDerivedTensorRightUnitor]

end TauCeti

end ModelComparison

section Unit

variable [(CochainComplex.KFlat.localizerMorphism C).IsLeftDerivabilityStructure]
  [HasDerivedCategory C]

namespace TauCeti

variable (C)

/-- The derived tensor product with the unit `𝟙_ C` placed in degree `0` on the left is naturally
isomorphic to the identity of the derived category. -/
def derivedTensorLeftUnitor :
    (derivedTensor C).obj ((DerivedCategory.singleFunctor C 0).obj (𝟙_ C)) ≅ 𝟭 _ :=
  leftDerivedTensorLeftUnitor (derivedTensor C) (derivedTensorCounit C)

/-- On a complex model `L`, the derived left unitor is the derived tensor comparison followed by
the left unitor of cochain complexes. -/
@[simp]
theorem derivedTensorLeftUnitor_hom_app_Q (L : CochainComplex C ℤ) :
    (derivedTensorLeftUnitor C).hom.app (DerivedCategory.Q.obj L) =
      ((derivedTensorCounit C).app (𝟙_ (CochainComplex C ℤ))).app L ≫
        DerivedCategory.Q.map (λ_ L).hom :=
  leftDerivedTensorLeftUnitor_hom_app_Q (derivedTensor C) (derivedTensorCounit C) L

/-- The derived tensor product with the unit `𝟙_ C` placed in degree `0` on the right is naturally
isomorphic to the identity of the derived category. -/
def derivedTensorRightUnitor :
    (derivedTensor C).flip.obj ((DerivedCategory.singleFunctor C 0).obj (𝟙_ C)) ≅ 𝟭 _ :=
  leftDerivedTensorRightUnitor (derivedTensor C) (derivedTensorCounit C)

/-- On a complex model `K`, the derived right unitor is the derived tensor comparison followed by
the right unitor of cochain complexes. -/
@[simp]
theorem derivedTensorRightUnitor_hom_app_Q (K : CochainComplex C ℤ) :
    (derivedTensorRightUnitor C).hom.app (DerivedCategory.Q.obj K) =
      ((derivedTensorCounit C).app K).app (𝟙_ (CochainComplex C ℤ)) ≫
        DerivedCategory.Q.map (ρ_ K).hom :=
  leftDerivedTensorRightUnitor_hom_app_Q (derivedTensor C) (derivedTensorCounit C) K

end TauCeti

end Unit

end

section Symmetry

variable [HasDerivedCategory C]
  (LF : DerivedCategory C ⥤ DerivedCategory C ⥤ DerivedCategory C)
  (α : (((whiskeringLeft₂ (DerivedCategory C)).obj DerivedCategory.Q).obj
    DerivedCategory.Q).obj LF ⟶
      MonoidalCategory.curriedTensor (CochainComplex C ℤ) ⋙
        (whiskeringRight _ _ _).obj (DerivedCategory.Q (C := C)))
  [LF.IsLeftDerivedFunctor₂ α (quasiIso C (.up ℤ)) (quasiIso C (.up ℤ))]

namespace TauCeti

section Braided

variable [BraidedCategory C]

/-- The Koszul braiding transported to a flip isomorphism on the postcomposed total tensor
bifunctor. -/
def koszulDerivedFlipIso :
    (MonoidalCategory.curriedTensor (CochainComplex C ℤ) ⋙
        (whiskeringRight _ _ _).obj (DerivedCategory.Q (C := C))).flip ≅
      MonoidalCategory.curriedTensor (CochainComplex C ℤ) ⋙
        (whiskeringRight _ _ _).obj (DerivedCategory.Q (C := C)) :=
  Functor.whiskeringRightFlipIso
      (MonoidalCategory.curriedTensor (CochainComplex C ℤ))
      (DerivedCategory.Q (C := C)) ≪≫
    Functor.isoWhiskerRight
      ((flipFunctor _ _ _).mapIso
          (BraidedCategory.curriedBraidingNatIso (CochainComplex C ℤ)) ≪≫
        (flipping (C := CochainComplex C ℤ) (D := CochainComplex C ℤ)
          (E := CochainComplex C ℤ)).counitIso.app _)
      ((whiskeringRight _ _ _).obj DerivedCategory.Q)

/-- Forward component of `koszulDerivedFlipIso` on complexes `(K, L)`. -/
@[simp]
lemma koszulDerivedFlipIso_hom_app_app (K L : CochainComplex C ℤ) :
    ((koszulDerivedFlipIso (C := C)).hom.app K).app L =
      DerivedCategory.Q.map (β_ L K).hom := by
  simp [koszulDerivedFlipIso, BraidedCategory.curriedBraidingNatIso]

/-- Inverse component of `koszulDerivedFlipIso` on complexes `(K, L)`. -/
@[simp]
lemma koszulDerivedFlipIso_inv_app_app (K L : CochainComplex C ℤ) :
    ((koszulDerivedFlipIso (C := C)).inv.app K).app L =
      DerivedCategory.Q.map (β_ L K).inv := by
  simp [koszulDerivedFlipIso, BraidedCategory.curriedBraidingNatIso]

/-- **Symmetry of the derived tensor product.** The Koszul braiding induces a natural isomorphism
`LF.flip ≅ LF` on any left derived tensor bifunctor `(LF, α)`. -/
def leftDerivedTensorFlipIso : LF.flip ≅ LF :=
  LF.leftDerived₂FlipIso α (quasiIso C (.up ℤ)) (koszulDerivedFlipIso (C := C))

/-- Whiskered counit compatibility of `(leftDerivedTensorFlipIso LF α).hom` with `α` and
`koszulDerivedFlipIso`. -/
@[reassoc (attr := simp)]
lemma leftDerivedTensorFlipIso_hom_fac :
    (((whiskeringLeft₂ (DerivedCategory C)).obj DerivedCategory.Q).obj DerivedCategory.Q).map
        (leftDerivedTensorFlipIso LF α).hom ≫ α =
      (DerivedCategory.Q.whiskeringLeft₂FlipIso DerivedCategory.Q LF).hom ≫
        (flipFunctor _ _ _).map α ≫ (koszulDerivedFlipIso (C := C)).hom :=
  leftDerived₂FlipIso_hom_fac LF α (quasiIso C (.up ℤ)) (koszulDerivedFlipIso (C := C))

/-- Whiskered counit compatibility of `(leftDerivedTensorFlipIso LF α).inv` with `α` and
`koszulDerivedFlipIso`. -/
@[reassoc (attr := simp)]
lemma leftDerivedTensorFlipIso_inv_fac :
    (((whiskeringLeft₂ (DerivedCategory C)).obj DerivedCategory.Q).obj DerivedCategory.Q).map
        (leftDerivedTensorFlipIso LF α).inv ≫
        (DerivedCategory.Q.whiskeringLeft₂FlipIso DerivedCategory.Q LF).hom ≫
        (flipFunctor _ _ _).map α =
      α ≫ (koszulDerivedFlipIso (C := C)).inv :=
  leftDerived₂FlipIso_inv_fac LF α (quasiIso C (.up ℤ)) (koszulDerivedFlipIso (C := C))

/-- Compatibility of `leftDerivedTensorFlipIso` with the Koszul braiding on images of complexes. -/
@[reassoc (attr := simp)]
lemma leftDerivedTensorFlipIso_hom_app_app_Q (K L : CochainComplex C ℤ) :
    ((leftDerivedTensorFlipIso LF α).hom.app (DerivedCategory.Q.obj K)).app
        (DerivedCategory.Q.obj L) ≫ (α.app K).app L =
      (α.app L).app K ≫ DerivedCategory.Q.map (β_ L K).hom := by
  simp only [leftDerivedTensorFlipIso, leftDerived₂FlipIso_hom_app_app_L,
    koszulDerivedFlipIso_hom_app_app]

/-- Compatibility of the inverse of `leftDerivedTensorFlipIso` with the inverse Koszul braiding on
images of complexes. -/
@[reassoc (attr := simp)]
lemma leftDerivedTensorFlipIso_inv_app_app_Q (K L : CochainComplex C ℤ) :
    ((leftDerivedTensorFlipIso LF α).inv.app (DerivedCategory.Q.obj K)).app
        (DerivedCategory.Q.obj L) ≫ (α.app L).app K =
      (α.app K).app L ≫ DerivedCategory.Q.map (β_ L K).inv := by
  simp only [leftDerivedTensorFlipIso, leftDerived₂FlipIso_inv_app_app_L,
    koszulDerivedFlipIso_inv_app_app]

/-- When both comparison morphisms `(α.app L).app K` and `(α.app K).app L` are invertible (in
particular, when either `K` or `L` is K-flat), `leftDerivedTensorFlipIso` on `(Q.obj K, Q.obj L)`
is the swapped model comparison followed by the localized Koszul braiding and the inverse target
comparison. -/
lemma leftDerivedTensorFlipIso_app_app_Q (K L : CochainComplex C ℤ)
    [IsIso ((α.app L).app K)] [IsIso ((α.app K).app L)] :
    ((leftDerivedTensorFlipIso LF α).app (DerivedCategory.Q.obj K)).app
        (DerivedCategory.Q.obj L) =
      asIso ((α.app L).app K) ≪≫ DerivedCategory.Q.mapIso (β_ L K) ≪≫
        (asIso ((α.app K).app L)).symm := by
  ext
  rw [← cancel_mono ((α.app K).app L)]
  simp

section Unitor

variable [(CochainComplex.KFlat.localizerMorphism C).IsLeftDerivabilityStructure]

/-- The Koszul flip at `𝟙` followed by the left derived unitor equals the right derived
unitor as a natural transformation. -/
@[reassoc (attr := simp)]
lemma leftDerivedTensorFlipIso_hom_app_comp_leftUnitor :
    (leftDerivedTensorFlipIso LF α).hom.app
        (DerivedCategory.Q.obj (𝟙_ (CochainComplex C ℤ))) ≫
      (leftDerivedTensorLeftUnitor LF α).hom =
      (leftDerivedTensorRightUnitor LF α).hom := by
  refine Localization.natTrans_ext DerivedCategory.Q (quasiIso C (.up ℤ)) fun K ↦ ?_
  simp only [NatTrans.comp_app, leftDerivedTensorLeftUnitor_hom_app_Q,
    leftDerivedTensorFlipIso_hom_app_app_Q_assoc, leftDerivedTensorRightUnitor_hom_app_Q]
  rw [← DerivedCategory.Q.map_comp, braiding_leftUnitor]

/-- The Koszul flip at `(𝟙, X)` followed by the left derived unitor equals the right derived
unitor. -/
@[reassoc (attr := simp)]
lemma leftDerivedTensorFlipIso_hom_app_app_comp_leftUnitor (X : DerivedCategory C) :
    ((leftDerivedTensorFlipIso LF α).hom.app
        (DerivedCategory.Q.obj (𝟙_ (CochainComplex C ℤ)))).app X ≫
      (leftDerivedTensorLeftUnitor LF α).hom.app X =
      (leftDerivedTensorRightUnitor LF α).hom.app X :=
  NatTrans.congr_app (leftDerivedTensorFlipIso_hom_app_comp_leftUnitor LF α) X

/-- The flipped Koszul flip at `𝟙` followed by the right derived unitor equals the left derived
unitor as a natural transformation. -/
@[reassoc (attr := simp)]
lemma flip_leftDerivedTensorFlipIso_hom_app_comp_rightUnitor :
    ((flipFunctor _ _ _).map (leftDerivedTensorFlipIso LF α).hom).app
        (DerivedCategory.Q.obj (𝟙_ (CochainComplex C ℤ))) ≫
      (leftDerivedTensorRightUnitor LF α).hom =
      (leftDerivedTensorLeftUnitor LF α).hom := by
  refine Localization.natTrans_ext DerivedCategory.Q (quasiIso C (.up ℤ)) fun K ↦ ?_
  simp only [NatTrans.comp_app, flipFunctor_map_app_app, leftDerivedTensorRightUnitor_hom_app_Q,
    leftDerivedTensorFlipIso_hom_app_app_Q_assoc, leftDerivedTensorLeftUnitor_hom_app_Q]
  rw [← DerivedCategory.Q.map_comp, braiding_rightUnitor]

/-- The Koszul flip at `(X, 𝟙)` followed by the right derived unitor equals the left derived
unitor. -/
@[reassoc (attr := simp)]
lemma leftDerivedTensorFlipIso_hom_app_app_comp_rightUnitor (X : DerivedCategory C) :
    ((leftDerivedTensorFlipIso LF α).hom.app X).app
        (DerivedCategory.Q.obj (𝟙_ (CochainComplex C ℤ))) ≫
      (leftDerivedTensorRightUnitor LF α).hom.app X =
      (leftDerivedTensorLeftUnitor LF α).hom.app X :=
  NatTrans.congr_app (flip_leftDerivedTensorFlipIso_hom_app_comp_rightUnitor LF α) X

/-- The inverse Koszul flip at `𝟙` followed by the right derived unitor equals the left derived
unitor as a natural transformation. -/
@[reassoc (attr := simp)]
lemma leftDerivedTensorFlipIso_inv_app_comp_rightUnitor :
    (leftDerivedTensorFlipIso LF α).inv.app
        (DerivedCategory.Q.obj (𝟙_ (CochainComplex C ℤ))) ≫
      (leftDerivedTensorRightUnitor LF α).hom =
      (leftDerivedTensorLeftUnitor LF α).hom := by
  rw [← leftDerivedTensorFlipIso_hom_app_comp_leftUnitor LF α, ← NatTrans.comp_app_assoc,
    Iso.inv_hom_id, NatTrans.id_app, Category.id_comp]

/-- The inverse Koszul flip at `(𝟙, X)` followed by the right derived unitor equals the left
derived unitor. -/
@[reassoc (attr := simp)]
lemma leftDerivedTensorFlipIso_inv_app_app_comp_rightUnitor (X : DerivedCategory C) :
    ((leftDerivedTensorFlipIso LF α).inv.app
        (DerivedCategory.Q.obj (𝟙_ (CochainComplex C ℤ)))).app X ≫
      (leftDerivedTensorRightUnitor LF α).hom.app X =
      (leftDerivedTensorLeftUnitor LF α).hom.app X :=
  NatTrans.congr_app (leftDerivedTensorFlipIso_inv_app_comp_rightUnitor LF α) X

/-- The flipped inverse Koszul flip at `𝟙` followed by the left derived unitor equals the right
derived unitor as a natural transformation. -/
@[reassoc (attr := simp)]
lemma flip_leftDerivedTensorFlipIso_inv_app_comp_leftUnitor :
    ((flipFunctor _ _ _).map (leftDerivedTensorFlipIso LF α).inv).app
        (DerivedCategory.Q.obj (𝟙_ (CochainComplex C ℤ))) ≫
      (leftDerivedTensorLeftUnitor LF α).hom =
      (leftDerivedTensorRightUnitor LF α).hom := by
  rw [← flip_leftDerivedTensorFlipIso_hom_app_comp_rightUnitor LF α, ← NatTrans.comp_app_assoc,
    ← Functor.map_comp, Iso.inv_hom_id]
  simp

/-- The inverse Koszul flip at `(X, 𝟙)` followed by the left derived unitor equals the right
derived unitor. -/
@[reassoc (attr := simp)]
lemma leftDerivedTensorFlipIso_inv_app_app_comp_leftUnitor (X : DerivedCategory C) :
    ((leftDerivedTensorFlipIso LF α).inv.app X).app
        (DerivedCategory.Q.obj (𝟙_ (CochainComplex C ℤ))) ≫
      (leftDerivedTensorLeftUnitor LF α).hom.app X =
      (leftDerivedTensorRightUnitor LF α).hom.app X :=
  NatTrans.congr_app (flip_leftDerivedTensorFlipIso_inv_app_comp_leftUnitor LF α) X

/-- The inverse right derived unitor followed by the Koszul flip at `(𝟙, -)` equals the inverse
left derived unitor as a natural transformation. -/
@[reassoc (attr := simp)]
lemma leftDerivedTensorRightUnitor_inv_comp_leftDerivedTensorFlipIso_hom_app :
    (leftDerivedTensorRightUnitor LF α).inv ≫
        (leftDerivedTensorFlipIso LF α).hom.app
          (DerivedCategory.Q.obj (𝟙_ (CochainComplex C ℤ))) =
      (leftDerivedTensorLeftUnitor LF α).inv := by
  rw [← cancel_mono (leftDerivedTensorLeftUnitor LF α).hom, Category.assoc,
    leftDerivedTensorFlipIso_hom_app_comp_leftUnitor, Iso.inv_hom_id, Iso.inv_hom_id]

/-- The inverse right derived unitor followed by the Koszul flip at `(𝟙, X)` equals the inverse
left derived unitor. -/
@[reassoc (attr := simp)]
lemma leftDerivedTensorRightUnitor_inv_app_comp_leftDerivedTensorFlipIso_hom_app_app
    (X : DerivedCategory C) :
    (leftDerivedTensorRightUnitor LF α).inv.app X ≫
        ((leftDerivedTensorFlipIso LF α).hom.app
          (DerivedCategory.Q.obj (𝟙_ (CochainComplex C ℤ)))).app X =
      (leftDerivedTensorLeftUnitor LF α).inv.app X :=
  NatTrans.congr_app
    (leftDerivedTensorRightUnitor_inv_comp_leftDerivedTensorFlipIso_hom_app LF α) X

/-- The inverse left derived unitor followed by the flipped Koszul flip at `𝟙` equals the inverse
right derived unitor as a natural transformation. -/
@[reassoc (attr := simp)]
lemma leftDerivedTensorLeftUnitor_inv_comp_flip_leftDerivedTensorFlipIso_hom_app :
    (leftDerivedTensorLeftUnitor LF α).inv ≫
        ((flipFunctor _ _ _).map (leftDerivedTensorFlipIso LF α).hom).app
          (DerivedCategory.Q.obj (𝟙_ (CochainComplex C ℤ))) =
      (leftDerivedTensorRightUnitor LF α).inv := by
  rw [← cancel_mono (leftDerivedTensorRightUnitor LF α).hom, Category.assoc,
    flip_leftDerivedTensorFlipIso_hom_app_comp_rightUnitor, Iso.inv_hom_id, Iso.inv_hom_id]

/-- The inverse left derived unitor followed by the Koszul flip at `(X, 𝟙)` equals the inverse
right derived unitor. -/
@[reassoc (attr := simp)]
lemma leftDerivedTensorLeftUnitor_inv_app_comp_leftDerivedTensorFlipIso_hom_app_app
    (X : DerivedCategory C) :
    (leftDerivedTensorLeftUnitor LF α).inv.app X ≫
        ((leftDerivedTensorFlipIso LF α).hom.app X).app
          (DerivedCategory.Q.obj (𝟙_ (CochainComplex C ℤ))) =
      (leftDerivedTensorRightUnitor LF α).inv.app X :=
  NatTrans.congr_app
    (leftDerivedTensorLeftUnitor_inv_comp_flip_leftDerivedTensorFlipIso_hom_app LF α) X

/-- The inverse left derived unitor followed by the inverse Koszul flip at `(𝟙, -)` equals the
inverse right derived unitor as a natural transformation. -/
@[reassoc (attr := simp)]
lemma leftDerivedTensorLeftUnitor_inv_comp_leftDerivedTensorFlipIso_inv_app :
    (leftDerivedTensorLeftUnitor LF α).inv ≫
        (leftDerivedTensorFlipIso LF α).inv.app
          (DerivedCategory.Q.obj (𝟙_ (CochainComplex C ℤ))) =
      (leftDerivedTensorRightUnitor LF α).inv := by
  rw [← cancel_mono (leftDerivedTensorRightUnitor LF α).hom, Category.assoc,
    leftDerivedTensorFlipIso_inv_app_comp_rightUnitor, Iso.inv_hom_id, Iso.inv_hom_id]

/-- The inverse left derived unitor followed by the inverse Koszul flip at `(𝟙, X)` equals the
inverse right derived unitor. -/
@[reassoc (attr := simp)]
lemma leftDerivedTensorLeftUnitor_inv_app_comp_leftDerivedTensorFlipIso_inv_app_app
    (X : DerivedCategory C) :
    (leftDerivedTensorLeftUnitor LF α).inv.app X ≫
        ((leftDerivedTensorFlipIso LF α).inv.app
          (DerivedCategory.Q.obj (𝟙_ (CochainComplex C ℤ)))).app X =
      (leftDerivedTensorRightUnitor LF α).inv.app X :=
  NatTrans.congr_app
    (leftDerivedTensorLeftUnitor_inv_comp_leftDerivedTensorFlipIso_inv_app LF α) X

/-- The inverse right derived unitor followed by the flipped inverse Koszul flip at `𝟙` equals the
inverse left derived unitor as a natural transformation. -/
@[reassoc (attr := simp)]
lemma leftDerivedTensorRightUnitor_inv_comp_flip_leftDerivedTensorFlipIso_inv_app :
    (leftDerivedTensorRightUnitor LF α).inv ≫
        ((flipFunctor _ _ _).map (leftDerivedTensorFlipIso LF α).inv).app
          (DerivedCategory.Q.obj (𝟙_ (CochainComplex C ℤ))) =
      (leftDerivedTensorLeftUnitor LF α).inv := by
  rw [← cancel_mono (leftDerivedTensorLeftUnitor LF α).hom, Category.assoc,
    flip_leftDerivedTensorFlipIso_inv_app_comp_leftUnitor, Iso.inv_hom_id, Iso.inv_hom_id]

/-- The inverse right derived unitor followed by the inverse Koszul flip at `(X, 𝟙)` equals the
inverse left derived unitor. -/
@[reassoc (attr := simp)]
lemma leftDerivedTensorRightUnitor_inv_app_comp_leftDerivedTensorFlipIso_inv_app_app
    (X : DerivedCategory C) :
    (leftDerivedTensorRightUnitor LF α).inv.app X ≫
        ((leftDerivedTensorFlipIso LF α).inv.app X).app
          (DerivedCategory.Q.obj (𝟙_ (CochainComplex C ℤ))) =
      (leftDerivedTensorLeftUnitor LF α).inv.app X :=
  NatTrans.congr_app
    (leftDerivedTensorRightUnitor_inv_comp_flip_leftDerivedTensorFlipIso_inv_app LF α) X

/- Note: `derivedTensorLeftUnitor C` and `derivedTensorRightUnitor C` are defined directly as
`leftDerivedTensorLeftUnitor (derivedTensor C) (derivedTensorCounit C)` and
`leftDerivedTensorRightUnitor (derivedTensor C) (derivedTensorCounit C)`, which relies on the
definitional equality `(DerivedCategory.singleFunctor C 0).obj (𝟙_ C) =
DerivedCategory.Q.obj (𝟙_ (CochainComplex C ℤ))` (via `DerivedCategory.Q_obj_single_obj`, since
`DerivedCategory.singleFunctor` is an `abbrev` and `𝟙_ (CochainComplex C ℤ)` is definitionally
`(HomologicalComplex.single C (.up ℤ) 0).obj (𝟙_ C)`). All specialized natural-transformation
lemmas below share this same definitional reduction. -/

omit LF α [LF.IsLeftDerivedFunctor₂ α (quasiIso C (.up ℤ)) (quasiIso C (.up ℤ))] in
/-- The Koszul flip at `𝟙_ C[0]` followed by `derivedTensorLeftUnitor` equals
`derivedTensorRightUnitor` as a natural transformation. -/
@[reassoc (attr := simp)]
lemma leftDerivedTensorFlipIso_hom_app_comp_derivedTensorLeftUnitor :
    (leftDerivedTensorFlipIso (derivedTensor C) (derivedTensorCounit C)).hom.app
        ((DerivedCategory.singleFunctor C 0).obj (𝟙_ C)) ≫
      (derivedTensorLeftUnitor C).hom =
      (derivedTensorRightUnitor C).hom :=
  leftDerivedTensorFlipIso_hom_app_comp_leftUnitor (derivedTensor C) (derivedTensorCounit C)

omit LF α [LF.IsLeftDerivedFunctor₂ α (quasiIso C (.up ℤ)) (quasiIso C (.up ℤ))] in
/-- The Koszul flip at `(𝟙_ C[0], X)` followed by `derivedTensorLeftUnitor` equals
`derivedTensorRightUnitor`. -/
@[reassoc (attr := simp)]
lemma leftDerivedTensorFlipIso_hom_app_app_comp_derivedTensorLeftUnitor
    (X : DerivedCategory C) :
    ((leftDerivedTensorFlipIso (derivedTensor C) (derivedTensorCounit C)).hom.app
        ((DerivedCategory.singleFunctor C 0).obj (𝟙_ C))).app X ≫
      (derivedTensorLeftUnitor C).hom.app X =
      (derivedTensorRightUnitor C).hom.app X :=
  NatTrans.congr_app leftDerivedTensorFlipIso_hom_app_comp_derivedTensorLeftUnitor X

omit LF α [LF.IsLeftDerivedFunctor₂ α (quasiIso C (.up ℤ)) (quasiIso C (.up ℤ))] in
/-- The flipped Koszul flip at `𝟙_ C[0]` followed by `derivedTensorRightUnitor` equals
`derivedTensorLeftUnitor` as a natural transformation. -/
@[reassoc (attr := simp)]
lemma flip_leftDerivedTensorFlipIso_hom_app_comp_derivedTensorRightUnitor :
    ((flipFunctor _ _ _).map
        (leftDerivedTensorFlipIso (derivedTensor C) (derivedTensorCounit C)).hom).app
        ((DerivedCategory.singleFunctor C 0).obj (𝟙_ C)) ≫
      (derivedTensorRightUnitor C).hom =
      (derivedTensorLeftUnitor C).hom :=
  flip_leftDerivedTensorFlipIso_hom_app_comp_rightUnitor
    (derivedTensor C) (derivedTensorCounit C)

omit LF α [LF.IsLeftDerivedFunctor₂ α (quasiIso C (.up ℤ)) (quasiIso C (.up ℤ))] in
/-- The Koszul flip at `(X, 𝟙_ C[0])` followed by `derivedTensorRightUnitor` equals
`derivedTensorLeftUnitor`. -/
@[reassoc (attr := simp)]
lemma leftDerivedTensorFlipIso_hom_app_app_comp_derivedTensorRightUnitor
    (X : DerivedCategory C) :
    ((leftDerivedTensorFlipIso (derivedTensor C) (derivedTensorCounit C)).hom.app X).app
        ((DerivedCategory.singleFunctor C 0).obj (𝟙_ C)) ≫
      (derivedTensorRightUnitor C).hom.app X =
      (derivedTensorLeftUnitor C).hom.app X :=
  NatTrans.congr_app flip_leftDerivedTensorFlipIso_hom_app_comp_derivedTensorRightUnitor X

omit LF α [LF.IsLeftDerivedFunctor₂ α (quasiIso C (.up ℤ)) (quasiIso C (.up ℤ))] in
/-- The inverse Koszul flip at `𝟙_ C[0]` followed by `derivedTensorRightUnitor` equals
`derivedTensorLeftUnitor` as a natural transformation. -/
@[reassoc (attr := simp)]
lemma leftDerivedTensorFlipIso_inv_app_comp_derivedTensorRightUnitor :
    (leftDerivedTensorFlipIso (derivedTensor C) (derivedTensorCounit C)).inv.app
        ((DerivedCategory.singleFunctor C 0).obj (𝟙_ C)) ≫
      (derivedTensorRightUnitor C).hom =
      (derivedTensorLeftUnitor C).hom :=
  leftDerivedTensorFlipIso_inv_app_comp_rightUnitor (derivedTensor C) (derivedTensorCounit C)

omit LF α [LF.IsLeftDerivedFunctor₂ α (quasiIso C (.up ℤ)) (quasiIso C (.up ℤ))] in
/-- The inverse Koszul flip at `(𝟙_ C[0], X)` followed by `derivedTensorRightUnitor` equals
`derivedTensorLeftUnitor`. -/
@[reassoc (attr := simp)]
lemma leftDerivedTensorFlipIso_inv_app_app_comp_derivedTensorRightUnitor
    (X : DerivedCategory C) :
    ((leftDerivedTensorFlipIso (derivedTensor C) (derivedTensorCounit C)).inv.app
        ((DerivedCategory.singleFunctor C 0).obj (𝟙_ C))).app X ≫
      (derivedTensorRightUnitor C).hom.app X =
      (derivedTensorLeftUnitor C).hom.app X :=
  NatTrans.congr_app leftDerivedTensorFlipIso_inv_app_comp_derivedTensorRightUnitor X

omit LF α [LF.IsLeftDerivedFunctor₂ α (quasiIso C (.up ℤ)) (quasiIso C (.up ℤ))] in
/-- The flipped inverse Koszul flip at `𝟙_ C[0]` followed by `derivedTensorLeftUnitor` equals
`derivedTensorRightUnitor` as a natural transformation. -/
@[reassoc (attr := simp)]
lemma flip_leftDerivedTensorFlipIso_inv_app_comp_derivedTensorLeftUnitor :
    ((flipFunctor _ _ _).map
        (leftDerivedTensorFlipIso (derivedTensor C) (derivedTensorCounit C)).inv).app
        ((DerivedCategory.singleFunctor C 0).obj (𝟙_ C)) ≫
      (derivedTensorLeftUnitor C).hom =
      (derivedTensorRightUnitor C).hom :=
  flip_leftDerivedTensorFlipIso_inv_app_comp_leftUnitor
    (derivedTensor C) (derivedTensorCounit C)

omit LF α [LF.IsLeftDerivedFunctor₂ α (quasiIso C (.up ℤ)) (quasiIso C (.up ℤ))] in
/-- The inverse Koszul flip at `(X, 𝟙_ C[0])` followed by `derivedTensorLeftUnitor` equals
`derivedTensorRightUnitor`. -/
@[reassoc (attr := simp)]
lemma leftDerivedTensorFlipIso_inv_app_app_comp_derivedTensorLeftUnitor
    (X : DerivedCategory C) :
    ((leftDerivedTensorFlipIso (derivedTensor C) (derivedTensorCounit C)).inv.app X).app
        ((DerivedCategory.singleFunctor C 0).obj (𝟙_ C)) ≫
      (derivedTensorLeftUnitor C).hom.app X =
      (derivedTensorRightUnitor C).hom.app X :=
  NatTrans.congr_app flip_leftDerivedTensorFlipIso_inv_app_comp_derivedTensorLeftUnitor X

omit LF α [LF.IsLeftDerivedFunctor₂ α (quasiIso C (.up ℤ)) (quasiIso C (.up ℤ))] in
/-- The inverse `derivedTensorRightUnitor` followed by the Koszul flip at `(𝟙_ C[0], -)` equals
the inverse `derivedTensorLeftUnitor` as a natural transformation. -/
@[reassoc (attr := simp)]
lemma derivedTensorRightUnitor_inv_comp_leftDerivedTensorFlipIso_hom_app :
    (derivedTensorRightUnitor C).inv ≫
        (leftDerivedTensorFlipIso (derivedTensor C) (derivedTensorCounit C)).hom.app
          ((DerivedCategory.singleFunctor C 0).obj (𝟙_ C)) =
      (derivedTensorLeftUnitor C).inv :=
  leftDerivedTensorRightUnitor_inv_comp_leftDerivedTensorFlipIso_hom_app
    (derivedTensor C) (derivedTensorCounit C)

omit LF α [LF.IsLeftDerivedFunctor₂ α (quasiIso C (.up ℤ)) (quasiIso C (.up ℤ))] in
/-- The inverse `derivedTensorRightUnitor` followed by the Koszul flip at `(𝟙_ C[0], X)` equals
the inverse `derivedTensorLeftUnitor`. -/
@[reassoc (attr := simp)]
lemma derivedTensorRightUnitor_inv_app_comp_leftDerivedTensorFlipIso_hom_app_app
    (X : DerivedCategory C) :
    (derivedTensorRightUnitor C).inv.app X ≫
        ((leftDerivedTensorFlipIso (derivedTensor C) (derivedTensorCounit C)).hom.app
          ((DerivedCategory.singleFunctor C 0).obj (𝟙_ C))).app X =
      (derivedTensorLeftUnitor C).inv.app X :=
  NatTrans.congr_app derivedTensorRightUnitor_inv_comp_leftDerivedTensorFlipIso_hom_app X

omit LF α [LF.IsLeftDerivedFunctor₂ α (quasiIso C (.up ℤ)) (quasiIso C (.up ℤ))] in
/-- The inverse `derivedTensorLeftUnitor` followed by the flipped Koszul flip at `𝟙_ C[0]` equals
the inverse `derivedTensorRightUnitor` as a natural transformation. -/
@[reassoc (attr := simp)]
lemma derivedTensorLeftUnitor_inv_comp_flip_leftDerivedTensorFlipIso_hom_app :
    (derivedTensorLeftUnitor C).inv ≫
        ((flipFunctor _ _ _).map
          (leftDerivedTensorFlipIso (derivedTensor C) (derivedTensorCounit C)).hom).app
          ((DerivedCategory.singleFunctor C 0).obj (𝟙_ C)) =
      (derivedTensorRightUnitor C).inv :=
  leftDerivedTensorLeftUnitor_inv_comp_flip_leftDerivedTensorFlipIso_hom_app
    (derivedTensor C) (derivedTensorCounit C)

omit LF α [LF.IsLeftDerivedFunctor₂ α (quasiIso C (.up ℤ)) (quasiIso C (.up ℤ))] in
/-- The inverse `derivedTensorLeftUnitor` followed by the Koszul flip at `(X, 𝟙_ C[0])` equals
the inverse `derivedTensorRightUnitor`. -/
@[reassoc (attr := simp)]
lemma derivedTensorLeftUnitor_inv_app_comp_leftDerivedTensorFlipIso_hom_app_app
    (X : DerivedCategory C) :
    (derivedTensorLeftUnitor C).inv.app X ≫
        ((leftDerivedTensorFlipIso (derivedTensor C) (derivedTensorCounit C)).hom.app X).app
          ((DerivedCategory.singleFunctor C 0).obj (𝟙_ C)) =
      (derivedTensorRightUnitor C).inv.app X :=
  NatTrans.congr_app derivedTensorLeftUnitor_inv_comp_flip_leftDerivedTensorFlipIso_hom_app X

omit LF α [LF.IsLeftDerivedFunctor₂ α (quasiIso C (.up ℤ)) (quasiIso C (.up ℤ))] in
/-- The inverse `derivedTensorLeftUnitor` followed by the inverse Koszul flip at `(𝟙_ C[0], -)`
equals the inverse `derivedTensorRightUnitor` as a natural transformation. -/
@[reassoc (attr := simp)]
lemma derivedTensorLeftUnitor_inv_comp_leftDerivedTensorFlipIso_inv_app :
    (derivedTensorLeftUnitor C).inv ≫
        (leftDerivedTensorFlipIso (derivedTensor C) (derivedTensorCounit C)).inv.app
          ((DerivedCategory.singleFunctor C 0).obj (𝟙_ C)) =
      (derivedTensorRightUnitor C).inv :=
  leftDerivedTensorLeftUnitor_inv_comp_leftDerivedTensorFlipIso_inv_app
    (derivedTensor C) (derivedTensorCounit C)

omit LF α [LF.IsLeftDerivedFunctor₂ α (quasiIso C (.up ℤ)) (quasiIso C (.up ℤ))] in
/-- The inverse `derivedTensorLeftUnitor` followed by the inverse Koszul flip at `(𝟙_ C[0], X)`
equals the inverse `derivedTensorRightUnitor`. -/
@[reassoc (attr := simp)]
lemma derivedTensorLeftUnitor_inv_app_comp_leftDerivedTensorFlipIso_inv_app_app
    (X : DerivedCategory C) :
    (derivedTensorLeftUnitor C).inv.app X ≫
        ((leftDerivedTensorFlipIso (derivedTensor C) (derivedTensorCounit C)).inv.app
          ((DerivedCategory.singleFunctor C 0).obj (𝟙_ C))).app X =
      (derivedTensorRightUnitor C).inv.app X :=
  NatTrans.congr_app derivedTensorLeftUnitor_inv_comp_leftDerivedTensorFlipIso_inv_app X

omit LF α [LF.IsLeftDerivedFunctor₂ α (quasiIso C (.up ℤ)) (quasiIso C (.up ℤ))] in
/-- The inverse `derivedTensorRightUnitor` followed by the flipped inverse Koszul flip at
`𝟙_ C[0]` equals the inverse `derivedTensorLeftUnitor` as a natural transformation. -/
@[reassoc (attr := simp)]
lemma derivedTensorRightUnitor_inv_comp_flip_leftDerivedTensorFlipIso_inv_app :
    (derivedTensorRightUnitor C).inv ≫
        ((flipFunctor _ _ _).map
          (leftDerivedTensorFlipIso (derivedTensor C) (derivedTensorCounit C)).inv).app
          ((DerivedCategory.singleFunctor C 0).obj (𝟙_ C)) =
      (derivedTensorLeftUnitor C).inv :=
  leftDerivedTensorRightUnitor_inv_comp_flip_leftDerivedTensorFlipIso_inv_app
    (derivedTensor C) (derivedTensorCounit C)

omit LF α [LF.IsLeftDerivedFunctor₂ α (quasiIso C (.up ℤ)) (quasiIso C (.up ℤ))] in
/-- The inverse `derivedTensorRightUnitor` followed by the inverse Koszul flip at `(X, 𝟙_ C[0])`
equals the inverse `derivedTensorLeftUnitor`. -/
@[reassoc (attr := simp)]
lemma derivedTensorRightUnitor_inv_app_comp_leftDerivedTensorFlipIso_inv_app_app
    (X : DerivedCategory C) :
    (derivedTensorRightUnitor C).inv.app X ≫
        ((leftDerivedTensorFlipIso (derivedTensor C) (derivedTensorCounit C)).inv.app X).app
          ((DerivedCategory.singleFunctor C 0).obj (𝟙_ C)) =
      (derivedTensorLeftUnitor C).inv.app X :=
  NatTrans.congr_app derivedTensorRightUnitor_inv_comp_flip_leftDerivedTensorFlipIso_inv_app X

end Unitor

end Braided

section Symmetric

variable [SymmetricCategory C]

/-- Over symmetric coefficients, the inverse Koszul braiding mapped to `DerivedCategory C`
equals the swapped forward Koszul braiding. -/
@[simp]
lemma Q_map_braiding_inv (K L : CochainComplex C ℤ) :
    DerivedCategory.Q.map (β_ K L).inv = DerivedCategory.Q.map (β_ L K).hom := by
  rw [SymmetricCategory.braiding_swap_eq_inv_braiding]

/-- Over symmetric coefficients, the Koszul braiding mapped to `DerivedCategory C` is
involutive. -/
@[reassoc (attr := simp)]
lemma Q_map_braiding_comp (K L : CochainComplex C ℤ) :
    DerivedCategory.Q.map (β_ K L).hom ≫ DerivedCategory.Q.map (β_ L K).hom =
      𝟙 (DerivedCategory.Q.obj (K ⊗ L)) := by
  rw [← DerivedCategory.Q.map_comp, SymmetricCategory.symmetry, DerivedCategory.Q.map_id]

/-- Over symmetric coefficients, `koszulDerivedFlipIso` is involutive. -/
@[reassoc (attr := simp)]
lemma koszulDerivedFlipIso_involutive :
    (flipFunctor _ _ _).map (koszulDerivedFlipIso (C := C)).hom ≫
        (koszulDerivedFlipIso (C := C)).hom =
      (flipping (C := CochainComplex C ℤ) (D := CochainComplex C ℤ)
        (E := DerivedCategory C)).counitIso.hom.app
          (MonoidalCategory.curriedTensor (CochainComplex C ℤ) ⋙
            (whiskeringRight _ _ _).obj (DerivedCategory.Q (C := C))) := by
  ext K L
  simp

/-- Over symmetric coefficients, `leftDerivedTensorFlipIso` is involutive as a natural
transformation. -/
@[reassoc (attr := simp)]
lemma flip_leftDerivedTensorFlipIso_hom_comp :
    (flipFunctor _ _ _).map (leftDerivedTensorFlipIso LF α).hom ≫
        (leftDerivedTensorFlipIso LF α).hom =
      (flipping (C := DerivedCategory C) (D := DerivedCategory C)
        (E := DerivedCategory C)).counitIso.hom.app LF :=
  flip_leftDerived₂FlipIso_hom_comp LF α (quasiIso C (.up ℤ))
    (koszulDerivedFlipIso (C := C)) (koszulDerivedFlipIso_involutive (C := C))

/-- Over symmetric coefficients, the inverse of `leftDerivedTensorFlipIso` at `(X, Y)` equals its
forward map at `(Y, X)`. -/
@[simp]
lemma leftDerivedTensorFlipIso_inv_app_app (X Y : DerivedCategory C) :
    ((leftDerivedTensorFlipIso LF α).inv.app X).app Y =
      ((leftDerivedTensorFlipIso LF α).hom.app Y).app X :=
  leftDerived₂FlipIso_inv_app_app LF α (quasiIso C (.up ℤ))
    (koszulDerivedFlipIso (C := C)) (koszulDerivedFlipIso_involutive (C := C)) X Y

/-- Over symmetric coefficients, `leftDerivedTensorFlipIso` is involutive. -/
@[reassoc (attr := simp)]
lemma leftDerivedTensorFlipIso_hom_app_app_comp (X Y : DerivedCategory C) :
    ((leftDerivedTensorFlipIso LF α).hom.app X).app Y ≫
      ((leftDerivedTensorFlipIso LF α).hom.app Y).app X = 𝟙 ((LF.obj Y).obj X) :=
  leftDerived₂FlipIso_hom_app_app_comp LF α (quasiIso C (.up ℤ))
    (koszulDerivedFlipIso (C := C)) (koszulDerivedFlipIso_involutive (C := C)) X Y

end Symmetric

end TauCeti

end Symmetry
