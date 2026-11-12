/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.KFlat.DerivabilityStructure
public import TauCeti.Algebra.Homology.ModuleCat.KFlat.Tensor
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerivedTwo
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Product
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.LeftResolution
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.RingTheory.Flat.CategoryTheory

/-!
# The derived tensor product on unbounded module derived categories

Let `R` be a commutative ring. Applying the functorial K-flat resolution of
`TauCeti.Algebra.Homology.Monoidal.KFlat.DerivabilityStructure` to the free-forgetful counit
`forget (ModuleCat R) ⋙ ModuleCat.free R ⟶ 𝟭 (ModuleCat R)` shows that the inclusion
`CochainComplex.kFlatLocalizerMorphism (ModuleCat R)` of K-flat complexes into
`CochainComplex (ModuleCat R) ℤ` is a left derivability structure with respect to
quasi-isomorphisms.

Combining this derivability structure with the product derivability structure on
`CochainComplex (ModuleCat R) ℤ × CochainComplex (ModuleCat R) ℤ`, we prove that the total tensor
product of cochain complexes of `R`-modules admits a left derived bifunctor `⊗^L` with respect to
quasi-isomorphisms in both variables (`TauCeti.hasLeftDerivedFunctor₂_tensor`). Moreover:
* any left derived bifunctor of tensoring is computed on the nose whenever either factor is K-flat
  (`TauCeti.isIso_app_of_isLeftDerivedFunctor₂_tensor_of_isKFlat_left` and
  `TauCeti.isIso_app_of_isLeftDerivedFunctor₂_tensor_of_isKFlat_right`), and in particular
  whenever either factor is a bounded-above complex of flat modules or a flat module in a single
  degree;
* the left derived tensor bifunctor is absolute, remaining left derived after postcomposition with
  any functor (`TauCeti.isLeftDerivedFunctor₂_comp_of_isLeftDerivedFunctor₂_tensor`);
* `TauCeti.derivedTensor R` provides a canonical choice of `⊗^L` on `DerivedCategory (ModuleCat R)`
  with model isomorphisms `TauCeti.derivedTensorKFlatLeftIso` and
  `TauCeti.derivedTensorKFlatRightIso`.

## References

* N. Spaltenstein, *Resolutions of unbounded complexes*, Compositio Math. 65 (1988), 121–154.
* B. Kahn and G. Maltsiniotis, *Structures de dérivabilité*, Adv. Math. 218 (2008), 1286–1318.
* [Stacks Project, Tag 06Y4](https://stacks.math.columbia.edu/tag/06Y4),
  [Stacks Project, Tag 064L](https://stacks.math.columbia.edu/tag/064L), and
  [Stacks Project, Tag 064M](https://stacks.math.columbia.edu/tag/064M).
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Functor Limits HomologicalComplex
open scoped MonoidalCategory

universe u w

namespace CochainComplex

section ModuleCat

variable {R : Type u} [CommRing R]

private lemma preservesFiniteLimits_tensorLeft_free_obj (X : Type u) :
    PreservesFiniteLimits (MonoidalCategory.tensorLeft ((ModuleCat.free R).obj X)) :=
  (Module.Flat.iff_preservesFiniteLimits_tensorLeft ((ModuleCat.free R).obj X)).1 inferInstance

instance : (kFlatLocalizerMorphism (ModuleCat.{u} R)).IsLocalizedEquivalence := by
  have : AB5OfSize.{0, 0} (ModuleCat.{u} R) := AB5OfSize_of_univLE.{0, 0, u, u} _
  have (X : ModuleCat.{u} R) : PreservesFiniteLimits
      (MonoidalCategory.tensorLeft ((forget (ModuleCat.{u} R) ⋙ ModuleCat.free R).obj X)) :=
    preservesFiniteLimits_tensorLeft_free_obj X
  exact isLocalizedEquivalence_kFlatLocalizerMorphism
    (forget (ModuleCat.{u} R) ⋙ ModuleCat.free R) (ModuleCat.adj R).counit

instance : (kFlatLocalizerMorphism (ModuleCat.{u} R)).arrow.HasLeftResolutions := by
  have : AB5OfSize.{0, 0} (ModuleCat.{u} R) := AB5OfSize_of_univLE.{0, 0, u, u} _
  have (X : ModuleCat.{u} R) : PreservesFiniteLimits
      (MonoidalCategory.tensorLeft ((forget (ModuleCat.{u} R) ⋙ ModuleCat.free R).obj X)) :=
    preservesFiniteLimits_tensorLeft_free_obj X
  exact hasLeftResolutions_arrow_kFlatLocalizerMorphism
    (forget (ModuleCat.{u} R) ⋙ ModuleCat.free R) (ModuleCat.adj R).counit

instance (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    IsConnected ((kFlatLocalizerMorphism (ModuleCat.{u} R)).LeftResolution K) := by
  have : AB5OfSize.{0, 0} (ModuleCat.{u} R) := AB5OfSize_of_univLE.{0, 0, u, u} _
  have (X : ModuleCat.{u} R) : PreservesFiniteLimits
      (MonoidalCategory.tensorLeft ((forget (ModuleCat.{u} R) ⋙ ModuleCat.free R).obj X)) :=
    preservesFiniteLimits_tensorLeft_free_obj X
  exact isConnected_leftResolution_kFlatLocalizerMorphism
    (forget (ModuleCat.{u} R) ⋙ ModuleCat.free R) (ModuleCat.adj R).counit K

/-- The inclusion of K-flat complexes of `R`-modules into `CochainComplex (ModuleCat.{u} R) ℤ` is a
left derivability structure with respect to quasi-isomorphisms. -/
instance : (kFlatLocalizerMorphism (ModuleCat.{u} R)).IsLeftDerivabilityStructure := by
  have : AB5OfSize.{0, 0} (ModuleCat.{u} R) := AB5OfSize_of_univLE.{0, 0, u, u} _
  have (X : ModuleCat.{u} R) : PreservesFiniteLimits
      (MonoidalCategory.tensorLeft ((forget (ModuleCat.{u} R) ⋙ ModuleCat.free R).obj X)) :=
    preservesFiniteLimits_tensorLeft_free_obj X
  exact isLeftDerivabilityStructure_kFlatLocalizerMorphism
    (forget (ModuleCat.{u} R) ⋙ ModuleCat.free R) (ModuleCat.adj R).counit

end ModuleCat

end CochainComplex

namespace TauCeti

section GeneralTarget

variable {R : Type u} [CommRing R]
  {H : Type*} [Category* H]
  (F : CochainComplex (ModuleCat.{u} R) ℤ ⥤ H)
  (hF : (quasiIso (ModuleCat.{u} R) (.up ℤ)).IsInvertedBy F)

include hF in
/-- Resolving the first factor by K-flat complexes derives the postcomposition of the total tensor
product of `R`-module complexes with any functor `F` that inverts quasi-isomorphisms. -/
theorem derives_tensor_left_of_inverts :
    ((CochainComplex.kFlatLocalizerMorphism (ModuleCat.{u} R)).prod
      (LocalizerMorphism.id (quasiIso (ModuleCat.{u} R) (.up ℤ)))).Derives
      (uncurry.obj (MonoidalCategory.curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙
        (whiskeringRight _ _ _).obj F)) := by
  rintro ⟨P₁, L₁⟩ ⟨P₂, L₂⟩ ⟨f₁, f₂⟩ ⟨hf₁, hf₂⟩
  have : QuasiIso f₁.hom := (mem_quasiIso_iff _).1 hf₁
  have : QuasiIso f₂ := (mem_quasiIso_iff _).1 hf₂
  have : IsIso (F.map (f₁.hom ▷ L₁)) := hF _ ((mem_quasiIso_iff _).2 inferInstance)
  have : IsIso (F.map (P₂.obj ◁ f₂)) := hF _ ((mem_quasiIso_iff _).2 inferInstance)
  dsimp [uncurry, LocalizerMorphism.prod, LocalizerMorphism.id,
    CochainComplex.kFlatLocalizerMorphism]
  infer_instance

include hF in
/-- Resolving the second factor by K-flat complexes derives the postcomposition of the total tensor
product of `R`-module complexes with any functor `F` that inverts quasi-isomorphisms. -/
theorem derives_tensor_right_of_inverts :
    ((LocalizerMorphism.id (quasiIso (ModuleCat.{u} R) (.up ℤ))).prod
      (CochainComplex.kFlatLocalizerMorphism (ModuleCat.{u} R))).Derives
      (uncurry.obj (MonoidalCategory.curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙
        (whiskeringRight _ _ _).obj F)) := by
  rintro ⟨K₁, Q₁⟩ ⟨K₂, Q₂⟩ ⟨f₁, f₂⟩ ⟨hf₁, hf₂⟩
  have : QuasiIso f₁ := (mem_quasiIso_iff _).1 hf₁
  have : QuasiIso f₂.hom := (mem_quasiIso_iff _).1 hf₂
  have : IsIso (F.map (f₁ ▷ Q₁.obj)) := hF _ ((mem_quasiIso_iff _).2 inferInstance)
  have : IsIso (F.map (K₂ ◁ f₂.hom)) := hF _ ((mem_quasiIso_iff _).2 inferInstance)
  dsimp [uncurry, LocalizerMorphism.prod, LocalizerMorphism.id,
    CochainComplex.kFlatLocalizerMorphism]
  infer_instance

include hF in
/-- Postcomposing the total tensor product of `R`-module complexes with any functor `F` that
inverts quasi-isomorphisms yields a bifunctor admitting a left derived bifunctor with respect to
quasi-isomorphisms in both variables. -/
theorem hasLeftDerivedFunctor₂_tensor_of_inverts :
    (MonoidalCategory.curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙
      (whiskeringRight _ _ _).obj F).HasLeftDerivedFunctor₂
      (quasiIso (ModuleCat.{u} R) (.up ℤ)) (quasiIso (ModuleCat.{u} R) (.up ℤ)) := by
  have := (derives_tensor_left_of_inverts F hF).hasPointwiseLeftDerivedFunctor
  infer_instance

section Characterization

variable {D₁ D₂ : Type*} [Category* D₁] [Category* D₂]
  {L₁ : CochainComplex (ModuleCat.{u} R) ℤ ⥤ D₁}
  {L₂ : CochainComplex (ModuleCat.{u} R) ℤ ⥤ D₂}
  [L₁.IsLocalization (quasiIso (ModuleCat.{u} R) (.up ℤ))]
  [L₂.IsLocalization (quasiIso (ModuleCat.{u} R) (.up ℤ))]
  {LF : D₁ ⥤ D₂ ⥤ H}
  (α : (((whiskeringLeft₂ H).obj L₁).obj L₂).obj LF ⟶
    MonoidalCategory.curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙
      (whiskeringRight _ _ _).obj F)

include hF in
/-- A bifunctor `(LF, α)` is a left derived bifunctor of `curriedTensor ⋙ whiskeringRight F` if
and only if `(α.app P).app L` is an isomorphism whenever `P` is K-flat. -/
theorem isLeftDerivedFunctor₂_tensor_iff_isIso_left :
    LF.IsLeftDerivedFunctor₂ α
      (quasiIso (ModuleCat.{u} R) (.up ℤ)) (quasiIso (ModuleCat.{u} R) (.up ℤ)) ↔
      ∀ (P : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKFlat]
        (L : CochainComplex (ModuleCat.{u} R) ℤ), IsIso ((α.app P).app L) := by
  rw [Functor.IsLeftDerivedFunctor₂,
    (derives_tensor_left_of_inverts F hF).isLeftDerivedFunctor_iff_isIso]
  constructor
  · intro h P hP L
    exact h (⟨P, hP⟩, L)
  · rintro h ⟨⟨P, hP⟩, L⟩
    exact @h P hP L

include hF in
/-- A bifunctor `(LF, α)` is a left derived bifunctor of `curriedTensor ⋙ whiskeringRight F` if
and only if `(α.app K).app Q` is an isomorphism whenever `Q` is K-flat. -/
theorem isLeftDerivedFunctor₂_tensor_iff_isIso_right :
    LF.IsLeftDerivedFunctor₂ α
      (quasiIso (ModuleCat.{u} R) (.up ℤ)) (quasiIso (ModuleCat.{u} R) (.up ℤ)) ↔
      ∀ (K : CochainComplex (ModuleCat.{u} R) ℤ)
        (Q : CochainComplex (ModuleCat.{u} R) ℤ) [Q.IsKFlat], IsIso ((α.app K).app Q) := by
  rw [Functor.IsLeftDerivedFunctor₂,
    (derives_tensor_right_of_inverts F hF).isLeftDerivedFunctor_iff_isIso]
  constructor
  · intro h K Q hQ
    exact h (K, ⟨Q, hQ⟩)
  · rintro h ⟨K, ⟨Q, hQ⟩⟩
    exact @h K Q hQ

include hF in
/-- Any left derived bifunctor of tensoring is computed by the ordinary tensor product whenever the
left factor is K-flat. -/
theorem isIso_app_of_isLeftDerivedFunctor₂_tensor_of_isKFlat_left
    [LF.IsLeftDerivedFunctor₂ α
      (quasiIso (ModuleCat.{u} R) (.up ℤ)) (quasiIso (ModuleCat.{u} R) (.up ℤ))]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKFlat]
    (L : CochainComplex (ModuleCat.{u} R) ℤ) :
    IsIso ((α.app P).app L) :=
  (isLeftDerivedFunctor₂_tensor_iff_isIso_left F hF α).1 inferInstance P L

include hF in
/-- Any left derived bifunctor of tensoring is computed by the ordinary tensor product whenever the
right factor is K-flat. -/
theorem isIso_app_of_isLeftDerivedFunctor₂_tensor_of_isKFlat_right
    [LF.IsLeftDerivedFunctor₂ α
      (quasiIso (ModuleCat.{u} R) (.up ℤ)) (quasiIso (ModuleCat.{u} R) (.up ℤ))]
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (Q : CochainComplex (ModuleCat.{u} R) ℤ) [Q.IsKFlat] :
    IsIso ((α.app K).app Q) :=
  (isLeftDerivedFunctor₂_tensor_iff_isIso_right F hF α).1 inferInstance K Q

include hF in
/-- **Flat-model comparison on the left.** Any left derived bifunctor of tensoring is computed by
the ordinary tensor product whenever the left factor is a bounded-above complex of flat
`R`-modules. -/
theorem isIso_app_of_isLeftDerivedFunctor₂_tensor_of_boundedAbove_flat_left
    [LF.IsLeftDerivedFunctor₂ α
      (quasiIso (ModuleCat.{u} R) (.up ℤ)) (quasiIso (ModuleCat.{u} R) (.up ℤ))]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ) [P.IsStrictlyLE b]
    (hP : ∀ n, Module.Flat R (P.X n)) (L : CochainComplex (ModuleCat.{u} R) ℤ) :
    IsIso ((α.app P).app L) := by
  have : AB5OfSize.{0, 0} (ModuleCat.{u} R) := AB5OfSize_of_univLE.{0, 0, u, u} _
  have (n : ℤ) : PreservesFiniteLimits (MonoidalCategory.tensorLeft (P.X n)) :=
    (Module.Flat.iff_preservesFiniteLimits_tensorLeft (P.X n)).1 (hP n)
  have : P.IsKFlat := CochainComplex.isKFlat_of_boundedAbove_flat P b
  exact isIso_app_of_isLeftDerivedFunctor₂_tensor_of_isKFlat_left F hF α P L

include hF in
/-- **Flat-model comparison on the right.** Any left derived bifunctor of tensoring is computed by
the ordinary tensor product whenever the right factor is a bounded-above complex of flat
`R`-modules. -/
theorem isIso_app_of_isLeftDerivedFunctor₂_tensor_of_boundedAbove_flat_right
    [LF.IsLeftDerivedFunctor₂ α
      (quasiIso (ModuleCat.{u} R) (.up ℤ)) (quasiIso (ModuleCat.{u} R) (.up ℤ))]
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (Q : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ) [Q.IsStrictlyLE b]
    (hQ : ∀ n, Module.Flat R (Q.X n)) :
    IsIso ((α.app K).app Q) := by
  have : AB5OfSize.{0, 0} (ModuleCat.{u} R) := AB5OfSize_of_univLE.{0, 0, u, u} _
  have (n : ℤ) : PreservesFiniteLimits (MonoidalCategory.tensorLeft (Q.X n)) :=
    (Module.Flat.iff_preservesFiniteLimits_tensorLeft (Q.X n)).1 (hQ n)
  have : Q.IsKFlat := CochainComplex.isKFlat_of_boundedAbove_flat Q b
  exact isIso_app_of_isLeftDerivedFunctor₂_tensor_of_isKFlat_right F hF α K Q

include hF in
/-- Any left derived bifunctor of tensoring is computed by the ordinary tensor product when the
left factor is a flat `R`-module placed in a single cohomological degree `n`. -/
theorem isIso_app_of_isLeftDerivedFunctor₂_tensor_single_of_flat_left
    [LF.IsLeftDerivedFunctor₂ α
      (quasiIso (ModuleCat.{u} R) (.up ℤ)) (quasiIso (ModuleCat.{u} R) (.up ℤ))]
    (M : ModuleCat.{u} R) [Module.Flat R M] (n : ℤ)
    (L : CochainComplex (ModuleCat.{u} R) ℤ) :
    IsIso ((α.app ((HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) n).obj M)).app L) := by
  have : PreservesFiniteLimits (MonoidalCategory.tensorLeft M) :=
    (Module.Flat.iff_preservesFiniteLimits_tensorLeft M).1 inferInstance
  have : CochainComplex.IsKFlat ((HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) n).obj M) :=
    CochainComplex.isKFlat_single_of_flat M n
  exact isIso_app_of_isLeftDerivedFunctor₂_tensor_of_isKFlat_left F hF α _ L

include hF in
/-- Any left derived bifunctor of tensoring is computed by the ordinary tensor product when the
right factor is a flat `R`-module placed in a single cohomological degree `n`. -/
theorem isIso_app_of_isLeftDerivedFunctor₂_tensor_single_of_flat_right
    [LF.IsLeftDerivedFunctor₂ α
      (quasiIso (ModuleCat.{u} R) (.up ℤ)) (quasiIso (ModuleCat.{u} R) (.up ℤ))]
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (M : ModuleCat.{u} R) [Module.Flat R M] (n : ℤ) :
    IsIso ((α.app K).app ((HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) n).obj M)) := by
  have : PreservesFiniteLimits (MonoidalCategory.tensorLeft M) :=
    (Module.Flat.iff_preservesFiniteLimits_tensorLeft M).1 inferInstance
  have : CochainComplex.IsKFlat ((HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) n).obj M) :=
    CochainComplex.isKFlat_single_of_flat M n
  exact isIso_app_of_isLeftDerivedFunctor₂_tensor_of_isKFlat_right F hF α K _

omit [L₁.IsLocalization (quasiIso (ModuleCat.{u} R) (.up ℤ))]
  [L₂.IsLocalization (quasiIso (ModuleCat.{u} R) (.up ℤ))] in
/-- The counit transformation obtained by postcomposing a comparison `α` of a left derived tensor
bifunctor with a functor `G : H ⥤ E`. -/
def postcompDerivedTensorCounit {E : Type*} [Category* E] (G : H ⥤ E) :
    (((whiskeringLeft₂ E).obj L₁).obj L₂).obj (LF ⋙ (whiskeringRight D₂ H E).obj G) ⟶
      MonoidalCategory.curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙
        (whiskeringRight _ _ _).obj (F ⋙ G) where
  app X₁ :=
    { app X₂ := G.map ((α.app X₁).app X₂)
      naturality {_ _} g := by
        dsimp
        rw [← G.map_comp, ← G.map_comp]
        exact G.congr_map ((α.app X₁).naturality g) }
  naturality {_ _} f := by
    ext Y
    dsimp
    rw [← G.map_comp, ← G.map_comp]
    exact G.congr_map (congr_app (α.naturality f) Y)

omit [L₁.IsLocalization (quasiIso (ModuleCat.{u} R) (.up ℤ))]
  [L₂.IsLocalization (quasiIso (ModuleCat.{u} R) (.up ℤ))] in
/-- Evaluating `postcompDerivedTensorCounit` applies `G` to the component of `α`. -/
@[simp]
lemma postcompDerivedTensorCounit_app_app {E : Type*} [Category* E] (G : H ⥤ E)
    (X₁ X₂ : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((postcompDerivedTensorCounit F α G).app X₁).app X₂ = G.map ((α.app X₁).app X₂) :=
  (rfl)

include hF in
/-- **The left derived tensor bifunctor is absolute.** Postcomposing any left derived bifunctor
`(LF, α)` of `curriedTensor ⋙ whiskeringRight F` with an arbitrary functor `G : H ⥤ E` yields a
left derived bifunctor of `curriedTensor ⋙ whiskeringRight (F ⋙ G)`. -/
theorem isLeftDerivedFunctor₂_comp_of_isLeftDerivedFunctor₂_tensor
    {E : Type*} [Category* E] (G : H ⥤ E)
    [LF.IsLeftDerivedFunctor₂ α
      (quasiIso (ModuleCat.{u} R) (.up ℤ)) (quasiIso (ModuleCat.{u} R) (.up ℤ))] :
    (LF ⋙ (whiskeringRight D₂ H E).obj G).IsLeftDerivedFunctor₂
      (postcompDerivedTensorCounit F α G)
      (quasiIso (ModuleCat.{u} R) (.up ℤ)) (quasiIso (ModuleCat.{u} R) (.up ℤ)) := by
  have hFG : (quasiIso (ModuleCat.{u} R) (.up ℤ)).IsInvertedBy (F ⋙ G) := fun _ _ _ hf ↦ by
    dsimp
    have := hF _ hf
    infer_instance
  rw [isLeftDerivedFunctor₂_tensor_iff_isIso_left (F ⋙ G) hFG]
  intro P _ L
  have := isIso_app_of_isLeftDerivedFunctor₂_tensor_of_isKFlat_left F hF α P L
  rw [postcompDerivedTensorCounit_app_app]
  infer_instance

end Characterization

end GeneralTarget

section DerivedCategory

/-- **Existence of the derived tensor product.** For a commutative ring `R`, the total tensor
product of cochain complexes of `R`-modules followed by localization to
`DerivedCategory (ModuleCat R)` admits a left derived bifunctor `⊗^L` with respect to
quasi-isomorphisms in both variables. -/
theorem hasLeftDerivedFunctor₂_tensor (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    (MonoidalCategory.curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙
      (Functor.whiskeringRight _ _ _).obj
        (DerivedCategory.Q (C := ModuleCat.{u} R))).HasLeftDerivedFunctor₂
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) :=
  hasLeftDerivedFunctor₂_tensor_of_inverts
    (DerivedCategory.Q (C := ModuleCat.{u} R))
    (Localization.inverts DerivedCategory.Q (quasiIso (ModuleCat.{u} R) (.up ℤ)))

attribute [instance] hasLeftDerivedFunctor₂_tensor

variable (R : Type u) [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- The canonical left derived tensor bifunctor `⊗^L` on the unbounded derived category of
`R`-modules. -/
def derivedTensor :
    DerivedCategory (ModuleCat.{u} R) ⥤
      DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R) :=
  Functor.leftDerived₂
    (MonoidalCategory.curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙
      (whiskeringRight _ _ _).obj (DerivedCategory.Q (C := ModuleCat.{u} R)))
    DerivedCategory.Q DerivedCategory.Q
    (quasiIso (ModuleCat.{u} R) (.up ℤ)) (quasiIso (ModuleCat.{u} R) (.up ℤ))

/-- The universal counit comparing `derivedTensor R` on localized complexes with the ordinary
total tensor product of cochain complexes. -/
def derivedTensorCounit :
    (((whiskeringLeft₂ (DerivedCategory (ModuleCat.{u} R))).obj DerivedCategory.Q).obj
      DerivedCategory.Q).obj (derivedTensor R) ⟶
      MonoidalCategory.curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙
        (whiskeringRight _ _ _).obj (DerivedCategory.Q (C := ModuleCat.{u} R)) :=
  Functor.leftDerivedCounit₂
    (MonoidalCategory.curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙
      (whiskeringRight _ _ _).obj (DerivedCategory.Q (C := ModuleCat.{u} R)))
    DerivedCategory.Q DerivedCategory.Q
    (quasiIso (ModuleCat.{u} R) (.up ℤ)) (quasiIso (ModuleCat.{u} R) (.up ℤ))

instance : (derivedTensor R).IsLeftDerivedFunctor₂ (derivedTensorCounit R)
    (quasiIso (ModuleCat.{u} R) (.up ℤ)) (quasiIso (ModuleCat.{u} R) (.up ℤ)) := by
  dsimp [derivedTensor, derivedTensorCounit]
  infer_instance

variable {R}

instance (P L : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKFlat] :
    IsIso (((derivedTensorCounit R).app P).app L) :=
  isIso_app_of_isLeftDerivedFunctor₂_tensor_of_isKFlat_left
    DerivedCategory.Q
    (Localization.inverts DerivedCategory.Q (quasiIso (ModuleCat.{u} R) (.up ℤ)))
    (derivedTensorCounit R) P L

instance (K Q : CochainComplex (ModuleCat.{u} R) ℤ) [Q.IsKFlat] :
    IsIso (((derivedTensorCounit R).app K).app Q) :=
  isIso_app_of_isLeftDerivedFunctor₂_tensor_of_isKFlat_right
    DerivedCategory.Q
    (Localization.inverts DerivedCategory.Q (quasiIso (ModuleCat.{u} R) (.up ℤ)))
    (derivedTensorCounit R) K Q

/-- When `P` is K-flat, `(derivedTensor R).obj (Q.obj P)` is naturally isomorphic on `Q.obj L` to
the ordinary tensor product `Q.obj (P ⊗ L)`. -/
def derivedTensorKFlatLeftIso (P L : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKFlat] :
    ((derivedTensor R).obj (DerivedCategory.Q.obj P)).obj (DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj (P ⊗ L) :=
  asIso (((derivedTensorCounit R).app P).app L)

/-- The forward morphism of `derivedTensorKFlatLeftIso` is the counit component. -/
@[simp]
lemma derivedTensorKFlatLeftIso_hom (P L : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKFlat] :
    (derivedTensorKFlatLeftIso P L).hom = ((derivedTensorCounit R).app P).app L :=
  (rfl)

/-- When `Q` is K-flat, `(derivedTensor R).obj (Q.obj K)` on `Q.obj Q` is naturally isomorphic to
the ordinary tensor product `Q.obj (K ⊗ Q)`. -/
def derivedTensorKFlatRightIso (K Q : CochainComplex (ModuleCat.{u} R) ℤ) [Q.IsKFlat] :
    ((derivedTensor R).obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj Q) ≅
      DerivedCategory.Q.obj (K ⊗ Q) :=
  asIso (((derivedTensorCounit R).app K).app Q)

/-- The forward morphism of `derivedTensorKFlatRightIso` is the counit component. -/
@[simp]
lemma derivedTensorKFlatRightIso_hom (K Q : CochainComplex (ModuleCat.{u} R) ℤ) [Q.IsKFlat] :
    (derivedTensorKFlatRightIso K Q).hom = ((derivedTensorCounit R).app K).app Q :=
  (rfl)

end DerivedCategory

end TauCeti
