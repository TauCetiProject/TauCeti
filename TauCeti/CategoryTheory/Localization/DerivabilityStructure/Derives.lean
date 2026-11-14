/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerivedTwo

/-!
# Postcomposition absoluteness for functors derived via derivability structures

When a localizer morphism `Φ : LocalizerMorphism W₁ W₂` is a left derivability structure and
`h : Φ.Derives F` holds (meaning `Φ.functor ⋙ F` inverts `W₁`), any left derived functor `(LF, α)`
of `F` is computed pointwise on `Φ.functor.obj X₁`, so it remains a left derived functor of
`F ⋙ G` after postcomposition with any functor `G : H ⥤ E`
(`CategoryTheory.LocalizerMorphism.Derives.isLeftDerivedFunctor_comp`). Specializing to product
localizers yields two-variable postcomposition absoluteness for
`CategoryTheory.Functor.IsLeftDerivedFunctor₂`
(`CategoryTheory.LocalizerMorphism.Derives.isLeftDerivedFunctor₂_comp`).

## References

* B. Kahn and G. Maltsiniotis, *Structures de dérivabilité*, Adv. Math. 218 (2008), 1286–1318.
* J. Riou, *Formalization of derived categories in Lean/mathlib*, Ann. Formaliz. Math. 1 (2025),
  1–42, §5.3.
-/

public section

namespace CategoryTheory.LocalizerMorphism.Derives

section OneVariable

variable {C₁ C₂ D₂ H E : Type*} [Category* C₁] [Category* C₂] [Category* D₂]
  [Category* H] [Category* E]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
  {Φ : LocalizerMorphism W₁ W₂} {F : C₂ ⥤ H}

/-- If `Φ` derives `F : C₂ ⥤ H`, then `Φ` also derives `F ⋙ G` for every functor `G : H ⥤ E`. -/
lemma comp (h : Φ.Derives F) (G : H ⥤ E) : Φ.Derives (F ⋙ G) :=
  MorphismProperty.IsInvertedBy.of_comp W₁ (Φ.functor ⋙ F) h G

/-- **Absoluteness under postcomposition.** If `Φ` is a left derivability structure deriving
`F : C₂ ⥤ H`, then postcomposing any left derived functor `(LF, α)` of `F` with an arbitrary
functor `G : H ⥤ E` yields a left derived functor of `F ⋙ G`. -/
lemma isLeftDerivedFunctor_comp (h : Φ.Derives F) [Φ.IsLeftDerivabilityStructure]
    {L₂ : C₂ ⥤ D₂} [L₂.IsLocalization W₂] {LF : D₂ ⥤ H}
    (α : L₂ ⋙ LF ⟶ F) [LF.IsLeftDerivedFunctor α W₂] (G : H ⥤ E) :
    (LF ⋙ G).IsLeftDerivedFunctor
      ((Functor.associator L₂ LF G).inv ≫ Functor.whiskerRight α G) W₂ := by
  rw [(h.comp G).isLeftDerivedFunctor_iff_isIso]
  intro X₁
  have := h.isIso' α X₁
  dsimp
  infer_instance

end OneVariable

section TwoVariables

open CategoryTheory.Functor

variable {C₀ C₁ C₂ D₁ D₂ H E : Type*}
  [Category* C₀] [Category* C₁] [Category* C₂] [Category* D₁] [Category* D₂]
  [Category* H] [Category* E]
  {W₀ : MorphismProperty C₀} {F₀ : C₁ ⥤ C₂ ⥤ H}

/-- If `Φ` derives the uncurried bifunctor `uncurry.obj F₀`, then `Φ` also derives the uncurried
postcomposition `uncurry.obj (F₀ ⋙ (whiskeringRight C₂ H E).obj G)` for every `G : H ⥤ E`. -/
lemma uncurry_postcompose {W' : MorphismProperty (C₁ × C₂)} {Φ : LocalizerMorphism W₀ W'}
    (h : Φ.Derives (uncurry.obj F₀)) (G : H ⥤ E) :
    Φ.Derives (uncurry.obj (F₀ ⋙ (whiskeringRight C₂ H E).obj G)) :=
  (MorphismProperty.IsInvertedBy.iff_of_iso W₀
    (Functor.isoWhiskerLeft Φ.functor
      (NatIso.ofComponents (fun _ ↦ Iso.refl _)
        (by rintro ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩; simp) :
        uncurry.obj (F₀ ⋙ (whiskeringRight C₂ H E).obj G) ≅ uncurry.obj F₀ ⋙ G))).2
    (h.comp G)

/-- **Two-variable absoluteness under postcomposition.** If `Φ` is a left derivability structure on
`W₁.prod W₂` deriving `uncurry.obj F₀`, then postcomposing any left derived bifunctor `(LF, α)` of
`F₀` with an arbitrary functor `G : H ⥤ E` yields a left derived bifunctor of
`F₀ ⋙ (whiskeringRight C₂ H E).obj G`. -/
lemma isLeftDerivedFunctor₂_comp
    {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
    [W₁.ContainsIdentities] [W₂.ContainsIdentities]
    {Φ : LocalizerMorphism W₀ (W₁.prod W₂)} [Φ.IsLeftDerivabilityStructure]
    (h : Φ.Derives (uncurry.obj F₀))
    {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂} [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
    {LF : D₁ ⥤ D₂ ⥤ H} (α : (((whiskeringLeft₂ H).obj L₁).obj L₂).obj LF ⟶ F₀)
    [LF.IsLeftDerivedFunctor₂ α W₁ W₂] (G : H ⥤ E) :
    (LF ⋙ (whiskeringRight D₂ H E).obj G).IsLeftDerivedFunctor₂
      (Functor.whiskerRight α ((whiskeringRight C₂ H E).obj G)) W₁ W₂ := by
  rw [Functor.IsLeftDerivedFunctor₂, (h.uncurry_postcompose G).isLeftDerivedFunctor_iff_isIso]
  intro X₀
  have := h.isIso' (whiskeringLeft₂HomEquiv α) X₀
  dsimp [whiskeringLeft₂HomEquiv] at this ⊢
  infer_instance

end TwoVariables

end CategoryTheory.LocalizerMorphism.Derives
