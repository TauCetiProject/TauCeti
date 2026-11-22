/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Mates and conjugates

`CategoryTheory.mateEquiv_adjunction_id` is the case of the mate bijection
`CategoryTheory.mateEquiv` in which both adjunctions are identity adjunctions: a two-square
between the identity functors of the source and target category is its own mate.  Use it to
normalize a mate that has been routed through the identity functors, so a computation about
such a square can be read back on the square itself.

The internal-Hom comparison of a monoidal functor is one such computation: at the tensor unit
the left unitor identifies the unit with left tensoring by the unit, and the mate that remains
is taken between the two tensor--Hom adjunctions.

`CategoryTheory.Adjunction.homEquiv_conjugateEquiv` transposes a morphism across two adjunctions
whose left adjoints are compared by a natural transformation `α`: transposing along the first
adjunction and then applying the conjugate of `α` is transposing `α` followed by the morphism along
the second.
It computes transposes along an adjunction whose left adjoint is only known up to a comparison
with another left adjoint, such as a composite of pullback functors.

Let `P ⊣ Q` be adjunctions indexed by morphisms, with conjugate comparisons of the identity left
and right adjoints with identity functors, and of composite left and right adjoints with the left
and right adjoints of a composite. A family of endofunctors `W` with comparisons
`W ⋙ P ⟶ P ⋙ W` then respects the comparisons of the left adjoints as soon as the mate
comparisons `Q ⋙ W ⟶ W ⋙ Q` respect those of the right adjoints. This is how coherence of
comparisons with pullback is deduced from coherence with pushforward, for example for exterior
and symmetric powers of modules over schemes, where the pullback comparison is defined as the
mate of the pushforward comparison.

Both coherence statements are instances of
`CategoryTheory.Adjunction.whiskerLeft_eq_whiskerRight_iff_mateEquiv`: a square whiskered on its
left side agrees with a square whiskered on its right side exactly when their mates, whiskered on
the top and the bottom by the conjugate transformations, agree.

## Main declarations

* `CategoryTheory.mateEquiv_adjunction_id`;
* `CategoryTheory.Adjunction.homEquiv_conjugateEquiv`;
* `CategoryTheory.Adjunction.whiskerLeft_eq_whiskerRight_iff_mateEquiv`;
* `CategoryTheory.Adjunction.app_comp_map_app_eq_app_of_mateEquiv`: compatibility with a
  comparison of the left adjoint with the identity functor;
* `CategoryTheory.Adjunction.app_comp_map_app_eq_app_comp_map_app_comp_app_of_mateEquiv`:
  compatibility with a comparison of a left adjoint with a composite of left adjoints.
-/

public section

namespace CategoryTheory

open Category CategoryTheory.Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

/-- The mate of a two-square between the identity functors of the source and target category is
the two-square itself. -/
-- `high` priority: Mathlib's generated equational lemma `mateEquiv_apply` is itself a simp lemma
-- that unfolds the mate, so at the default priority this rule would never fire, and `simpNF`
-- rejects a simp lemma whose left-hand side another simp lemma already simplifies.
@[simp high]
theorem mateEquiv_adjunction_id {G H : C ⥤ D} (α : TwoSquare G (𝟭 C) (𝟭 D) H) :
    mateEquiv (Adjunction.id : (𝟭 C) ⊣ (𝟭 C))
      (Adjunction.id : (𝟭 D) ⊣ (𝟭 D)) α = α := by
  -- The mate is a whiskered composite of the units and counits of the two adjunctions with the
  -- component of the square; the unit and the counit of an identity adjunction are the identity
  -- maps, so every whiskered unit and counit is the identity and only the square survives.
  ext X
  simp

section Conjugate

namespace Adjunction

variable {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

/-- Transposing `a : L₁ c ⟶ d` along `adj₁` and then applying the conjugate of `α : L₂ ⟶ L₁` is
the transpose of `α.app c ≫ a` along `adj₂`. -/
theorem homEquiv_conjugateEquiv (α : L₂ ⟶ L₁) {c : C} {d : D} (a : L₁.obj c ⟶ d) :
    adj₁.homEquiv c d a ≫ (conjugateEquiv adj₁ adj₂ α).app d =
      adj₂.homEquiv c d (α.app c ≫ a) := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    ← unit_conjugateEquiv, Category.assoc, Category.assoc, NatTrans.naturality]

end Adjunction

end Conjugate

section MateCoherence

namespace Adjunction

/-- A two-square `c` whiskered on its left side by `f` agrees with a two-square `s` whiskered on its
right side by `g` if and only if their mates agree after whiskering the mate of `c` on the top by
the conjugate of `f` and the mate of `s` on the bottom by the conjugate of `g`. -/
theorem whiskerLeft_eq_whiskerRight_iff_mateEquiv {A : Type u₁} {B : Type u₂}
    {E : Type u₃} {F : Type u₄} [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} E]
    [Category.{v₄} F] {G : A ⥤ E} {H : B ⥤ F} {L₁ L₂ : A ⥤ B} {R₁ R₂ : B ⥤ A}
    {L₃ L₄ : E ⥤ F} {R₃ R₄ : F ⥤ E}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃) (adj₄ : L₄ ⊣ R₄)
    {f : L₂ ⟶ L₁} {g : L₃ ⟶ L₄} {c : TwoSquare G L₂ L₃ H} {s : TwoSquare G L₁ L₄ H} :
    c.whiskerLeft f = s.whiskerRight g ↔
      (mateEquiv adj₂ adj₃ c).whiskerTop (conjugateEquiv adj₁ adj₂ f) =
        (mateEquiv adj₁ adj₄ s).whiskerBottom (conjugateEquiv adj₄ adj₃ g) := by
  rw [← conjugateEquiv_mateEquiv_vcomp, ← mateEquiv_conjugateEquiv_vcomp, Equiv.apply_eq_iff_eq]

/-- Let `adj : P ⊣ Q` be an adjunction of endofunctors, `b : Q ≅ 𝟭 C` an isomorphism and
`a : P ⟶ 𝟭 C` the transformation conjugate to `b.inv`. If the mate `q` of a square
`c : W ⋙ P ⟶ P ⋙ W` is compatible with `b`, then `c` is compatible with `a`. -/
theorem app_comp_map_app_eq_app_of_mateEquiv {P Q : C ⥤ C} (adj : P ⊣ Q)
    (a : P ⟶ 𝟭 C) (b : Q ≅ 𝟭 C) (hab : conjugateEquiv Adjunction.id adj a = b.inv)
    {W : C ⥤ C} (c : TwoSquare W P P W) (q : TwoSquare Q W W Q) (hcq : mateEquiv adj adj c = q)
    (hq : ∀ M, q.app M ≫ b.hom.app (W.obj M) = W.map (b.hom.app M)) (M : C) :
    c.app M ≫ W.map (a.app M) = a.app (W.obj M) := by
  -- The proof follows that of `app_comp_map_app_eq_app_comp_map_app_comp_app_of_mateEquiv`
  -- below, with the identity square of `W` in place of the composite square. Across the mate
  -- bijection, `hab` and `hcq` turn whiskering `c` by `a` into whiskering `q` by `b.inv`, and
  -- `mateEquiv_adjunction_id` fixes the identity square of `W`.
  have h : c.whiskerLeft a = (TwoSquare.vId W).whiskerRight a := by
    rw [whiskerLeft_eq_whiskerRight_iff_mateEquiv Adjunction.id adj adj Adjunction.id,
      mateEquiv_adjunction_id, hcq, hab]
    ext N
    simp only [Functor.comp_obj, Functor.id_obj, TwoSquare.whiskerTop_app,
      TwoSquare.whiskerBottom_app, TwoSquare.vId_app, Category.id_comp]
    -- What is left is the inverse form of `hq`, obtained from `hq` by moving the components of
    -- `b` across the equation.
    rw [← cancel_mono (b.hom.app _)]
    simp only [Functor.id_obj, Category.assoc, hq, Iso.inv_hom_id_app]
    exact W.map_inv_hom' (b.app N)
  -- Components of the whiskered squares are the two sides of the asserted equation.
  simpa only [Functor.comp_obj, Functor.id_obj, TwoSquare.whiskerLeft_app, TwoSquare.vId_app,
    TwoSquare.whiskerRight_app, Category.comp_id] using congr_app h M

/-- Let `A : P₁ ⊣ Q₁`, `B : P₂ ⊣ Q₂` and `C : P₃ ⊣ Q₃` be adjunctions, with
`e : P₃ ⟶ P₁ ⋙ P₂` and `d : Q₂ ⋙ Q₁ ⟶ Q₃` conjugate. If the mates `qᵢ` of squares
`cᵢ : Wᵢ ⋙ Pᵢ ⟶ Pᵢ ⋙ Wᵢ₊₁` (with `c₃` from `W₁` to `W₃`) are compatible with `d`, then the `cᵢ`
are compatible with `e`. -/
theorem app_comp_map_app_eq_app_comp_map_app_comp_app_of_mateEquiv {C₁ : Type u₁}
    {C₂ : Type u₂} {C₃ : Type u₃} [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
    {P₁ : C₁ ⥤ C₂} {Q₁ : C₂ ⥤ C₁} {P₂ : C₂ ⥤ C₃} {Q₂ : C₃ ⥤ C₂} {P₃ : C₁ ⥤ C₃} {Q₃ : C₃ ⥤ C₁}
    (A : P₁ ⊣ Q₁) (B : P₂ ⊣ Q₂) (C : P₃ ⊣ Q₃) (e : P₃ ⟶ P₁ ⋙ P₂) (d : Q₂ ⋙ Q₁ ⟶ Q₃)
    (hed : conjugateEquiv (A.comp B) C e = d)
    {W₁ : C₁ ⥤ C₁} {W₂ : C₂ ⥤ C₂} {W₃ : C₃ ⥤ C₃}
    (c₁ : TwoSquare W₁ P₁ P₁ W₂) (c₂ : TwoSquare W₂ P₂ P₂ W₃) (c₃ : TwoSquare W₁ P₃ P₃ W₃)
    (q₁ : TwoSquare Q₁ W₂ W₁ Q₁) (q₂ : TwoSquare Q₂ W₃ W₂ Q₂) (q₃ : TwoSquare Q₃ W₃ W₁ Q₃)
    (h₁ : mateEquiv A A c₁ = q₁) (h₂ : mateEquiv B B c₂ = q₂) (h₃ : mateEquiv C C c₃ = q₃)
    (hq : ∀ N, q₁.app (Q₂.obj N) ≫ Q₁.map (q₂.app N) ≫ d.app (W₃.obj N) =
      W₁.map (d.app N) ≫ q₃.app N) (M : C₁) :
    c₃.app M ≫ W₃.map (e.app M) =
      e.app (W₁.obj M) ≫ P₂.map (c₁.app M) ≫ c₂.app (P₁.obj M) := by
  have h : c₃.whiskerLeft e = (TwoSquare.vComp c₁ c₂).whiskerRight e := by
    rw [(A.comp B).whiskerLeft_eq_whiskerRight_iff_mateEquiv C C (A.comp B),
      mateEquiv_hcomp, h₁, h₂, h₃, hed]
    ext N
    simp only [Functor.comp_obj, TwoSquare.whiskerTop_app, TwoSquare.whiskerBottom_app,
      TwoSquare.hComp_app, Category.assoc]
    exact (hq N).symm
  -- Components of the square operations are the two routes in the asserted diagram.
  simpa only [TwoSquare.whiskerLeft_app, TwoSquare.whiskerRight_app, TwoSquare.vComp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc] using congr_app h M

end Adjunction

end MateCoherence

end CategoryTheory
