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

Let `P ⊣ Q` be adjunctions indexed by morphisms, with identifications of the identity left and
right adjoints with identity functors, and of composite left and right adjoints with the left and
right adjoints of a composite, which are conjugate. A family of endofunctors `W` with comparisons
`W ⋙ P ⟶ P ⋙ W` then respects the identifications of the left adjoints as soon as the mate
comparisons `Q ⋙ W ⟶ W ⋙ Q` respect those of the right adjoints. This is how coherence of
comparisons with pullback is deduced from coherence with pushforward, for example for exterior
and symmetric powers of modules over schemes, where the pullback comparison is defined as the
mate of the pushforward comparison.

## Main declarations

* `CategoryTheory.mateEquiv_adjunction_id`;
* `CategoryTheory.Adjunction.homEquiv_conjugateEquiv`;
* `CategoryTheory.Adjunction.app_comp_map_hom_app_of_mateEquiv`: compatibility with the
  identifications of the left adjoint with the identity functor;
* `CategoryTheory.Adjunction.app_comp_map_inv_app_of_mateEquiv`: compatibility with the
  identification of a composite of left adjoints with a left adjoint.
-/

public section

namespace CategoryTheory

open Category CategoryTheory.Functor

universe v₁ v₂ v₃ u₁ u₂ u₃

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

/-- Let `adj : P ⊣ Q` be an adjunction of endofunctors whose left and right adjoints are
identified with `𝟭 C` by conjugate isomorphisms `a` and `b`. If the mate `q` of a square
`c : W ⋙ P ⟶ P ⋙ W` is compatible with `b`, then `c` is compatible with `a`. -/
theorem app_comp_map_hom_app_of_mateEquiv {P Q : C ⥤ C} (adj : P ⊣ Q)
    (a : P ≅ 𝟭 C) (b : Q ≅ 𝟭 C) (hab : conjugateEquiv Adjunction.id adj a.hom = b.inv)
    {W : C ⥤ C} (c : TwoSquare W P P W) (q : TwoSquare Q W W Q) (hcq : mateEquiv adj adj c = q)
    (hq : ∀ M, q.app M ≫ b.hom.app (W.obj M) = W.map (b.hom.app M)) (M : C) :
    c.app M ≫ W.map (a.hom.app M) = a.hom.app (W.obj M) := by
  -- Across the mate bijection, `hab` and `hcq` turn whiskering `c` by `a.hom` into whiskering `q`
  -- by `b.inv`, and `mateEquiv_adjunction_id` fixes the identity square of `W`.
  have h : c.whiskerLeft a.hom = (TwoSquare.vId W).whiskerRight a.hom := by
    apply (mateEquiv Adjunction.id adj).injective
    rw [conjugateEquiv_mateEquiv_vcomp, mateEquiv_conjugateEquiv_vcomp, mateEquiv_adjunction_id,
      hcq, hab]
    ext N
    simp only [Functor.comp_obj, Functor.id_obj, TwoSquare.whiskerTop_app,
      TwoSquare.whiskerBottom_app, TwoSquare.vId, NatTrans.comp_app, Functor.rightUnitor_hom_app,
      Functor.leftUnitor_inv_app, Category.comp_id, Category.id_comp]
    -- What is left is `hq` with `b.hom` replaced by `b.inv`.
    rw [← cancel_mono (b.hom.app _)]
    simp only [Functor.id_obj, Category.assoc, hq, ← W.map_comp, Iso.inv_hom_id_app, W.map_id]
  -- Components of the whiskered squares are the two sides of the asserted equation.
  simpa only [Functor.comp_obj, Functor.id_obj, TwoSquare.whiskerLeft_app, TwoSquare.vId,
    TwoSquare.whiskerRight_app, NatTrans.comp_app, Functor.rightUnitor_hom_app,
    Functor.leftUnitor_inv_app, Category.comp_id] using congr_app h M

/-- Let `A : P₁ ⊣ Q₁`, `B : P₂ ⊣ Q₂` and `C : P₃ ⊣ Q₃` be adjunctions, with `e : P₁ ⋙ P₂ ≅ P₃`
and `d : Q₂ ⋙ Q₁ ≅ Q₃` conjugate. If the mates `qᵢ` of squares `cᵢ : Wᵢ ⋙ Pᵢ ⟶ Pᵢ ⋙ Wᵢ₊₁`
(with `c₃` from `W₁` to `W₃`) are compatible with `d`, then the `cᵢ` are compatible with `e`. -/
theorem app_comp_map_inv_app_of_mateEquiv {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
    [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
    {P₁ : C₁ ⥤ C₂} {Q₁ : C₂ ⥤ C₁} {P₂ : C₂ ⥤ C₃} {Q₂ : C₃ ⥤ C₂} {P₃ : C₁ ⥤ C₃} {Q₃ : C₃ ⥤ C₁}
    (A : P₁ ⊣ Q₁) (B : P₂ ⊣ Q₂) (C : P₃ ⊣ Q₃) (e : P₁ ⋙ P₂ ≅ P₃) (d : Q₂ ⋙ Q₁ ≅ Q₃)
    (hed : conjugateEquiv (A.comp B) C e.inv = d.hom)
    {W₁ : C₁ ⥤ C₁} {W₂ : C₂ ⥤ C₂} {W₃ : C₃ ⥤ C₃}
    (c₁ : TwoSquare W₁ P₁ P₁ W₂) (c₂ : TwoSquare W₂ P₂ P₂ W₃) (c₃ : TwoSquare W₁ P₃ P₃ W₃)
    (q₁ : TwoSquare Q₁ W₂ W₁ Q₁) (q₂ : TwoSquare Q₂ W₃ W₂ Q₂) (q₃ : TwoSquare Q₃ W₃ W₁ Q₃)
    (h₁ : mateEquiv A A c₁ = q₁) (h₂ : mateEquiv B B c₂ = q₂) (h₃ : mateEquiv C C c₃ = q₃)
    (hq : ∀ N, q₁.app (Q₂.obj N) ≫ Q₁.map (q₂.app N) ≫ d.hom.app (W₃.obj N) =
      W₁.map (d.hom.app N) ≫ q₃.app N) (M : C₁) :
    c₃.app M ≫ W₃.map (e.inv.app M) =
      e.inv.app (W₁.obj M) ≫ P₂.map (c₁.app M) ≫ c₂.app (P₁.obj M) := by
  have h : c₃.whiskerLeft e.inv = (TwoSquare.vComp c₁ c₂).whiskerRight e.inv := by
    apply (mateEquiv (A.comp B) C).injective
    rw [conjugateEquiv_mateEquiv_vcomp, mateEquiv_conjugateEquiv_vcomp,
      mateEquiv_hcomp, h₁, h₂, h₃, hed]
    apply NatTrans.ext
    funext N
    simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.assoc]
    exact (hq N).symm
  -- Components of the square operations are the two routes in the asserted diagram.
  simpa only [TwoSquare.whiskerLeft_app, TwoSquare.whiskerRight_app, TwoSquare.vComp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc] using congr_app h M

end Adjunction

end MateCoherence

end CategoryTheory
