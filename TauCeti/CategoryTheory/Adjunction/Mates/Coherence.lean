/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Coherence of mates with identities and composites

Let `P ⊣ Q` be adjunctions indexed by morphisms, with identifications of the identity left and
right adjoints with identity functors, and of composite left and right adjoints with the left and
right adjoints of a composite, which are conjugate. A family of endofunctors `W` with comparisons
`W ⋙ P ⟶ P ⋙ W` then respects the identifications of the left adjoints as soon as the mate
comparisons `Q ⋙ W ⟶ W ⋙ Q` respect those of the right adjoints.

This is how coherence of comparisons with pullback is deduced from coherence with pushforward,
for example for exterior and symmetric powers of modules over schemes, where the pullback
comparison is defined as the mate of the pushforward comparison.

## Main declarations

* `CategoryTheory.TwoSquare.coherence_id_of_mateEquiv`: compatibility with the identifications
  of the left adjoint with the identity functor;
* `CategoryTheory.TwoSquare.coherence_comp_of_mateEquiv`: compatibility with the identification
  of a composite of left adjoints with a left adjoint.
-/

public section

namespace CategoryTheory

open Category

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace TwoSquare

/-- Let `adj : P ⊣ Q` be an adjunction of endofunctors whose left and right adjoints are
identified with `𝟭 C` by conjugate isomorphisms `a` and `b`. If the mate `q` of a square
`c : W ⋙ P ⟶ P ⋙ W` is compatible with `b`, then `c` is compatible with `a`. -/
theorem coherence_id_of_mateEquiv {C : Type u₁} [Category.{v₁} C] {P Q : C ⥤ C} (adj : P ⊣ Q)
    (a : P ≅ 𝟭 C) (b : Q ≅ 𝟭 C) (hab : conjugateEquiv Adjunction.id adj a.hom = b.inv)
    {W : C ⥤ C} (c : TwoSquare W P P W) (q : TwoSquare Q W W Q) (hcq : mateEquiv adj adj c = q)
    (hq : ∀ M, q.app M ≫ b.hom.app (W.obj M) = W.map (b.hom.app M)) (M : C) :
    c.app M ≫ W.map (a.hom.app M) = a.hom.app (W.obj M) := by
  have hu (N : C) : adj.unit.app N ≫ Q.map (a.hom.app N) = b.inv.app N := by
    simpa only [hab, Adjunction.id_unit, NatTrans.id_app, id_comp, Functor.id_obj] using
      (unit_conjugateEquiv Adjunction.id adj a.hom N).symm
  have hc : adj.unit.app (W.obj M) ≫ Q.map (c.app M) =
      W.map (adj.unit.app M) ≫ q.app (P.obj M) := by
    rw [← hcq]
    exact (unit_mateEquiv adj adj c M).symm
  have hn := q.naturality (a.hom.app M)
  dsimp only [Functor.comp_map] at hn
  apply (adj.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  -- Take the adjoint transpose, use naturality, then cancel the identity comparison.
  calc
    _ = (W.map (adj.unit.app M) ≫ q.app (P.obj M)) ≫
        Q.map (W.map (a.hom.app M)) := by
      simpa only [Functor.map_comp, Category.assoc] using
        congrArg (fun k ↦ k ≫ Q.map (W.map (a.hom.app M))) hc
    _ = W.map (adj.unit.app M) ≫ W.map (Q.map (a.hom.app M)) ≫ q.app M := by
      rw [Category.assoc, ← hn]
      simp only [Functor.id_obj]
    _ = W.map (b.inv.app M) ≫ q.app M := by
      rw [← W.map_comp_assoc, hu M]
    _ = W.map (b.inv.app M) ≫ W.map (b.hom.app M) ≫ b.inv.app (W.obj M) := by
      rw [(Iso.eq_comp_inv (b.app (W.obj M))).mpr (hq M)]
      simp only [Iso.app_inv]
    _ = b.inv.app (W.obj M) := by
      simp only [← W.map_comp_assoc, Iso.inv_hom_id_app, Functor.id_obj, W.map_id,
        Category.id_comp]
    _ = _ := (hu (W.obj M)).symm

/-- Let `A : P₁ ⊣ Q₁`, `B : P₂ ⊣ Q₂` and `C : P₃ ⊣ Q₃` be adjunctions, with `e : P₁ ⋙ P₂ ≅ P₃`
and `d : Q₂ ⋙ Q₁ ≅ Q₃` conjugate. If the mates `qᵢ` of squares `cᵢ : Wᵢ ⋙ Pᵢ ⟶ Pᵢ ⋙ Wᵢ₊₁`
(with `c₃` from `W₁` to `W₃`) are compatible with `d`, then the `cᵢ` are compatible with `e`. -/
theorem coherence_comp_of_mateEquiv {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
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

end TwoSquare

end CategoryTheory
