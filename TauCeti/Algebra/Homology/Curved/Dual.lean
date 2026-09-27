/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FGModuleCat.Dual
public import TauCeti.Algebra.Homology.Curved.Duplex

/-!
# Duality for curved duplexes

Let `X` be a curved duplex of curvature `w` in `FGModuleCat S` whose two components are
projective modules, and let `Xᵛ` be its algebraic dual, with components `X₀ᵛ` and `X₁ᵛ`. The
duality used throughout the theory of matrix factorizations crosses the two differentials and
puts the single minus sign on the second one:
```
(Pᵛ)₀ = P₀ᵛ                     (Pᵛ)₁ = P₁ᵛ
d₀ᵛ = (d₁)ᵗ : P₀ᵛ ⟶ P₁ᵛ         d₁ᵛ = -(d₀)ᵗ : P₁ᵛ ⟶ P₀ᵛ .
```
The two composites `d₀ᵛ ≫ d₁ᵛ` and `d₁ᵛ ≫ d₀ᵛ` are then both multiplication by `-w`, so duality
is a passage from curvature `w` to curvature `-w`. Transposition reverses composition, which is
why the differentials are crossed, and the sign is what compensates: a crossed pair of
transposes is the transpose of the original composite, and the minus sign turns `w` into `-w`.

Duality is contravariant, and this file records it as such: `CurvedDuplex.dualHom` sends a
morphism to a morphism from the dual of its target to the dual of its source, and reverses
identity and composition. Crossing the differentials twice therefore lands back at the original
curvature, with the negated double transposes as the differentials of a double dual, and the two
evaluations identify a double dual with the original duplex.

## Main definitions

* `CurvedDuplex.dual`: the dual of a curved duplex with projective components, of curvature `-w`.
* `CurvedDuplex.dualHom`: the dual of a morphism of curved duplexes, contravariantly.
* `CurvedDuplex.doubleDual`, `CurvedDuplex.doubleDualEquiv`: the double dual, of the original
  curvature, and its isomorphism with the original duplex.

## Main results

* `CurvedDuplex.negDualHom_comp_dualHom`: a crossed pair of transposes is the negated curvature.
* `CurvedDuplex.dual_d₀`, `CurvedDuplex.dual_d₁`: the crossed transposed differentials.
* `CurvedDuplex.dualHom_id`, `CurvedDuplex.dualHom_comp`: the dual of a morphism reverses identity
  and composition, which is what makes duality contravariant.
* `CurvedDuplex.doubleDualEquiv`: a double dual is isomorphic to the original curved duplex, by
  the evaluation pairing with the single minus sign on the even component.
-/

public section

universe u

namespace TauCeti

open CategoryTheory Category Preadditive Module

variable (S : Type u) [CommRing S] (w : S)

namespace CurvedDuplex

variable {S w}

/-- For a curved pair of maps `f` and `g` with `f ≫ g = w • 𝟙`, the composite of the negated
transpose of `g` with the transpose of `f` is multiplication by `-w` on the dual. This is the
computation behind the two differential equations of `CurvedDuplex.dual`. -/
theorem negDualHom_comp_dualHom {M N : FGModuleCat.{u} S} [Module.Projective S M]
    [Module.Projective S N] (f : M ⟶ N) (g : N ⟶ M) (h : f ≫ g = w • 𝟙 M) :
    ((-FGModuleCat.dualHom S g) ≫ FGModuleCat.dualHom S f) = -w • 𝟙 (FGModuleCat.dual S M) := by
  calc (-FGModuleCat.dualHom S g) ≫ FGModuleCat.dualHom S f
      = -(FGModuleCat.dualHom S g ≫ FGModuleCat.dualHom S f) := by simp only [neg_comp]
    _ = -FGModuleCat.dualHom S (f ≫ g) := by rw [FGModuleCat.dualHom_comp (f := f) (g := g)]
    _ = -FGModuleCat.dualHom S (w • 𝟙 M) := by rw [h]
    _ = -(w • FGModuleCat.dualHom S (𝟙 M)) := by rw [FGModuleCat.dualHom_smul]
    _ = -(w • 𝟙 (FGModuleCat.dual S M)) := by rw [FGModuleCat.dualHom_id]
    _ = -w • 𝟙 (FGModuleCat.dual S M) := by rw [neg_smul]

/-- The dual of a curved duplex with projective components is a curved duplex of the negated
curvature whose differentials are the crossed transposes, the minus sign on the second. -/
abbrev dual (X : CurvedDuplex (FGModuleCat.{u} S) w) [Module.Projective S X.X₀]
    [Module.Projective S X.X₁] : CurvedDuplex (FGModuleCat.{u} S) (-w) where
  X₀ := FGModuleCat.dual S X.X₀
  X₁ := FGModuleCat.dual S X.X₁
  d₀ := FGModuleCat.dualHom S X.d₁
  d₁ := -FGModuleCat.dualHom S X.d₀
  d₀_comp_d₁ := by
    rw [comp_neg]
    exact negDualHom_comp_dualHom X.d₀ X.d₁ X.d₀_comp_d₁
  d₁_comp_d₀ := negDualHom_comp_dualHom X.d₁ X.d₀ X.d₁_comp_d₀

@[simp] theorem dual_X₀ (X : CurvedDuplex (FGModuleCat.{u} S) w) [Module.Projective S X.X₀]
    [Module.Projective S X.X₁] : X.dual.X₀ = FGModuleCat.dual S X.X₀ := rfl

@[simp] theorem dual_X₁ (X : CurvedDuplex (FGModuleCat.{u} S) w) [Module.Projective S X.X₀]
    [Module.Projective S X.X₁] : X.dual.X₁ = FGModuleCat.dual S X.X₁ := rfl

@[simp] theorem dual_d₀ (X : CurvedDuplex (FGModuleCat.{u} S) w) [Module.Projective S X.X₀]
    [Module.Projective S X.X₁] : X.dual.d₀ = FGModuleCat.dualHom S X.d₁ := rfl

@[simp] theorem dual_d₁ (X : CurvedDuplex (FGModuleCat.{u} S) w) [Module.Projective S X.X₀]
    [Module.Projective S X.X₁] : X.dual.d₁ = -FGModuleCat.dualHom S X.d₀ := rfl

/-- The dual of a morphism of curved duplexes is a morphism from the dual of the target to the
dual of the source, with transposed components. The two commutativity conditions of `f` enter
with the two differentials exchanged, which is what the crossed transposes need. -/
@[expose] def dualHom {X Y : CurvedDuplex (FGModuleCat.{u} S) w} [Module.Projective S X.X₀]
    [Module.Projective S X.X₁] [Module.Projective S Y.X₀] [Module.Projective S Y.X₁] (f : X ⟶ Y) :
    Y.dual ⟶ X.dual :=
  homMk (FGModuleCat.dualHom S f.f₀) (FGModuleCat.dualHom S f.f₁)
    (by
      change FGModuleCat.dualHom S f.f₀ ≫ FGModuleCat.dualHom S X.d₁ =
        FGModuleCat.dualHom S Y.d₁ ≫ FGModuleCat.dualHom S f.f₁
      rw [← FGModuleCat.dualHom_comp, ← FGModuleCat.dualHom_comp, f.comm₁])
    (by
      change (FGModuleCat.dualHom S f.f₁) ≫ (-FGModuleCat.dualHom S X.d₀) =
        (-FGModuleCat.dualHom S Y.d₀) ≫ FGModuleCat.dualHom S f.f₀
      simp only [comp_neg, neg_comp]
      rw [← FGModuleCat.dualHom_comp, ← FGModuleCat.dualHom_comp, f.comm₀])

@[simp] theorem dualHom_f₀ {X Y : CurvedDuplex (FGModuleCat.{u} S) w} [Module.Projective S X.X₀]
    [Module.Projective S X.X₁] [Module.Projective S Y.X₀] [Module.Projective S Y.X₁] (f : X ⟶ Y) :
    (dualHom f).f₀ = FGModuleCat.dualHom S f.f₀ := rfl

@[simp] theorem dualHom_f₁ {X Y : CurvedDuplex (FGModuleCat.{u} S) w} [Module.Projective S X.X₀]
    [Module.Projective S X.X₁] [Module.Projective S Y.X₀] [Module.Projective S Y.X₁] (f : X ⟶ Y) :
    (dualHom f).f₁ = FGModuleCat.dualHom S f.f₁ := rfl

@[simp] theorem dualHom_id (X : CurvedDuplex (FGModuleCat.{u} S) w) [Module.Projective S X.X₀]
    [Module.Projective S X.X₁] :
    dualHom (𝟙 X) = 𝟙 X.dual :=
  hom_ext (FGModuleCat.dualHom_id S).symm (FGModuleCat.dualHom_id S).symm

@[simp] theorem dualHom_comp {X Y Z : CurvedDuplex (FGModuleCat.{u} S) w} [Module.Projective S X.X₀]
    [Module.Projective S X.X₁] [Module.Projective S Y.X₀] [Module.Projective S Y.X₁]
    [Module.Projective S Z.X₀] [Module.Projective S Z.X₁] (f : X ⟶ Y) (g : Y ⟶ Z) :
    dualHom (f ≫ g) = dualHom g ≫ dualHom f := by
  refine hom_ext ?_ ?_
  · exact FGModuleCat.dualHom_comp S f.f₀ g.f₀
  · exact FGModuleCat.dualHom_comp S f.f₁ g.f₁

/-- The double dual of a curved duplex is a curved duplex of the *same* curvature: the two minus
signs contributed by the two duals cancel. It is therefore stated directly at curvature `w`
instead of as a second application of `CurvedDuplex.dual`, whose curvature term would be `- -w`,
a term Lean does not identify with `w`. Its differentials are the negated double transposes. -/
abbrev doubleDual (X : CurvedDuplex (FGModuleCat.{u} S) w) [Module.Projective S X.X₀]
    [Module.Projective S X.X₁] : CurvedDuplex (FGModuleCat.{u} S) w where
  X₀ := FGModuleCat.dual S (FGModuleCat.dual S X.X₀)
  X₁ := FGModuleCat.dual S (FGModuleCat.dual S X.X₁)
  d₀ := -FGModuleCat.dualHom S (FGModuleCat.dualHom S X.d₀)
  d₁ := -FGModuleCat.dualHom S (FGModuleCat.dualHom S X.d₁)
  d₀_comp_d₁ := by
    calc (-FGModuleCat.dualHom S (FGModuleCat.dualHom S X.d₀))
        ≫ (-FGModuleCat.dualHom S (FGModuleCat.dualHom S X.d₁))
        = FGModuleCat.dualHom S (FGModuleCat.dualHom S X.d₀) ≫
            FGModuleCat.dualHom S (FGModuleCat.dualHom S X.d₁) := by
              rw [Preadditive.neg_comp_neg]
      _ = FGModuleCat.dualHom S (FGModuleCat.dualHom S (X.d₀ ≫ X.d₁)) := by
        rw [← FGModuleCat.dualHom_comp, ← FGModuleCat.dualHom_comp]
      _ = FGModuleCat.dualHom S (FGModuleCat.dualHom S (w • 𝟙 X.X₀)) := by rw [X.d₀_comp_d₁]
      _ = w • FGModuleCat.dualHom S (FGModuleCat.dualHom S (𝟙 X.X₀)) := by
        simp only [FGModuleCat.dualHom_smul]
      _ = w • 𝟙 (FGModuleCat.dual S (FGModuleCat.dual S X.X₀)) := by
        rw [FGModuleCat.dualHom_id, FGModuleCat.dualHom_id]
  d₁_comp_d₀ := by
    calc (-FGModuleCat.dualHom S (FGModuleCat.dualHom S X.d₁))
        ≫ (-FGModuleCat.dualHom S (FGModuleCat.dualHom S X.d₀))
        = FGModuleCat.dualHom S (FGModuleCat.dualHom S X.d₁) ≫
            FGModuleCat.dualHom S (FGModuleCat.dualHom S X.d₀) := by
              rw [Preadditive.neg_comp_neg]
      _ = FGModuleCat.dualHom S (FGModuleCat.dualHom S (X.d₁ ≫ X.d₀)) := by
        rw [← FGModuleCat.dualHom_comp, ← FGModuleCat.dualHom_comp]
      _ = FGModuleCat.dualHom S (FGModuleCat.dualHom S (w • 𝟙 X.X₁)) := by rw [X.d₁_comp_d₀]
      _ = w • FGModuleCat.dualHom S (FGModuleCat.dualHom S (𝟙 X.X₁)) := by
        simp only [FGModuleCat.dualHom_smul]
      _ = w • 𝟙 (FGModuleCat.dual S (FGModuleCat.dual S X.X₁)) := by
        rw [FGModuleCat.dualHom_id, FGModuleCat.dualHom_id]

/-- A double dual is isomorphic to the original curved duplex. The isomorphism is the evaluation
pairing, with the single minus sign on the even component: that is the placement which makes the
two commutativity conditions hold against the negated double transposes. -/
@[expose] noncomputable def doubleDualEquiv (X : CurvedDuplex (FGModuleCat.{u} S) w)
    [Module.Projective S X.X₀] [Module.Projective S X.X₁] : doubleDual X ≅ X :=
  isoMk
    { hom := -(FGModuleCat.dualEvalEquiv S X.X₀).hom
      inv := -(FGModuleCat.dualEvalEquiv S X.X₀).inv
      hom_inv_id := by
        change (-(FGModuleCat.dualEvalEquiv S X.X₀).hom) ≫
          (-(FGModuleCat.dualEvalEquiv S X.X₀).inv)
            = 𝟙 (FGModuleCat.dual S (FGModuleCat.dual S X.X₀))
        rw [Preadditive.neg_comp_neg, (FGModuleCat.dualEvalEquiv S X.X₀).hom_inv_id]
      inv_hom_id := by
        change (-(FGModuleCat.dualEvalEquiv S X.X₀).inv) ≫
          (-(FGModuleCat.dualEvalEquiv S X.X₀).hom) = 𝟙 X.X₀
        rw [Preadditive.neg_comp_neg, (FGModuleCat.dualEvalEquiv S X.X₀).inv_hom_id] }
    { hom := (FGModuleCat.dualEvalEquiv S X.X₁).hom
      inv := (FGModuleCat.dualEvalEquiv S X.X₁).inv
      hom_inv_id := by
        change (FGModuleCat.dualEvalEquiv S X.X₁).hom ≫ (FGModuleCat.dualEvalEquiv S X.X₁).inv
          = 𝟙 (FGModuleCat.dual S (FGModuleCat.dual S X.X₁))
        exact (FGModuleCat.dualEvalEquiv S X.X₁).hom_inv_id
      inv_hom_id := by
        change (FGModuleCat.dualEvalEquiv S X.X₁).inv ≫
          (FGModuleCat.dualEvalEquiv S X.X₁).hom = 𝟙 X.X₁
        exact (FGModuleCat.dualEvalEquiv S X.X₁).inv_hom_id }
    (by
      change (-(FGModuleCat.dualEvalEquiv S X.X₀).hom) ≫ X.d₀ =
        (-FGModuleCat.dualHom S (FGModuleCat.dualHom S X.d₀)) ≫
          (FGModuleCat.dualEvalEquiv S X.X₁).hom
      rw [neg_comp, neg_comp, FGModuleCat.dualHom_dualHom_dualEvalEquiv])
    (by
      change (FGModuleCat.dualEvalEquiv S X.X₁).hom ≫ X.d₁ =
        (-FGModuleCat.dualHom S (FGModuleCat.dualHom S X.d₁)) ≫
          (-(FGModuleCat.dualEvalEquiv S X.X₀).hom)
      rw [Preadditive.neg_comp_neg, FGModuleCat.dualHom_dualHom_dualEvalEquiv])

end CurvedDuplex

end TauCeti
