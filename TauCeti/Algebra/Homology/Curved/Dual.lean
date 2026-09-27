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

The two differential equations of the dual are the crossed-transpose computation
`FGModuleCat.negDualHom_comp_dualHom`, and the two differential equations of the double dual are
its one-dual-further version `FGModuleCat.negDualHom_dualHom_comp_negDualHom_dualHom`; both live
in `TauCeti/Algebra/Category/FGModuleCat/Dual.lean` and are stated for morphisms of
`FGModuleCat` alone, so this file only records how they apply to a curved duplex.

## Main definitions

* `CurvedDuplex.dual`: the dual of a curved duplex with projective components, of curvature `-w`.
* `CurvedDuplex.dualHom`: the dual of a morphism of curved duplexes, contravariantly.
* `CurvedDuplex.doubleDual`, `CurvedDuplex.doubleDualIso`: the double dual, of the original
  curvature, and its isomorphism with the original duplex.

## Main results

* `CurvedDuplex.dual_d₀`, `CurvedDuplex.dual_d₁`: the crossed transposed differentials.
* `CurvedDuplex.dualHom_f₀`, `CurvedDuplex.dualHom_f₁`: the components of a dual morphism are the
  transposes of the components.
* `CurvedDuplex.dualHom_id`, `CurvedDuplex.dualHom_comp`: the dual of a morphism reverses identity
  and composition, which is what makes duality contravariant.
* `CurvedDuplex.doubleDual_d₀`, `CurvedDuplex.doubleDual_d₁`: the negated double transposes.
* `CurvedDuplex.doubleDualIso`, `CurvedDuplex.doubleDualIso_f₀`, `CurvedDuplex.doubleDualIso_f₁`:
  a double dual is isomorphic to the original curved duplex, by the evaluation pairing with the
  single minus sign on the even component.
-/

public section

universe u

namespace TauCeti

open CategoryTheory Category Preadditive Module

variable (S : Type u) [CommRing S] (w : S)

namespace CurvedDuplex

variable {S w}

/-- The dual of a curved duplex with projective components is a curved duplex of the negated
curvature whose differentials are the crossed transposes, the minus sign on the second. -/
abbrev dual (X : CurvedDuplex (FGModuleCat.{u} S) w) [Module.Projective S X.X₀]
    [Module.Projective S X.X₁] : CurvedDuplex (FGModuleCat.{u} S) (-w) where
  X₀ := FGModuleCat.dual S X.X₀
  X₁ := FGModuleCat.dual S X.X₁
  d₀ := FGModuleCat.dualHom S X.d₁
  d₁ := -FGModuleCat.dualHom S X.d₀
  d₀_comp_d₁ := by
    rw [comp_neg, ← FGModuleCat.dualHom_comp, X.d₀_comp_d₁,
      FGModuleCat.dualHom_smul, FGModuleCat.dualHom_id, neg_smul]
  d₁_comp_d₀ := by
    rw [Preadditive.neg_comp, ← FGModuleCat.dualHom_comp, X.d₁_comp_d₀,
      FGModuleCat.dualHom_smul, FGModuleCat.dualHom_id, neg_smul]

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
def dualHom {X Y : CurvedDuplex (FGModuleCat.{u} S) w} [Module.Projective S X.X₀]
    [Module.Projective S X.X₁] [Module.Projective S Y.X₀] [Module.Projective S Y.X₁] (f : X ⟶ Y) :
    Y.dual ⟶ X.dual :=
  homMk (FGModuleCat.dualHom S f.f₀) (FGModuleCat.dualHom S f.f₁)
    (by rw [← FGModuleCat.dualHom_comp, ← FGModuleCat.dualHom_comp, f.comm₁])
    (by
      simp only [comp_neg, neg_comp]
      rw [← FGModuleCat.dualHom_comp, ← FGModuleCat.dualHom_comp, f.comm₀])

/-- The underlying curved-duplex morphism of a dual morphism is the pair of transposes, built by
`CurvedDuplex.homMk` from the commutativity conditions of `f`. This is the rewriting form of
`CurvedDuplex.dualHom`, which is not exposed; `CurvedDuplex.dualHom_f₀` and
`CurvedDuplex.dualHom_f₁` are the two components. -/
theorem dualHom_hom {X Y : CurvedDuplex (FGModuleCat.{u} S) w} [Module.Projective S X.X₀]
    [Module.Projective S X.X₁] [Module.Projective S Y.X₀] [Module.Projective S Y.X₁] (f : X ⟶ Y) :
    CurvedDuplex.dualHom f = CurvedDuplex.homMk (FGModuleCat.dualHom S f.f₀)
      (FGModuleCat.dualHom S f.f₁)
      (by rw [← FGModuleCat.dualHom_comp, ← FGModuleCat.dualHom_comp, f.comm₁])
      (by
        simp only [comp_neg, neg_comp]
        rw [← FGModuleCat.dualHom_comp, ← FGModuleCat.dualHom_comp, f.comm₀]) := (rfl)

@[simp] theorem dualHom_f₀ {X Y : CurvedDuplex (FGModuleCat.{u} S) w} [Module.Projective S X.X₀]
    [Module.Projective S X.X₁] [Module.Projective S Y.X₀] [Module.Projective S Y.X₁] (f : X ⟶ Y) :
    (dualHom f).f₀ = FGModuleCat.dualHom S f.f₀ :=
  by rw [dualHom_hom, CurvedDuplex.homMk_f₀]

@[simp] theorem dualHom_f₁ {X Y : CurvedDuplex (FGModuleCat.{u} S) w} [Module.Projective S X.X₀]
    [Module.Projective S X.X₁] [Module.Projective S Y.X₀] [Module.Projective S Y.X₁] (f : X ⟶ Y) :
    (dualHom f).f₁ = FGModuleCat.dualHom S f.f₁ :=
  by rw [dualHom_hom, CurvedDuplex.homMk_f₁]

@[simp] theorem dualHom_id (X : CurvedDuplex (FGModuleCat.{u} S) w) [Module.Projective S X.X₀]
    [Module.Projective S X.X₁] :
    dualHom (𝟙 X) = 𝟙 X.dual :=
  hom_ext ((CurvedDuplex.dualHom_f₀ (𝟙 X)).trans (by simp))
    ((CurvedDuplex.dualHom_f₁ (𝟙 X)).trans (by simp))

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
  d₀_comp_d₁ :=
    FGModuleCat.negDualHom_dualHom_comp_negDualHom_dualHom S w X.d₀ X.d₁ X.d₀_comp_d₁
  d₁_comp_d₀ :=
    FGModuleCat.negDualHom_dualHom_comp_negDualHom_dualHom S w X.d₁ X.d₀ X.d₁_comp_d₀

@[simp] theorem doubleDual_X₀ (X : CurvedDuplex (FGModuleCat.{u} S) w) [Module.Projective S X.X₀]
    [Module.Projective S X.X₁] :
    (X.doubleDual).X₀ = FGModuleCat.dual S (FGModuleCat.dual S X.X₀) := rfl

@[simp] theorem doubleDual_X₁ (X : CurvedDuplex (FGModuleCat.{u} S) w) [Module.Projective S X.X₀]
    [Module.Projective S X.X₁] :
    (X.doubleDual).X₁ = FGModuleCat.dual S (FGModuleCat.dual S X.X₁) := rfl

@[simp] theorem doubleDual_d₀ (X : CurvedDuplex (FGModuleCat.{u} S) w) [Module.Projective S X.X₀]
    [Module.Projective S X.X₁] :
    (X.doubleDual).d₀ = -FGModuleCat.dualHom S (FGModuleCat.dualHom S X.d₀) := rfl

@[simp] theorem doubleDual_d₁ (X : CurvedDuplex (FGModuleCat.{u} S) w) [Module.Projective S X.X₀]
    [Module.Projective S X.X₁] :
    (X.doubleDual).d₁ = -FGModuleCat.dualHom S (FGModuleCat.dualHom S X.d₁) := rfl

/-- A double dual is isomorphic to the original curved duplex. The isomorphism is the evaluation
pairing, with the single minus sign on the even component: that is the placement which makes the
two commutativity conditions hold against the negated double transposes. -/
noncomputable def doubleDualIso (X : CurvedDuplex (FGModuleCat.{u} S) w)
    [Module.Projective S X.X₀] [Module.Projective S X.X₁] : X.doubleDual ≅ X :=
  isoMk
    { hom := -(FGModuleCat.dualEvalIso S X.X₀).hom
      inv := -(FGModuleCat.dualEvalIso S X.X₀).inv
      hom_inv_id := by
        simp only [Preadditive.neg_comp_neg, (FGModuleCat.dualEvalIso S X.X₀).hom_inv_id]
      inv_hom_id := by
        simp only [Preadditive.neg_comp_neg, (FGModuleCat.dualEvalIso S X.X₀).inv_hom_id] }
    { hom := (FGModuleCat.dualEvalIso S X.X₁).hom
      inv := (FGModuleCat.dualEvalIso S X.X₁).inv
      hom_inv_id := by
        exact (FGModuleCat.dualEvalIso S X.X₁).hom_inv_id
      inv_hom_id := by
        exact (FGModuleCat.dualEvalIso S X.X₁).inv_hom_id }
    (by rw [neg_comp, neg_comp, FGModuleCat.dualHom_dualHom_dualEvalIso])
    (by rw [Preadditive.neg_comp_neg, FGModuleCat.dualHom_dualHom_dualEvalIso])

/-- The even component of the double dual isomorphism is the negated evaluation isomorphism. -/
@[simp] theorem doubleDualIso_f₀ (X : CurvedDuplex (FGModuleCat.{u} S) w)
    [Module.Projective S X.X₀] [Module.Projective S X.X₁] :
    (X.doubleDualIso).hom.f₀ = -(FGModuleCat.dualEvalIso S X.X₀).hom := (rfl)

/-- The odd component of the double dual isomorphism is the evaluation isomorphism. -/
@[simp] theorem doubleDualIso_f₁ (X : CurvedDuplex (FGModuleCat.{u} S) w)
    [Module.Projective S X.X₀] [Module.Projective S X.X₁] :
    (X.doubleDualIso).hom.f₁ = (FGModuleCat.dualEvalIso S X.X₁).hom := (rfl)

/-- The even component of the inverse of the double dual isomorphism is the negated inverse
evaluation isomorphism. -/
@[simp] theorem doubleDualIso_inv_f₀ (X : CurvedDuplex (FGModuleCat.{u} S) w)
    [Module.Projective S X.X₀] [Module.Projective S X.X₁] :
    (X.doubleDualIso).inv.f₀ = -(FGModuleCat.dualEvalIso S X.X₀).inv := (rfl)

/-- The odd component of the inverse of the double dual isomorphism is the inverse evaluation
isomorphism. -/
@[simp] theorem doubleDualIso_inv_f₁ (X : CurvedDuplex (FGModuleCat.{u} S) w)
    [Module.Projective S X.X₀] [Module.Projective S X.X₁] :
    (X.doubleDualIso).inv.f₁ = (FGModuleCat.dualEvalIso S X.X₁).inv := (rfl)


end CurvedDuplex

end TauCeti
