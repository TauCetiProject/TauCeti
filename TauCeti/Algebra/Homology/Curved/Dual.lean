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

Duality is contravariant, and this file records it as such: `CurvedDuplex.dualMap` sends a
morphism to a morphism from the dual of its target to the dual of its source, and reverses
identity and composition. Crossing the differentials twice therefore lands back at the original
curvature, with the negated double transposes as the differentials of a double dual, and the two
evaluations identify a double dual with the original duplex.

The two differential equations of the dual are the crossed-transpose computations
`FGModuleCat.negDualMap_comp_dualMap` and `FGModuleCat.dualMap_negDualMap`, the two placements of
the minus sign between the crossed transposes, and the two differential equations of the double
dual are its one-dual-further version `FGModuleCat.negDualMap_dualMap_comp_negDualMap_dualMap`.
Those three statements quantify over a curved pair of morphisms of `FGModuleCat`, so the curvature
is part of their hypothesis, and the only places they are used are the differential equations of
the duals defined below. They are proved here, in the `FGModuleCat` namespace their statements
belong to and beside those constructions, rather than in the module-duality file, which knows
nothing about curvature.

## Main definitions

* `CurvedDuplex.dual`: the dual of a curved duplex with projective components, of curvature `-w`.
* `CurvedDuplex.dualMap`: the dual of a morphism of curved duplexes, contravariantly.
* `CurvedDuplex.doubleDual`, `CurvedDuplex.doubleDualIso`: the double dual, of the original
  curvature, and its isomorphism with the original duplex.

## Main results

* `CurvedDuplex.dual_d₀`, `CurvedDuplex.dual_d₁`: the crossed transposed differentials.
* `CurvedDuplex.dualMap_f₀`, `CurvedDuplex.dualMap_f₁`: the components of a dual morphism are the
  transposes of the components; `CurvedDuplex.dualMap` itself is not exposed.
* `CurvedDuplex.dualMap_id`, `CurvedDuplex.dualMap_comp`, `CurvedDuplex.dualMap_zero`,
  `CurvedDuplex.dualMap_add`: the dual of a morphism reverses identity and composition and is
  additive, which is what makes duality contravariant.
* `FGModuleCat.negDualMap_comp_dualMap`, `FGModuleCat.dualMap_negDualMap`: the composite of the
  crossed transposes of a curved pair of morphisms, with the single minus sign on either of them,
  is multiplication by `-w` on the dual. These are the two differential equations of
  `CurvedDuplex.dual`.
* `FGModuleCat.negDualMap_dualMap_comp_negDualMap_dualMap`: the same computation one dual further,
  for the two negated double transposes, which is the original curvature again. This is what makes
  the two differential equations of `CurvedDuplex.doubleDual` hold.
* `CurvedDuplex.doubleDual_d₀`, `CurvedDuplex.doubleDual_d₁`: the negated double transposes.
* `CurvedDuplex.doubleDualIso`, `CurvedDuplex.doubleDualIso_f₀`, `CurvedDuplex.doubleDualIso_f₁`:
  a double dual is isomorphic to the original curved duplex, by the evaluation pairing with the
  single minus sign on the even component.
-/

public section

universe u

open CategoryTheory Category Preadditive Module

/-! ### Crossed-transpose curvature equations

The three statements below are the differential equations of the duals defined in this file, and
they are proved here rather than in `TauCeti.Algebra.Category.FGModuleCat.Dual`: each of them
quantifies over a *curved pair* of morphisms, so the curvature is part of its hypothesis, and the
only places they are used are the `d₀_comp_d₁` and `d₁_comp_d₀` fields of the duals below. They
are stated in the `FGModuleCat` namespace, which is the namespace their statements belong to. -/

namespace FGModuleCat

variable (R : Type u) [CommRing R]

/-- For a curved pair of maps `f` and `g` with `f ≫ g = w • 𝟙`, the composite of the negated
transpose of `g` with the transpose of `f` is multiplication by `-w` on the dual. This is one of
the two differential equations of a dual of curvature `-w`, the one in which the minus sign sits
on the left-hand factor of the composite; `FGModuleCat.dualMap_negDualMap` is the same
calculation with the minus sign on the right-hand factor. -/
theorem negDualMap_comp_dualMap {M N : FGModuleCat.{u} R} [Module.Projective R M]
    [Module.Projective R N] (w : R) (f : M ⟶ N) (g : N ⟶ M) (h : f ≫ g = w • 𝟙 M) :
    ((-FGModuleCat.dualMap g) ≫ FGModuleCat.dualMap f) = -w • 𝟙 (FGModuleCat.dual R M) := by
  calc (-FGModuleCat.dualMap g) ≫ FGModuleCat.dualMap f
      = -(FGModuleCat.dualMap g ≫ FGModuleCat.dualMap f) := by simp only [neg_comp]
    _ = -FGModuleCat.dualMap (f ≫ g) := by
      rw [FGModuleCat.dualMap_comp (f := f) (g := g)]
    _ = -FGModuleCat.dualMap (w • 𝟙 M) := by rw [h]
    _ = -(w • FGModuleCat.dualMap (𝟙 M)) := by rw [FGModuleCat.dualMap_smul]
    _ = -(w • 𝟙 (FGModuleCat.dual R M)) := by rw [FGModuleCat.dualMap_id]
    _ = -w • 𝟙 (FGModuleCat.dual R M) := by rw [neg_smul]

/-- The other placement of the minus sign: for a curved pair of maps `f` and `g` with
`f ≫ g = w • 𝟙`, the composite of the transpose of `g` with the negated transpose of `f` is
multiplication by `-w` on the dual. This is the other of the two differential equations of a
dual of curvature `-w`, the one in which the minus sign sits on the right-hand factor of the
composite. It is `FGModuleCat.negDualMap_comp_dualMap` read the other way round, since negating
either factor of a composite negates the composite. -/
theorem dualMap_negDualMap {M N : FGModuleCat.{u} R} [Module.Projective R M]
    [Module.Projective R N] (w : R) (f : M ⟶ N) (g : N ⟶ M) (h : f ≫ g = w • 𝟙 M) :
    (FGModuleCat.dualMap g ≫ (-FGModuleCat.dualMap f)) = -w • 𝟙 (FGModuleCat.dual R M) := by
  rw [Preadditive.comp_neg, ← Preadditive.neg_comp, negDualMap_comp_dualMap (R := R) w f g h]

/-- The same computation one dual further: the composite of the two negated double transposes of
a curved pair of maps is multiplication by the original `w` on the double dual. This is the
computation behind the two differential equations of a double dual, and the reason a double dual
has the same curvature as its source. -/
theorem negDualMap_dualMap_comp_negDualMap_dualMap {M N : FGModuleCat.{u} R}
    [Module.Projective R M] [Module.Projective R N] (w : R) (f : M ⟶ N) (g : N ⟶ M)
    (h : f ≫ g = w • 𝟙 M) :
    ((-FGModuleCat.dualMap (FGModuleCat.dualMap f)) ≫
      (-FGModuleCat.dualMap (FGModuleCat.dualMap g)))
      = w • 𝟙 (FGModuleCat.dual R (FGModuleCat.dual R M)) := by
  calc (-FGModuleCat.dualMap (FGModuleCat.dualMap f)) ≫
        (-FGModuleCat.dualMap (FGModuleCat.dualMap g))
      = FGModuleCat.dualMap (FGModuleCat.dualMap f) ≫
          FGModuleCat.dualMap (FGModuleCat.dualMap g) := by
            rw [Preadditive.neg_comp_neg]
    _ = FGModuleCat.dualMap (FGModuleCat.dualMap (f ≫ g)) := by
      rw [← FGModuleCat.dualMap_comp, ← FGModuleCat.dualMap_comp]
    _ = FGModuleCat.dualMap (FGModuleCat.dualMap (w • 𝟙 M)) := by rw [h]
    _ = w • FGModuleCat.dualMap (FGModuleCat.dualMap (𝟙 M)) := by
      simp only [FGModuleCat.dualMap_smul]
    _ = w • 𝟙 (FGModuleCat.dual R (FGModuleCat.dual R M)) := by
      rw [FGModuleCat.dualMap_id, FGModuleCat.dualMap_id]

end FGModuleCat

namespace TauCeti

variable (S : Type u) [CommRing S] (w : S)

namespace CurvedDuplex

variable {S w}

/-- The dual of a curved duplex with projective components is a curved duplex of the negated
curvature whose differentials are the crossed transposes, the minus sign on the second. -/
abbrev dual (X : CurvedDuplex (FGModuleCat.{u} S) w) [Module.Projective S X.X₀]
    [Module.Projective S X.X₁] : CurvedDuplex (FGModuleCat.{u} S) (-w) where
  X₀ := FGModuleCat.dual S X.X₀
  X₁ := FGModuleCat.dual S X.X₁
  d₀ := FGModuleCat.dualMap X.d₁
  d₁ := -FGModuleCat.dualMap X.d₀
  d₀_comp_d₁ := FGModuleCat.dualMap_negDualMap S w X.d₀ X.d₁ X.d₀_comp_d₁
  d₁_comp_d₀ := FGModuleCat.negDualMap_comp_dualMap S w X.d₁ X.d₀ X.d₁_comp_d₀

/-- The even component of a dual curved duplex is the dual of the even component. -/
@[simp] theorem dual_X₀ (X : CurvedDuplex (FGModuleCat.{u} S) w) [Module.Projective S X.X₀]
    [Module.Projective S X.X₁] : X.dual.X₀ = FGModuleCat.dual S X.X₀ := rfl

/-- The odd component of a dual curved duplex is the dual of the odd component. -/
@[simp] theorem dual_X₁ (X : CurvedDuplex (FGModuleCat.{u} S) w) [Module.Projective S X.X₀]
    [Module.Projective S X.X₁] : X.dual.X₁ = FGModuleCat.dual S X.X₁ := rfl

/-- The even differential of a dual is the transpose of the *odd* differential of the original.
The differentials are crossed because transposition reverses composition, so that the two
composites of the dual are the transposes of the two composites of the original. -/
@[simp] theorem dual_d₀ (X : CurvedDuplex (FGModuleCat.{u} S) w) [Module.Projective S X.X₀]
    [Module.Projective S X.X₁] : X.dual.d₀ = FGModuleCat.dualMap X.d₁ := rfl

/-- The odd differential of a dual is the negated transpose of the even differential of the
original. The single minus sign is what turns a curvature `w` into a curvature `-w`. -/
@[simp] theorem dual_d₁ (X : CurvedDuplex (FGModuleCat.{u} S) w) [Module.Projective S X.X₀]
    [Module.Projective S X.X₁] : X.dual.d₁ = -FGModuleCat.dualMap X.d₀ := rfl

/-- The dual of a morphism of curved duplexes is a morphism from the dual of the target to the
dual of the source, with transposed components. The two commutativity conditions of `f` enter
with the two differentials exchanged, which is what the crossed transposes need. -/
def dualMap {X Y : CurvedDuplex (FGModuleCat.{u} S) w} [Module.Projective S X.X₀]
    [Module.Projective S X.X₁] [Module.Projective S Y.X₀] [Module.Projective S Y.X₁] (f : X ⟶ Y) :
    Y.dual ⟶ X.dual :=
  homMk (FGModuleCat.dualMap f.f₀) (FGModuleCat.dualMap f.f₁)
    (by rw [← FGModuleCat.dualMap_comp, ← FGModuleCat.dualMap_comp, f.comm₁])
    (by
      simp only [comp_neg, neg_comp]
      rw [← FGModuleCat.dualMap_comp, ← FGModuleCat.dualMap_comp, f.comm₀])

/-- The even component of the dual of a morphism of curved duplexes is the transpose of the even
component of the morphism. -/
@[simp] theorem dualMap_f₀ {X Y : CurvedDuplex (FGModuleCat.{u} S) w} [Module.Projective S X.X₀]
    [Module.Projective S X.X₁] [Module.Projective S Y.X₀] [Module.Projective S Y.X₁] (f : X ⟶ Y) :
    (dualMap f).f₀ = FGModuleCat.dualMap f.f₀ := (rfl)

/-- The odd component of the dual of a morphism of curved duplexes is the transpose of the odd
component of the morphism. -/
@[simp] theorem dualMap_f₁ {X Y : CurvedDuplex (FGModuleCat.{u} S) w} [Module.Projective S X.X₀]
    [Module.Projective S X.X₁] [Module.Projective S Y.X₀] [Module.Projective S Y.X₁] (f : X ⟶ Y) :
    (dualMap f).f₁ = FGModuleCat.dualMap f.f₁ := (rfl)

/-- Dualization is contravariant on morphisms: the dual of the identity of a curved duplex
is the identity of its dual. -/
@[simp] theorem dualMap_id (X : CurvedDuplex (FGModuleCat.{u} S) w) [Module.Projective S X.X₀]
    [Module.Projective S X.X₁] :
    dualMap (𝟙 X) = 𝟙 X.dual :=
  hom_ext ((CurvedDuplex.dualMap_f₀ (𝟙 X)).trans (by simp))
    ((CurvedDuplex.dualMap_f₁ (𝟙 X)).trans (by simp))

/-- Dualization is contravariant on morphisms: the dual of a composite is the composite of
the duals in the opposite order. -/
@[simp] theorem dualMap_comp {X Y Z : CurvedDuplex (FGModuleCat.{u} S) w} [Module.Projective S X.X₀]
    [Module.Projective S X.X₁] [Module.Projective S Y.X₀] [Module.Projective S Y.X₁]
    [Module.Projective S Z.X₀] [Module.Projective S Z.X₁] (f : X ⟶ Y) (g : Y ⟶ Z) :
    dualMap (f ≫ g) = dualMap g ≫ dualMap f := by
  refine hom_ext ?_ ?_
  · exact FGModuleCat.dualMap_comp f.f₀ g.f₀
  · exact FGModuleCat.dualMap_comp f.f₁ g.f₁

/-- Dualization is contravariant on morphisms and additive: the dual of the zero morphism of a
curved duplex is the zero morphism of its dual. -/
@[simp] theorem dualMap_zero (X Y : CurvedDuplex (FGModuleCat.{u} S) w) [Module.Projective S X.X₀]
    [Module.Projective S X.X₁] [Module.Projective S Y.X₀] [Module.Projective S Y.X₁] :
    dualMap (0 : X ⟶ Y) = 0 :=
  hom_ext (by simp) (by simp)

/-- Dualization is contravariant on morphisms and additive: the dual of a sum of morphisms of
curved duplexes is the sum of the duals. -/
@[simp] theorem dualMap_add {X Y : CurvedDuplex (FGModuleCat.{u} S) w} [Module.Projective S X.X₀]
    [Module.Projective S X.X₁] [Module.Projective S Y.X₀] [Module.Projective S Y.X₁]
    (f g : X ⟶ Y) :
    dualMap (f + g) = dualMap f + dualMap g :=
  hom_ext (by simp) (by simp)

/-- The double dual of a curved duplex is a curved duplex of the *same* curvature: each of its
differentials is the negated double transpose of the corresponding differential of the original,
and the two minus signs cancel when the differentials are composed, so the composite is
multiplication by `w` again. The evaluation pairing with the single minus sign on the even
component identifies it with the original duplex, as `CurvedDuplex.doubleDualIso` records. -/
abbrev doubleDual (X : CurvedDuplex (FGModuleCat.{u} S) w) [Module.Projective S X.X₀]
    [Module.Projective S X.X₁] : CurvedDuplex (FGModuleCat.{u} S) w where
  X₀ := FGModuleCat.dual S (FGModuleCat.dual S X.X₀)
  X₁ := FGModuleCat.dual S (FGModuleCat.dual S X.X₁)
  d₀ := -FGModuleCat.dualMap (FGModuleCat.dualMap X.d₀)
  d₁ := -FGModuleCat.dualMap (FGModuleCat.dualMap X.d₁)
  d₀_comp_d₁ :=
    FGModuleCat.negDualMap_dualMap_comp_negDualMap_dualMap S w X.d₀ X.d₁ X.d₀_comp_d₁
  d₁_comp_d₀ :=
    FGModuleCat.negDualMap_dualMap_comp_negDualMap_dualMap S w X.d₁ X.d₀ X.d₁_comp_d₀

/-- The even component of a double dual is the double dual of the even component. -/
@[simp] theorem doubleDual_X₀ (X : CurvedDuplex (FGModuleCat.{u} S) w) [Module.Projective S X.X₀]
    [Module.Projective S X.X₁] :
    (X.doubleDual).X₀ = FGModuleCat.dual S (FGModuleCat.dual S X.X₀) := rfl

/-- The odd component of a double dual is the double dual of the odd component. -/
@[simp] theorem doubleDual_X₁ (X : CurvedDuplex (FGModuleCat.{u} S) w) [Module.Projective S X.X₀]
    [Module.Projective S X.X₁] :
    (X.doubleDual).X₁ = FGModuleCat.dual S (FGModuleCat.dual S X.X₁) := rfl

/-- The even differential of a double dual is the negated double transpose of the even
differential of the original. Crossing twice no longer swaps the two components, and the two
minus signs cancel when the differentials are composed, so the curvature is `w` again. -/
@[simp] theorem doubleDual_d₀ (X : CurvedDuplex (FGModuleCat.{u} S) w) [Module.Projective S X.X₀]
    [Module.Projective S X.X₁] :
    (X.doubleDual).d₀ = -FGModuleCat.dualMap (FGModuleCat.dualMap X.d₀) := rfl

/-- The odd differential of a double dual is the negated double transpose of the odd
differential of the original, with the sign on the odd component. -/
@[simp] theorem doubleDual_d₁ (X : CurvedDuplex (FGModuleCat.{u} S) w) [Module.Projective S X.X₀]
    [Module.Projective S X.X₁] :
    (X.doubleDual).d₁ = -FGModuleCat.dualMap (FGModuleCat.dualMap X.d₁) := rfl

/-- A double dual is isomorphic to the original curved duplex. The isomorphism is the evaluation
pairing, with the single minus sign on the even component: that is the placement which makes the
two commutativity conditions hold against the negated double transposes. -/
noncomputable def doubleDualIso (X : CurvedDuplex (FGModuleCat.{u} S) w)
    [Module.Projective S X.X₀] [Module.Projective S X.X₁] : X.doubleDual ≅ X :=
  isoMk
    { hom := -(FGModuleCat.dualEvalIso X.X₀).hom
      inv := -(FGModuleCat.dualEvalIso X.X₀).inv
      hom_inv_id := by
        simp only [Preadditive.neg_comp_neg, (FGModuleCat.dualEvalIso X.X₀).hom_inv_id]
      inv_hom_id := by
        simp only [Preadditive.neg_comp_neg, (FGModuleCat.dualEvalIso X.X₀).inv_hom_id] }
    { hom := (FGModuleCat.dualEvalIso X.X₁).hom
      inv := (FGModuleCat.dualEvalIso X.X₁).inv
      hom_inv_id := by
        exact (FGModuleCat.dualEvalIso X.X₁).hom_inv_id
      inv_hom_id := by
        exact (FGModuleCat.dualEvalIso X.X₁).inv_hom_id }
    (by rw [neg_comp, neg_comp, FGModuleCat.dualEvalIso_hom_naturality])
    (by rw [Preadditive.neg_comp_neg, FGModuleCat.dualEvalIso_hom_naturality])

/-- The even component of the double dual isomorphism is the negated evaluation isomorphism. -/
@[simp] theorem doubleDualIso_f₀ (X : CurvedDuplex (FGModuleCat.{u} S) w)
    [Module.Projective S X.X₀] [Module.Projective S X.X₁] :
    (X.doubleDualIso).hom.f₀ = -(FGModuleCat.dualEvalIso X.X₀).hom := (rfl)

/-- The odd component of the double dual isomorphism is the evaluation isomorphism. -/
@[simp] theorem doubleDualIso_f₁ (X : CurvedDuplex (FGModuleCat.{u} S) w)
    [Module.Projective S X.X₀] [Module.Projective S X.X₁] :
    (X.doubleDualIso).hom.f₁ = (FGModuleCat.dualEvalIso X.X₁).hom := (rfl)

/-- The even component of the inverse of the double dual isomorphism is the negated inverse
evaluation isomorphism. -/
@[simp] theorem doubleDualIso_inv_f₀ (X : CurvedDuplex (FGModuleCat.{u} S) w)
    [Module.Projective S X.X₀] [Module.Projective S X.X₁] :
    (X.doubleDualIso).inv.f₀ = -(FGModuleCat.dualEvalIso X.X₀).inv := (rfl)

/-- The odd component of the inverse of the double dual isomorphism is the inverse evaluation
isomorphism. -/
@[simp] theorem doubleDualIso_inv_f₁ (X : CurvedDuplex (FGModuleCat.{u} S) w)
    [Module.Projective S X.X₀] [Module.Projective S X.X₁] :
    (X.doubleDualIso).inv.f₁ = (FGModuleCat.dualEvalIso X.X₁).inv := (rfl)


end CurvedDuplex

end TauCeti
