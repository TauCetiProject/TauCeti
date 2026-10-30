/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Compactification.Basic

/-!
# Products of scheme compactifications over a base

Given compactifications of `f : X ⟶ S` and `g : Y ⟶ S`, their ambient fibre product
compactifies `X ×_S Y ⟶ S`. The interior is the product of the two quasi-compact open
immersions. This construction is functorial in refinement maps in both variables, as
`Compactification.prodFunctor`.

These are products of two different morphisms over a common base, not categorical products
in the category of compactifications of one fixed morphism. No density is asserted: products
over a base need not preserve scheme-theoretic density without further hypotheses.
The construction supplies product compactification diagrams for proper-support functors.

## References

* The Stacks Project, Section 38.32, *Compactifications* (tag 0ATT).
* The constructions use the compactification carrier in
  `TauCeti.AlgebraicGeometry.Compactification.Basic` and Mathlib's
  `CategoryTheory.MorphismProperty.pullbackMap`.
-/

public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace TauCeti.Compactification

variable {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}

noncomputable section

/-- The product over `S` of two compactifications, compactifying `X ×_S Y ⟶ S`.
No density hypothesis on either compactification is needed. -/
-- The ambient scheme and maps must compute when elaborating the dependent projection formulas.
@[expose, implicit_reducible]
def prod (C : Compactification f) (D : Compactification g) :
    Compactification (pullback.fst f g ≫ f) := by
  let j := pullback.map f g C.p D.p C.j D.j (𝟙 S) (by simp) (by simp)
  have hj : IsOpenImmersion j :=
    MorphismProperty.pullbackMap (P := @IsOpenImmersion) inferInstance inferInstance
      C.obj.ι_π.symm D.obj.ι_π.symm
  have hqc : QuasiCompact j :=
    MorphismProperty.pullbackMap (P := @QuasiCompact) inferInstance inferInstance
      C.obj.ι_π.symm D.obj.ι_π.symm
  exact ofHom j (pullback.fst C.p D.p ≫ C.p) (by simp [j])

@[simp]
theorem prod_Xbar (C : Compactification f) (D : Compactification g) :
    (C.prod D).Xbar = pullback C.p D.p :=
  (rfl)

theorem prod_j (C : Compactification f) (D : Compactification g) :
    (C.prod D).j = pullback.map f g C.p D.p C.j D.j (𝟙 S) (by simp) (by simp) :=
  (rfl)

@[simp]
theorem prod_p (C : Compactification f) (D : Compactification g) :
    (C.prod D).p = pullback.fst C.p D.p ≫ C.p :=
  (rfl)

/-- The first ambient projection restricts to the first projection on the interiors. -/
@[reassoc (attr := simp)]
theorem prod_j_fst (C : Compactification f) (D : Compactification g) :
    (C.prod D).j ≫ pullback.fst C.p D.p = pullback.fst f g ≫ C.j := by
  simp [prod_j]

/-- The second ambient projection restricts to the second projection on the interiors. -/
@[reassoc (attr := simp)]
theorem prod_j_snd (C : Compactification f) (D : Compactification g) :
    (C.prod D).j ≫ pullback.snd C.p D.p = pullback.snd f g ≫ D.j := by
  simp [prod_j]

/-- The refinement of product compactifications induced by refinements of both factors. -/
def prodMap {C₁ C₂ : Compactification f} {D₁ D₂ : Compactification g}
    (h : C₁ ⟶ C₂) (k : D₁ ⟶ D₂) : C₁.prod D₁ ⟶ C₂.prod D₂ :=
  ObjectProperty.homMk
    { h := pullback.map C₁.p D₁.p C₂.p D₂.p h.hom.h k.hom.h (𝟙 S)
        (by simp) (by simp)
      ι_h := by
        apply pullback.hom_ext <;> simp [Category.assoc]
      h_π := by simp }

theorem prodMap_hom_h {C₁ C₂ : Compactification f} {D₁ D₂ : Compactification g}
    (h : C₁ ⟶ C₂) (k : D₁ ⟶ D₂) :
    (prodMap h k).hom.h =
      pullback.map C₁.p D₁.p C₂.p D₂.p h.hom.h k.hom.h (𝟙 S) (by simp) (by simp) :=
  (rfl)

/-- The product refinement commutes with the first ambient projection. -/
@[reassoc (attr := simp)]
theorem prodMap_fst {C₁ C₂ : Compactification f} {D₁ D₂ : Compactification g}
    (h : C₁ ⟶ C₂) (k : D₁ ⟶ D₂) :
    (prodMap h k).hom.h ≫ pullback.fst C₂.p D₂.p =
      pullback.fst C₁.p D₁.p ≫ h.hom.h := by
  simp [prodMap_hom_h]

/-- The product refinement commutes with the second ambient projection. -/
@[reassoc (attr := simp)]
theorem prodMap_snd {C₁ C₂ : Compactification f} {D₁ D₂ : Compactification g}
    (h : C₁ ⟶ C₂) (k : D₁ ⟶ D₂) :
    (prodMap h k).hom.h ≫ pullback.snd C₂.p D₂.p =
      pullback.snd C₁.p D₁.p ≫ k.hom.h := by
  simp [prodMap_hom_h]

@[simp]
theorem prodMap_id (C : Compactification f) (D : Compactification g) :
    prodMap (𝟙 C) (𝟙 D) = 𝟙 (C.prod D) := by
  apply ObjectProperty.hom_ext
  apply Factorisation.Hom.ext
  -- Normalize the identity map's dependent ambient scheme before categorical simplification.
  dsimp only [prod, ofHom]
  apply pullback.hom_ext <;> simp

@[simp]
theorem prodMap_comp {C₁ C₂ C₃ : Compactification f} {D₁ D₂ D₃ : Compactification g}
    (h₁ : C₁ ⟶ C₂) (h₂ : C₂ ⟶ C₃) (k₁ : D₁ ⟶ D₂) (k₂ : D₂ ⟶ D₃) :
    prodMap (h₁ ≫ h₂) (k₁ ≫ k₂) = prodMap h₁ k₁ ≫ prodMap h₂ k₂ := by
  apply ObjectProperty.hom_ext
  apply Factorisation.Hom.ext
  apply pullback.hom_ext <;> simp [Category.assoc]

/-- Product compactification is functorial in both refinement variables. -/
-- Expose the object assignment so morphism formulas have definitionally matching endpoints.
@[expose, implicit_reducible]
def prodFunctor : Compactification f × Compactification g ⥤
    Compactification (pullback.fst f g ≫ f) where
  obj C := C.1.prod C.2
  map h := prodMap h.1 h.2
  map_id C := prodMap_id C.1 C.2
  map_comp h k := prodMap_comp h.1 k.1 h.2 k.2

@[simp]
theorem prodFunctor_obj (C : Compactification f × Compactification g) :
    prodFunctor.obj C = C.1.prod C.2 :=
  (rfl)

@[simp]
theorem prodFunctor_map {C D : Compactification f × Compactification g} (h : C ⟶ D) :
    prodFunctor.map h = prodMap h.1 h.2 :=
  (rfl)

end

end TauCeti.Compactification
