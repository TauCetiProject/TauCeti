/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.CategoryTheory.Monoidal.Linear
public import TauCeti.CategoryTheory.Preadditive.Schur

/-!
# Scalars in a monoidal category

A *scalar* in a monoidal category `C` is an endomorphism `a : 𝟙_ C ⟶ 𝟙_ C` of the unit. Whiskering
an object by a scalar is compatible with every morphism to or from the unit: a scalar acting on
the unit factor of `Y ⊗ 𝟙_ C` can be moved past any morphism `Y ⊗ 𝟙_ C ⟶ 𝟙_ C`
(`TauCeti.whiskerLeft_scalar_comp`), and dually a scalar acting on the unit factor of `𝟙_ C ⊗ Y`
can be moved past any morphism `𝟙_ C ⟶ 𝟙_ C ⊗ Y` (`TauCeti.comp_scalar_whiskerRight`). In
particular scalars commute with each other (`TauCeti.scalar_comm`).

A scalar `a` acts on every object `Y` in two ways, from the left as
`(λ_ Y).inv ≫ a ▷ Y ≫ (λ_ Y).hom` and from the right as `(ρ_ Y).inv ≫ Y ◁ a ≫ (ρ_ Y).hom`. The two
actions need not agree in a general monoidal category, but they do in a braided one
(`TauCeti.leftUnitor_inv_scalar_whiskerRight_leftUnitor_hom`). They also agree in a linear one
over an algebraically closed field whose unit is simple with finite-dimensional endomorphisms,
where every scalar is a multiple of the identity
(`TauCeti.leftUnitor_inv_scalar_whiskerRight_leftUnitor_hom_of_simple`).
-/

public section

open CategoryTheory MonoidalCategory

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- A scalar acting on the unit factor of `Y ⊗ 𝟙_ C` can be moved past any morphism to the unit:
`Y ◁ a ≫ e = e ≫ a`. -/
@[reassoc]
theorem whiskerLeft_scalar_comp {Y : C} (a : 𝟙_ C ⟶ 𝟙_ C) (e : Y ⊗ 𝟙_ C ⟶ 𝟙_ C) :
    Y ◁ a ≫ e = e ≫ a := by
  -- On the unit, `a` is conjugate to `𝟙_ C ◁ a` by the right unitor, which commutes with `Y ◁ a`.
  have ha : a = (ρ_ (𝟙_ C)).inv ≫ 𝟙_ C ◁ a ≫ (ρ_ (𝟙_ C)).hom := by
    rw [← unitors_equal, ← unitors_inv_equal, leftUnitor_naturality, Iso.inv_hom_id_assoc]
  conv_rhs => rw [ha, rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc,
    rightUnitor_naturality]
  simp

/-- A scalar acting on the unit factor of `𝟙_ C ⊗ Y` can be moved past any morphism from the
unit: `e ≫ a ▷ Y = a ≫ e`. -/
@[reassoc]
theorem comp_scalar_whiskerRight {Y : C} (a : 𝟙_ C ⟶ 𝟙_ C) (e : 𝟙_ C ⟶ 𝟙_ C ⊗ Y) :
    e ≫ a ▷ Y = a ≫ e := by
  -- On the unit, `a` is conjugate to `a ▷ 𝟙_ C` by the left unitor, which commutes with `a ▷ Y`.
  have ha : a = (λ_ (𝟙_ C)).inv ≫ a ▷ 𝟙_ C ≫ (λ_ (𝟙_ C)).hom := by
    rw [unitors_equal, unitors_inv_equal, rightUnitor_naturality, Iso.inv_hom_id_assoc]
  conv_rhs => rw [ha, Category.assoc, Category.assoc, ← leftUnitor_naturality,
    ← whisker_exchange_assoc, ← leftUnitor_inv_naturality_assoc]
  simp

/-- **Scalars commute**: the endomorphisms of the unit form a commutative monoid. -/
theorem scalar_comm (a b : 𝟙_ C ⟶ 𝟙_ C) : a ≫ b = b ≫ a := by
  rw [← cancel_epi (λ_ (𝟙_ C)).hom, ← leftUnitor_naturality_assoc, unitors_equal,
    whiskerLeft_scalar_comp, Category.assoc]

/-- In a braided monoidal category, a scalar acts on every object in the same way from the left
and from the right. -/
theorem leftUnitor_inv_scalar_whiskerRight_leftUnitor_hom [BraidedCategory C]
    (a : 𝟙_ C ⟶ 𝟙_ C) (Y : C) :
    (λ_ Y).inv ≫ a ▷ Y ≫ (λ_ Y).hom = (ρ_ Y).inv ≫ Y ◁ a ≫ (ρ_ Y).hom := by
  -- The braiding `𝟙_ C ⊗ Y ≅ Y ⊗ 𝟙_ C` is natural and identifies the two unitors.
  rw [← braiding_rightUnitor, BraidedCategory.braiding_naturality_left_assoc,
    leftUnitor_inv_braiding_assoc]

/-- If the tensor unit is simple with finite-dimensional endomorphisms over an algebraically
closed field, a scalar acts on every object in the same way from the left and from the right. -/
theorem leftUnitor_inv_scalar_whiskerRight_leftUnitor_hom_of_simple (k : Type w) [Field k]
    [IsAlgClosed k] [Preadditive C] [MonoidalPreadditive C] [Linear k C] [MonoidalLinear k C]
    [Limits.HasKernels C] [Simple (𝟙_ C)] [FiniteDimensional k (𝟙_ C ⟶ 𝟙_ C)]
    (a : 𝟙_ C ⟶ 𝟙_ C) (Y : C) :
    (λ_ Y).inv ≫ a ▷ Y ≫ (λ_ Y).hom = (ρ_ Y).inv ≫ Y ◁ a ≫ (ρ_ Y).hom := by
  obtain ⟨c, rfl⟩ := endomorphism_simple_eq_smul_id k a
  simp

end TauCeti
