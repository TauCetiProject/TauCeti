/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-!
# Fundamental group path representatives

This file records small API lemmas for the path-homotopy-class representative of an element
of Mathlib's `FundamentalGroup`.
-/

namespace TauCeti

open FundamentalGroup

variable {X : Type*} [TopologicalSpace X] {x : X}

/-- The identity element of the fundamental group is represented by the constant path. -/
@[simp]
lemma fundamentalGroup_toPath_one :
    (1 : FundamentalGroup X x).toPath = Path.Homotopic.Quotient.refl x :=
  by
    -- `FundamentalGroup.toPath` is the endomorphism hom coerced through
    -- `End.asHom`; Mathlib has no named `toPath_one` lemma, so expose that
    -- definitional bridge before using the categorical identity lemma.
    change CategoryTheory.End.asHom
      (1 : CategoryTheory.End (FundamentalGroupoid.mk x)) =
      Path.Homotopic.Quotient.refl x
    rw [CategoryTheory.End.one_def, FundamentalGroupoid.id_eq_path_refl]
    -- The previous rewrite leaves the raw quotient constructor, while
    -- `Path.Homotopic.Quotient.refl` is a wrapper around the same class.
    change Path.Homotopic.Quotient.mk (Path.refl x) = Path.Homotopic.Quotient.refl x
    rw [Path.Homotopic.Quotient.mk_refl]

/-- Mathlib's multiplication convention for fundamental-group loops as path homotopy classes.

The fundamental group is the endomorphism group of a fundamental-groupoid object, so
multiplication follows categorical endomorphism multiplication. On path homotopy classes this
means `γ * δ` is represented by first traversing `δ`, then `γ`. -/
@[simp]
lemma fundamentalGroup_toPath_mul (γ δ : FundamentalGroup X x) :
    (γ * δ).toPath = Path.Homotopic.Quotient.trans δ.toPath γ.toPath :=
  by
    -- There is no named Mathlib lemma bridging `(γ * δ).toPath` to
    -- endomorphism multiplication, so first expose the underlying hom in the
    -- fundamental groupoid and then use the named category/path lemmas below.
    change (γ * δ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk x) =
      Path.Homotopic.Quotient.trans δ.toPath γ.toPath
    calc
      (γ * δ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk x)
          = CategoryTheory.CategoryStruct.comp
              (δ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk x)
              (γ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk x) := by
            exact CategoryTheory.End.mul_def
              (xs := (γ : CategoryTheory.End (FundamentalGroupoid.mk x)))
              (ys := (δ : CategoryTheory.End (FundamentalGroupoid.mk x)))
      _ = Path.Homotopic.Quotient.trans δ.toPath γ.toPath := by
            rw [FundamentalGroupoid.comp_eq]

end TauCeti
