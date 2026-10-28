/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Linear.Biproduct
public import TauCeti.CategoryTheory.Semisimple.Multiplicity

/-!
# Hom dimensions in a split finite semisimple category

Over an algebraically closed field, Schur's lemma identifies the multiplicity of a simple object
in a finite semisimple category with the dimension of the corresponding Hom space. Both
orientations are recorded: morphisms from the simple object and morphisms to it have the same
dimension, equal to its decomposition multiplicity.

The algebraic-closedness and finite-dimensionality assumptions are essential. Over a nonsplit
field, the endomorphism division algebra of a simple object can have dimension greater than one,
so the dimension of its Hom space need not equal its decomposition multiplicity.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti

universe v u w

variable (k : Type w) [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [Abelian C] [Linear k C]
  [IsFiniteSemisimpleCategory C] [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]

attribute [local instance] Abelian.hasFiniteBiproducts

/-- The dimension of the morphisms from a simple object to an object is the multiplicity of that
simple object in the target. -/
@[simp]
theorem finrank_hom_simple_eq_simpleMultiplicities (S X : C) [Simple S] :
    Module.finrank k (S ⟶ X) = simpleMultiplicities X (SimpleClasses.classOf S) := by
  classical
  obtain ⟨ι, hι, f, hf, hbf, ⟨e⟩⟩ :=
    IsFiniteSemisimpleCategory.exists_biproduct_simples X
  let := hι
  let := hf
  let := hbf
  rw [simpleMultiplicities_apply_classOf_eq_sum f e S,
    (CategoryTheory.Linear.homCongr k (Iso.refl S) e).finrank_eq,
    finrank_homTo_biproduct]
  simp_rw [CategoryTheory.finrank_hom_simple_simple]

/-- The dimension of the morphisms from an object to a simple object is the multiplicity of that
simple object in the source. -/
@[simp]
theorem finrank_homTo_simple_eq_simpleMultiplicities (X S : C) [Simple S] :
    Module.finrank k (X ⟶ S) = simpleMultiplicities X (SimpleClasses.classOf S) := by
  classical
  obtain ⟨ι, hι, f, hf, hbf, ⟨e⟩⟩ :=
    IsFiniteSemisimpleCategory.exists_biproduct_simples X
  let := hι
  let := hf
  let := hbf
  rw [simpleMultiplicities_apply_classOf_eq_sum f e S,
    (CategoryTheory.Linear.homCongr k e (Iso.refl S)).finrank_eq,
    finrank_hom_biproduct]
  simp_rw [CategoryTheory.finrank_hom_simple_simple]
  simp only [Iso.nonempty_iso_symm]

end TauCeti
