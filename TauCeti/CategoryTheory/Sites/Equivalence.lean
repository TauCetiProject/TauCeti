/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Abelian

/-!
# Additivity of transport along an equivalence of sites

Transport is precomposition on the underlying presheaves, hence is additive for preadditive
coefficients. Both directions are available to consumers without file-local instances.
-/

public section

namespace CategoryTheory.Equivalence

universe v₁ v₂ v₃ u₁ u₂ u₃
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (e : C ≌ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (A : Type u₃) [Category.{v₃} A] [Preadditive A] [e.inverse.IsDenseSubsite K J]

/-- Transport of sheaves along a site equivalence is additive precomposition. -/
instance sheafCongr_functor_additive : (e.sheafCongr J K A).functor.Additive := by
  unfold Equivalence.sheafCongr Equivalence.sheafCongr.functor
  infer_instance

/-- Inverse site transport, as the functor of the inverse equivalence, is additive. -/
instance sheafCongr_symm_functor_additive : (e.sheafCongr J K A).symm.functor.Additive := by
  -- The functor of the inverse equivalence is its inverse functor.
  exact (Equivalence.inverse_additive _ : (e.sheafCongr J K A).inverse.Additive)

end CategoryTheory.Equivalence
