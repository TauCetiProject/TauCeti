/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.DoldKan.FunctorGamma

/-!
# The functor `Γ₀` on the summands of its splitting

The simplicial object `Γ₀.obj K` attached to a chain complex `K` comes with a splitting
`Γ₀.splitting K` whose summand indexed by an epimorphism `[m] ⟶ [k]` is `K.X k`. The map of
simplicial objects induced by a chain map `f : K ⟶ K'` acts on each summand by the component of
`f` in the corresponding degree (`AlgebraicTopology.DoldKan.Γ₀.map_app_on_summand`).
-/

public section

open CategoryTheory Limits SimplicialObject

namespace AlgebraicTopology.DoldKan.Γ₀

variable {C : Type*} [Category* C] [Preadditive C] [HasFiniteCoproducts C]

/-- On the summand of `Γ₀.obj K` indexed by `A`, the map induced by a chain map `f : K ⟶ K'` is
the component of `f` in degree `A.1.unop.len`, followed by the inclusion of the summand of
`Γ₀.obj K'` indexed by `A`. -/
@[reassoc]
lemma map_app_on_summand {K K' : ChainComplex C ℕ} (f : K ⟶ K') (Δ : SimplexCategoryᵒᵖ)
    (A : Splitting.IndexSet Δ) :
    ((Γ₀.splitting K).cofan Δ).inj A ≫ ((Γ₀ : ChainComplex C ℕ ⥤ _).map f).app Δ =
      f.f A.1.unop.len ≫ ((Γ₀.splitting K').cofan Δ).inj A :=
  Splitting.ι_desc _ _ _ _

end AlgebraicTopology.DoldKan.Γ₀
