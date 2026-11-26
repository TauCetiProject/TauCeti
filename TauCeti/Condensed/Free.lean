/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.Condensed.Functors
public import Mathlib.Condensed.Module

/-!
# Maps out of free condensed modules on profinite sets

For a profinite set `S`, the free condensed `R`-module `R[S]` on the condensed set represented by
`S` corepresents sections over `S`: by the free-forgetful adjunction and the Yoneda lemma for
sheaves, morphisms `R[S] ⟶ M` correspond to elements of `M(S)`
(`Profinite.freeModuleHomEquiv`), naturally in `S` (`Profinite.freeModuleHomEquiv_comp`) and in
`M` (`Profinite.freeModuleHomEquiv_postcomp`). This is
the analogue for condensed modules of `LightProfinite.freeModuleHomEquiv`.
-/

public section

universe u

open CategoryTheory Opposite Condensed

namespace Profinite

variable {R : Type (u + 1)} [Ring R] {M : CondensedMod.{u} R}

/-- Maps from the free condensed module on a profinite set `S` correspond to sections over `S`. -/
noncomputable def freeModuleHomEquiv (S : Profinite.{u}) :
    ((free R).obj S.toCondensed ⟶ M) ≃ M.obj.obj (op (profiniteToCompHaus.obj S)) :=
  ((freeForgetAdjunction R).homEquiv _ _).trans (coherentTopology CompHaus).uliftYonedaEquiv.{u + 1}

/-- Precomposing with the free map induced by `f : S ⟶ T` restricts a section on `T` to `S` along
`f`. -/
theorem freeModuleHomEquiv_comp {S T : Profinite.{u}} (f : S ⟶ T)
    (g : (free R).obj T.toCondensed ⟶ M) :
    S.freeModuleHomEquiv ((free R).map (profiniteToCondensed.map f) ≫ g) =
      M.obj.map (profiniteToCompHaus.map f).op (T.freeModuleHomEquiv g) :=
  -- `profiniteToCondensed` is by definition the ulifted Yoneda sheaf functor on `CompHaus`,
  -- restricted to profinite sets.
  (congrArg (coherentTopology CompHaus).uliftYonedaEquiv.{u + 1}
    ((freeForgetAdjunction R).homEquiv_naturality_left (profiniteToCondensed.map f) g)).trans
    ((coherentTopology CompHaus).uliftYonedaEquiv_naturality _ _).symm

/-- Postcomposing with a morphism of condensed modules applies its component over `S` to the
corresponding section. -/
theorem freeModuleHomEquiv_postcomp {N : CondensedMod.{u} R} (S : Profinite.{u})
    (g : (free R).obj S.toCondensed ⟶ M) (f : M ⟶ N) :
    S.freeModuleHomEquiv (g ≫ f) = f.hom.app _ (S.freeModuleHomEquiv g) :=
  congrArg (coherentTopology CompHaus).uliftYonedaEquiv.{u + 1}
    ((freeForgetAdjunction R).homEquiv_naturality_right g f)

end Profinite
