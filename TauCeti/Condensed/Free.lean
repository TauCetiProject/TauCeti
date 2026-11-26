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
(`Profinite.freeModuleHomEquiv`, computed by `Profinite.freeModuleHomEquiv_apply`), naturally in
`S` (`Profinite.freeModuleHomEquiv_comp`) and in `M` (`Profinite.freeModuleHomEquiv_postcomp`).
This is the analogue for condensed modules of `LightProfinite.freeModuleHomEquiv`.
-/

public section

universe u

open CategoryTheory Opposite Condensed

namespace Profinite

variable {R : Type (u + 1)} [Ring R] {M : CondensedMod.{u} R}

/-- The underlying equivalence of `Profinite.freeModuleHomEquiv`: the free-forgetful adjunction
followed by the Yoneda lemma for sheaves. -/
private noncomputable def freeModuleHomEquivAux (S : Profinite.{u}) :
    ((free R).obj S.toCondensed ⟶ M) ≃ M.obj.obj (op (profiniteToCompHaus.obj S)) :=
  ((freeForgetAdjunction R).homEquiv _ _).trans (coherentTopology CompHaus).uliftYonedaEquiv.{u + 1}

private theorem freeModuleHomEquivAux_postcomp {N : CondensedMod.{u} R} (S : Profinite.{u})
    (g : (free R).obj S.toCondensed ⟶ M) (f : M ⟶ N) :
    S.freeModuleHomEquivAux (g ≫ f) = f.hom.app _ (S.freeModuleHomEquivAux g) :=
  congrArg (coherentTopology CompHaus).uliftYonedaEquiv.{u + 1}
    ((freeForgetAdjunction R).homEquiv_naturality_right g f)

/-- Maps from the free condensed module on a profinite set `S` correspond to sections over `S`. -/
noncomputable def freeModuleHomEquiv (S : Profinite.{u}) :
    ((free R).obj S.toCondensed ⟶ M) ≃+ M.obj.obj (op (profiniteToCompHaus.obj S)) where
  __ := S.freeModuleHomEquivAux
  map_add' g g' := by
    -- Every map is the identity of `R[S]` followed by itself, and the component over `S` of a sum
    -- of morphisms is the sum of the components.
    have h (φ : (free R).obj S.toCondensed ⟶ M) :
        S.freeModuleHomEquivAux φ = φ.hom.app _ (S.freeModuleHomEquivAux (𝟙 _)) := by
      rw [← freeModuleHomEquivAux_postcomp, Category.id_comp]
    simp only [Equiv.toFun_as_coe, h (g + g'), h g, h g', Sheaf.Hom.add_app, ModuleCat.hom_add,
      LinearMap.add_apply]

/-- The section corresponding to a map from the free condensed module is obtained from the
free-forgetful adjunction followed by the Yoneda lemma for sheaves. -/
theorem freeModuleHomEquiv_apply (S : Profinite.{u}) (g : (free R).obj S.toCondensed ⟶ M) :
    S.freeModuleHomEquiv g = (coherentTopology CompHaus).uliftYonedaEquiv.{u + 1}
      ((freeForgetAdjunction R).homEquiv _ _ g) :=
  (rfl)

/-- Precomposing with the free map induced by `f : S ⟶ T` restricts a section on `T` to `S` along
`f`. -/
@[simp↓] -- Prefer restriction to coefficient naturality on this composite.
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
@[simp]
theorem freeModuleHomEquiv_postcomp {N : CondensedMod.{u} R} (S : Profinite.{u})
    (g : (free R).obj S.toCondensed ⟶ M) (f : M ⟶ N) :
    S.freeModuleHomEquiv (g ≫ f) = f.hom.app _ (S.freeModuleHomEquiv g) :=
  S.freeModuleHomEquivAux_postcomp g f

/-- The map corresponding to the restriction along `f : S ⟶ T` of a section on `T` is the free map
induced by `f` followed by the map corresponding to that section. -/
theorem freeModuleHomEquiv_symm_comp {S T : Profinite.{u}} (f : S ⟶ T)
    (s : M.obj.obj (op (profiniteToCompHaus.obj T))) :
    S.freeModuleHomEquiv.symm (M.obj.map (profiniteToCompHaus.map f).op s) =
      (free R).map (profiniteToCondensed.map f) ≫ T.freeModuleHomEquiv.symm s := by
  rw [AddEquiv.symm_apply_eq, freeModuleHomEquiv_comp, AddEquiv.apply_symm_apply]

/-- Postcomposing the map corresponding to a section applies the morphism of condensed modules. -/
@[simp]
theorem freeModuleHomEquiv_symm_postcomp {N : CondensedMod.{u} R} (S : Profinite.{u})
    (s : M.obj.obj (op (profiniteToCompHaus.obj S))) (f : M ⟶ N) :
    S.freeModuleHomEquiv.symm (f.hom.app _ s) = S.freeModuleHomEquiv.symm s ≫ f := by
  rw [AddEquiv.symm_apply_eq, freeModuleHomEquiv_postcomp, AddEquiv.apply_symm_apply]

end Profinite
