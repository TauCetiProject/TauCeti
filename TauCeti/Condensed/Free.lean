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
# Maps out of free condensed modules on compact Hausdorff spaces

For a compact Hausdorff space `S`, the free condensed `R`-module `R[S]` on the condensed set
represented by `S` corepresents sections over `S`: by the free-forgetful adjunction and the Yoneda
lemma for sheaves, morphisms `R[S] ⟶ M` correspond to elements of `M(S)`
(`CompHaus.freeModuleHomEquiv`, computed by `CompHaus.freeModuleHomEquiv_apply`), naturally in
`S` (`CompHaus.freeModuleHomEquiv_comp`) and in `M` (`CompHaus.freeModuleHomEquiv_postcomp`).
This is the analogue for condensed modules of `LightProfinite.freeModuleHomEquiv`.
-/

public section

universe u

open CategoryTheory Opposite Condensed

namespace CompHaus

variable {R : Type (u + 1)} [Ring R] {M : CondensedMod.{u} R}

/-- The underlying equivalence of `CompHaus.freeModuleHomEquiv`: the free-forgetful adjunction
followed by the Yoneda lemma for sheaves. -/
private noncomputable def freeModuleHomEquivAux (S : CompHaus.{u}) :
    ((free R).obj S.toCondensed ⟶ M) ≃ M.obj.obj (op S) :=
  ((freeForgetAdjunction R).homEquiv _ _).trans (coherentTopology CompHaus).uliftYonedaEquiv.{u + 1}

private theorem freeModuleHomEquivAux_postcomp {N : CondensedMod.{u} R} (S : CompHaus.{u})
    (g : (free R).obj S.toCondensed ⟶ M) (f : M ⟶ N) :
    S.freeModuleHomEquivAux (g ≫ f) = f.hom.app _ (S.freeModuleHomEquivAux g) :=
  congrArg (coherentTopology CompHaus).uliftYonedaEquiv.{u + 1}
    ((freeForgetAdjunction R).homEquiv_naturality_right g f)

/-- Maps from the free condensed module on a compact Hausdorff space `S` correspond to sections
over `S`. -/
noncomputable def freeModuleHomEquiv (S : CompHaus.{u}) :
    ((free R).obj S.toCondensed ⟶ M) ≃+ M.obj.obj (op S) where
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
theorem freeModuleHomEquiv_apply (S : CompHaus.{u}) (g : (free R).obj S.toCondensed ⟶ M) :
    S.freeModuleHomEquiv g = (coherentTopology CompHaus).uliftYonedaEquiv.{u + 1}
      ((freeForgetAdjunction R).homEquiv _ _ g) :=
  (rfl)

/-- Precomposing with the free map induced by `f : S ⟶ T` restricts a section on `T` to `S` along
`f`. -/
@[simp↓] -- Prefer restriction to coefficient naturality on this composite.
theorem freeModuleHomEquiv_comp {S T : CompHaus.{u}} (f : S ⟶ T)
    (g : (free R).obj T.toCondensed ⟶ M) :
    S.freeModuleHomEquiv ((free R).map (compHausToCondensed.map f) ≫ g) =
      M.obj.map f.op (T.freeModuleHomEquiv g) :=
  -- `compHausToCondensed` is by definition the ulifted Yoneda sheaf functor on `CompHaus`.
  (congrArg (coherentTopology CompHaus).uliftYonedaEquiv.{u + 1}
    ((freeForgetAdjunction R).homEquiv_naturality_left (compHausToCondensed.map f) g)).trans
    ((coherentTopology CompHaus).uliftYonedaEquiv_naturality _ _).symm

/-- Postcomposing with a morphism of condensed modules applies its component over `S` to the
corresponding section. -/
@[simp]
theorem freeModuleHomEquiv_postcomp {N : CondensedMod.{u} R} (S : CompHaus.{u})
    (g : (free R).obj S.toCondensed ⟶ M) (f : M ⟶ N) :
    S.freeModuleHomEquiv (g ≫ f) = f.hom.app _ (S.freeModuleHomEquiv g) :=
  S.freeModuleHomEquivAux_postcomp g f

/-- The map corresponding to the restriction along `f : S ⟶ T` of a section on `T` is the free map
induced by `f` followed by the map corresponding to that section. -/
theorem freeModuleHomEquiv_symm_comp {S T : CompHaus.{u}} (f : S ⟶ T)
    (s : M.obj.obj (op T)) :
    S.freeModuleHomEquiv.symm (M.obj.map f.op s) =
      (free R).map (compHausToCondensed.map f) ≫ T.freeModuleHomEquiv.symm s := by
  rw [AddEquiv.symm_apply_eq, freeModuleHomEquiv_comp, AddEquiv.apply_symm_apply]

/-- Postcomposing the map corresponding to a section applies the morphism of condensed modules. -/
@[simp]
theorem freeModuleHomEquiv_symm_postcomp {N : CondensedMod.{u} R} (S : CompHaus.{u})
    (s : M.obj.obj (op S)) (f : M ⟶ N) :
    S.freeModuleHomEquiv.symm (f.hom.app _ s) = S.freeModuleHomEquiv.symm s ≫ f := by
  rw [AddEquiv.symm_apply_eq, freeModuleHomEquiv_postcomp, AddEquiv.apply_symm_apply]

end CompHaus
