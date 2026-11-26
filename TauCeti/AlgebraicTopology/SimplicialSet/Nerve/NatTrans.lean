/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Homotopy
public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.StdSimplex
public import TauCeti.CategoryTheory.Functor.Currying

/-!
# The simplicial homotopy of nerves induced by a natural transformation

A natural transformation `η : F ⟶ G` between functors `F G : C ⥤ D` is the same as a functor
`[1] × C ⥤ D` restricting to `F` and `G` on the two ends, namely
`Functor.uncurry.obj (ComposableArrows.mk₁ η)`. Since `Δ[1]` is the nerve of `[1]` and the nerve
preserves products, its nerve is a simplicial homotopy `N C ⊗ Δ[1] ⟶ N D` from `nerveMap F` to
`nerveMap G` (`CategoryTheory.NatTrans.nerveHomotopy`): an `n`-simplex `(x, s)` of the cylinder,
a string `x` of `n` composable arrows of `C` together with a monotone map `s : [n] ⟶ [1]`, goes to
the string of `D` obtained by applying `F` at the positions where `s` is `0` and `G` where it is
`1`, joined by a component of `η`. Over a vertex `c` of `N C`, the homotopy moves along the edge
`η.app c` (`CategoryTheory.NatTrans.nerveHomotopy_h_app_verticalEdge`).

Realized, this is the homotopy of classifying spaces induced by a natural transformation.

## References

* D. Quillen, *Higher algebraic K-theory: I*, Lecture Notes in Math. 341 (1973), §1, Prop. 2.
* G. Segal, *Classifying spaces and spectral sequences*, Publ. Math. IHÉS 34 (1968), §2.
-/

public section

open CategoryTheory MonoidalCategory Simplicial SSet

universe v u

namespace CategoryTheory.NatTrans

variable {C D : Type u} [Category.{v} C] [Category.{v} D] {F G : C ⥤ D}

/-- On a simplex `(x, s)` of `N C ⊗ Δ[1]` with `N C`-coordinate `y` and whose `[1]`-coordinate is
constant at `b`, as on the ends `N C ⊗ {0}` and `N C ⊗ {1}` of the cylinder, the string of `D`
assigned by the homotopy induced by `η` is the image of `y` under the end `F` or `G` at `b`. -/
private lemma prod'_comp_uncurry_mk₁_of_asOrderHom_eq (η : F ⟶ G) {m : SimplexCategoryᵒᵖ}
    (x : (nerve C ⊗ Δ[1] : SSet.{max u v}).obj m) {y : (nerve C).obj m} (b : Fin 2)
    (hx : x.1 = y) (hb : ∀ k, stdSimplex.asOrderHom x.2 k = b) :
    (stdSimplex.asOrderHom x.2).monotone.functor.prod' x.1 ⋙
      Functor.uncurry.obj (ComposableArrows.mk₁ η) = y ⋙ (ComposableArrows.mk₁ η).obj b := by
  rw [stdSimplex.asOrderHom_monotone_functor_eq_const _ b hb, ← hx]
  exact Functor.const_obj_prod'_comp_uncurry_obj _ b x.1

/-- The simplicial homotopy from `nerveMap F` to `nerveMap G` induced by a natural transformation
`η : F ⟶ G`: the nerve of the functor `[1] × C ⥤ D` given by `η`, precomposed with the
identification of `N C ⊗ Δ[1]` with the nerve of `[1] × C`. -/
noncomputable def nerveHomotopy (η : F ⟶ G) : SSet.Homotopy (nerveMap F) (nerveMap G) :=
  SSet.Homotopy.mk'
    { app _ := ↾fun x ↦ (stdSimplex.asOrderHom x.2).monotone.functor.prod' x.1 ⋙
        Functor.uncurry.obj (ComposableArrows.mk₁ η)
      naturality _ _ _ := rfl }
    (by
      refine NatTrans.ext (funext fun ⟨⟨n⟩⟩ ↦ ConcreteCategory.hom_ext _ _ fun x ↦ ?_)
      rw [NatTrans.comp_app, ConcreteCategory.comp_apply]
      exact prod'_comp_uncurry_mk₁_of_asOrderHom_eq η _ 0 (ι₀_app_fst x) (ι₀_app_snd_apply x))
    (by
      refine NatTrans.ext (funext fun ⟨⟨n⟩⟩ ↦ ConcreteCategory.hom_ext _ _ fun x ↦ ?_)
      rw [NatTrans.comp_app, ConcreteCategory.comp_apply]
      exact prod'_comp_uncurry_mk₁_of_asOrderHom_eq η _ 1 (ι₁_app_fst x) (ι₁_app_snd_apply x))

/-- The homotopy induced by `η` sends an `n`-simplex `(x, s)` of `N C ⊗ Δ[1]` to the string of
composable arrows of `D` obtained from the string `(s, x)` of `[1] × C` by the functor
`[1] × C ⥤ D` given by `η`. -/
lemma nerveHomotopy_h_app (η : F ⟶ G) {m : SimplexCategoryᵒᵖ}
    (x : (nerve C ⊗ Δ[1] : SSet.{max u v}).obj m) :
    η.nerveHomotopy.h.app m x = (stdSimplex.asOrderHom x.2).monotone.functor.prod' x.1 ⋙
      Functor.uncurry.obj (ComposableArrows.mk₁ η) :=
  (rfl)

/-- Over the vertex of an object `c`, the homotopy induced by `η` moves along the edge `η.app c`:
it sends the vertical edge `{c} × Δ[1]` of the cylinder to the `1`-simplex `η.app c` of `N D`. -/
lemma nerveHomotopy_h_app_verticalEdge (η : F ⟶ G) (c : C) :
    η.nerveHomotopy.h.app _ (verticalEdge (nerveEquiv.symm c)) =
      (nerve.edgeMk (η.app c)).edge := by
  have h₁ : (verticalEdge (X := nerve C) (nerveEquiv.symm c)).1 = ComposableArrows.mk₁ (𝟙 c) :=
    (verticalEdge_fst _).trans (nerve.σ₀_mk₀_eq c)
  have h₂ : (stdSimplex.asOrderHom
      (verticalEdge (X := nerve C) (nerveEquiv.symm c)).2).monotone.functor = 𝟭 (Fin 2) := by
    rw [verticalEdge_snd (X := nerve C) (nerveEquiv.symm c)]
    exact Functor.ext (fun i ↦ by fin_cases i <;> rfl) (fun _ _ _ ↦ Subsingleton.elim _ _)
  rw [nerveHomotopy_h_app, h₁, h₂, nerve.edgeMk_edge]
  exact ComposableArrows.ext₁ rfl rfl (by simp)

end CategoryTheory.NatTrans
