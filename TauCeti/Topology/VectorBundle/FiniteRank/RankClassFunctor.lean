/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.ParacompactHomotopyCat
public import TauCeti.Topology.VectorBundle.FiniteRank.HomotopyInvariance

/-!
# Rank-`k` vector bundles as a functor on the homotopy category

For a complete normed `ℝ`-algebra `𝕜`, sending a paracompact Hausdorff space `X` to the set
`FiniteRankBundleCore.RankClass 𝕜 X k` of isomorphism classes of rank-`k` vector-bundle cores over
`X`, with pullback of classes, is a functor `TauCeti.rankClassFunctor 𝕜 k : HoParaᵒᵖ ⥤ Type _` on
the homotopy category `TauCeti.ParacompactHomotopyCat`: homotopic maps pull back isomorphic cores
(`TauCeti.FiniteRankBundleCore.pullbackRankClass_eq_of_homotopic`).

## Main definitions

* `TauCeti.rankClassFunctor`: rank-`k` vector bundles as a functor on `HoParaᵒᵖ`.

## Main results

* `TauCeti.rankClassFunctor_obj`, `TauCeti.rankClassFunctor_map_homMk`: the functor sends `X` to
  its rank-`k` classes and the class of `f` to pullback along `f`.
-/

public section

open CategoryTheory Opposite

universe u v

namespace TauCeti

open FiniteRankBundleCore

variable (𝕜 : Type v) [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] [CompleteSpace 𝕜] (k : ℕ)

/-- Pullback of isomorphism classes of rank-`k` cores, as a contravariant functor on paracompact
Hausdorff spaces into types, before passing to homotopy classes. It is public and exposed because
the exposed `rankClassFunctor` is built from it. -/
@[expose] def rankClassFunctorAux : isParacompactT2.{u}.FullSubcategory ⥤ (Type (max u v))ᵒᵖ where
  obj X := op (RankClass 𝕜 X.obj k)
  map f := (TypeCat.ofHom (pullbackRankClass f.hom.hom k)).op
  map_id X := by
    apply Quiver.Hom.unop_inj
    ext c
    exact pullbackRankClass_id k c
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    ext c
    exact (pullbackRankClass_comp f.hom.hom g.hom.hom k c).symm

/-- **Rank-`k` vector bundles on the homotopy category.** `X ↦ Vect_k(X)`, the isomorphism
classes of rank-`k` vector-bundle cores over `X`, with pullback of classes; homotopic maps pull
back isomorphic cores. The body is exposed because the statement of `rankClassFunctor_map_homMk`
types its argument through `rankClassFunctor_obj`, which holds by unfolding. -/
@[expose] def rankClassFunctor : ParacompactHomotopyCat.{u}ᵒᵖ ⥤ Type (max u v) :=
  (CategoryTheory.Quotient.lift paracompactHomotopicRel.{u} (rankClassFunctorAux.{u, v} 𝕜 k)
    fun _ _ _ _ h ↦
    Quiver.Hom.unop_inj (congrArg TypeCat.ofHom
      (pullbackRankClass_eq_of_homotopic (paracompactHomotopicRel_iff.1 h) k))).leftOp

/-- `rankClassFunctor` sends `X` to the rank-`k` classes over `X`. -/
theorem rankClassFunctor_obj (X : ParacompactHomotopyCat.{u}) :
    (rankClassFunctor 𝕜 k).obj (op X) = RankClass 𝕜 X.as.obj k :=
  (rfl)

/-- `rankClassFunctor` acts on the class of `f` by pulling back rank-`k` classes along `f`. -/
@[simp]
theorem rankClassFunctor_map_homMk {X Y : ParacompactHomotopyCat.{u}} (f : C(X.as.obj, Y.as.obj))
    (c : RankClass 𝕜 Y.as.obj k) :
    (rankClassFunctor 𝕜 k).map (ParacompactHomotopyCat.homMk f).op c = pullbackRankClass f k c :=
  (rfl)

end TauCeti
