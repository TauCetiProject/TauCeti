/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CoordinateRealification
public import TauCeti.Topology.VectorBundle.FiniteRank.Biproduct
public import TauCeti.Topology.VectorBundle.FiniteRank.CoordinateFunctor

/-!
# Realification and complexification of finite-rank bundle cores

The realification of a complex core of rank `n` is the real core of rank `n + n` with the same
charts, whose transitions are the original complex transition matrices read in the real
coordinates `TauCeti.realCoords` (real parts first, imaginary parts second). The
complexification of a real core of rank `n` is the complex core of rank `n` with the same charts,
whose transitions are the complex-linear extensions of the real transition matrices. Both arise
from continuous coordinate functors (`TauCeti.CoordinateFunctor.realify`,
`TauCeti.CoordinateFunctor.complexify`), so they are functors

* `FiniteRankBundleCore.realify B : FiniteRankBundleCore ℂ B ⥤ FiniteRankBundleCore ℝ B`,
* `FiniteRankBundleCore.complexify B : FiniteRankBundleCore ℝ B ⥤ FiniteRankBundleCore ℂ B`,

acting on bundle maps by realifying or complexifying their fibre maps. Both functors are additive,
hence preserve Whitney sums, and they send trivial cores to trivial cores
(`TauCeti.CoordinateFunctor.mapCoreTrivialIso`).

`FiniteRankBundleCore.realifyComplexifyIso` identifies the realification of the complexification
of a real core `A` with the Whitney sum `A ⊕ A`, by the identity on coordinates; it is natural in
`A` (`realifyComplexifyIso_naturality_fst`, `realifyComplexifyIso_naturality_snd`). This is the
bundle-level form of the relation `r ∘ c = 2` between realification and complexification in real
K-theory.

## References

* M. F. Atiyah, *K-Theory*, §1.2 and §3.
-/

public section

open CategoryTheory

namespace TauCeti

namespace CoordinateFunctor

/-- Realification of complex coordinate spaces: `Fin n → ℂ` is read in the real coordinates
`Fin (n + n) → ℝ`, and complex-linear maps are read as real-linear maps. -/
-- Expose the dimension function so that coordinate spaces of realifications reduce.
@[expose]
noncomputable def realify : CoordinateFunctor ℂ ℝ where
  rank n := n + n
  map g := g.realifyCoords
  continuous_map _ _ := ContinuousLinearMap.continuous_realifyCoords
  map_id _ := ContinuousLinearMap.realifyCoords_id
  map_comp := ContinuousLinearMap.realifyCoords_comp

@[simp] theorem rank_realify (n : ℕ) : realify.rank n = n + n := (rfl)

@[simp] theorem map_realify {m n : ℕ} (g : (Fin m → ℂ) →L[ℂ] (Fin n → ℂ)) :
    realify.map g = g.realifyCoords := (rfl)

/-- Complexification of real coordinate spaces: `Fin n → ℝ` becomes `Fin n → ℂ`, and real-linear
maps are extended complex-linearly. -/
-- Expose the dimension function so that coordinate spaces of complexifications reduce.
@[expose]
noncomputable def complexify : CoordinateFunctor ℝ ℂ where
  rank n := n
  map g := g.complexifyCoords
  continuous_map _ _ := ContinuousLinearMap.continuous_complexifyCoords
  map_id _ := ContinuousLinearMap.complexifyCoords_id
  map_comp := ContinuousLinearMap.complexifyCoords_comp

@[simp] theorem rank_complexify (n : ℕ) : complexify.rank n = n := (rfl)

@[simp] theorem map_complexify {m n : ℕ} (g : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ)) :
    complexify.map g = g.complexifyCoords := (rfl)

end CoordinateFunctor

namespace FiniteRankBundleCore

universe u

variable (B : Type u) [TopologicalSpace B]

/-- Realification of complex finite-rank bundle cores: a complex bundle of rank `n` is regarded as
a real bundle of rank `n + n`. -/
-- Expose the object map so that coordinate spaces of realifications reduce.
@[expose]
noncomputable def realify : FiniteRankBundleCore ℂ B ⥤ FiniteRankBundleCore ℝ B :=
  CoordinateFunctor.realify.functor B

/-- Complexification of real finite-rank bundle cores: a real bundle of rank `n` is tensored
fibrewise with `ℂ`, giving a complex bundle of rank `n`. -/
-- Expose the object map so that coordinate spaces of complexifications reduce.
@[expose]
noncomputable def complexify : FiniteRankBundleCore ℝ B ⥤ FiniteRankBundleCore ℂ B :=
  CoordinateFunctor.complexify.functor B

/-- Realification is additive; in particular it preserves Whitney sums. -/
instance : (realify B).Additive :=
  CoordinateFunctor.realify.functor_additive ContinuousLinearMap.realifyCoords_add

/-- Complexification is additive; in particular it preserves Whitney sums. -/
instance : (complexify B).Additive :=
  CoordinateFunctor.complexify.functor_additive ContinuousLinearMap.complexifyCoords_add

variable {B}

theorem realify_obj (A : FiniteRankBundleCore ℂ B) :
    (realify B).obj A = CoordinateFunctor.realify.mapCore A := (rfl)

theorem complexify_obj (A : FiniteRankBundleCore ℝ B) :
    (complexify B).obj A = CoordinateFunctor.complexify.mapCore A := (rfl)

@[simp] theorem rank_realify_obj (A : FiniteRankBundleCore ℂ B) :
    ((realify B).obj A).rank = A.rank + A.rank := (rfl)

@[simp] theorem rank_complexify_obj (A : FiniteRankBundleCore ℝ B) :
    ((complexify B).obj A).rank = A.rank := (rfl)

@[simp] theorem localTriv_baseSet_realify_obj (A : FiniteRankBundleCore ℂ B) (i : B) :
    (((realify B).obj A).core.localTriv i).baseSet = A.core.baseSet i := (rfl)

@[simp] theorem localTriv_baseSet_complexify_obj (A : FiniteRankBundleCore ℝ B) (i : B) :
    (((complexify B).obj A).core.localTriv i).baseSet = A.core.baseSet i := (rfl)

/-- The transitions of a realification are the realified transitions. -/
@[simp] theorem coordChange_realify_obj (A : FiniteRankBundleCore ℂ B) (i j x : B) :
    ((realify B).obj A).core.coordChange i j x = (A.core.coordChange i j x).realifyCoords := (rfl)

/-- The transitions of a complexification are the complexified transitions. -/
@[simp] theorem coordChange_complexify_obj (A : FiniteRankBundleCore ℝ B) (i j x : B) :
    ((complexify B).obj A).core.coordChange i j x =
      (A.core.coordChange i j x).complexifyCoords := (rfl)

/-- On every fibre, the realification of a bundle map is the realified fibre map. -/
@[simp] theorem fiberMap_realify_map {A D : FiniteRankBundleCore ℂ B} (f : A ⟶ D) (x : B) :
    ((realify B).map f).fiberMap x = (f.fiberMap x).realifyCoords :=
  CoordinateFunctor.fiberMap_mapHom _ f x

/-- On every fibre, the complexification of a bundle map is the complexified fibre map. -/
@[simp] theorem fiberMap_complexify_map {A D : FiniteRankBundleCore ℝ B} (f : A ⟶ D) (x : B) :
    ((complexify B).map f).fiberMap x = (f.fiberMap x).complexifyCoords :=
  CoordinateFunctor.fiberMap_mapHom _ f x

/-! ### Realification of a complexification -/

/-- The realification of the complexification of a real core `A` is the Whitney sum `A ⊕ A`:
the real and imaginary parts of the complexified fibre give the two summands. On coordinates the
isomorphism is the identity of `Fin (A.rank + A.rank) → ℝ`. -/
noncomputable def realifyComplexifyIso (A : FiniteRankBundleCore ℝ B) :
    (realify B).obj ((complexify B).obj A) ≅ whitneySum A A :=
  constIso (fun _ => (Set.inter_self _).symm) (ContinuousLinearEquiv.refl ℝ _)
    -- Both transitions are the block-diagonal doubling of the transition of `A`.
    fun i j x _ _ => ContinuousLinearMap.ext fun v => congrArg (fun S => S v)
      (ContinuousLinearMap.realifyCoords_complexifyCoords (A.core.coordChange i j x))

@[simp] theorem fiberMap_realifyComplexifyIso_hom (A : FiniteRankBundleCore ℝ B) (x : B) :
    (realifyComplexifyIso A).hom.fiberMap x =
      ContinuousLinearMap.id ℝ (Fin (A.rank + A.rank) → ℝ) := by
  rw [realifyComplexifyIso]
  exact fiberMap_constIso_hom _ _ _ x

@[simp] theorem fiberMap_realifyComplexifyIso_inv (A : FiniteRankBundleCore ℝ B) (x : B) :
    (realifyComplexifyIso A).inv.fiberMap x =
      ContinuousLinearMap.id ℝ (Fin (A.rank + A.rank) → ℝ) := by
  rw [realifyComplexifyIso]
  exact fiberMap_constIso_inv _ _ _ x

/-- Naturality of `realifyComplexifyIso`, on the first Whitney summand. -/
@[reassoc]
theorem realifyComplexifyIso_naturality_fst {A D : FiniteRankBundleCore ℝ B} (f : A ⟶ D) :
    (realify B).map ((complexify B).map f) ≫ (realifyComplexifyIso D).hom ≫ whitneyFst D D =
      (realifyComplexifyIso A).hom ≫ whitneyFst A A ≫ f := by
  refine hom_ext fun x => ?_
  simp only [fiberMap_comp, fiberMap_realify_map, fiberMap_complexify_map,
    fiberMap_realifyComplexifyIso_hom, fiberMap_whitneyFst]
  -- At each coordinate vector, both sides are the first block of the doubled transition.
  exact ContinuousLinearMap.ext fun v => congrArg Prod.fst
    (ContinuousLinearMap.splitCoords_realifyCoords_complexifyCoords (f.fiberMap x) v)

/-- Naturality of `realifyComplexifyIso`, on the second Whitney summand. -/
@[reassoc]
theorem realifyComplexifyIso_naturality_snd {A D : FiniteRankBundleCore ℝ B} (f : A ⟶ D) :
    (realify B).map ((complexify B).map f) ≫ (realifyComplexifyIso D).hom ≫ whitneySnd D D =
      (realifyComplexifyIso A).hom ≫ whitneySnd A A ≫ f := by
  refine hom_ext fun x => ?_
  simp only [fiberMap_comp, fiberMap_realify_map, fiberMap_complexify_map,
    fiberMap_realifyComplexifyIso_hom, fiberMap_whitneySnd]
  -- At each coordinate vector, both sides are the second block of the doubled transition.
  exact ContinuousLinearMap.ext fun v => congrArg Prod.snd
    (ContinuousLinearMap.splitCoords_realifyCoords_complexifyCoords (f.fiberMap x) v)

end FiniteRankBundleCore
end TauCeti
