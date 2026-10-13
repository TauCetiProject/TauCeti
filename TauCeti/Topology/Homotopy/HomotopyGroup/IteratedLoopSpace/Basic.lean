/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.HomotopyGroup.LoopSpace
public import TauCeti.Topology.Homotopy.HomotopyGroup.Map
public import TauCeti.Topology.Homotopy.IteratedLoopSpace

/-!
# Homotopy groups of iterated loop spaces

The shift of homotopy groups along the `k`-fold iterated loop space
`TauCeti.BasedTopologicalSpace.iteratedLoopSpace` of a based space,
`π_(m + 1)(Ω^[k] X) ≃* π_(m + 1 + k)(X)`, by iterating
`HomotopyGroup.pathLoopSpaceMulEquiv`.

## Main declarations

* `TauCeti.BasedTopologicalSpace.piIteratedLoopSpaceMulEquiv`:
  `π_(m + 1)(Ω^[k] X) ≃* π_(m + 1 + k)(X)`, natural in `X` by
  `TauCeti.BasedTopologicalSpace.piIteratedLoopSpaceMulEquiv_map`.
-/

public section

universe u

namespace TauCeti

open HomotopyGroup
open scoped Topology Topology.Homotopy

namespace HomotopyGroup

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}

/-- The shift `pathLoopSpaceMulEquiv` is natural: it commutes with the maps induced on homotopy
groups by a based map `f` and by any map `F` of loop spaces that postcomposes loops with `f`. -/
theorem pathLoopSpaceMulEquiv_map (f : C(X, Y)) (hf : f x = y) (F : C(Ω X x, Ω Y y))
    (hF : F (Path.refl x) = Path.refl y) (hFf : ∀ γ t, F γ t = f (γ t)) (m : ℕ)
    (a : π_ (m + 1) (Ω X x) (Path.refl x)) :
    pathLoopSpaceMulEquiv m (map F hF a) = map f hf (pathLoopSpaceMulEquiv m a) := by
  induction a using Quotient.inductionOn with
  | h p =>
    rw [map_mk, pathLoopSpaceMulEquiv_mk, pathLoopSpaceMulEquiv_mk, map_mk]
    refine congrArg _ (GenLoop.ext _ _ fun t => ?_)
    simp [hFf]

end HomotopyGroup

namespace BasedTopologicalSpace

/-- **The homotopy groups of the `k`-fold loop space are the homotopy groups of the space,
shifted by `k`**: `π_(m + 1)(Ω^[k] X) ≃* π_(m + 1 + k)(X)`. -/
-- Both cases typecheck by definitional unfolding of the exposed `iteratedLoopSpace` and
-- `loopSpace`: `Ω^[0] X` is `X`, and `Ω^[k + 1] X` is `Ω^[k] (Ω X)` (the iterate recurses on the
-- argument), where `Ω X` has carrier `Path _ _` (Mathlib's `Ω`) based at `Path.refl _`, which is
-- the source of `pathLoopSpaceMulEquiv`. The ascriptions on the `omega` proofs fix the indices of
-- `finCongr`, which are not determined by unification at that point.
noncomputable def piIteratedLoopSpaceMulEquiv :
    (k : ℕ) → (X : BasedTopologicalSpace.{u}) → (m : ℕ) →
      π_ (m + 1) (X.iteratedLoopSpace k).carrier (X.iteratedLoopSpace k).basepoint ≃*
        π_ (m + 1 + k) X.carrier X.basepoint
  | 0, _, _ => MulEquiv.refl _
  | k + 1, X, m =>
    (piIteratedLoopSpaceMulEquiv k X.loopSpace m).trans
      ((congrMulEquiv (finCongr (by omega : m + 1 + k = m + k + 1))).trans
        ((pathLoopSpaceMulEquiv (X := X.carrier) (x := X.basepoint) (m + k)).trans
          (congrMulEquiv (finCongr (by omega : m + k + 2 = m + 1 + (k + 1))))))

/-- In degree `k = 0` the shift is the identity. -/
@[simp]
theorem piIteratedLoopSpaceMulEquiv_zero (X : BasedTopologicalSpace.{u}) (m : ℕ) :
    X.piIteratedLoopSpaceMulEquiv 0 m = MulEquiv.refl _ := by
  rw [piIteratedLoopSpaceMulEquiv.eq_1]

/-- The shift along `k + 1` loops is the shift along `k` loops for the loop space `Ω X`,
followed by the one-loop shift `pathLoopSpaceMulEquiv`, with the degrees reindexed. -/
@[simp]
theorem piIteratedLoopSpaceMulEquiv_succ (X : BasedTopologicalSpace.{u}) (k m : ℕ) :
    X.piIteratedLoopSpaceMulEquiv (k + 1) m =
      ((X.loopSpace.piIteratedLoopSpaceMulEquiv k m).trans
        ((congrMulEquiv (finCongr (by omega : m + 1 + k = m + k + 1))).trans
          ((pathLoopSpaceMulEquiv (X := X.carrier) (x := X.basepoint) (m + k)).trans
            (congrMulEquiv (finCongr (by omega : m + k + 2 = m + 1 + (k + 1))))))) := by
  rw [piIteratedLoopSpaceMulEquiv.eq_2]

/-- **The shift `π_(m + 1)(Ω^[k] X) ≃* π_(m + 1 + k)(X)` is natural in `X`**: it commutes with the
maps induced on homotopy groups by a based map `f` and by `Ω^[k] f`. -/
theorem piIteratedLoopSpaceMulEquiv_map :
    (k : ℕ) → {X Y : BasedTopologicalSpace.{u}} → (f : Hom X Y) → (m : ℕ) →
      (a : π_ (m + 1) (X.iteratedLoopSpace k).carrier (X.iteratedLoopSpace k).basepoint) →
      Y.piIteratedLoopSpaceMulEquiv k m (HomotopyGroup.map (f.iteratedLoopSpace k).toContinuousMap
          (f.iteratedLoopSpace k).map_basepoint a) =
        HomotopyGroup.map f.toContinuousMap f.map_basepoint
          (X.piIteratedLoopSpaceMulEquiv k m a)
  | 0, _, _, _, _, _ => by
    rw [piIteratedLoopSpaceMulEquiv_zero, piIteratedLoopSpaceMulEquiv_zero]
    rfl
  | k + 1, X, Y, f, m, a =>
    (DFunLike.congr_fun (piIteratedLoopSpaceMulEquiv_succ Y k m) _).trans <|
      (congrArg (fun b => congrMulEquiv (finCongr (by omega : m + k + 2 = m + 1 + (k + 1)))
          (pathLoopSpaceMulEquiv (X := Y.carrier) (x := Y.basepoint) (m + k)
            (congrMulEquiv (finCongr (by omega : m + 1 + k = m + k + 1)) b)))
        (piIteratedLoopSpaceMulEquiv_map k f.loopSpace m a)).trans <|
      (congrArg (fun b => congrMulEquiv (finCongr (by omega : m + k + 2 = m + 1 + (k + 1))) b)
        ((congrArg (pathLoopSpaceMulEquiv (X := Y.carrier) (x := Y.basepoint) (m + k))
          (HomotopyGroup.map_congrMulEquiv _ _ _ _).symm).trans
          (HomotopyGroup.pathLoopSpaceMulEquiv_map _ _ _ _
            (fun γ t => Hom.loopSpace_apply f γ t) _ _))).trans
        (HomotopyGroup.map_congrMulEquiv _ _ _ _).symm

end BasedTopologicalSpace

end TauCeti
