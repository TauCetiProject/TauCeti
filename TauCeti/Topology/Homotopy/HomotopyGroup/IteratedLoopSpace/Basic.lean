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
  -- The `k = 0` case is the identity on both sides, since `Ω^[0] f` is `f`.
  | 0, _, _, _, _, _ => by
    rw [Hom.iteratedLoopSpace_zero, piIteratedLoopSpaceMulEquiv_zero,
      piIteratedLoopSpaceMulEquiv_zero]
    rfl
  | k + 1, X, Y, f, m, a => by
    -- Four commuting squares: the induction hypothesis for `Ω f`, then `map_congrMulEquiv` for
    -- the first reindexing, `pathLoopSpaceMulEquiv_map` for the one-loop shift, and
    -- `map_congrMulEquiv` for the last reindexing.
    rw [Hom.iteratedLoopSpace_succ]
    calc _ = _ := DFunLike.congr_fun (piIteratedLoopSpaceMulEquiv_succ Y k m) _
      _ = _ := congrArg (fun b => congrMulEquiv (finCongr (by omega : m + k + 2 =
            m + 1 + (k + 1)))
          (pathLoopSpaceMulEquiv (X := Y.carrier) (x := Y.basepoint) (m + k)
            (congrMulEquiv (finCongr (by omega : m + 1 + k = m + k + 1)) b)))
        (piIteratedLoopSpaceMulEquiv_map k f.loopSpace m a)
      _ = _ := congrArg (congrMulEquiv (finCongr (by omega : m + k + 2 = m + 1 + (k + 1))))
        ((congrArg (pathLoopSpaceMulEquiv (X := Y.carrier) (x := Y.basepoint) (m + k))
          (HomotopyGroup.map_congrMulEquiv _ _ _ _).symm).trans
          (HomotopyGroup.pathLoopSpaceMulEquiv_map _ _ _ _
            (fun γ t => Hom.loopSpace_apply f γ t) _ _))
      _ = _ := (HomotopyGroup.map_congrMulEquiv _ _ _ _).symm

end BasedTopologicalSpace

end TauCeti
