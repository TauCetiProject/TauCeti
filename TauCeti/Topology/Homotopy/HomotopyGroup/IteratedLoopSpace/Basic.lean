/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.HomotopyGroup.LoopSpace
public import TauCeti.Topology.Homotopy.IteratedLoopSpace.Homeomorph
public import TauCeti.Topology.PathComponent

/-!
# Homotopy groups of iterated loop spaces

The shift of homotopy groups along the `k`-fold iterated loop space
`TauCeti.BasedTopologicalSpace.iteratedLoopSpace` of a based space,
`π_(m + 1)(Ω^[k] X) ≃* π_(m + 1 + k)(X)`, by iterating
`HomotopyGroup.pathLoopSpaceMulEquiv`, and its degree-zero form
`π₀(Ω^[k] X) ≃ π_k(X)`, which identifies the path components of the `k`-fold loop space with the
`k`-th homotopy group. In degree zero there is no group structure on the left, so the latter is a
bijection of pointed sets: the component of the constant iterated loop goes to the class of the
constant cube loop, the identity when `k` is positive. It is obtained by reading an iterated loop
as a cube loop through `TauCeti.BasedTopologicalSpace.iteratedLoopSpaceHomeomorph`, and a path
component of the space of cube loops as a homotopy class through
`HomotopyGroup.zerothHomotopyEquiv`.

## Main declarations

* `TauCeti.BasedTopologicalSpace.piIteratedLoopSpaceMulEquiv`:
  `π_(m + 1)(Ω^[k] X) ≃* π_(m + 1 + k)(X)`, natural in `X` by
  `TauCeti.BasedTopologicalSpace.piIteratedLoopSpaceMulEquiv_map`.
* `TauCeti.BasedTopologicalSpace.zerothHomotopyIteratedLoopSpaceEquiv`:
  `π₀(Ω^[k] X) ≃ π_k(X)`, based by
  `TauCeti.BasedTopologicalSpace.zerothHomotopyIteratedLoopSpaceEquiv_mk_basepoint` and natural in
  `X` by `TauCeti.BasedTopologicalSpace.zerothHomotopyIteratedLoopSpaceEquiv_map`; for `k = 2` it
  is `TauCeti.zerothHomotopyDoubleLoopSpaceEquiv`
  (`TauCeti.BasedTopologicalSpace.zerothHomotopyIteratedLoopSpaceEquiv_two`).
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
@[simp]
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
          (ContinuousMap.map_congrMulEquiv _ _ _ _).symm).trans
          (ContinuousMap.pathLoopSpaceMulEquiv_map _ _ _
            (fun γ t => Hom.loopSpace_apply f γ t) _ _))
      _ = _ := (ContinuousMap.map_congrMulEquiv _ _ _ _).symm

/-! ### Path components of iterated loop spaces -/

/-- **The path components of the `k`-fold loop space are the `k`-th homotopy group**:
`π₀(Ω^[k] X) ≃ π_k(X)`. The component of an iterated loop goes to the homotopy class of the cube
loop it defines under `iteratedLoopSpaceHomeomorph`. -/
noncomputable def zerothHomotopyIteratedLoopSpaceEquiv (X : BasedTopologicalSpace.{u}) (k : ℕ) :
    ZerothHomotopy (X.iteratedLoopSpace k).carrier ≃ π_ k X.carrier X.basepoint :=
  (iteratedLoopSpaceHomeomorph k X).zerothHomotopyCongr.trans zerothHomotopyEquiv

/-- The component of an iterated loop `γ` goes to the class of the cube loop of `γ`. -/
@[simp]
theorem zerothHomotopyIteratedLoopSpaceEquiv_mk (X : BasedTopologicalSpace.{u}) (k : ℕ)
    (γ : (X.iteratedLoopSpace k).carrier) :
    X.zerothHomotopyIteratedLoopSpaceEquiv k (.mk γ) =
      ⟦iteratedLoopSpaceHomeomorph k X γ⟧ := by
  rw [zerothHomotopyIteratedLoopSpaceEquiv, Equiv.trans_apply,
    Homeomorph.zerothHomotopyCongr_mk]
  exact zerothHomotopyEquiv_mk _

/-- The class of a cube loop `p` comes from the component of the iterated loop that `p`
defines. -/
@[simp]
theorem zerothHomotopyIteratedLoopSpaceEquiv_symm_mk (X : BasedTopologicalSpace.{u}) (k : ℕ)
    (p : Ω^ (Fin k) X.carrier X.basepoint) :
    (X.zerothHomotopyIteratedLoopSpaceEquiv k).symm (⟦p⟧ : π_ k X.carrier X.basepoint) =
      .mk ((iteratedLoopSpaceHomeomorph k X).symm p) :=
  (Equiv.symm_apply_eq _).2 <| by
    rw [zerothHomotopyIteratedLoopSpaceEquiv_mk, Homeomorph.apply_symm_apply]

/-- **The bijection `π₀(Ω^[k] X) ≃ π_k(X)` is based**: the component of the constant iterated
loop goes to the class of the constant cube loop. -/
theorem zerothHomotopyIteratedLoopSpaceEquiv_mk_basepoint (X : BasedTopologicalSpace.{u})
    (k : ℕ) :
    X.zerothHomotopyIteratedLoopSpaceEquiv k (.mk (X.iteratedLoopSpace k).basepoint) =
      ⟦GenLoop.const⟧ := by
  rw [zerothHomotopyIteratedLoopSpaceEquiv_mk, iteratedLoopSpaceHomeomorph_basepoint]

/-- In positive degree, the component of the constant iterated loop goes to the identity of
`π_(k + 1)(X)`. -/
theorem zerothHomotopyIteratedLoopSpaceEquiv_succ_mk_basepoint (X : BasedTopologicalSpace.{u})
    (k : ℕ) :
    X.zerothHomotopyIteratedLoopSpaceEquiv (k + 1)
        (.mk (X.iteratedLoopSpace (k + 1)).basepoint) = 1 := by
  rw [zerothHomotopyIteratedLoopSpaceEquiv_mk_basepoint, HomotopyGroup.one_def]

/-- **The bijection `π₀(Ω^[k] X) ≃ π_k(X)` is natural in `X`**: it carries the component of
`Ω^[k] f` applied to an iterated loop `γ` to the image under `f` of the class of `γ`. -/
theorem zerothHomotopyIteratedLoopSpaceEquiv_map {X Y : BasedTopologicalSpace.{u}} (f : Hom X Y)
    (k : ℕ) (γ : (X.iteratedLoopSpace k).carrier) :
    Y.zerothHomotopyIteratedLoopSpaceEquiv k (.mk (f.iteratedLoopSpace k γ)) =
      HomotopyGroup.map f.toContinuousMap f.map_basepoint
        (X.zerothHomotopyIteratedLoopSpaceEquiv k (.mk γ)) := by
  rw [zerothHomotopyIteratedLoopSpaceEquiv_mk, zerothHomotopyIteratedLoopSpaceEquiv_mk,
    iteratedLoopSpaceHomeomorph_map, HomotopyGroup.map_mk]

-- `Ω^[2] X` is `Ω (Ω X)` by definitional unfolding of the exposed `iteratedLoopSpace`, so both
-- bijections have the same type.
/-- For `k = 2` the bijection is `TauCeti.zerothHomotopyDoubleLoopSpaceEquiv`: both send the
component of a double loop `β` to the class of the square `(t₀, t₁) ↦ β t₀ t₁`. -/
theorem zerothHomotopyIteratedLoopSpaceEquiv_two (X : BasedTopologicalSpace.{u}) :
    X.zerothHomotopyIteratedLoopSpaceEquiv 2 = zerothHomotopyDoubleLoopSpaceEquiv X.basepoint := by
  ext c
  induction c using Quotient.inductionOn with | h β =>
  refine (zerothHomotopyIteratedLoopSpaceEquiv_mk X 2 β).trans ?_
  refine Eq.trans ?_ (zerothHomotopyDoubleLoopSpaceEquiv_mk X.basepoint β).symm
  refine Eq.trans ?_ (fundamentalGroupLoopSpaceMulEquiv_fromPath_mk β).symm
  exact congrArg _ (GenLoop.ext _ _ fun t ↦
    (iteratedLoopSpaceHomeomorph_two_apply X β t).trans (GenLoop.fromDoubleLoop_apply β t).symm)

end BasedTopologicalSpace

end TauCeti
