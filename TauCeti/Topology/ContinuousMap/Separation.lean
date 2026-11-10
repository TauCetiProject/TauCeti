/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Basic

/-!
# Point-separating families of continuous functions make the source Hausdorff

If a set of continuous functions from `X` into a Hausdorff space `F` separates the points of `X`,
then `X` is itself Hausdorff, because `X` embeds injectively and continuously into a product of
copies of `F`.

## Main declaration

* `t2Space_of_separatesPoints`: a point-separating set of continuous functions into a Hausdorff
  space makes the source a Hausdorff space.
-/

public section

/-- Continuous functions into a Hausdorff space that separate points make the source Hausdorff. -/
theorem t2Space_of_separatesPoints {X F : Type*} [TopologicalSpace X] [TopologicalSpace F]
    [T2Space F] {B : Set C(X, F)}
    (h : Set.SeparatesPoints ((fun b : C(X, F) => (b : X → F)) '' B)) : T2Space X := by
  refine T2Space.of_injective_continuous (f := fun x (b : B) => b.1 x) (fun x y hxy => ?_)
    (continuous_pi fun b => b.1.continuous)
  by_contra hne
  obtain ⟨_, ⟨b, hb, rfl⟩, hbxy⟩ := h hne
  exact hbxy (congrFun hxy ⟨b, hb⟩)
