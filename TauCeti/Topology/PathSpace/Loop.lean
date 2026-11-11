/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Path

/-!
# Loop maps of fixed-interval loop spaces

A based map `f : X → Y`, `f x = y`, induces the continuous map of fixed-interval loop spaces
`Ω f : Path x x → Path y y`, `γ ↦ f ∘ γ` (`ContinuousMap.loopMap`). It sends the constant loop to
the constant loop, commutes with concatenation of loops, and is functorial in `f`. The
constructions here do not involve homotopy groups.

## Main definitions

* `ContinuousMap.loopMap`: the map `Path x x → Path y y` of loop spaces induced by a based map.
-/

public section

namespace ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}

/-- The map `Path x x → Path y y` of fixed-interval loop spaces induced by a based map `f`,
`f x = y`: a loop `γ` is sent to `f ∘ γ`. -/
def loopMap (f : C(X, Y)) (hf : f x = y) : C(Path x x, Path y y) where
  toFun γ := (γ.map f.continuous).cast hf.symm hf.symm
  continuous_toFun := continuous_induced_rng.2 <|
    (ContinuousMap.continuous_postcomp f).comp continuous_induced_dom

@[simp]
theorem loopMap_apply (f : C(X, Y)) (hf : f x = y) (γ : Path x x) (t : unitInterval) :
    f.loopMap hf γ t = f (γ t) :=
  (rfl)

/-- The loop map sends the constant loop to the constant loop. -/
@[simp]
theorem loopMap_refl (f : C(X, Y)) (hf : f x = y) : f.loopMap hf (Path.refl x) = Path.refl y :=
  Path.ext (funext fun _ ↦ hf)

/-- The loop map commutes with concatenation of loops. -/
@[simp]
theorem loopMap_trans (f : C(X, Y)) (hf : f x = y) (γ δ : Path x x) :
    f.loopMap hf (γ.trans δ) = (f.loopMap hf γ).trans (f.loopMap hf δ) := by
  ext t
  simp only [loopMap_apply, Path.trans_apply]
  split_ifs <;> rfl

/-- The loop map of the identity is the identity. -/
@[simp]
theorem loopMap_id :
    (ContinuousMap.id X).loopMap (rfl : id x = x) = ContinuousMap.id (Path x x) :=
  ContinuousMap.ext fun _ ↦ Path.ext (funext fun _ ↦ rfl)

/-- The loop map of a composite is the composite of the loop maps. -/
theorem loopMap_comp {Z : Type*} [TopologicalSpace Z] {z : Z} (g : C(Y, Z)) (hg : g y = z)
    (f : C(X, Y)) (hf : f x = y) :
    (g.comp f).loopMap (by rw [comp_apply, hf, hg]) = (g.loopMap hg).comp (f.loopMap hf) :=
  ContinuousMap.ext fun _ ↦ Path.ext (funext fun _ ↦ rfl)

end ContinuousMap
