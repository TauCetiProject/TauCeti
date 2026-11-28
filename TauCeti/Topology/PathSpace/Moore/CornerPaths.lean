/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PathSpace.Moore.Comparison.Basic

/-!
# Moore paths along the segments from the corner of a cube

For a map `f : I^ι → X` from a cube, the image under `f` of the straight segment from the corner
`0` to a point `d` of the cube, `t ↦ f (t • d)`, is a Moore path of length one from `f 0` to `f d`
(`TauCeti.MoorePath.cornerPaths`). These paths depend continuously on `d`, so they form a
continuous family of Moore paths from the single point `f 0` to all the points of `f`. Along such a
family, the pullback along `f` of a path fibration is fibre homotopy trivial, with the fibre over
`f 0` as fibre.

## Main definitions

* `TauCeti.MoorePath.cornerPaths f`: the family of Moore paths `d ↦ (t ↦ f (t • d))`.

## Main results

* `TauCeti.MoorePath.cornerPaths_apply_toNNReal`: the path `cornerPaths f d` is `t ↦ f (t • d)`.
-/

public noncomputable section

open unitInterval

namespace TauCeti

namespace MoorePath

variable {ι X : Type*} [TopologicalSpace X]

/-- The images under `f : I^ι → X` of the straight segments from the corner `0` of the cube to its
points: the Moore path of length one `t ↦ f (t • d)` from `f 0` to `f d`, for each point `d`. -/
def cornerPaths (f : C(ι → I, X)) : C(ι → I, MoorePath X) :=
  let H : C((ι → I) × I, X) := f.comp ⟨fun z i ↦ z.2 * z.1 i, continuous_pi fun i ↦
    ((continuous_subtypeVal.comp continuous_snd).mul
      (continuous_subtypeVal.comp ((continuous_apply i).comp continuous_fst))).subtype_mk _⟩
  ⟨fun d ↦ ofUnitPath (H.curry d), continuous_ofUnitPath.comp H.curry.continuous⟩

/-- At a time `t` of the unit interval, the Moore path `cornerPaths f d` is at `f (t • d)`. -/
@[simp]
theorem cornerPaths_apply_toNNReal (f : C(ι → I, X)) (d : ι → I) (t : I) :
    cornerPaths f d (toNNReal t) = f fun i ↦ t * d i := by
  simp [cornerPaths]

@[simp]
theorem source_cornerPaths (f : C(ι → I, X)) (d : ι → I) : (cornerPaths f d).source = f 0 := by
  simp [cornerPaths, Pi.zero_def]

@[simp]
theorem target_cornerPaths (f : C(ι → I, X)) (d : ι → I) : (cornerPaths f d).target = f d := by
  simp [cornerPaths]

@[simp]
theorem length_cornerPaths (f : C(ι → I, X)) (d : ι → I) : (cornerPaths f d).length = 1 := by
  simp [cornerPaths]

end MoorePath

end TauCeti
