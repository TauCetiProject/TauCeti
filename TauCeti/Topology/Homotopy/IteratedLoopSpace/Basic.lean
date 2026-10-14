/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Path
public import TauCeti.Topology.Category.BasedTopologicalSpace

/-!
# Iterated loop spaces

The loop space of a based topological space, as Mathlib's `Path x x` based at the constant loop,
and its `k`-fold iterate. Iterated loop spaces are the based mapping spaces out of spheres,
`Map_*(S^k, X) ≅ Ω^[k] X`; the constructions here do not involve homotopy groups.

## Main declarations

* `TauCeti.BasedTopologicalSpace.loopSpace`: the loop space `Ω X`, based at the constant loop.
* `TauCeti.BasedTopologicalSpace.iteratedLoopSpace`: the `k`-fold iterated loop space `Ω^[k] X`,
  with `iteratedLoopSpace_zero` and `iteratedLoopSpace_succ` its two defining equations.
* `TauCeti.BasedTopologicalSpace.Hom.loopSpace` and
  `TauCeti.BasedTopologicalSpace.Hom.iteratedLoopSpace`: the induced maps `Ω f` and `Ω^[k] f`,
  given by postcomposition, compatible with identities and composition.
-/

public section

universe u

namespace TauCeti

namespace BasedTopologicalSpace

/-- The loop space `Ω X`: loops at the basepoint, based at the constant loop. -/
-- Exposed so that equivalences out of `iteratedLoopSpace` can be defined by recursion in other
-- modules; users should go through `iteratedLoopSpace_zero` and `iteratedLoopSpace_succ`.
@[expose] def loopSpace (X : BasedTopologicalSpace.{u}) : BasedTopologicalSpace.{u} where
  carrier := Path X.basepoint X.basepoint
  basepoint := Path.refl X.basepoint

/-- The `k`-fold iterated loop space `Ω^[k] X`, the `k`-th iterate of `loopSpace` at `X`. -/
-- Exposed for the same reason as `loopSpace`.
@[expose] def iteratedLoopSpace (X : BasedTopologicalSpace.{u}) (k : ℕ) :
    BasedTopologicalSpace.{u} :=
  loopSpace^[k] X

/-- The zeroth iterated loop space is the space itself. -/
@[simp]
theorem iteratedLoopSpace_zero (X : BasedTopologicalSpace.{u}) : X.iteratedLoopSpace 0 = X :=
  Function.iterate_zero_apply _ _

/-- The `(k + 1)`-fold iterated loop space is the `k`-fold iterated loop space of the loop space,
the form in which the iterate unfolds. -/
@[simp]
theorem iteratedLoopSpace_succ (X : BasedTopologicalSpace.{u}) (k : ℕ) :
    X.iteratedLoopSpace (k + 1) = X.loopSpace.iteratedLoopSpace k :=
  Function.iterate_succ_apply _ _ _

/-- The `(k + 1)`-fold iterated loop space is the loop space of the `k`-fold one. -/
theorem iteratedLoopSpace_succ' (X : BasedTopologicalSpace.{u}) (k : ℕ) :
    X.iteratedLoopSpace (k + 1) = (X.iteratedLoopSpace k).loopSpace :=
  Function.iterate_succ_apply' _ _ _

/-- A loop in the loop space is a function on the unit interval. -/
instance (X : BasedTopologicalSpace.{u}) :
    FunLike X.loopSpace.carrier unitInterval X.carrier :=
  inferInstanceAs (FunLike (Path X.basepoint X.basepoint) unitInterval X.carrier)

@[simp]
theorem loopSpace_carrier (X : BasedTopologicalSpace.{u}) :
    X.loopSpace.carrier = Path X.basepoint X.basepoint :=
  rfl

@[simp]
theorem loopSpace_basepoint (X : BasedTopologicalSpace.{u}) :
    X.loopSpace.basepoint = Path.refl X.basepoint :=
  rfl

namespace Hom

variable {X Y Z : BasedTopologicalSpace.{u}}

/-- The map `Ω f : Ω X → Ω Y` induced by a based map `f`: postcomposition of loops with `f`. -/
def loopSpace (f : Hom X Y) : Hom X.loopSpace Y.loopSpace where
  toContinuousMap :=
    ⟨fun γ => (γ.map (map_continuous f)).cast f.map_basepoint.symm f.map_basepoint.symm,
      continuous_induced_rng.2 <|
        (ContinuousMap.continuous_postcomp f.toContinuousMap).comp continuous_induced_dom⟩
  map_basepoint := by
    exact DFunLike.ext _ _ fun _ => f.map_basepoint

/-- The induced loop map postcomposes loops with `f`, for a loop viewed as an element of the
carrier of `ΩX`. -/
theorem loopSpace_apply' (f : Hom X Y) (γ : X.loopSpace.carrier) (t : unitInterval) :
    f.loopSpace γ t = f (γ t) := by
  rw [loopSpace]
  rfl

/-- The induced loop map postcomposes loops with `f`. -/
@[simp]
theorem loopSpace_apply (f : Hom X Y) (γ : Path X.basepoint X.basepoint) (t : unitInterval) :
    @DFunLike.coe (Path Y.basepoint Y.basepoint) unitInterval (fun _ => Y.carrier) _
      (@DFunLike.coe (X.loopSpace.Hom Y.loopSpace) (Path X.basepoint X.basepoint)
        (fun _ => Path Y.basepoint Y.basepoint) _ f.loopSpace γ) t = f (γ t) :=
  loopSpace_apply' f γ t

@[simp]
theorem loopSpace_id (X : BasedTopologicalSpace.{u}) : (Hom.id X).loopSpace = Hom.id X.loopSpace :=
  DFunLike.ext _ _ fun γ => DFunLike.ext _ _ fun t => by
    rw [loopSpace_apply', Hom.id_apply, Hom.id_apply]

@[simp]
theorem loopSpace_comp (g : Hom Y Z) (f : Hom X Y) :
    (g.comp f).loopSpace = g.loopSpace.comp f.loopSpace :=
  DFunLike.ext _ _ fun γ => DFunLike.ext _ _ fun t => by
    simp only [loopSpace_apply', Hom.comp_apply]

/-- The map `Ω^[k] f : Ω^[k] X → Ω^[k] Y` induced by a based map `f`. -/
def iteratedLoopSpace : (k : ℕ) → {X Y : BasedTopologicalSpace.{u}} → Hom X Y →
    Hom (X.iteratedLoopSpace k) (Y.iteratedLoopSpace k)
  | 0, _, _, f => f
  | k + 1, _, _, f => iteratedLoopSpace k f.loopSpace

@[simp]
theorem iteratedLoopSpace_zero (f : Hom X Y) : f.iteratedLoopSpace 0 = f := by
  rw [iteratedLoopSpace.eq_1]

@[simp]
theorem iteratedLoopSpace_succ (f : Hom X Y) (k : ℕ) :
    f.iteratedLoopSpace (k + 1) = f.loopSpace.iteratedLoopSpace k := by
  rw [iteratedLoopSpace.eq_2]

@[simp]
theorem iteratedLoopSpace_id (X : BasedTopologicalSpace.{u}) :
    ∀ k : ℕ, (Hom.id X).iteratedLoopSpace k = Hom.id (X.iteratedLoopSpace k)
  -- the sides differ only by the definitional unfolding of `iteratedLoopSpace` at `k = 0`
  | 0 => by rw [iteratedLoopSpace_zero]; rfl
  -- the sides differ only by the definitional unfolding `Ω^[k + 1] X = Ω^[k] (Ω X)`
  | k + 1 => by
    rw [iteratedLoopSpace_succ, loopSpace_id, iteratedLoopSpace_id X.loopSpace k]; rfl

@[simp]
theorem iteratedLoopSpace_comp (g : Hom Y Z) (f : Hom X Y) (k : ℕ) :
    (g.comp f).iteratedLoopSpace k = (g.iteratedLoopSpace k).comp (f.iteratedLoopSpace k) := by
  -- in each case the sides differ only by the definitional unfolding of the iterate,
  -- `Ω^[0] X = X` and `Ω^[k + 1] X = Ω^[k] (Ω X)`
  induction k generalizing X Y Z with
  | zero => rw [iteratedLoopSpace_zero, iteratedLoopSpace_zero, iteratedLoopSpace_zero]; rfl
  | succ k ih =>
    rw [iteratedLoopSpace_succ, iteratedLoopSpace_succ, iteratedLoopSpace_succ, loopSpace_comp,
      ih]; rfl

end Hom

end BasedTopologicalSpace

end TauCeti
