/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Half-spaces and epigraphs in an ℓ² product

This file defines the open normal half-space and the open region above the graph of a continuous
function in `WithLp 2 (ℝ × E)`. These are the model domains used by graph flattening and Sobolev
trace theory.

## Main declarations

* `TauCeti.normalHalfSpace`: the region above a constant normal coordinate.
* `TauCeti.normalEpigraph`: the region above the graph of a continuous function.
-/

public section

namespace TauCeti

open Set TopologicalSpace

variable {E : Type*} [NormedAddCommGroup E]

/-- The open half-space to the right of the normal coordinate `a` in the ℓ² product `ℝ × E`. -/
def normalHalfSpace (a : ℝ) : Opens (WithLp 2 (ℝ × E)) :=
  ⟨{x | a < (WithLp.ofLp x).1},
    isOpen_lt continuous_const (WithLp.prod_continuous_ofLp 2 ℝ E).fst⟩

/-- Membership in the normal-coordinate half-space is a strict inequality. -/
@[simp]
theorem mem_normalHalfSpace (a : ℝ) (x : WithLp 2 (ℝ × E)) :
    x ∈ normalHalfSpace (E := E) a ↔ a < (WithLp.ofLp x).1 := Iff.rfl

/-- As a set, the right normal half-space is `{x | a < x.fst}`. -/
theorem coe_normalHalfSpace (a : ℝ) :
    (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) =
      {x | a < (WithLp.ofLp x).1} :=
  Set.ext (mem_normalHalfSpace a)

/-- The open region `{x | φ x.snd < x.fst}` above the graph of a continuous function
`φ : E → ℝ` in the ℓ² product `ℝ × E`. -/
def normalEpigraph (φ : C(E, ℝ)) : Opens (WithLp 2 (ℝ × E)) :=
  ⟨{x | φ x.snd < x.fst}, isOpen_lt (by fun_prop) (by fun_prop)⟩

/-- Membership in the region above the graph is a strict inequality. -/
@[simp]
theorem mem_normalEpigraph (φ : C(E, ℝ)) (x : WithLp 2 (ℝ × E)) :
    x ∈ normalEpigraph φ ↔ φ x.snd < x.fst :=
  Iff.rfl

/-- As a set, the region above the graph is `{x | φ x.snd < x.fst}`. -/
theorem coe_normalEpigraph (φ : C(E, ℝ)) :
    (normalEpigraph φ : Set (WithLp 2 (ℝ × E))) = {x | φ x.snd < x.fst} :=
  Set.ext (mem_normalEpigraph φ)

/-- The region above the graph of `0` is the half-space `{0 < t}`. -/
@[simp]
theorem normalEpigraph_zero : normalEpigraph (0 : C(E, ℝ)) = normalHalfSpace 0 := by
  ext x
  simp

end TauCeti

end
