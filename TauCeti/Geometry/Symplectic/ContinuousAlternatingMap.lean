/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Alternating.Basic
public import TauCeti.Geometry.Symplectic.AlmostComplex
public import TauCeti.LinearAlgebra.BilinearMap.Multilinear

/-!
# Symplectic forms from continuous alternating two-forms

`SymplecticForm.ofContinuousAlternatingMap` reads a nondegenerate continuous alternating
map in two variables as an algebraic symplectic form. Nondegeneracy need only be checked
in the left variable, since alternation supplies the corresponding right-variable condition.
The evaluation lemma identifies the resulting bilinear form with the original two-form.
-/

public section

namespace TauCeti.SymplecticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

/-- A continuous alternating two-form with trivial left kernel gives an algebraic symplectic
form. No finite-dimensionality assumption is needed. -/
def ofContinuousAlternatingMap (ω : V [⋀^Fin 2]→L[ℝ] ℝ)
    (hnd : ∀ v, (∀ w, ω ![v, w] = 0) → v = 0) : SymplecticForm V where
  toBilinForm := ω.toAlternatingMap.toMultilinearMap.toBilinMap
  isAlt := ω.toAlternatingMap.isAlt_toBilinMap
  nondegenerate := ω.toAlternatingMap.isAlt_toBilinMap.isRefl.nondegenerate_iff_separatingLeft.mpr
    (fun v hv ↦ hnd v fun w ↦ (MultilinearMap.toBilinMap_apply _ v w).symm.trans (hv w))

/-- The symplectic form constructed from a continuous two-form has the same evaluations. -/
@[simp]
theorem ofContinuousAlternatingMap_apply (ω : V [⋀^Fin 2]→L[ℝ] ℝ)
    (hnd : ∀ v, (∀ w, ω ![v, w] = 0) → v = 0) (v w : V) :
    ofContinuousAlternatingMap ω hnd v w = ω ![v, w] :=
  MultilinearMap.toBilinMap_apply _ v w

end TauCeti.SymplecticForm
