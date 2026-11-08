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
Pulling a two-form back along a continuous linear equivalence preserves this left
nondegeneracy (`ContinuousAlternatingMap.nondegenerate_compContinuousLinearEquiv`).
-/

public section

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

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

namespace ContinuousAlternatingMap

variable {𝕜 F V W : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- A two-form with trivial left kernel, pulled back along a continuous linear equivalence, still
has trivial left kernel. -/
theorem nondegenerate_compContinuousLinearEquiv (a : V [⋀^Fin 2]→L[𝕜] W) (e : F ≃L[𝕜] V)
    (hnd : ∀ v, (∀ w, a ![v, w] = 0) → v = 0) :
    ∀ v, (∀ w, a.compContinuousLinearMap (e : F →L[𝕜] V) ![v, w] = 0) → v = 0 := fun v hv ↦ by
  have hval (u w : F) : a.compContinuousLinearMap (e : F →L[𝕜] V) ![u, w] = a ![e u, e w] := by
    rw [compContinuousLinearMap_apply]
    congr 1
    ext i
    fin_cases i <;> rfl
  refine e.injective ((hnd (e v) fun w ↦ ?_).trans e.map_zero.symm)
  simpa [hval] using hv (e.symm w)

end ContinuousAlternatingMap
