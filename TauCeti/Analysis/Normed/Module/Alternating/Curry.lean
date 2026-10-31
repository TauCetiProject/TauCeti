/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Alternating.Curry
public import TauCeti.Topology.Algebra.Module.Alternating.Curry

/-!
# Comparing normed and topological interior products

The normed `ContinuousAlternatingMap.curryLeft` agrees pointwise with the norm-free
`ContinuousAlternatingMap.curryLeftTopological`. This comparison lets normed applications use
the topological interior-product API without importing wedge constructions.

Currying a continuous alternating map of two vectors in its first slot and reading the result as
a linear map gives its **flat map** `f ↦ (v ↦ f(v, ·))`, a continuous linear map
`ContinuousAlternatingMap.flatL`.
-/

public section

namespace ContinuousAlternatingMap

variable {E F₁ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]

/-- The normed and norm-free interior products agree on normed spaces. -/
theorem curryLeft_eq_curryLeftTopological {n : ℕ}
    (f : E [⋀^Fin (n + 1)]→L[ℝ] F₁) (x : E) :
    f.curryLeft x = f.curryLeftTopological x := by
  ext v
  simp only [ContinuousAlternatingMap.curryLeft_apply_apply,
    ContinuousAlternatingMap.curryLeftTopological_apply_apply]

section flatL

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (𝕜 E F) in
/-- The **flat map** of continuous alternating maps of two vectors, `f ↦ (v ↦ f(v, ·))`: currying
in the first slot, then reading the resulting alternating map of one vector as a linear map. -/
noncomputable def flatL : (E [⋀^Fin 2]→L[𝕜] F) →L[𝕜] E →L[𝕜] E →L[𝕜] F :=
  ContinuousLinearMap.compL 𝕜 E (E [⋀^Fin 1]→L[𝕜] F) (E →L[𝕜] F)
      (ofSubsingletonLIE (𝕜 := 𝕜) (E := E) (F := F) (ι := Fin 1)
        0).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    (curryLeftLI (𝕜 := 𝕜) (E := E) (F := F) (n := 1)).toContinuousLinearMap

/-- The flat map of `f` at `v`, read back as an alternating map of one vector, is the curried
map `f(v, ·)`. -/
@[simp]
theorem ofSubsingleton_flatL_apply (f : E [⋀^Fin 2]→L[𝕜] F) (v : E) :
    ofSubsingleton 𝕜 E F (0 : Fin 1) (flatL 𝕜 E F f v) = f.curryLeft v :=
  (ofSubsingletonLIE (𝕜 := 𝕜) (E := E) (F := F) (ι := Fin 1) 0).apply_symm_apply _

/-- The flat map evaluates the alternating map on the pair. -/
@[simp]
theorem flatL_apply_apply (f : E [⋀^Fin 2]→L[𝕜] F) (v w : E) : flatL 𝕜 E F f v w = f ![v, w] :=
  DFunLike.congr_fun (ofSubsingleton_flatL_apply f v) ![w]

end flatL

end ContinuousAlternatingMap
