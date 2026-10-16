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

end ContinuousAlternatingMap
