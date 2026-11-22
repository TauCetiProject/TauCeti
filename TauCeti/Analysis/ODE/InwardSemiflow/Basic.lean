/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.ForwardSemiflow.Basic
public import TauCeti.Analysis.Convex.Cone.StrictInward

/-!
# Interior entry and persistence of inward forward semiflows

Proves that the maximal forward semiflow `TauCeti.forwardSemiflow` of a strictly inward vector
field in a convex set `C` immediately enters and remains in `interior C`
(`Convex.forwardSemiflow_mem_interior` and `Convex.forwardSemiflow_mem_interior_of_mem_interior`).
Local existence/continuity and `C^m` regularity appear in `Existence.lean` and `Smooth.lean`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2012, Chapter 9,
  Theorems 9.12 and 9.24–9.26.
* H. Brezis, *On a characterization of flow-invariant sets*, Comm. Pure Appl. Math. 23 (1970),
  261–263.
-/

public section

open Set

section ForwardSemiflowGeometry

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {C S : Set E} {X : E → E} {x : E}

/-- **Interior entry and persistence of `forwardSemiflow`.** When `S ⊆ C` for a convex set `C` and
`X` is strictly inward to `C` on `S`, `forwardSemiflow X S` lies in `interior C` at every strictly
positive time in its forward interval. -/
theorem Convex.forwardSemiflow_mem_interior (hC : Convex ℝ C) (hSC : S ⊆ C)
    (hX_in : ∀ y ∈ S, X y ∈ strictInwardCone C y)
    {t : ℝ} (ht : t ∈ forwardSemiflowInterval X S x) (ht_pos : 0 < t) :
    forwardSemiflow X S t x ∈ interior C := by
  obtain ⟨_, _, _, htI, hγt, _, hS, hγ'⟩ := exists_integralCurve_eq_forwardSemiflow ht
  rw [← hγt]
  exact hC.mapsTo_Ioo_interior_of_hasDerivWithinAt_Ico (hS.mono_right hSC)
    (fun _ hs ↦ hγ' _ (Ioo_subset_Ico_self hs))
    (fun _ hs ↦ hX_in _ (hS (Ioo_subset_Ico_self hs))) ⟨ht_pos, htI.2⟩

/-- If `x ∈ interior C`, then `forwardSemiflow X S t x ∈ interior C` for all times `t` in its
forward interval (including `t = 0`). -/
theorem Convex.forwardSemiflow_mem_interior_of_mem_interior (hC : Convex ℝ C) (hSC : S ⊆ C)
    (hX_in : ∀ y ∈ S, X y ∈ strictInwardCone C y)
    (hx : x ∈ interior C) {t : ℝ} (ht : t ∈ forwardSemiflowInterval X S x) :
    forwardSemiflow X S t x ∈ interior C := by
  rcases (nonneg_of_mem_forwardSemiflowInterval ht).eq_or_lt with rfl | ht_pos
  exacts [by simpa using hx, hC.forwardSemiflow_mem_interior hSC hX_in ht ht_pos]

end ForwardSemiflowGeometry
