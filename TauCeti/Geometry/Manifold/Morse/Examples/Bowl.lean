/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.NormSq
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
public import TauCeti.Geometry.Manifold.Morse.Hessian
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.Morse.Prod

/-!
# The bowl of a product of inner product spaces and of the plane

On a product `E × F` of finite-dimensional real inner product spaces, with its self-model, the
function `(u, v) ↦ ‖u‖ ^ 2 + ‖v‖ ^ 2` is the model of a nondegenerate minimum. This file reads off
its critical data, and that of its negative, as functions on a manifold. The saddle
`(u, v) ↦ -‖u‖ ^ 2 + ‖v‖ ^ 2` is treated in `TauCeti.Geometry.Manifold.Morse.Examples.Saddle`.

* **The bowl model.** On `E × F` the function `(u, v) ↦ ‖u‖ ^ 2 + ‖v‖ ^ 2` has the origin as its
  only critical point (`TauCeti.criticalPoints_norm_sq_add_norm_sq`), so it has one critical point
  (`TauCeti.totalCriticalCount_norm_sq_add_norm_sq`), which is nondegenerate
  (`TauCeti.isMorse_norm_sq_add_norm_sq`), a minimum of Morse index `0`
  (`TauCeti.manifoldMorseIndex_norm_sq_add_norm_sq`). Its negative
  `(u, v) ↦ -‖u‖ ^ 2 - ‖v‖ ^ 2` has Morse index `dim E + dim F`
  (`TauCeti.manifoldMorseIndex_neg_norm_sq_sub_norm_sq`).
* **The bowl of the plane.** For `E = F = ℝ` this is `f (x, y) = x² + y²` on `ℝ × ℝ`. It has the
  origin as its only critical point (`TauCeti.criticalPoints_sq_add_sq`), so it has one critical
  point (`TauCeti.totalCriticalCount_sq_add_sq`), which is nondegenerate
  (`TauCeti.isMorse_sq_add_sq`), a minimum of Morse index `0`
  (`TauCeti.manifoldMorseIndex_sq_add_sq`). Its negative `-x² - y²` has Morse index `2`
  (`TauCeti.manifoldMorseIndex_neg_sq_sub_sq`), the dimension of the plane, so the bowl splits the
  dimension `2` as `0 + 2`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §2, Lemma 2.2 (the Morse lemma), whose normal form at a minimum this model is.
-/

public section

open Set Module
open scoped Manifold

namespace TauCeti

/-! ### The bowl model on a product of inner product spaces -/

section BowlModel

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F]

omit [InnerProductSpace ℝ E] [InnerProductSpace ℝ F] in
/-- The bowl model `(u, v) ↦ ‖u‖ ^ 2 + ‖v‖ ^ 2` as a separated sum. -/
private theorem norm_sq_add_norm_sq_eq_comp :
    (fun p : E × F ↦ ‖p.1‖ ^ 2 + ‖p.2‖ ^ 2) =
      (fun u : E ↦ ‖u‖ ^ 2) ∘ Prod.fst + (fun v : F ↦ ‖v‖ ^ 2) ∘ Prod.snd :=
  rfl

/-- **The origin is the only critical point** of the bowl model `(u, v) ↦ ‖u‖ ^ 2 + ‖v‖ ^ 2`. -/
@[simp]
theorem criticalPoints_norm_sq_add_norm_sq :
    criticalPoints 𝓘(ℝ, E × F) (fun p : E × F ↦ ‖p.1‖ ^ 2 + ‖p.2‖ ^ 2) = {0} := by
  ext ⟨u, v⟩
  rw [mem_criticalPoints_iff_fderiv_eq_zero, norm_sq_add_norm_sq_eq_comp,
    fderiv_comp_fst_add_comp_snd_eq_zero_iff ((contDiff_norm_sq ℝ).differentiable one_ne_zero u)
      ((contDiff_norm_sq ℝ).differentiable one_ne_zero v), fderiv_norm_sq_eq_zero_iff,
    fderiv_norm_sq_eq_zero_iff, mem_singleton_iff, Prod.mk_eq_zero]

/-- The bowl model `(u, v) ↦ ‖u‖ ^ 2 + ‖v‖ ^ 2` has exactly one critical point. -/
@[simp]
theorem totalCriticalCount_norm_sq_add_norm_sq :
    totalCriticalCount 𝓘(ℝ, E × F) (fun p : E × F ↦ ‖p.1‖ ^ 2 + ‖p.2‖ ^ 2) = 1 := by
  rw [totalCriticalCount_def, criticalPoints_norm_sq_add_norm_sq, encard_singleton]

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- **The bowl model `(u, v) ↦ ‖u‖ ^ 2 + ‖v‖ ^ 2` is a Morse function**: its only critical point,
the origin, is nondegenerate. -/
theorem isMorse_norm_sq_add_norm_sq :
    IsMorse 𝓘(ℝ, E × F) (fun p : E × F ↦ ‖p.1‖ ^ 2 + ‖p.2‖ ^ 2) := by
  refine isMorse_modelSpace_iff.2 ⟨((contDiff_norm_sq ℝ).comp contDiff_fst).add
    ((contDiff_norm_sq ℝ).comp contDiff_snd), hasNondegenerateCriticalPointsOn_iff.2
      fun p _ hp ↦ ?_⟩
  have hp0 : p = 0 := by
    simpa using mem_criticalPoints_iff_fderiv_eq_zero.2 hp
  rw [hp0, norm_sq_add_norm_sq_eq_comp, ← Prod.mk_zero_zero]
  exact isNondegenerateCriticalPoint_norm_sq.comp_fst_add_comp_snd
    isNondegenerateCriticalPoint_norm_sq

/-- **The bowl model `(u, v) ↦ ‖u‖ ^ 2 + ‖v‖ ^ 2` has Morse index `0`** at every point. -/
theorem manifoldMorseIndex_norm_sq_add_norm_sq (p : E × F) :
    manifoldMorseIndex 𝓘(ℝ, E × F) (fun p : E × F ↦ ‖p.1‖ ^ 2 + ‖p.2‖ ^ 2) p = 0 := by
  obtain ⟨u, v⟩ := p
  rw [manifoldMorseIndex_modelSpace, norm_sq_add_norm_sq_eq_comp, morseIndex_comp_fst_add_comp_snd
    (contDiff_norm_sq ℝ).contDiffAt (contDiff_norm_sq ℝ).contDiffAt, morseIndex_norm_sq,
    morseIndex_norm_sq]

/-- **The negative `(u, v) ↦ -‖u‖ ^ 2 - ‖v‖ ^ 2` of the bowl model has Morse index
`dim E + dim F`** at every point, the dimension of `E × F`. -/
theorem manifoldMorseIndex_neg_norm_sq_sub_norm_sq (p : E × F) :
    manifoldMorseIndex 𝓘(ℝ, E × F) (fun p : E × F ↦ -‖p.1‖ ^ 2 - ‖p.2‖ ^ 2) p =
      finrank ℝ E + finrank ℝ F := by
  obtain ⟨u, v⟩ := p
  have h : (fun p : E × F ↦ -‖p.1‖ ^ 2 - ‖p.2‖ ^ 2) =
      (fun u : E ↦ -‖u‖ ^ 2) ∘ Prod.fst + (fun v : F ↦ -‖v‖ ^ 2) ∘ Prod.snd := by
    ext p
    simp [sub_eq_add_neg]
  rw [manifoldMorseIndex_modelSpace, h, morseIndex_comp_fst_add_comp_snd
    (contDiff_norm_sq ℝ).neg.contDiffAt (contDiff_norm_sq ℝ).neg.contDiffAt, morseIndex_neg_norm_sq,
    morseIndex_neg_norm_sq]

end BowlModel

/-! ### The bowl of the plane -/

section Bowl

/-- The bowl `x² + y²` of the plane is the bowl model `(u, v) ↦ ‖u‖ ^ 2 + ‖v‖ ^ 2` on `ℝ × ℝ`. -/
private theorem sq_add_sq_eq :
    (fun p : ℝ × ℝ ↦ p.1 ^ 2 + p.2 ^ 2) = fun p : ℝ × ℝ ↦ ‖p.1‖ ^ 2 + ‖p.2‖ ^ 2 := by
  ext p
  simp [Real.norm_eq_abs, sq_abs]

/-- **The origin is the only critical point of the bowl** `x² + y²` of the plane. -/
@[simp]
theorem criticalPoints_sq_add_sq :
    criticalPoints 𝓘(ℝ, ℝ × ℝ) (fun p : ℝ × ℝ ↦ p.1 ^ 2 + p.2 ^ 2) = {0} := by
  rw [sq_add_sq_eq, criticalPoints_norm_sq_add_norm_sq]

/-- The bowl `x² + y²` of the plane has exactly one critical point. -/
@[simp]
theorem totalCriticalCount_sq_add_sq :
    totalCriticalCount 𝓘(ℝ, ℝ × ℝ) (fun p : ℝ × ℝ ↦ p.1 ^ 2 + p.2 ^ 2) = 1 := by
  rw [sq_add_sq_eq, totalCriticalCount_norm_sq_add_norm_sq]

/-- The bowl `x² + y²` of the plane is a Morse function. -/
theorem isMorse_sq_add_sq : IsMorse 𝓘(ℝ, ℝ × ℝ) (fun p : ℝ × ℝ ↦ p.1 ^ 2 + p.2 ^ 2) := by
  rw [sq_add_sq_eq]
  exact isMorse_norm_sq_add_norm_sq

/-- **The bowl `x² + y²` of the plane has Morse index `0`** at every point. -/
theorem manifoldMorseIndex_sq_add_sq (p : ℝ × ℝ) :
    manifoldMorseIndex 𝓘(ℝ, ℝ × ℝ) (fun p : ℝ × ℝ ↦ p.1 ^ 2 + p.2 ^ 2) p = 0 := by
  rw [sq_add_sq_eq, manifoldMorseIndex_norm_sq_add_norm_sq]

/-- **The negative `-x² - y²` of the bowl of the plane has Morse index `2`** at every point, the
dimension of the plane. -/
theorem manifoldMorseIndex_neg_sq_sub_sq (p : ℝ × ℝ) :
    manifoldMorseIndex 𝓘(ℝ, ℝ × ℝ) (fun p : ℝ × ℝ ↦ -p.1 ^ 2 - p.2 ^ 2) p = 2 := by
  have h : (fun p : ℝ × ℝ ↦ -p.1 ^ 2 - p.2 ^ 2) = fun p : ℝ × ℝ ↦ -‖p.1‖ ^ 2 - ‖p.2‖ ^ 2 := by
    ext p
    simp [Real.norm_eq_abs, sq_abs]
  rw [h, manifoldMorseIndex_neg_norm_sq_sub_norm_sq, finrank_self]

end Bowl

end TauCeti
