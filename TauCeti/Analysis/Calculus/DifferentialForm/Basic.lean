/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic

/-!
# Locality and linear pullback of the exterior derivative

The exterior derivative `extDerivWithin ω s x` of a differential form on a normed space is the
alternatization of `fderivWithin 𝕜 ω s x`, so, like the derivative, it only sees the set `s`
near `x`. These are the exterior-derivative versions of `fderivWithin_congr_set'` and
`fderivWithin_congr_set`; they are what makes the exterior derivative of forms on manifolds,
computed in charts, insensitive to the set away from the base point.

`ContinuousLinearMap.extDerivWithin_pullback` also proves naturality under a fixed linear map
using only within-set differentiability, with no second derivative or interior-density hypothesis.
`ContinuousLinearMap.extDerivWithin_compContinuousAlternatingMap` is the corresponding naturality
in the coefficient space, and `TauCeti.extDerivWithin_smul_field` extends `extDerivWithin_smul` to
scalars, such as `ℂ`, that act on the coefficients but not on the domain.
-/

public section

open Filter Set
open scoped Topology

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : ℕ} {ω : E → E [⋀^Fin n]→L[𝕜] F} {s t : Set E} {x : E}

namespace TauCeti

/-- The exterior derivative within a set does not change when the set is modified away from a
point `y`, as long as it is unchanged near the base point (punctured at `y`). -/
theorem extDerivWithin_congr_set' (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    extDerivWithin ω s x = extDerivWithin ω t x := by
  rw [extDerivWithin, extDerivWithin, fderivWithin_congr_set' y h]

/-- The exterior derivative within a set only depends on the germ of the set at the base
point. -/
theorem extDerivWithin_congr_set (h : s =ᶠ[𝓝 x] t) :
    extDerivWithin ω s x = extDerivWithin ω t x :=
  extDerivWithin_congr_set' x <| h.filter_mono inf_le_left

/-- Iterating the exterior derivative within a set still depends only on the germ of that set. -/
theorem extDerivWithin_extDerivWithin_congr_set (h : s =ᶠ[𝓝 x] t) :
    extDerivWithin (extDerivWithin ω s) s x = extDerivWithin (extDerivWithin ω t) t x := by
  rw [extDerivWithin_congr_set h]
  apply Filter.EventuallyEq.extDerivWithin_eq
  · filter_upwards [h.eventuallyEq_nhds.filter_mono nhdsWithin_le_nhds] with y hy
    exact extDerivWithin_congr_set hy
  · exact extDerivWithin_congr_set h

/-- The exterior derivative within a set commutes with multiplication of the coefficients by a
scalar from a division semiring acting on the coefficient space, such as `ℂ` acting on a complex
space regarded over `ℝ`. No differentiability is needed. -/
theorem extDerivWithin_smul_field {R : Type*} [DivisionSemiring R] [Module R F]
    [SMulCommClass 𝕜 R F] [ContinuousConstSMul R F] (c : R) (ω : E → E [⋀^Fin n]→L[𝕜] F)
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    extDerivWithin (c • ω) s x = c • extDerivWithin ω s x := by
  have h := fderivWithin_const_smul_field (f := ω) c hs
  rw [extDerivWithin, extDerivWithin, h]
  exact ContinuousAlternatingMap.alternatizeUncurryFin_smul c _

/-- The exterior derivative commutes with multiplication of the coefficients by a scalar from a
division semiring acting on the coefficient space. -/
theorem extDeriv_smul_field {R : Type*} [DivisionSemiring R] [Module R F]
    [SMulCommClass 𝕜 R F] [ContinuousConstSMul R F] (c : R) (ω : E → E [⋀^Fin n]→L[𝕜] F) :
    extDeriv (c • ω) x = c • extDeriv ω x := by
  simp only [← extDerivWithin_univ, extDerivWithin_smul_field c ω uniqueDiffWithinAt_univ]

end TauCeti

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : ℕ}

/-- The exterior derivative of a continuous linear differential form is its alternatization. -/
@[simp]
lemma extDeriv_eq (ω : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) (x : E) :
    extDeriv ω x = ContinuousAlternatingMap.alternatizeUncurryFin ω := by
  simp [extDeriv]

/-- Exterior differentiation commutes with pullback by a continuous linear map, with only
within-set differentiability of the form. -/
theorem extDerivWithin_pullback {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    (L : E →L[𝕜] E') {ω : E' → E' [⋀^Fin n]→L[𝕜] F}
    {s : Set E} {t : Set E'} {x : E} (hs : UniqueDiffWithinAt 𝕜 s x)
    (hω : DifferentiableWithinAt 𝕜 ω t (L x)) (hL : MapsTo L s t) :
    extDerivWithin (fun y ↦ (ω (L y)).compContinuousLinearMap L) s x =
      (extDerivWithin ω t (L x)).compContinuousLinearMap L := by
  let C := ContinuousAlternatingMap.compContinuousLinearMapCLM (F := F) (ι := Fin n) L
  have hd := (C.hasFDerivAt.comp_hasFDerivWithinAt x
    (hω.hasFDerivWithinAt.comp x L.hasFDerivAt.hasFDerivWithinAt hL)).fderivWithin hs
  -- Express the flat pullback as a composite with the continuous-linear pullback operator.
  change fderivWithin 𝕜 (fun y ↦ (ω (L y)).compContinuousLinearMap L) s x =
    C.comp ((fderivWithin 𝕜 ω t (L x)).comp L) at hd
  ext v
  simp only [extDerivWithin, hd, ContinuousAlternatingMap.alternatizeUncurryFin_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply]
  apply Finset.sum_congr rfl
  intro i _
  rfl

/-- Exterior differentiation commutes with a fixed continuous linear map of coefficients, for a
form differentiable within the set. -/
theorem extDerivWithin_compContinuousAlternatingMap {G : Type*} [NormedAddCommGroup G]
    [NormedSpace 𝕜 G] (L : F →L[𝕜] G) {ω : E → E [⋀^Fin n]→L[𝕜] F} {s : Set E} {x : E}
    (hs : UniqueDiffWithinAt 𝕜 s x) (hω : DifferentiableWithinAt 𝕜 ω s x) :
    extDerivWithin (fun y ↦ L.compContinuousAlternatingMap (ω y)) s x =
      L.compContinuousAlternatingMap (extDerivWithin ω s x) := by
  let C := compContinuousAlternatingMapCLM 𝕜 E F G (Fin n) L
  have hd : fderivWithin 𝕜 (fun y ↦ L.compContinuousAlternatingMap (ω y)) s x =
      C.comp (fderivWithin 𝕜 ω s x) :=
    (C.hasFDerivAt.comp_hasFDerivWithinAt x hω.hasFDerivWithinAt).fderivWithin hs
  ext v
  simp [extDerivWithin, hd, C, ContinuousAlternatingMap.alternatizeUncurryFin_apply]

/-- Exterior differentiation commutes with a fixed continuous linear map of coefficients, for a
differentiable form. -/
theorem extDeriv_compContinuousAlternatingMap {G : Type*} [NormedAddCommGroup G]
    [NormedSpace 𝕜 G] (L : F →L[𝕜] G) {ω : E → E [⋀^Fin n]→L[𝕜] F} {x : E}
    (hω : DifferentiableAt 𝕜 ω x) :
    extDeriv (fun y ↦ L.compContinuousAlternatingMap (ω y)) x =
      L.compContinuousAlternatingMap (extDeriv ω x) := by
  simp only [← extDerivWithin_univ]
  exact L.extDerivWithin_compContinuousAlternatingMap uniqueDiffWithinAt_univ
    hω.differentiableWithinAt

end ContinuousLinearMap

end
