/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Unitization
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import TauCeti.Analysis.CStarAlgebra.Trace.Basic

import TauCeti.Algebra.Algebra.Unitization

/-!
# Unitary invariance of traces

Unitary invariance for traces `τ : B → ℝ≥0∞` (`TauCeti.IsTrace`) on a C⋆-algebra `B`:
`τ(uxu⋆) = τ(x)` for `x ∈ B₊` and every unitary, or more generally every isometry, `u` of the
forced unitization `B^† = Unitization ℂ B`. The product `uxu⋆` lies in `B`, which is an ideal of
`B^†`; it is `z⋆z` for `z = x^{1/2}u⋆ ∈ B`, while `zz⋆ = x^{1/2}u⋆ux^{1/2} = x`, so the trace
identity gives `τ(uxu⋆) = τ(x)`.

## Main definitions

* `Unitization.conjStar`: the element `uxu⋆` of `B`, for `u ∈ B^†` and `x ∈ B`.

## Main results

* `Unitization.inr_conjStar`: `uxu⋆` computed in `B^†` is the image of `u.conjStar x`.
* `TauCeti.IsTrace.map_conjStar`: invariance under conjugation by isometries `u⋆u = 1` of `B^†`.
* `TauCeti.IsTrace.map_conjStar_of_mem_unitary`: unitary invariance.
-/

public section

open scoped ENNReal NNReal

variable {B : Type*} [NonUnitalCStarAlgebra B]

namespace Unitization

/-- The element `uxu⋆` of `B`, for `u` in the unitization `B^†` and `x ∈ B`: the `B`-part of the
product `uxu⋆` computed in `B^†`, which lies in the ideal `B`. -/
def conjStar (u : Unitization ℂ B) (x : B) : B :=
  (u * (x : Unitization ℂ B) * star u).snd

/-- `uxu⋆` computed in `B^†` is the image of `u.conjStar x`. -/
@[simp]
theorem inr_conjStar (u : Unitization ℂ B) (x : B) :
    (inr (u.conjStar x) : Unitization ℂ B) = u * (x : Unitization ℂ B) * star u :=
  inr_snd_of_fst_eq_zero (by simp)

end Unitization

namespace TauCeti

variable [PartialOrder B] [StarOrderedRing B] {τ : B → ℝ≥0∞}

namespace IsTrace

/-- **Isometric invariance of traces**: `τ(uxu⋆) = τ(x)` for `x ∈ B₊` and every isometry
`u⋆u = 1` of the forced unitization `B^†`. -/
theorem map_conjStar (hτ : IsTrace τ) {u : Unitization ℂ B} (hu : star u * u = 1) {x : B}
    (hx : 0 ≤ x) : τ (u.conjStar x) = τ x := by
  -- `z = x^{1/2} u⋆ ∈ B` has `z⋆z = uxu⋆` and `zz⋆ = x`.
  set s := CFC.sqrt x
  have hs : star s = s := (CFC.sqrt_nonneg x).isSelfAdjoint.star_eq
  have hss : s * s = x := CFC.sqrt_mul_sqrt_self x hx
  set z : B := ((s : Unitization ℂ B) * star u).snd
  have hz : (z : Unitization ℂ B) = (s : Unitization ℂ B) * star u :=
    Unitization.inr_snd_of_fst_eq_zero (by simp)
  have hsu : star (s : Unitization ℂ B) = s := by rw [← Unitization.inr_star, hs]
  have h₁ : star z * z = u.conjStar x := Unitization.inr_injective (R := ℂ) <| by
    simp [hz, ← hss, hsu, mul_assoc]
  have h₂ : z * star z = x := Unitization.inr_injective (R := ℂ) <| by
    simp [hz, ← hss, hsu, mul_assoc, ← mul_assoc (star u), hu]
  rw [← h₁, hτ.map_star_mul_self, h₂]

/-- **Unitary invariance of traces**: `τ(uxu⋆) = τ(x)` for `x ∈ B₊` and every unitary `u` of the
forced unitization `B^†`. -/
theorem map_conjStar_of_mem_unitary (hτ : IsTrace τ) {u : Unitization ℂ B}
    (hu : u ∈ unitary (Unitization ℂ B)) {x : B} (hx : 0 ≤ x) : τ (u.conjStar x) = τ x :=
  hτ.map_conjStar (Unitary.star_mul_self_of_mem hu) hx

end IsTrace

end TauCeti
