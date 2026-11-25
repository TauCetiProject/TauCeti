/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Unitization
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import TauCeti.Analysis.CStarAlgebra.Trace.Basic

/-!
# Unitary invariance and directed suprema of traces

Two further parts of TracesOnCStarAlgebras Tr1.1 for traces `τ : B → ℝ≥0∞`
(`TauCeti.IsTrace`) on a C⋆-algebra `B`:

* **Unitary invariance** (`TauCeti.IsTrace.map_unitary_conj`): `τ(uxu⋆) = τ(x)` for `x ∈ B₊`
  and every unitary `u` of the forced unitization `B^† = Unitization ℂ B`. The product `uxu⋆`
  lies in `B`, which is an ideal of `B^†`; it is `z⋆z` for `z = x^{1/2}u⋆ ∈ B`, while
  `zz⋆ = x^{1/2}u⋆ux^{1/2} = x`, so the trace identity gives `τ(uxu⋆) = τ(x)`.
* **Directed suprema** (`TauCeti.IsTrace.iSup`): the pointwise supremum of an upward directed
  family of traces is a trace, since in `[0, ∞]` suprema of directed families commute with sums
  and with multiplication by a constant.

## Main definitions

* `TauCeti.unitaryConj`: the element `uxu⋆` of `B`, for `u ∈ B^†` and `x ∈ B`.

## Main results

* `TauCeti.coe_unitaryConj`: `uxu⋆` computed in `B^†` is the image of `TauCeti.unitaryConj`.
* `TauCeti.IsTrace.map_unitary_conj`: unitary invariance.
* `TauCeti.IsTrace.iSup`: suprema of upward directed families of traces are traces.
-/

public section

open scoped ENNReal NNReal

namespace TauCeti

/-- An element of the unitization with scalar part `0` is the image of its `A`-part. -/
theorem _root_.Unitization.inr_snd_of_fst_eq_zero {R A : Type*} [Zero R] {w : Unitization R A}
    (h : w.fst = 0) :
    ((w.snd : A) : Unitization R A) = w :=
  Unitization.ext (by simp [h]) rfl

variable {B : Type*} [NonUnitalCStarAlgebra B]

/-- The element `uxu⋆` of `B`, for `u` in the unitization `B^†` and `x ∈ B`: the `B`-part of the
product `uxu⋆` computed in `B^†`, which lies in the ideal `B`. -/
def unitaryConj (u : Unitization ℂ B) (x : B) : B :=
  (u * (x : Unitization ℂ B) * star u).snd

/-- `uxu⋆` computed in `B^†` is the image of `unitaryConj u x`. -/
@[simp]
theorem coe_unitaryConj (u : Unitization ℂ B) (x : B) :
    ((unitaryConj u x : B) : Unitization ℂ B) = u * (x : Unitization ℂ B) * star u :=
  Unitization.inr_snd_of_fst_eq_zero (by simp)

variable [PartialOrder B] [StarOrderedRing B] {τ : B → ℝ≥0∞}

namespace IsTrace

/-- **Unitary invariance of traces**: `τ(uxu⋆) = τ(x)` for `x ∈ B₊` and every unitary `u` of the
forced unitization `B^†` (TracesOnCStarAlgebras Tr1.1). -/
theorem map_unitary_conj (hτ : IsTrace τ) {u : Unitization ℂ B}
    (hu : u ∈ unitary (Unitization ℂ B)) {x : B} (hx : 0 ≤ x) :
    τ (unitaryConj u x) = τ x := by
  -- `z = x^{1/2} u⋆ ∈ B` has `z⋆z = uxu⋆` and `zz⋆ = x`.
  set s := CFC.sqrt x
  have hs : star s = s := (CFC.sqrt_nonneg x).isSelfAdjoint.star_eq
  have hss : s * s = x := CFC.sqrt_mul_sqrt_self x hx
  set z : B := ((s : Unitization ℂ B) * star u).snd
  have hz : (z : Unitization ℂ B) = (s : Unitization ℂ B) * star u :=
    Unitization.inr_snd_of_fst_eq_zero (by simp)
  have hsu : star (s : Unitization ℂ B) = s := by rw [← Unitization.inr_star, hs]
  have hxx : (x : Unitization ℂ B) = (s : Unitization ℂ B) * s := by
    rw [← Unitization.inr_mul, hss]
  have h₁ : star z * z = unitaryConj u x := Unitization.inr_injective (R := ℂ) <| by
    rw [Unitization.inr_mul, Unitization.inr_star, hz, coe_unitaryConj, star_mul, star_star, hsu,
      hxx]
    simp only [mul_assoc]
  have h₂ : z * star z = x := Unitization.inr_injective (R := ℂ) <| by
    rw [Unitization.inr_mul, Unitization.inr_star, hz, star_mul, star_star, hsu, hxx, mul_assoc,
      ← mul_assoc (star u), Unitary.star_mul_self_of_mem hu, one_mul]
  rw [← h₁, hτ.map_star_mul_self, h₂]

omit [StarOrderedRing B] in
/-- **Directed suprema of traces**: the pointwise supremum of an upward directed family of
traces is a trace (TracesOnCStarAlgebras Tr1.1). -/
protected theorem iSup {ι : Type*} {τ : ι → B → ℝ≥0∞} (hτ : ∀ i, IsTrace (τ i))
    (hd : Directed (· ≤ ·) τ) : IsTrace (⨆ i, τ i) where
  map_add_of_nonneg x y hx hy := by
    simp only [iSup_apply, (hτ _).map_add_of_nonneg hx hy]
    refine (ENNReal.iSup_add_iSup fun i j ↦ ?_).symm
    obtain ⟨k, hik, hjk⟩ := hd i j
    exact ⟨k, add_le_add (hik x) (hjk y)⟩
  map_nnreal_smul_of_nonneg c x hx := by
    simp only [iSup_apply, (hτ _).map_nnreal_smul_of_nonneg c hx, ENNReal.mul_iSup]
  map_star_mul_self x := by
    simp only [iSup_apply, (hτ _).map_star_mul_self]

end IsTrace

end TauCeti
