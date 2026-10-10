/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5

Staged for Tau Ceti: the Banach-space Sylvester lower bound.
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# The Sylvester lower bound from an inverse-norm bound

If `A` has a bounded left inverse with `‖A⁻¹‖ ≤ (ρ + δ)⁻¹` and `‖B‖ ≤ ρ`, then
every solution of

```
A X - X B = C
```

satisfies `δ ‖X‖ ≤ ‖C‖`.

## Why this is not an inner-product statement

Davis--Kahan 1970 Theorem 5.1 is stated for **Banach** spaces and for *any
compatible operator norm*, and the argument really does use nothing else: from
`A X = C + X B` and a left inverse,

`X = A⁻¹ C + A⁻¹ X B`,

so `‖X‖ ≤ ‖A⁻¹‖‖C‖ + ‖A⁻¹‖‖X‖‖B‖ ≤ (ρ+δ)⁻¹(‖C‖ + ρ‖X‖)`, and multiplying by
`ρ + δ` cancels `ρ‖X‖` from both sides.  No inner product, no self-adjointness,
no completeness, no spectral theory, and no Neumann series — the series is
needed for *existence* of a solution, not for the bound on one.

The repository's other Sylvester lower bounds all assume a Hilbert space,
because they are proved through coercivity or through the spectral theorem.
This one is the source statement.

## "Any compatible operator norm"

`opNorm_le_of_sylvester_of_leftInverse` is stated for an arbitrary function
`N` on `F →L[𝕜] E` subject to exactly the three properties the proof consumes:
subadditivity and the two one-sided ideal bounds.  Those are what "compatible
operator norm" means, and they are also what a symmetric-norm-ideal gauge
supplies, so the same theorem covers the unitarily-invariant-norm reading of
Theorem 5.1.  `norm_le_of_sylvester_of_leftInverse` is the specialisation to
the operator norm itself.

## Main results

* `TauCeti.ContinuousLinearMap.opNorm_le_of_sylvester_of_leftInverse`
* `TauCeti.ContinuousLinearMap.norm_le_of_sylvester_of_leftInverse`

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForTauCeti`; it has had no prior home.
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** — the `ForTauCeti` import firewall admits only
  Mathlib, `TauCeti` and `ForTauCeti`.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **The Sylvester equation solved for `X` through a left inverse of `A`.**

`A X = C + X B`, so applying `A⁻¹` on the left gives `X = A⁻¹C + A⁻¹ X B`.  This
is the fixed-point form the estimate below is read off. -/
theorem eq_leftInverse_comp_add_of_sylvester
    {A Ainv : E →L[𝕜] E}
    (hinv : Ainv ∘L A = ContinuousLinearMap.id 𝕜 E)
    {B : F →L[𝕜] F} {X C : F →L[𝕜] E}
    (hEq : A ∘L X - X ∘L B = C) :
    X = Ainv ∘L C + Ainv ∘L (X ∘L B) := by
  have hAX : A ∘L X = C + X ∘L B := by rw [← hEq]; abel
  calc X = ContinuousLinearMap.id 𝕜 E ∘L X := by
        rw [ContinuousLinearMap.id_comp]
    _ = (Ainv ∘L A) ∘L X := by rw [hinv]
    _ = Ainv ∘L (A ∘L X) := ContinuousLinearMap.comp_assoc _ _ _
    _ = Ainv ∘L (C + X ∘L B) := by rw [hAX]
    _ = Ainv ∘L C + Ainv ∘L (X ∘L B) := by rw [ContinuousLinearMap.comp_add]

/-- Absorb a left-inverse fixed-point estimate in any compatible operator size.

This is the analytic core of the bounded and partial-map Sylvester estimates.  It
only uses the fixed-point identity `X = L C + L X B`, the inverse norm bound, and
the two ideal inequalities for the chosen size function. -/
theorem opNorm_le_of_leftInverse_fixedPoint
    {N : (F →L[𝕜] E) → ℝ}
    (hadd : ∀ f g : F →L[𝕜] E, N (f + g) ≤ N f + N g)
    (hidealL : ∀ (C : E →L[𝕜] E) (f : F →L[𝕜] E), N (C ∘L f) ≤ ‖C‖ * N f)
    (hidealR : ∀ (f : F →L[𝕜] E) (C : F →L[𝕜] F), N (f ∘L C) ≤ N f * ‖C‖)
    (hNnonneg : ∀ f : F →L[𝕜] E, 0 ≤ N f)
    {L : E →L[𝕜] E} {B : F →L[𝕜] F} {X C : F →L[𝕜] E} {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ : 0 < δ)
    (hL : ‖L‖ ≤ (ρ + δ)⁻¹) (hB : ‖B‖ ≤ ρ)
    (hfix : X = L ∘L C + L ∘L (X ∘L B)) :
    δ * N X ≤ N C := by
  have hρδ : 0 < ρ + δ := by linarith
  have hstep : N X ≤ ‖L‖ * N C + ‖L‖ * (N X * ‖B‖) := by
    calc
      N X = N (L ∘L C + L ∘L (X ∘L B)) := by rw [← hfix]
      _ ≤ N (L ∘L C) + N (L ∘L (X ∘L B)) := hadd _ _
      _ ≤ ‖L‖ * N C + ‖L‖ * N (X ∘L B) :=
        add_le_add (hidealL _ _) (hidealL _ _)
      _ ≤ ‖L‖ * N C + ‖L‖ * (N X * ‖B‖) :=
        add_le_add le_rfl
          (mul_le_mul_of_nonneg_left (hidealR _ _) (norm_nonneg L))
  have hbound : N X ≤ (ρ + δ)⁻¹ * N C + (ρ + δ)⁻¹ * (N X * ρ) := by
    refine hstep.trans (add_le_add ?_ ?_)
    · exact mul_le_mul_of_nonneg_right hL (hNnonneg C)
    · exact mul_le_mul hL (mul_le_mul_of_nonneg_left hB (hNnonneg X))
        (mul_nonneg (hNnonneg X) (norm_nonneg B)) (inv_nonneg.mpr hρδ.le)
  have hmul : (ρ + δ) * N X ≤ N C + N X * ρ := by
    have h := mul_le_mul_of_nonneg_left hbound hρδ.le
    rwa [mul_add, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hρδ.ne', one_mul, one_mul] at h
  nlinarith [hmul]

/-- **Davis--Kahan 1970 Theorem 5.1, for any compatible operator norm.**

`N` is an arbitrary size function on `F →L[𝕜] E` subject to the three
properties the proof uses: subadditivity, and the two one-sided ideal bounds.
An operator norm has them, and so does a symmetric-norm-ideal gauge, so this one
statement covers both readings of the source theorem.

The hypotheses are the source's: a bounded left inverse of `A` with
`‖A⁻¹‖ ≤ (ρ + δ)⁻¹`, and `‖B‖ ≤ ρ`. -/
theorem opNorm_le_of_sylvester_of_leftInverse
    {N : (F →L[𝕜] E) → ℝ}
    (hadd : ∀ f g : F →L[𝕜] E, N (f + g) ≤ N f + N g)
    (hidealL : ∀ (C : E →L[𝕜] E) (f : F →L[𝕜] E), N (C ∘L f) ≤ ‖C‖ * N f)
    (hidealR : ∀ (f : F →L[𝕜] E) (C : F →L[𝕜] F), N (f ∘L C) ≤ N f * ‖C‖)
    (hNnonneg : ∀ f : F →L[𝕜] E, 0 ≤ N f)
    {A Ainv : E →L[𝕜] E}
    (hinv : Ainv ∘L A = ContinuousLinearMap.id 𝕜 E)
    {B : F →L[𝕜] F} {X C : F →L[𝕜] E} {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ : 0 < δ)
    (hAinv : ‖Ainv‖ ≤ (ρ + δ)⁻¹) (hB : ‖B‖ ≤ ρ)
    (hEq : A ∘L X - X ∘L B = C) :
    δ * N X ≤ N C := by
  have hρδ : 0 < ρ + δ := by linarith
  have hX : X = Ainv ∘L C + Ainv ∘L (X ∘L B) :=
    eq_leftInverse_comp_add_of_sylvester hinv hEq
  -- `N X ≤ ‖A⁻¹‖ N C + ‖A⁻¹‖ (N X) ‖B‖`.
  have hstep : N X ≤ ‖Ainv‖ * N C + ‖Ainv‖ * (N X * ‖B‖) := by
    calc N X = N (Ainv ∘L C + Ainv ∘L (X ∘L B)) := by rw [← hX]
      _ ≤ N (Ainv ∘L C) + N (Ainv ∘L (X ∘L B)) := hadd _ _
      _ ≤ ‖Ainv‖ * N C + ‖Ainv‖ * N (X ∘L B) :=
          add_le_add (hidealL _ _) (hidealL _ _)
      _ ≤ ‖Ainv‖ * N C + ‖Ainv‖ * (N X * ‖B‖) :=
          add_le_add le_rfl
            (mul_le_mul_of_nonneg_left (hidealR _ _) (norm_nonneg _))
  -- Insert the two hypotheses on `‖A⁻¹‖` and `‖B‖`.
  have hbound : N X ≤ (ρ + δ)⁻¹ * N C + (ρ + δ)⁻¹ * (N X * ρ) := by
    refine hstep.trans (add_le_add ?_ ?_)
    · exact mul_le_mul_of_nonneg_right hAinv (hNnonneg C)
    · exact mul_le_mul hAinv (mul_le_mul_of_nonneg_left hB (hNnonneg X))
        (mul_nonneg (hNnonneg X) (norm_nonneg B)) (inv_nonneg.mpr hρδ.le)
  -- Clear the inverse and cancel `ρ * N X`.
  have hmul : (ρ + δ) * N X ≤ N C + N X * ρ := by
    have h := mul_le_mul_of_nonneg_left hbound hρδ.le
    rwa [mul_add, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hρδ.ne', one_mul, one_mul] at h
  nlinarith [hmul]

/-- **Davis--Kahan 1970 Theorem 5.1** at the operator norm: with a bounded left
inverse satisfying `‖A⁻¹‖ ≤ (ρ + δ)⁻¹` and `‖B‖ ≤ ρ`, any solution of
`A X - X B = C` obeys `δ ‖X‖ ≤ ‖C‖`.

Banach spaces; no inner product, no completeness, no self-adjointness. -/
theorem norm_le_of_sylvester_of_leftInverse
    {A Ainv : E →L[𝕜] E}
    (hinv : Ainv ∘L A = ContinuousLinearMap.id 𝕜 E)
    {B : F →L[𝕜] F} {X C : F →L[𝕜] E} {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ : 0 < δ)
    (hAinv : ‖Ainv‖ ≤ (ρ + δ)⁻¹) (hB : ‖B‖ ≤ ρ)
    (hEq : A ∘L X - X ∘L B = C) :
    δ * ‖X‖ ≤ ‖C‖ :=
  opNorm_le_of_sylvester_of_leftInverse
    (fun f g => norm_add_le f g)
    (fun C f => ContinuousLinearMap.opNorm_comp_le C f)
    (fun f C => ContinuousLinearMap.opNorm_comp_le f C)
    (fun f => norm_nonneg f)
    hinv hρ hδ hAinv hB hEq


/-- **The Sylvester equation solved through a right inverse of `B`.**

From `A X - X B = C` and `B B⁻¹ = 1`, right composition gives
`X = A X B⁻¹ - C B⁻¹`. -/
theorem eq_comp_rightInverse_sub_of_sylvester
    {B Binv : F →L[𝕜] F}
    (hinv : B ∘L Binv = ContinuousLinearMap.id 𝕜 F)
    {A : E →L[𝕜] E} {X C : F →L[𝕜] E}
    (hEq : A ∘L X - X ∘L B = C) :
    X = (A ∘L X) ∘L Binv - C ∘L Binv := by
  have hXB : X ∘L B = A ∘L X - C := by
    rw [← hEq]
    abel
  calc
    X = X ∘L ContinuousLinearMap.id 𝕜 F := by rw [ContinuousLinearMap.comp_id]
    _ = X ∘L (B ∘L Binv) := by rw [hinv]
    _ = (X ∘L B) ∘L Binv := (ContinuousLinearMap.comp_assoc _ _ _).symm
    _ = (A ∘L X - C) ∘L Binv := by rw [hXB]
    _ = (A ∘L X) ∘L Binv - C ∘L Binv := by rw [ContinuousLinearMap.sub_comp]

/-- **The symmetric Davis--Kahan Theorem 5.1 estimate**, with a bounded right
inverse of the right block.

The size function has the same ideal properties as in the left-inverse theorem,
plus invariance under negation, which is automatic for every norm. -/
theorem opNorm_le_of_sylvester_of_rightInverse
    {N : (F →L[𝕜] E) → ℝ}
    (hadd : ∀ f g : F →L[𝕜] E, N (f + g) ≤ N f + N g)
    (hneg : ∀ f : F →L[𝕜] E, N (-f) = N f)
    (hidealL : ∀ (C : E →L[𝕜] E) (f : F →L[𝕜] E), N (C ∘L f) ≤ ‖C‖ * N f)
    (hidealR : ∀ (f : F →L[𝕜] E) (C : F →L[𝕜] F), N (f ∘L C) ≤ N f * ‖C‖)
    (hNnonneg : ∀ f : F →L[𝕜] E, 0 ≤ N f)
    {B Binv : F →L[𝕜] F}
    (hinv : B ∘L Binv = ContinuousLinearMap.id 𝕜 F)
    {A : E →L[𝕜] E} {X C : F →L[𝕜] E} {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ : 0 < δ)
    (hBinv : ‖Binv‖ ≤ (ρ + δ)⁻¹) (hA : ‖A‖ ≤ ρ)
    (hEq : A ∘L X - X ∘L B = C) :
    δ * N X ≤ N C := by
  have hρδ : 0 < ρ + δ := by linarith
  have hX : X = (A ∘L X) ∘L Binv - C ∘L Binv :=
    eq_comp_rightInverse_sub_of_sylvester hinv hEq
  have hfirst : N ((A ∘L X) ∘L Binv) ≤ ‖A‖ * N X * ‖Binv‖ := by
    calc
      N ((A ∘L X) ∘L Binv) ≤ N (A ∘L X) * ‖Binv‖ := hidealR _ _
      _ ≤ (‖A‖ * N X) * ‖Binv‖ :=
        mul_le_mul_of_nonneg_right (hidealL _ _) (norm_nonneg Binv)
  have hsecond : N (C ∘L Binv) ≤ N C * ‖Binv‖ := hidealR _ _
  have hstep : N X ≤ ‖A‖ * N X * ‖Binv‖ + N C * ‖Binv‖ := by
    calc
      N X = N ((A ∘L X) ∘L Binv - C ∘L Binv) := by rw [← hX]
      _ = N ((A ∘L X) ∘L Binv + -(C ∘L Binv)) := by rw [sub_eq_add_neg]
      _ ≤ N ((A ∘L X) ∘L Binv) + N (-(C ∘L Binv)) := hadd _ _
      _ = N ((A ∘L X) ∘L Binv) + N (C ∘L Binv) := by rw [hneg]
      _ ≤ ‖A‖ * N X * ‖Binv‖ + N C * ‖Binv‖ := add_le_add hfirst hsecond
  have hbound : N X ≤ ρ * N X * (ρ + δ)⁻¹ + N C * (ρ + δ)⁻¹ := by
    refine hstep.trans (add_le_add ?_ ?_)
    · calc
        ‖A‖ * N X * ‖Binv‖ ≤ ρ * N X * ‖Binv‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hA (hNnonneg X)) (norm_nonneg Binv)
        _ ≤ ρ * N X * (ρ + δ)⁻¹ :=
          mul_le_mul_of_nonneg_left hBinv (mul_nonneg hρ (hNnonneg X))
    · exact mul_le_mul_of_nonneg_left hBinv (hNnonneg C)
  have hmul := mul_le_mul_of_nonneg_left hbound hρδ.le
  have hnormalize :
      (ρ + δ) * (ρ * N X * (ρ + δ)⁻¹ + N C * (ρ + δ)⁻¹) =
        ρ * N X + N C := by
    calc
      (ρ + δ) * (ρ * N X * (ρ + δ)⁻¹ + N C * (ρ + δ)⁻¹) =
          ((ρ + δ) * (ρ + δ)⁻¹) * (ρ * N X) +
            ((ρ + δ) * (ρ + δ)⁻¹) * N C := by ring
      _ = ρ * N X + N C := by rw [mul_inv_cancel₀ hρδ.ne']; ring
  rw [hnormalize] at hmul
  nlinarith [hmul]

/-- The right-inverse form of Theorem 5.1 at the ordinary operator norm. -/
theorem norm_le_of_sylvester_of_rightInverse
    {B Binv : F →L[𝕜] F}
    (hinv : B ∘L Binv = ContinuousLinearMap.id 𝕜 F)
    {A : E →L[𝕜] E} {X C : F →L[𝕜] E} {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ : 0 < δ)
    (hBinv : ‖Binv‖ ≤ (ρ + δ)⁻¹) (hA : ‖A‖ ≤ ρ)
    (hEq : A ∘L X - X ∘L B = C) :
    δ * ‖X‖ ≤ ‖C‖ :=
  opNorm_le_of_sylvester_of_rightInverse
    (fun f g => norm_add_le f g)
    (fun f => norm_neg f)
    (fun C f => ContinuousLinearMap.opNorm_comp_le C f)
    (fun f C => ContinuousLinearMap.opNorm_comp_le f C)
    (fun f => norm_nonneg f)
    hinv hρ hδ hBinv hA hEq

end ContinuousLinearMap
