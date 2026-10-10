/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Reflection

/-!
# Diagonal and off-diagonal blocks of an operator

Let `U` be a submodule of an inner product space `E` admitting an orthogonal projection `P_U`.
Relative to the orthogonal decomposition `E = U ⊕ Uᗮ`, a bounded operator `A` on `E` is a
`2 × 2` block operator. Its *diagonal part* `U.diagBlock A = P_U A P_U + P_{Uᗮ} A P_{Uᗮ}` keeps
the `U → U` and `Uᗮ → Uᗮ` blocks, and its *off-diagonal part*
`U.offDiagBlock A = P_U A P_{Uᗮ} + P_{Uᗮ} A P_U` keeps the `Uᗮ → U` and `U → Uᗮ` blocks.

Both parts are expressed through the reflection `R_U = 2 P_U - 1` across `U`: conjugating by
`R_U` fixes the diagonal blocks and negates the off-diagonal ones, so the two parts are the
average and the half-difference of `A` and `R_U A R_U`. Since `R_U` is an isometry, these
formulas turn operator-norm estimates for `A` into estimates for its blocks.

## Main definitions

* `Submodule.diagBlock U A`: the block-diagonal part of `A` relative to `U ⊕ Uᗮ`.
* `Submodule.offDiagBlock U A`: the off-diagonal part of `A` relative to `U ⊕ Uᗮ`.

## Main results

* `Submodule.diagBlock_add_offDiagBlock`: the two parts sum to `A`.
* `Submodule.diagBlock_diagBlock`, `Submodule.offDiagBlock_offDiagBlock`,
  `Submodule.diagBlock_offDiagBlock`, `Submodule.offDiagBlock_diagBlock`: taking either part is
  idempotent, and each part annihilates the other.
* `Submodule.two_smul_diagBlock`: `2 • U.diagBlock A = A + R_U A R_U`.
* `Submodule.two_smul_offDiagBlock`: `2 • U.offDiagBlock A = A - R_U A R_U`.
* `Submodule.commute_reflection_iff`: `R_U` commutes with `A` exactly when `P_U` does.
* `Submodule.offDiagBlock_eq_zero_iff`, `Submodule.diagBlock_eq_self_iff`: `A` is block
  diagonal exactly when `P_U` commutes with `A`.

## References

* C. Davis, W. M. Kahan, *The rotation of eigenvectors by a perturbation. III*,
  SIAM J. Numer. Anal. **7** (1970).
-/

public section

noncomputable section

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]

/-- The block-diagonal part `P_U A P_U + P_{Uᗮ} A P_{Uᗮ}` of an operator `A` relative to the
orthogonal decomposition `E = U ⊕ Uᗮ`. -/
def diagBlock (A : E →L[𝕜] E) : E →L[𝕜] E :=
  U.starProjection ∘L A ∘L U.starProjection + Uᗮ.starProjection ∘L A ∘L Uᗮ.starProjection

/-- The off-diagonal part `P_U A P_{Uᗮ} + P_{Uᗮ} A P_U` of an operator `A` relative to the
orthogonal decomposition `E = U ⊕ Uᗮ`. -/
def offDiagBlock (A : E →L[𝕜] E) : E →L[𝕜] E :=
  U.starProjection ∘L A ∘L Uᗮ.starProjection + Uᗮ.starProjection ∘L A ∘L U.starProjection

theorem diagBlock_def (A : E →L[𝕜] E) :
    U.diagBlock A =
      U.starProjection ∘L A ∘L U.starProjection + Uᗮ.starProjection ∘L A ∘L Uᗮ.starProjection :=
  (rfl)

theorem offDiagBlock_def (A : E →L[𝕜] E) :
    U.offDiagBlock A =
      U.starProjection ∘L A ∘L Uᗮ.starProjection + Uᗮ.starProjection ∘L A ∘L U.starProjection :=
  (rfl)

/-- Taking the diagonal part is additive. -/
@[simp]
theorem diagBlock_add (A B : E →L[𝕜] E) :
    U.diagBlock (A + B) = U.diagBlock A + U.diagBlock B := by
  simp only [diagBlock, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
  abel

/-- Taking the diagonal part commutes with scalar multiplication. -/
@[simp]
theorem diagBlock_smul (c : 𝕜) (A : E →L[𝕜] E) : U.diagBlock (c • A) = c • U.diagBlock A := by
  simp only [diagBlock, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_add]

/-- Taking the off-diagonal part is additive. -/
@[simp]
theorem offDiagBlock_add (A B : E →L[𝕜] E) :
    U.offDiagBlock (A + B) = U.offDiagBlock A + U.offDiagBlock B := by
  simp only [offDiagBlock, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
  abel

/-- Taking the off-diagonal part commutes with scalar multiplication. -/
@[simp]
theorem offDiagBlock_smul (c : 𝕜) (A : E →L[𝕜] E) :
    U.offDiagBlock (c • A) = c • U.offDiagBlock A := by
  simp only [offDiagBlock, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_add]

@[simp]
theorem diagBlock_zero : U.diagBlock 0 = 0 := by
  simp [diagBlock]

@[simp]
theorem offDiagBlock_zero : U.offDiagBlock 0 = 0 := by
  simp [offDiagBlock]

/-- Taking the diagonal part commutes with negation. -/
@[simp]
theorem diagBlock_neg (A : E →L[𝕜] E) : U.diagBlock (-A) = -U.diagBlock A := by
  simpa using U.diagBlock_smul (-1) A

/-- Taking the off-diagonal part commutes with negation. -/
@[simp]
theorem offDiagBlock_neg (A : E →L[𝕜] E) : U.offDiagBlock (-A) = -U.offDiagBlock A := by
  simpa using U.offDiagBlock_smul (-1) A

/-- Taking the diagonal part commutes with subtraction. -/
@[simp]
theorem diagBlock_sub (A B : E →L[𝕜] E) :
    U.diagBlock (A - B) = U.diagBlock A - U.diagBlock B := by
  rw [sub_eq_add_neg, diagBlock_add, diagBlock_neg, sub_eq_add_neg]

/-- Taking the off-diagonal part commutes with subtraction. -/
@[simp]
theorem offDiagBlock_sub (A B : E →L[𝕜] E) :
    U.offDiagBlock (A - B) = U.offDiagBlock A - U.offDiagBlock B := by
  rw [sub_eq_add_neg, offDiagBlock_add, offDiagBlock_neg, sub_eq_add_neg]

/-- Every operator is the sum of its diagonal and off-diagonal parts. -/
@[simp]
theorem diagBlock_add_offDiagBlock (A : E →L[𝕜] E) :
    U.diagBlock A + U.offDiagBlock A = A := by
  simp only [diagBlock, offDiagBlock, starProjection_orthogonal', ← ContinuousLinearMap.mul_def]
  noncomm_ring

/-- The diagonal part of `A` is the average of `A` and its conjugate `R_U A R_U` by the
reflection across `U`. -/
theorem two_smul_diagBlock (A : E →L[𝕜] E) :
    2 • U.diagBlock A = A + (U.reflection : E →L[𝕜] E) ∘L A ∘L (U.reflection : E →L[𝕜] E) := by
  simp only [diagBlock, coe_reflection, starProjection_orthogonal',
    ← ContinuousLinearMap.mul_def]
  noncomm_ring

/-- The off-diagonal part of `A` is half the difference of `A` and its conjugate `R_U A R_U` by
the reflection across `U`. -/
theorem two_smul_offDiagBlock (A : E →L[𝕜] E) :
    2 • U.offDiagBlock A = A - (U.reflection : E →L[𝕜] E) ∘L A ∘L (U.reflection : E →L[𝕜] E) := by
  simp only [offDiagBlock, coe_reflection, starProjection_orthogonal',
    ← ContinuousLinearMap.mul_def]
  noncomm_ring

/-- The reflection across `U` commutes with an operator exactly when the orthogonal projection
onto `U` does, that is, exactly when `U` reduces the operator. -/
theorem commute_reflection_iff {A : E →L[𝕜] E} :
    Commute (U.reflection : E →L[𝕜] E) A ↔ Commute U.starProjection A := by
  rw [coe_reflection]
  refine ⟨fun h => ?_, fun h => (h.smul_left 2).sub_left (Commute.one_left A)⟩
  have h2 : Commute ((2 : 𝕜)⁻¹ • (2 • U.starProjection - 1 + 1)) A :=
    (h.add_left (Commute.one_left A)).smul_left _
  rwa [sub_add_cancel, ← ofNat_smul_eq_nsmul 𝕜, inv_smul_smul₀ two_ne_zero] at h2

/-- The off-diagonal part of `A` vanishes exactly when `A` commutes with the orthogonal
projection onto `U`, that is, when `A` is block diagonal relative to `U ⊕ Uᗮ`. -/
@[simp]
theorem offDiagBlock_eq_zero_iff {A : E →L[𝕜] E} :
    U.offDiagBlock A = 0 ↔ Commute U.starProjection A := by
  simp only [offDiagBlock, starProjection_orthogonal', ← ContinuousLinearMap.mul_def]
  have hP := U.isIdempotentElem_starProjection
  have h0 := hP.mul_one_sub_self
  have h1 := hP.one_sub_mul_self
  set P := U.starProjection
  constructor
  · intro h
    -- Compressing the off-diagonal part by `P` on the left isolates the block `P A (1 - P)`, and
    -- on the right isolates the block `(1 - P) A P`.
    have hl : P * (A * (1 - P)) = 0 := by
      simpa only [mul_add, ← mul_assoc, hP.eq, h0, zero_mul, add_zero, mul_zero]
        using congrArg (P * ·) h
    have hr : (1 - P) * (A * P) = 0 := by
      simpa only [add_mul, mul_assoc, hP.eq, h1, mul_zero, zero_add, zero_mul]
        using congrArg (· * P) h
    rw [mul_sub, mul_one, mul_sub, sub_eq_zero] at hl
    rw [sub_mul, one_mul, sub_eq_zero] at hr
    exact hl.trans hr.symm
  · intro h
    have h' : Commute A (1 - P) := (Commute.one_right A).sub_right h.symm
    rw [h'.eq, ← h.eq, ← mul_assoc, ← mul_assoc, h0, h1, zero_mul, add_zero]

/-- An operator equals its diagonal part exactly when it commutes with the orthogonal projection
onto `U`. -/
@[simp]
theorem diagBlock_eq_self_iff {A : E →L[𝕜] E} :
    U.diagBlock A = A ↔ Commute U.starProjection A := by
  rw [← offDiagBlock_eq_zero_iff, ← add_eq_left (a := U.diagBlock A),
    diagBlock_add_offDiagBlock, eq_comm]

/-- The diagonal part of any operator commutes with the orthogonal projection onto `U`. -/
theorem commute_starProjection_diagBlock (A : E →L[𝕜] E) :
    Commute U.starProjection (U.diagBlock A) := by
  simp only [diagBlock, starProjection_orthogonal', ← ContinuousLinearMap.mul_def]
  have hP := U.isIdempotentElem_starProjection
  have h0 := hP.mul_one_sub_self
  have h1 := hP.one_sub_mul_self
  set P := U.starProjection
  -- Both products reduce to `P A P`, since `P (1 - P) = (1 - P) P = 0`.
  have hPP (B : E →L[𝕜] E) : P * (P * B) = P * B := by rw [← mul_assoc, hP.eq]
  have h0' (B : E →L[𝕜] E) : P * ((1 - P) * B) = 0 := by rw [← mul_assoc, h0, zero_mul]
  change P * _ = _ * P
  simp only [mul_add, add_mul, mul_assoc, hP.eq, h1, hPP, h0', mul_zero, add_zero]

/-- The diagonal part of the diagonal part of `A` is the diagonal part of `A`. -/
@[simp]
theorem diagBlock_diagBlock (A : E →L[𝕜] E) : U.diagBlock (U.diagBlock A) = U.diagBlock A :=
  (U.diagBlock_eq_self_iff).2 (U.commute_starProjection_diagBlock A)

/-- The off-diagonal part of the diagonal part of `A` vanishes. -/
@[simp]
theorem offDiagBlock_diagBlock (A : E →L[𝕜] E) : U.offDiagBlock (U.diagBlock A) = 0 :=
  (U.offDiagBlock_eq_zero_iff).2 (U.commute_starProjection_diagBlock A)

/-- The diagonal part of the off-diagonal part of `A` vanishes. -/
@[simp]
theorem diagBlock_offDiagBlock (A : E →L[𝕜] E) : U.diagBlock (U.offDiagBlock A) = 0 := by
  have h := congrArg U.diagBlock (U.diagBlock_add_offDiagBlock A)
  rwa [diagBlock_add, diagBlock_diagBlock, add_eq_left] at h

/-- The off-diagonal part of the off-diagonal part of `A` is the off-diagonal part of `A`. -/
@[simp]
theorem offDiagBlock_offDiagBlock (A : E →L[𝕜] E) :
    U.offDiagBlock (U.offDiagBlock A) = U.offDiagBlock A := by
  have h := congrArg U.offDiagBlock (U.diagBlock_add_offDiagBlock A)
  rwa [offDiagBlock_add, offDiagBlock_diagBlock, zero_add] at h

/-- The diagonal part of `A` relative to `Uᗮ ⊕ Uᗮᗮ` is its diagonal part relative to `U ⊕ Uᗮ`. -/
@[simp]
theorem diagBlock_orthogonal (A : E →L[𝕜] E) : Uᗮ.diagBlock A = U.diagBlock A := by
  simp only [diagBlock, starProjection_orthogonal', ← ContinuousLinearMap.mul_def]
  noncomm_ring

/-- The off-diagonal part of `A` relative to `Uᗮ ⊕ Uᗮᗮ` is its off-diagonal part relative to
`U ⊕ Uᗮ`. -/
@[simp]
theorem offDiagBlock_orthogonal (A : E →L[𝕜] E) : Uᗮ.offDiagBlock A = U.offDiagBlock A := by
  simp only [offDiagBlock, starProjection_orthogonal', ← ContinuousLinearMap.mul_def]
  noncomm_ring

end Submodule
