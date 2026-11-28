/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.IndefiniteUnitaryGroup
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import TauCeti.Algebra.Star.Projection.Conjugate
import TauCeti.Analysis.CStarAlgebra.Projection.Orthogonal
import TauCeti.Analysis.Matrix.EuclideanLin.Projection
import TauCeti.LinearAlgebra.Matrix.DotProduct

/-!
# Dilations of an isotropic subspace close to the identity in `U(J)`

Let `J` be a hermitian involution over `ℝ` or `ℂ` (any `RCLike` field) and `A` a matrix whose
columns span a totally isotropic subspace for the form `⟨u, v⟩ = star u ⬝ᵥ J *ᵥ v`, that is
`Aᴴ * J * A = 0`. For every `c ≥ 0` and every `x` in the unitary group
`U(J) = Matrix.unitaryGroupOf J` (an orthogonal group `O(p, q)` over `ℝ`), this file constructs
`y ∈ U(J)` with `‖y - 1‖ ≤ c` in the operator norm such that the conjugate `g = x * y * x⁻¹` is a
dilation along the columns of `A`:

* `g * A = (1 + c) • A`;
* `g` preserves the form on the `J`-orthogonal of the columns: `⟨w, g v⟩ = ⟨w, v⟩` whenever
  `Aᴴ * J *ᵥ v = 0` and `Aᴴ * J *ᵥ w = 0`.

So, for every `c ≥ 0` and every `x`, the elements of `U(J)` that dilate the columns of `A` by
`1 + c` and preserve the form on their `J`-orthogonal include a conjugate `x * y * x⁻¹` with
`‖y - 1‖ ≤ c`; the factor `1 + c` does not depend on `x`. This is the hypothesis on dilations
under which idempotent kernels kill the functions invariant under the unipotent radical
(`TauCeti.rightRegularIntegral_apply_eq_zero`).

The element `y` is written down from the orthogonal projector `P` onto the column space of
`B = x⁻¹ * A` (`Matrix.exists_isStarProjection_mul_eq_self_and_eq_mul`) and from
`Q = J * P * J`, the orthogonal projector onto the image of that space under `J`:

```text
y = 1 + c • P - (c / (1 + c)) • Q.
```

As the column space of `B` is totally isotropic, `P * J * P = 0`, so `P` and `Q` are orthogonal
projectors with `P * Q = Q * P = 0` (`IsStarProjection.conjugate`,
`IsSelfAdjoint.isStarOrtho_conjugate`). Then `J * y = y' * J` with
`y' = 1 - (c / (1 + c)) • P + c • Q` and `y * y' = 1`, so that `star y * J * y = J`. For the norm,
`y - 1 = (c / (1 + c)) • (P - Q) + (c - c / (1 + c)) • P`, where `(P - Q)² = P + Q` is a projector,
so `‖P - Q‖ ≤ 1` by the C⋆-identity (`IsStarProjection.norm_sub_le_one`).

## Main results

* `Matrix.unitaryGroupOf.exists_norm_sub_one_le_and_conj_dilates`: the construction above.

## Provenance

The construction of `y` from the orthogonal projector onto the column space of `x⁻¹ * A` and from
its image under conjugation by `J` is that of `New.DiscreteSeries.exists_conj_mem_dilationGroup`
(file `src/Lib/DiscreteSeries/CuspKernel.lean`) in grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

open WithLp
open scoped Matrix.Norms.L2Operator

namespace Matrix

variable {𝕜 n m : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

variable {J : Matrix n n 𝕜}

/-- The dilation `1 + c • P - (c / (1 + c)) • (J * P * J)` along the range of `P`. -/
private noncomputable def dilation (J P : Matrix n n 𝕜) (c : ℝ) : Matrix n n 𝕜 :=
  1 + (c : 𝕜) • P - ((c / (1 + c) : ℝ) : 𝕜) • (J * P * J)

/-- The projector `Q = J * P * J` is a star projection orthogonal to `P`, when the range of the
star projection `P` is totally isotropic for the hermitian involution `J`. -/
private theorem isStarProjection_mul_mul (hJ : J.IsHermitian) (hJJ : J * J = 1) {P : Matrix n n 𝕜}
    (hP : IsStarProjection P) (hPJP : P * J * P = 0) :
    IsStarProjection (J * P * J) ∧ P * (J * P * J) = 0 ∧ J * P * J * P = 0 := by
  have hJs : star J = J := hJ
  have hQ := hP.conjugate (u := J) (by rw [hJs, hJJ])
  have hPQ := hP.isSelfAdjoint.isStarOrtho_conjugate (u := J) hPJP
  rw [hJs] at hQ hPQ
  exact ⟨hQ, hPQ.mul_eq_zero' hQ.isSelfAdjoint, hPQ.mul_eq_zero hQ.isSelfAdjoint⟩

/-- The dilation preserves the form of `J`: `star y * J * y = J`. -/
private theorem star_dilation_mul_mul (hJ : J.IsHermitian) (hJJ : J * J = 1) {P : Matrix n n 𝕜}
    (hP : IsStarProjection P) (hPJP : P * J * P = 0) {c : ℝ} (hc : 0 ≤ c) :
    star (dilation J P c) * J * dilation J P c = J := by
  obtain ⟨hQ, hPQ, hQP⟩ := isStarProjection_mul_mul hJ hJJ hP hPJP
  have hc' : ((c / (1 + c) : ℝ) : 𝕜) * (1 + c) = c := by
    have h1 : (1 + (c : 𝕜)) ≠ 0 := by exact_mod_cast (by linarith : (1 + c) ≠ 0)
    push_cast
    exact div_mul_cancel₀ _ h1
  -- `J` exchanges `P` and `Q = J * P * J`: `J * Q = P * J` and `J * P = Q * J`.
  have hJQ : J * (J * P * J) = P * J := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hJJ,
    Matrix.one_mul]
  have hJP : J * P = J * P * J * J := by rw [Matrix.mul_assoc _ J J, hJJ, Matrix.mul_one]
  unfold dilation
  set Q := J * P * J
  -- `y` is self-adjoint, `J * y = y' * J`, and `y * y' = 1`.
  have hstar : star (1 + (c : 𝕜) • P - ((c / (1 + c) : ℝ) : 𝕜) • Q) =
      1 + (c : 𝕜) • P - ((c / (1 + c) : ℝ) : 𝕜) • Q := by
    simp [star_sub, star_add, star_smul, hP.isSelfAdjoint.star_eq, hQ.isSelfAdjoint.star_eq]
  have hJy : J * (1 + (c : 𝕜) • P - ((c / (1 + c) : ℝ) : 𝕜) • Q) =
      (1 - ((c / (1 + c) : ℝ) : 𝕜) • P + (c : 𝕜) • Q) * J := by
    simp only [mul_add, mul_sub, add_mul, sub_mul, mul_one, one_mul, mul_smul_comm,
      smul_mul_assoc, hJQ, ← hJP]
    abel
  have hyy : (1 + (c : 𝕜) • P - ((c / (1 + c) : ℝ) : 𝕜) • Q) *
      (1 - ((c / (1 + c) : ℝ) : 𝕜) • P + (c : 𝕜) • Q) = 1 := by
    simp only [mul_add, mul_sub, add_mul, sub_mul, mul_one, one_mul, mul_smul_comm,
      smul_mul_assoc, hP.isIdempotentElem.eq, hQ.isIdempotentElem.eq, hPQ, hQP, smul_zero]
    linear_combination (norm := module) (-1 : 𝕜) • (hc' • (P + Q))
  rw [hstar, Matrix.mul_assoc, hJy, ← Matrix.mul_assoc, hyy, Matrix.one_mul]

/-- The dilation is within `c` of `1` in the operator norm. -/
private theorem norm_dilation_sub_one_le (hJ : J.IsHermitian) (hJJ : J * J = 1)
    {P : Matrix n n 𝕜} (hP : IsStarProjection P) (hPJP : P * J * P = 0) {c : ℝ} (hc : 0 ≤ c) :
    ‖dilation J P c - 1‖ ≤ c := by
  obtain ⟨hQ, hPQ, -⟩ := isStarProjection_mul_mul hJ hJJ hP hPJP
  set Q := J * P * J
  set c' := c / (1 + c)
  have hc'0 : 0 ≤ c' := by positivity
  have hc'c : c' ≤ c := div_le_self hc (by linarith)
  have hPQ1 : ‖P - Q‖ ≤ 1 := hP.norm_sub_le_one hQ
    ((hP.isSelfAdjoint.isStarOrtho_iff_mul_eq_zero hQ.isSelfAdjoint).2 hPQ)
  have h : dilation J P c - 1 = (c' : 𝕜) • (P - Q) + ((c - c' : ℝ) : 𝕜) • P := by
    simp only [dilation, c', RCLike.ofReal_sub]
    module
  rw [h]
  calc _ ≤ ‖(c' : 𝕜) • (P - Q)‖ + ‖((c - c' : ℝ) : 𝕜) • P‖ := norm_add_le _ _
    _ ≤ c' * 1 + (c - c') * 1 := by
        rw [norm_smul, norm_smul, RCLike.norm_ofReal, RCLike.norm_ofReal, abs_of_nonneg hc'0,
          abs_of_nonneg (by linarith)]
        exact add_le_add (mul_le_mul_of_nonneg_left hPQ1 hc'0)
          (mul_le_mul_of_nonneg_left hP.norm_le (by linarith))
    _ = c := by ring

/-- The case `x = 1` of `Matrix.unitaryGroupOf.exists_norm_sub_one_le_and_conj_dilates`. -/
private theorem exists_star_mul_mul_eq_and_norm_sub_one_le [Finite m] (hJ : J.IsHermitian)
    (hJJ : J * J = 1) {B : Matrix n m 𝕜} (hB : Bᴴ * J * B = 0) {c : ℝ} (hc : 0 ≤ c) :
    ∃ Y : Matrix n n 𝕜, star Y * J * Y = J ∧ ‖Y - 1‖ ≤ c ∧ Y * B = (1 + (c : 𝕜)) • B ∧
      ∀ v w : n → 𝕜, (Bᴴ * J) *ᵥ v = 0 → (Bᴴ * J) *ᵥ w = 0 →
        star w ⬝ᵥ J *ᵥ (Y *ᵥ v) = star w ⬝ᵥ J *ᵥ v := by
  have := Fintype.ofFinite m
  obtain ⟨P, M, hP, hPB, hPM⟩ := exists_isStarProjection_mul_eq_self_and_eq_mul B
  have hPM' : P = Mᴴ * Bᴴ := by
    rw [← hP.isSelfAdjoint.star_eq, star_eq_conjTranspose, hPM, conjTranspose_mul]
  have hPJP : P * J * P = 0 :=
    calc P * J * P = Mᴴ * Bᴴ * J * (B * M) := by rw [← hPM', ← hPM]
      _ = Mᴴ * (Bᴴ * J * B) * M := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hB, Matrix.mul_zero, Matrix.zero_mul]
  -- `P * J` kills the `J`-orthogonal of the columns of `B`.
  have hPJ : ∀ v : n → 𝕜, (Bᴴ * J) *ᵥ v = 0 → (P * J) *ᵥ v = 0 := fun v hv => by
    rw [hPM', Matrix.mul_assoc, ← mulVec_mulVec, hv, mulVec_zero]
  refine ⟨dilation J P c, star_dilation_mul_mul hJ hJJ hP hPJP hc,
    norm_dilation_sub_one_le hJ hJJ hP hPJP hc, ?_, fun v w hv hw => ?_⟩
  · have hQB : J * P * J * B = 0 := by
      rw [← hPB, ← Matrix.mul_assoc, (isStarProjection_mul_mul hJ hJJ hP hPJP).2.2,
        Matrix.zero_mul]
    simp only [dilation, Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, hPB,
      hQB, smul_zero, sub_zero, add_smul, one_smul]
  · -- `y v = v + c • P v`, since `Q v = J * (P * J) v = 0`, and `⟨w, J P v⟩ = ⟨P J w, v⟩ = 0`.
    have hQv : (J * P * J) *ᵥ v = 0 := by
      rw [mul_assoc, ← mulVec_mulVec, hPJ v hv, mulVec_zero]
    have hJP : star w ⬝ᵥ J *ᵥ (P *ᵥ v) = 0 := by
      have h : (P * J)ᴴ = J * P := by
        rw [conjTranspose_mul, hJ.eq, ← star_eq_conjTranspose, hP.isSelfAdjoint.star_eq]
      rw [dotProduct_mulVec, dotProduct_mulVec, vecMul_vecMul, ← h, ← star_mulVec, hPJ w hw,
        star_zero, zero_dotProduct]
    simp only [dilation, add_mulVec, sub_mulVec, one_mulVec, smul_mulVec, hQv, smul_zero,
      sub_zero, mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, hJP, smul_zero,
      add_zero]

namespace unitaryGroupOf

/-- **Dilations of an isotropic subspace, conjugated close to `1`.** Let `J` be a hermitian
involution and `A` a matrix whose columns span a totally isotropic subspace for the form
`⟨u, v⟩ = star u ⬝ᵥ J *ᵥ v`, that is `Aᴴ * J * A = 0`. For `c ≥ 0` and `x ∈ U(J)` there is
`y ∈ U(J)` with `‖y - 1‖ ≤ c` in the operator norm such that `g = x * y * x⁻¹` dilates the columns
of `A` by `1 + c`, `g * A = (1 + c) • A`, and preserves the form on their `J`-orthogonal:
`⟨w, g v⟩ = ⟨w, v⟩` whenever `Aᴴ * J *ᵥ v = 0` and `Aᴴ * J *ᵥ w = 0`. -/
theorem exists_norm_sub_one_le_and_conj_dilates [Finite m] (hJ : J.IsHermitian) (hJJ : J * J = 1)
    {A : Matrix n m 𝕜} (hA : Aᴴ * J * A = 0) {c : ℝ} (hc : 0 ≤ c) (x : unitaryGroupOf J) :
    ∃ y : unitaryGroupOf J, ‖((y : GL n 𝕜) : Matrix n n 𝕜) - 1‖ ≤ c ∧
      (((x * y * x⁻¹ : unitaryGroupOf J) : GL n 𝕜) : Matrix n n 𝕜) * A = (1 + (c : 𝕜)) • A ∧
      ∀ v w : n → 𝕜, (Aᴴ * J) *ᵥ v = 0 → (Aᴴ * J) *ᵥ w = 0 →
        star w ⬝ᵥ J *ᵥ ((((x * y * x⁻¹ : unitaryGroupOf J) : GL n 𝕜) : Matrix n n 𝕜) *ᵥ v) =
          star w ⬝ᵥ J *ᵥ v := by
  set X : Matrix n n 𝕜 := ((x : GL n 𝕜) : Matrix n n 𝕜)
  set X' : Matrix n n 𝕜 := (((x⁻¹ : unitaryGroupOf J) : GL n 𝕜) : Matrix n n 𝕜)
  have hXX' : X * X' = 1 := by simp [X, X']
  have hX' : star X' * J * X' = J := mem_unitaryGroupOf_iff.mp (x⁻¹).property
  -- Apply the case `x = 1` to `B = x⁻¹ * A`, whose columns are again totally isotropic.
  have hB : (X' * A)ᴴ * J * (X' * A) = 0 := by
    rw [conjTranspose_mul_mul_mul_of_star_mul_mul_eq hX' A, hA]
  have hX'' : X'ᴴ * (J * X') = J := by
    rw [← Matrix.mul_assoc, ← star_eq_conjTranspose, hX']
  have hBv : ∀ v : n → 𝕜, ((X' * A)ᴴ * J) *ᵥ (X' *ᵥ v) = (Aᴴ * J) *ᵥ v := fun v => by
    rw [mulVec_mulVec]
    simp only [conjTranspose_mul, Matrix.mul_assoc, hX'']
  obtain ⟨Y, hY, hYn, hYB, hYf⟩ :=
    exists_star_mul_mul_eq_and_norm_sub_one_le hJ hJJ hB hc
  have hg : (((x * ofMatrix (isUnit_iff_exists_inv.2 ⟨J, hJJ⟩) Y hY * x⁻¹ :
      unitaryGroupOf J) : GL n 𝕜) : Matrix n n 𝕜) = X * Y * X' := by
    simp [X, X']
  -- `⟨w, x u⟩ = ⟨x⁻¹ w, u⟩`, as `x` preserves the form.
  have key : ∀ w u : n → 𝕜, star w ⬝ᵥ J *ᵥ (X *ᵥ u) = star (X' *ᵥ w) ⬝ᵥ J *ᵥ u :=
    fun w u => by
      have h : star (X *ᵥ (X' *ᵥ w)) ⬝ᵥ J *ᵥ (X *ᵥ u) = star (X' *ᵥ w) ⬝ᵥ J *ᵥ u :=
        mem_unitaryGroupOf_iff_forall_dotProduct.mp x.property (X' *ᵥ w) u
      rwa [mulVec_mulVec, hXX', one_mulVec] at h
  refine ⟨ofMatrix (isUnit_iff_exists_inv.2 ⟨J, hJJ⟩) Y hY, by simpa using hYn, ?_,
    fun v w hv hw => ?_⟩
  · have hXA : X * (X' * A) = A := by rw [← Matrix.mul_assoc, hXX', Matrix.one_mul]
    simp only [hg, Matrix.mul_assoc, hYB, Matrix.mul_smul, hXA]
  · have h₁ : (X * Y * X') *ᵥ v = X *ᵥ (Y *ᵥ (X' *ᵥ v)) := by
      simp only [mulVec_mulVec, Matrix.mul_assoc]
    have h₂ : X *ᵥ (X' *ᵥ v) = v := by rw [mulVec_mulVec, hXX', one_mulVec]
    rw [hg, h₁, key, hYf _ _ ((hBv v).trans hv) ((hBv w).trans hw), ← key, h₂]

end unitaryGroupOf

end Matrix
