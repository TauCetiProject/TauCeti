/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The Hermitian part of a two-form in a unitary frame of `ℝ⁴`

Let `X` be an almost Kähler four-manifold with symplectic form `ω`, compatible almost complex
structure `J` and metric `g(v, w) = ω(v, J w)`. At a point, choose a unitary oriented frame
`e₁, e₂, e₃, e₄`, so that `J e₁ = e₂`, `J e₃ = e₄` and `ω = e¹² + e³⁴`. A real two-form `F` is
then a skew-symmetric `4 × 4` matrix, `F(v, w) = v ⬝ F w`, and its *Hermitian part* is the
symmetric bilinear form
```
B(v, w) = (F(v, J w) + F(w, J v)) / 2.
```
In the large-parameter analysis of the Seiberg–Witten equations on a symplectic four-manifold,
a uniform lower bound `B ≥ -C g` for the curvature `F = i F_a` is what controls the
anti-self-dual part `F_a⁻`. This file proves the pointwise linear algebra that turns such a lower
bound into a bound on the anti-self-dual part `F⁻` of `F`.

Decompose `Λ² = ℝ ω ⊕ Λ⁻ ⊕ Λ_J⁻`, where `Λ⁻` is the anti-self-dual part and `Λ_J⁻` the
anti-`J`-invariant forms, which are self-dual and orthogonal to `ω`. With
`c = ⟨F, ω⟩ / 2`, we show

* `B = c g + F⁻ J`: the `ω`-component contributes `c g`, the anti-self-dual part contributes the
  symmetric matrix `F⁻ J`, and the anti-`J`-invariant forms contribute nothing;
* `(F⁻ J)² = (|F⁻|² / 2) Id`, so `F⁻ J` has eigenvalues `± |F⁻| / √2`;
* hence the smallest eigenvalue of `B` is `c - |F⁻| / √2`, and `B ≥ -C g` gives
  `|F⁻| ≤ √2 (c + C)`.

The two-form norm is the one for which `e^{ij}`, `i < j`, are orthonormal, so `|ω|² = 2`, and the
orientation is `e¹²³⁴`, the one for which `ω ∧ ω > 0`. Frames are indexed by `Fin 4` in the order
`e₁, e₂, e₃, e₄`, rather than by the `Fin 2 ⊕ Fin 2` of Mathlib's symplectic `Matrix.J`, so that
this orientation is the standard order of the indices.

## Main declarations

* `TauCeti.SeibergWitten.frameComplexStructure`, `TauCeti.SeibergWitten.frameKahlerForm`: the
  matrices of `J` and `ω` in a unitary frame.
* `Matrix.frameHodgeStar`, `Matrix.frameAntiSelfDualPart`, `Matrix.frameInner`: the Hodge star,
  the anti-self-dual part `F⁻ = (F - ⋆F) / 2` and the inner product of two-forms.
* `Matrix.frameHermitianForm`: the Hermitian part `B` of a two-form.
* `Matrix.frameHodgeStar_frameAntiSelfDualPart`,
  `Matrix.frameHodgeStar_sub_frameAntiSelfDualPart`: `F⁻` is anti-self-dual and `F - F⁻` is
  self-dual.
* `Matrix.frameHermitianForm_eq`: `B = c Id + F⁻ J`.
* `Matrix.frameHermitianForm_eq_zero`: anti-`J`-invariant forms have zero Hermitian part.
* `Matrix.frameAntiSelfDualPart_mul_frameComplexStructure_mul_self`: `(F⁻ J)² = (|F⁻|² / 2) Id`.
* `Matrix.posSemidef_frameHermitianForm_sub_smul_one_iff`: `B - μ Id` is positive semidefinite
  exactly when `μ ≤ c - |F⁻| / √2`.
* `Matrix.isLeast_frameHermitianForm_eigenvalues`: the smallest eigenvalue of `B` is
  `c - |F⁻| / √2`.
* `Matrix.sqrt_frameInner_frameAntiSelfDualPart_le`: `B + C Id ≥ 0` implies
  `|F⁻| ≤ √2 (c + C)`.

## References

* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996.
* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845--918.
* C. H. Taubes, *Seiberg–Witten and Gromov invariants for symplectic 4-manifolds*,
  First International Press Lecture Series 2 (2000).
-/

public section

noncomputable section

namespace TauCeti.SeibergWitten

open Matrix

/-- The almost complex structure in a unitary frame of `ℝ⁴`: `J e₁ = e₂` and `J e₃ = e₄`. -/
def frameComplexStructure : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, -1, 0, 0; 1, 0, 0, 0; 0, 0, 0, -1; 0, 0, 1, 0]

/-- The symplectic form `ω = e¹² + e³⁴` in a unitary frame of `ℝ⁴`, as a skew-symmetric matrix
`ω(v, w) = v ⬝ ω w`. -/
def frameKahlerForm : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0]

/-- Unfolding lemma for `frameComplexStructure`. -/
theorem frameComplexStructure_def :
    frameComplexStructure = !![0, -1, 0, 0; 1, 0, 0, 0; 0, 0, 0, -1; 0, 0, 1, 0] :=
  (rfl)

/-- Unfolding lemma for `frameKahlerForm`. -/
theorem frameKahlerForm_def :
    frameKahlerForm = !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0] :=
  (rfl)

/-- `J² = -1`. -/
@[simp]
theorem frameComplexStructure_mul_self : frameComplexStructure * frameComplexStructure = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [frameComplexStructure, Matrix.mul_apply, Fin.sum_univ_four]

/-- `J` is orthogonal and skew: `Jᵀ = -J`. -/
@[simp]
theorem transpose_frameComplexStructure : frameComplexStructureᵀ = -frameComplexStructure := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [frameComplexStructure]

/-- The frame is unitary: the metric `g(v, w) = ω(v, J w)` is the standard inner product. -/
theorem frameKahlerForm_mul_frameComplexStructure :
    frameKahlerForm * frameComplexStructure = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [frameKahlerForm, frameComplexStructure, Matrix.mul_apply, Fin.sum_univ_four]

end TauCeti.SeibergWitten

namespace Matrix

open TauCeti.SeibergWitten

variable (F G : Matrix (Fin 4) (Fin 4) ℝ)

/-- The Hodge star on two-forms on `ℝ⁴` with the orientation `e¹²³⁴`, in a unitary frame:
`⋆e¹² = e³⁴`, `⋆e¹³ = -e²⁴` and `⋆e¹⁴ = e²³`. It reads only the entries above the diagonal, so
it is meant for skew-symmetric `F`. -/
def frameHodgeStar : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, F 2 3, -F 1 3, F 1 2;
    -F 2 3, 0, F 0 3, -F 0 2;
    F 1 3, -F 0 3, 0, F 0 1;
    -F 1 2, F 0 2, -F 0 1, 0]

/-- The anti-self-dual part `F⁻ = (F - ⋆F) / 2` of a two-form. -/
def frameAntiSelfDualPart : Matrix (Fin 4) (Fin 4) ℝ :=
  (1 / 2 : ℝ) • (F - F.frameHodgeStar)

/-- The inner product of two-forms on `ℝ⁴` for which the `e^{ij}`, `i < j`, are orthonormal:
`⟨F, G⟩ = ∑_{i < j} F_ij G_ij` for skew-symmetric `F` and `G`. -/
def frameInner : ℝ :=
  (∑ i, ∑ j, F i j * G i j) / 2

/-- The Hermitian part `B(v, w) = (F(v, J w) + F(w, J v)) / 2` of a two-form `F`, as a symmetric
matrix. -/
def frameHermitianForm : Matrix (Fin 4) (Fin 4) ℝ :=
  (1 / 2 : ℝ) • (F * frameComplexStructure + (F * frameComplexStructure)ᵀ)

variable {F G}

/-- Unfolding lemma for `frameHodgeStar`. -/
theorem frameHodgeStar_def :
    F.frameHodgeStar =
      !![0, F 2 3, -F 1 3, F 1 2;
        -F 2 3, 0, F 0 3, -F 0 2;
        F 1 3, -F 0 3, 0, F 0 1;
        -F 1 2, F 0 2, -F 0 1, 0] :=
  (rfl)

/-- Unfolding lemma for `frameAntiSelfDualPart`. -/
theorem frameAntiSelfDualPart_def :
    F.frameAntiSelfDualPart = (1 / 2 : ℝ) • (F - F.frameHodgeStar) :=
  (rfl)

/-- Unfolding lemma for `frameInner`. -/
theorem frameInner_def : F.frameInner G = (∑ i, ∑ j, F i j * G i j) / 2 :=
  (rfl)

/-- Unfolding lemma for `frameHermitianForm`. -/
theorem frameHermitianForm_def :
    F.frameHermitianForm =
      (1 / 2 : ℝ) • (F * frameComplexStructure + (F * frameComplexStructure)ᵀ) :=
  (rfl)

/-- A skew-symmetric `4 × 4` matrix is determined by its six entries above the diagonal. -/
private theorem eq_of_transpose_eq_neg (hF : Fᵀ = -F) :
    F = !![0, F 0 1, F 0 2, F 0 3;
      -F 0 1, 0, F 1 2, F 1 3;
      -F 0 2, -F 1 2, 0, F 2 3;
      -F 0 3, -F 1 3, -F 2 3, 0] := by
  have h (i j : Fin 4) : F j i = -F i j := by simpa using congrFun (congrFun hF i) j
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;>
    linarith [h 0 0, h 1 1, h 2 2, h 3 3, h 0 1, h 0 2, h 0 3, h 1 2, h 1 3, h 2 3]

/-! ### The Hodge star and the anti-self-dual part -/

/-- The Hodge star of a two-form is a two-form. -/
@[simp]
theorem transpose_frameHodgeStar : F.frameHodgeStarᵀ = -F.frameHodgeStar := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [frameHodgeStar]

/-- The Hodge star on two-forms is an involution. -/
theorem frameHodgeStar_frameHodgeStar (hF : Fᵀ = -F) : F.frameHodgeStar.frameHodgeStar = F := by
  rw [eq_of_transpose_eq_neg hF]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [frameHodgeStar]

/-- The symplectic form `ω = e¹² + e³⁴` is self-dual. -/
@[simp]
theorem frameHodgeStar_frameKahlerForm : frameKahlerForm.frameHodgeStar = frameKahlerForm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [frameHodgeStar, frameKahlerForm]

/-- The anti-self-dual part of a two-form is a two-form. -/
theorem transpose_frameAntiSelfDualPart (hF : Fᵀ = -F) :
    F.frameAntiSelfDualPartᵀ = -F.frameAntiSelfDualPart := by
  simp only [frameAntiSelfDualPart, transpose_smul, transpose_sub, hF, transpose_frameHodgeStar]
  module

/-- The anti-self-dual part `F⁻` is anti-self-dual: `⋆F⁻ = -F⁻`. -/
theorem frameHodgeStar_frameAntiSelfDualPart (hF : Fᵀ = -F) :
    F.frameAntiSelfDualPart.frameHodgeStar = -F.frameAntiSelfDualPart := by
  rw [eq_of_transpose_eq_neg hF]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [frameHodgeStar, frameAntiSelfDualPart] <;> ring

/-- The complement `F - F⁻` of the anti-self-dual part is self-dual. -/
theorem frameHodgeStar_sub_frameAntiSelfDualPart (hF : Fᵀ = -F) :
    (F - F.frameAntiSelfDualPart).frameHodgeStar = F - F.frameAntiSelfDualPart := by
  rw [eq_of_transpose_eq_neg hF]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [frameHodgeStar, frameAntiSelfDualPart] <;> ring

/-! ### The inner product of two-forms -/

/-- On two-forms, `⟨F, ω⟩ = F₁₂ + F₃₄`. -/
theorem frameInner_frameKahlerForm (hF : Fᵀ = -F) :
    F.frameInner frameKahlerForm = F 0 1 + F 2 3 := by
  rw [eq_of_transpose_eq_neg hF]
  simp [frameInner, frameKahlerForm, Fin.sum_univ_four]
  ring

/-- `|F⁻|² = ((F₁₂ - F₃₄)² + (F₁₃ + F₂₄)² + (F₁₄ - F₂₃)²) / 2`. -/
theorem frameInner_frameAntiSelfDualPart_self (hF : Fᵀ = -F) :
    F.frameAntiSelfDualPart.frameInner F.frameAntiSelfDualPart =
      ((F 0 1 - F 2 3) ^ 2 + (F 0 2 + F 1 3) ^ 2 + (F 0 3 - F 1 2) ^ 2) / 2 := by
  rw [eq_of_transpose_eq_neg hF]
  simp [frameInner, frameAntiSelfDualPart, frameHodgeStar, Fin.sum_univ_four]
  ring

/-- The inner product of two-forms is symmetric. -/
theorem frameInner_comm : F.frameInner G = G.frameInner F := by
  simp only [frameInner, mul_comm (F _ _)]

/-- The squared norm `|F|² = ⟨F, F⟩` of a two-form is nonnegative. -/
theorem frameInner_self_nonneg (F : Matrix (Fin 4) (Fin 4) ℝ) : 0 ≤ F.frameInner F := by
  unfold frameInner
  exact div_nonneg (Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ mul_self_nonneg _)
    zero_le_two

/-! ### The Hermitian part -/

/-- `B(v, w) = (F(v, J w) + F(w, J v)) / 2`. -/
theorem dotProduct_frameHermitianForm_mulVec (v w : Fin 4 → ℝ) :
    v ⬝ᵥ (F.frameHermitianForm *ᵥ w) =
      (v ⬝ᵥ (F *ᵥ (frameComplexStructure *ᵥ w)) + w ⬝ᵥ (F *ᵥ (frameComplexStructure *ᵥ v))) /
        2 := by
  have h : v ⬝ᵥ ((F * frameComplexStructure)ᵀ *ᵥ w) =
      w ⬝ᵥ (F *ᵥ (frameComplexStructure *ᵥ v)) := by
    rw [mulVec_transpose, dotProduct_comm, ← dotProduct_mulVec, mulVec_mulVec]
  rw [frameHermitianForm, smul_mulVec, add_mulVec, dotProduct_smul, dotProduct_add, h,
    ← mulVec_mulVec, smul_eq_mul]
  ring

/-- The Hermitian part of a two-form is symmetric. -/
@[simp]
theorem transpose_frameHermitianForm : F.frameHermitianFormᵀ = F.frameHermitianForm := by
  simp [frameHermitianForm, add_comm]

/-- The Hermitian part of a two-form is `B = c Id + F⁻ J` with `c = ⟨F, ω⟩ / 2`. -/
theorem frameHermitianForm_eq (hF : Fᵀ = -F) :
    F.frameHermitianForm = (F.frameInner frameKahlerForm / 2) • 1 +
      F.frameAntiSelfDualPart * frameComplexStructure := by
  rw [eq_of_transpose_eq_neg hF]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [frameHermitianForm, frameAntiSelfDualPart, frameHodgeStar, frameInner, frameKahlerForm,
      frameComplexStructure, Fin.sum_univ_four] <;> ring

/-- Anti-`J`-invariant two-forms, `F(J v, J w) = -F(v, w)`, have zero Hermitian part. -/
theorem frameHermitianForm_eq_zero (hF : Fᵀ = -F)
    (hJ : frameComplexStructureᵀ * F * frameComplexStructure = -F) :
    F.frameHermitianForm = 0 := by
  have hJF : frameComplexStructure * F = -(F * frameComplexStructure) := by
    calc frameComplexStructure * F =
          frameComplexStructure * -(frameComplexStructureᵀ * F * frameComplexStructure) := by
            rw [hJ, neg_neg]
      _ = -(F * frameComplexStructure) := by
        simp only [transpose_frameComplexStructure, neg_mul, neg_neg, ← mul_assoc,
          frameComplexStructure_mul_self, one_mul]
  simp [frameHermitianForm, transpose_mul, hF, transpose_frameComplexStructure, hJF]

/-- `F⁻ J` is symmetric. -/
theorem transpose_frameAntiSelfDualPart_mul_frameComplexStructure (hF : Fᵀ = -F) :
    (F.frameAntiSelfDualPart * frameComplexStructure)ᵀ =
      F.frameAntiSelfDualPart * frameComplexStructure := by
  rw [eq_of_transpose_eq_neg hF]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [frameAntiSelfDualPart, frameHodgeStar, frameComplexStructure, mul_apply,
      Fin.sum_univ_four] <;> ring

/-- `F⁻ J` is trace free. -/
theorem trace_frameAntiSelfDualPart_mul_frameComplexStructure (hF : Fᵀ = -F) :
    (F.frameAntiSelfDualPart * frameComplexStructure).trace = 0 := by
  rw [eq_of_transpose_eq_neg hF]
  simp [trace, frameAntiSelfDualPart, frameHodgeStar, frameComplexStructure, Fin.sum_univ_four]
  ring

/-- `(F⁻ J)² = (|F⁻|² / 2) Id`: the anti-self-dual part acts through a scaled orthogonal
symmetric matrix. -/
theorem frameAntiSelfDualPart_mul_frameComplexStructure_mul_self (hF : Fᵀ = -F) :
    F.frameAntiSelfDualPart * frameComplexStructure *
        (F.frameAntiSelfDualPart * frameComplexStructure) =
      (F.frameAntiSelfDualPart.frameInner F.frameAntiSelfDualPart / 2) • 1 := by
  rw [frameInner_frameAntiSelfDualPart_self hF, eq_of_transpose_eq_neg hF]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [frameAntiSelfDualPart, frameHodgeStar, frameComplexStructure, mul_apply,
      Fin.sum_univ_four] <;> ring

/-! ### The smallest eigenvalue of the Hermitian part -/

/-- `(F⁻ J)² = l² Id` for `l = |F⁻| / √2`. -/
private theorem frameAntiSelfDualPart_mul_frameComplexStructure_mul_self' (hF : Fᵀ = -F) :
    F.frameAntiSelfDualPart * frameComplexStructure *
        (F.frameAntiSelfDualPart * frameComplexStructure) =
      (√(F.frameAntiSelfDualPart.frameInner F.frameAntiSelfDualPart) / √2 *
        (√(F.frameAntiSelfDualPart.frameInner F.frameAntiSelfDualPart) / √2)) • 1 := by
  rw [frameAntiSelfDualPart_mul_frameComplexStructure_mul_self hF, div_mul_div_comm,
    Real.mul_self_sqrt (frameInner_self_nonneg _), Real.mul_self_sqrt zero_le_two]

/-- `c - |F⁻| / √2` is an eigenvalue of the Hermitian part `B` of a two-form, where
`c = ⟨F, ω⟩ / 2`. -/
theorem exists_frameHermitianForm_mulVec_eq (hF : Fᵀ = -F) :
    ∃ v ≠ 0, F.frameHermitianForm *ᵥ v =
      (F.frameInner frameKahlerForm / 2 -
        √(F.frameAntiSelfDualPart.frameInner F.frameAntiSelfDualPart) / √2) • v := by
  have hMM := frameAntiSelfDualPart_mul_frameComplexStructure_mul_self' hF
  set M := F.frameAntiSelfDualPart * frameComplexStructure
  set l := √(F.frameAntiSelfDualPart.frameInner F.frameAntiSelfDualPart) / √2
  -- `M (l - M) = -l (l - M)` since `M² = l²`, so a nonzero column of `l - M` is an eigenvector
  -- of `M` for `-l`; if `l - M = 0`, then `l = 0` because `M` is trace free.
  obtain ⟨v, hv0, hv⟩ : ∃ v ≠ 0, M *ᵥ v = -l • v := by
    by_cases h : l • (1 : Matrix (Fin 4) (Fin 4) ℝ) - M = 0
    · have hM : M = l • 1 := (sub_eq_zero.1 h).symm
      have hl : l = 0 := by
        have htr : M.trace = 0 := trace_frameAntiSelfDualPart_mul_frameComplexStructure hF
        rw [hM, trace_smul, trace_one] at htr
        simpa using htr
      exact ⟨Pi.single 0 1, by simp [Pi.single_eq_zero_iff], by
        rw [hM, hl, zero_smul, zero_mulVec, neg_zero, zero_smul]⟩
    · obtain ⟨j, hj⟩ : ∃ j, (l • 1 - M) *ᵥ Pi.single j 1 ≠ 0 := by
        by_contra! hc
        exact h (ext_of_mulVec_single fun j ↦ by rw [hc j, zero_mulVec])
      refine ⟨_, hj, ?_⟩
      rw [mulVec_mulVec, ← smul_mulVec]
      congr 1
      rw [mul_sub, hMM, mul_smul_comm, mul_one, smul_sub, smul_smul]
      module
  refine ⟨v, hv0, ?_⟩
  rw [frameHermitianForm_eq hF, add_mulVec, smul_mulVec, one_mulVec, hv, sub_smul]
  module

/-- `B - μ Id` is positive semidefinite exactly when `μ ≤ c - |F⁻| / √2`, where `B` is the
Hermitian part of a two-form and `c = ⟨F, ω⟩ / 2`. Together with
`exists_frameHermitianForm_mulVec_eq`, `c - |F⁻| / √2` is the smallest eigenvalue of `B`. -/
theorem posSemidef_frameHermitianForm_sub_smul_one_iff (hF : Fᵀ = -F) (μ : ℝ) :
    (F.frameHermitianForm - μ • 1).PosSemidef ↔
      μ ≤ F.frameInner frameKahlerForm / 2 -
        √(F.frameAntiSelfDualPart.frameInner F.frameAntiSelfDualPart) / √2 := by
  obtain ⟨v, hv0, hv⟩ := exists_frameHermitianForm_mulVec_eq hF
  have hMM := frameAntiSelfDualPart_mul_frameComplexStructure_mul_self' hF
  set c := F.frameInner frameKahlerForm / 2
  set M := F.frameAntiSelfDualPart * frameComplexStructure
  set l := √(F.frameAntiSelfDualPart.frameInner F.frameAntiSelfDualPart) / √2
  constructor
  · intro h
    have hpos : 0 < v ⬝ᵥ v :=
      lt_of_le_of_ne (dotProduct_self_star_nonneg v) (Ne.symm (dotProduct_self_eq_zero.not.2 hv0))
    have := h.dotProduct_mulVec_nonneg v
    rw [star_trivial, sub_mulVec, hv, smul_mulVec, one_mulVec, ← sub_smul, dotProduct_smul,
      smul_eq_mul] at this
    nlinarith
  · intro h
    refine .of_dotProduct_mulVec_nonneg ?_ fun x ↦ ?_
    · rw [isHermitian_iff_isSymm, IsSymm, transpose_sub, transpose_frameHermitianForm,
        transpose_smul, transpose_one]
    -- Cauchy–Schwarz and `M² = l²` with `M` symmetric give `|x ⬝ M x| ≤ l |x|²`.
    have hMx : (M *ᵥ x) ⬝ᵥ (M *ᵥ x) = (l * l) * (x ⬝ᵥ x) := by
      calc (M *ᵥ x) ⬝ᵥ (M *ᵥ x) = x ⬝ᵥ (Mᵀ *ᵥ (M *ᵥ x)) := by
            rw [dotProduct_mulVec x Mᵀ, vecMul_transpose]
        _ = (l * l) * (x ⬝ᵥ x) := by
          rw [transpose_frameAntiSelfDualPart_mul_frameComplexStructure hF, mulVec_mulVec, hMM,
            smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]
    have hCS : (x ⬝ᵥ (M *ᵥ x)) ^ 2 ≤ (l * (x ⬝ᵥ x)) ^ 2 :=
      calc (x ⬝ᵥ (M *ᵥ x)) ^ 2 ≤ (x ⬝ᵥ x) * ((M *ᵥ x) ⬝ᵥ (M *ᵥ x)) := by
            simpa only [dotProduct, sq] using
              Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x (M *ᵥ x)
        _ = (l * (x ⬝ᵥ x)) ^ 2 := by rw [hMx]; ring
    have hl : 0 ≤ l := by positivity
    have hx : 0 ≤ x ⬝ᵥ x := dotProduct_self_star_nonneg x
    have hB : x ⬝ᵥ ((F.frameHermitianForm - μ • 1) *ᵥ x) =
        (c - μ) * (x ⬝ᵥ x) + x ⬝ᵥ (M *ᵥ x) := by
      rw [frameHermitianForm_eq hF, sub_mulVec, add_mulVec, smul_mulVec, smul_mulVec, one_mulVec,
        dotProduct_sub, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      ring
    rw [star_trivial, hB]
    nlinarith [(abs_le_of_sq_le_sq' hCS (mul_nonneg hl hx)).1]

/-- The smallest eigenvalue of the Hermitian part `B` of a two-form is `c - |F⁻| / √2`, where
`c = ⟨F, ω⟩ / 2`. -/
theorem isLeast_frameHermitianForm_eigenvalues (hF : Fᵀ = -F) :
    IsLeast {μ : ℝ | ∃ v ≠ 0, F.frameHermitianForm *ᵥ v = μ • v}
      (F.frameInner frameKahlerForm / 2 -
        √(F.frameAntiSelfDualPart.frameInner F.frameAntiSelfDualPart) / √2) := by
  refine ⟨exists_frameHermitianForm_mulVec_eq hF, fun μ ⟨v, hv0, hv⟩ ↦ ?_⟩
  have hpos : 0 < v ⬝ᵥ v :=
    lt_of_le_of_ne (dotProduct_self_star_nonneg v) (Ne.symm (dotProduct_self_eq_zero.not.2 hv0))
  have := ((posSemidef_frameHermitianForm_sub_smul_one_iff hF _).2 le_rfl).dotProduct_mulVec_nonneg
    v
  rw [star_trivial, sub_mulVec, hv, smul_mulVec, one_mulVec, ← sub_smul, dotProduct_smul,
    smul_eq_mul] at this
  nlinarith

/-- If `B + C Id` is positive semidefinite, where `B` is the Hermitian part of a two-form, then
`|F⁻| ≤ √2 (c + C)` with `c = ⟨F, ω⟩ / 2`. -/
theorem sqrt_frameInner_frameAntiSelfDualPart_le (hF : Fᵀ = -F) {C : ℝ}
    (h : (F.frameHermitianForm + C • 1).PosSemidef) :
    √(F.frameAntiSelfDualPart.frameInner F.frameAntiSelfDualPart) ≤
      √2 * (F.frameInner frameKahlerForm / 2 + C) := by
  rw [← sub_neg_eq_add, ← neg_smul, posSemidef_frameHermitianForm_sub_smul_one_iff hF] at h
  have h2 : (0 : ℝ) < √2 := by positivity
  have h' : √(F.frameAntiSelfDualPart.frameInner F.frameAntiSelfDualPart) / √2 ≤
      F.frameInner frameKahlerForm / 2 + C := by linarith
  rw [div_le_iff₀ h2] at h'
  linarith

end Matrix
