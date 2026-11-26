/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Topology.Algebra.Module.Determinant
public import TauCeti.Analysis.Normed.Operator.SNumbers.Hilbert
import TauCeti.Analysis.InnerProductSpace.PiL2
import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.EckartYoung
import TauCeti.LinearAlgebra.Matrix.CornerMinor
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.Topology.Algebra.Module.Determinant

/-!
# Determinant quantities and the maximal difference theorem

For a bounded linear map `T : E →L[𝕜] F` between seminormed spaces over `ℝ` or `ℂ`, the `n`-th
*determinant quantity* is
`Δₙ(T) = sup {‖det(B ∘ T ∘ A)‖₊ : A : ℓ₂ⁿ → E, B : F → ℓ₂ⁿ, ‖A‖ ≤ 1, ‖B‖ ≤ 1}`,
where `ℓ₂ⁿ = EuclideanSpace 𝕜 (Fin n)`. Unlike an s-number sequence, `Δ₀(T) = 1`, `Δ₁(T) = ‖T‖₊`,
and `Δₙ(c • T) = ‖c‖₊ⁿ Δₙ(T)`: `Δₙ(T)` measures the largest `n`-dimensional Euclidean volume gain
across compressions of `T`.

The determinant quantities satisfy two complementary recursions that bridge the largest s-number
sequence (the approximation numbers `aₙ = singularValue`) and the Hilbert numbers `hₙ`:

1. **Lower recursion** (`ContinuousLinearMap.pow_div_mul_singularValue_mul_detNumber_le`):
   `(kᵏ / (k + 1)ᵏ⁺¹) aₖ(T) Δₖ(T) ≤ Δₖ₊₁(T)` (with `0⁰ = 1`).
2. **Upper recursion** (`ContinuousLinearMap.detNumber_succ_le`):
   `Δₙ₊₁(T) ≤ hₙ(T) Δₙ(T)`.

Together these recursions characterize positivity of `Δₙ₊₁(T)` by `0 < aₙ(T)`
(`ContinuousLinearMap.detNumber_succ_pos_iff`) and yield the sharp maximal difference bound
`aₙ(T) ≤ ((n + 1)ⁿ⁺¹ / nⁿ) hₙ(T)`
(`ContinuousLinearMap.singularValue_le_pow_div_pow_mul_hilbertNumber`), Pietsch's maximal
difference bound `aₙ(T) ≤ e (n + 1) hₙ(T)`
(`ContinuousLinearMap.singularValue_le_exp_mul_hilbertNumber`), and the vanishing equivalence
`hₙ(T) = 0 ↔ aₙ(T) = 0` (`ContinuousLinearMap.hilbertNumber_eq_zero_iff`).

## Main declarations

* `ContinuousLinearMap.detNumber`: the determinant quantities `Δₙ(T)`.
* `ContinuousLinearMap.isLUB_detNumber`: supremum characterization of `Δₙ(T)`.
* `ContinuousLinearMap.nnnorm_det_comp_comp_le_detNumber`: `‖det(B T A)‖₊ ≤ ‖B‖₊ⁿ Δₙ(T) ‖A‖₊ⁿ`.
* `ContinuousLinearMap.detNumber_zero`, `ContinuousLinearMap.detNumber_one`: `Δ₀(T) = 1` and
  `Δ₁(T) = ‖T‖₊`.
* `ContinuousLinearMap.pow_div_mul_singularValue_mul_detNumber_le`: the lower recursion
  `(kᵏ / (k + 1)ᵏ⁺¹) aₖ(T) Δₖ(T) ≤ Δₖ₊₁(T)`.
* `ContinuousLinearMap.detNumber_succ_le`: the upper recursion `Δₙ₊₁(T) ≤ hₙ(T) Δₙ(T)`.
* `ContinuousLinearMap.detNumber_succ_pos_iff`, `ContinuousLinearMap.detNumber_succ_eq_zero_iff`:
  `0 < Δₙ₊₁(T) ↔ 0 < aₙ(T)` and `Δₙ₊₁(T) = 0 ↔ aₙ(T) = 0`.
* `ContinuousLinearMap.singularValue_le_pow_div_pow_mul_hilbertNumber`: sharp maximal difference
  bound `aₙ(T) ≤ ((n + 1)ⁿ⁺¹ / nⁿ) hₙ(T)`.
* `ContinuousLinearMap.singularValue_le_exp_mul_hilbertNumber`: maximal difference bound
  `aₙ(T) ≤ e (n + 1) hₙ(T)`.
* `ContinuousLinearMap.hilbertNumber_eq_zero_iff`: `hₙ(T) = 0 ↔ aₙ(T) = 0`.

## References

* A. Pietsch, *s-Numbers of operators in Banach spaces*, Studia Math. 51 (1974), 201–223.
* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge Studies in Advanced Mathematics 13,
  Cambridge University Press (1987), §2.10.
* B. Carl, A. Hinrichs, *On s-numbers and Weyl inequalities of operators in Banach spaces*,
  Bull. Lond. Math. Soc. 41 (2009), 332–340.
* M. Ullrich, *Inequalities between s-numbers*, Adv. Oper. Theory 9 (2024), art. 82.
* M. Ullrich, *On bounds between all s-numbers and widths of convex sets*, arXiv:2608.05024
  (2026), Theorem 1 and Lemmas 3–4.
* M. Ullrich, *Formalizing s-numbers of operators in Lean*, arXiv:2603.22592 (2026).
* M. Ullrich, Lean-SNumbers (Apache-2.0), <https://github.com/mario-ullrich/Lean-SNumbers>,
  `SNumbers/MaxDifference.lean` and `BasicResults/Determinant.lean`: an earlier Lean formalization
  of the determinant quantities and maximal difference inequality.
-/

public section

open scoped NNReal lp

namespace ContinuousLinearMap

section Basic

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The `n`-th determinant quantity `Δₙ(T)` of a bounded linear map `T`: the supremum of
`‖(B ∘L T ∘L A).det‖₊` over all contractions `A : EuclideanSpace 𝕜 (Fin n) →L[𝕜] E` and
`B : F →L[𝕜] EuclideanSpace 𝕜 (Fin n)`. Notice `Δ₀(T) = 1` (`detNumber_zero`) and
`Δ₁(T) = ‖T‖₊` (`detNumber_one`). -/
noncomputable def detNumber (T : E →L[𝕜] F) (n : ℕ) : ℝ≥0 :=
  ⨆ p : {p : (EuclideanSpace 𝕜 (Fin n) →L[𝕜] E) × (F →L[𝕜] EuclideanSpace 𝕜 (Fin n)) //
      ‖p.1‖ ≤ 1 ∧ ‖p.2‖ ≤ 1},
    ‖(p.val.2 ∘L T ∘L p.val.1).det‖₊

/-- `Δₙ(T)` is the supremum of `‖(B ∘L T ∘L A).det‖₊` over contractions `A : ℓ₂ⁿ → E` and
`B : F → ℓ₂ⁿ`. -/
theorem detNumber_def (T : E →L[𝕜] F) (n : ℕ) :
    T.detNumber n =
      ⨆ p : {p : (EuclideanSpace 𝕜 (Fin n) →L[𝕜] E) × (F →L[𝕜] EuclideanSpace 𝕜 (Fin n)) //
          ‖p.1‖ ≤ 1 ∧ ‖p.2‖ ≤ 1},
        ‖(p.val.2 ∘L T ∘L p.val.1).det‖₊ := by
  rw [detNumber]

private instance (n : ℕ) :
    Nonempty {p : (EuclideanSpace 𝕜 (Fin n) →L[𝕜] E) × (F →L[𝕜] EuclideanSpace 𝕜 (Fin n)) //
      ‖p.1‖ ≤ 1 ∧ ‖p.2‖ ≤ 1} :=
  ⟨⟨0, by simp, by simp⟩⟩

private theorem mem_upperBounds_range_nnnorm_det_comp_comp (T : E →L[𝕜] F) (n : ℕ) :
    ‖T‖₊ ^ n ∈ upperBounds (Set.range fun p :
        {p : (EuclideanSpace 𝕜 (Fin n) →L[𝕜] E) × (F →L[𝕜] EuclideanSpace 𝕜 (Fin n)) //
          ‖p.1‖ ≤ 1 ∧ ‖p.2‖ ≤ 1} ↦
      ‖(p.val.2 ∘L T ∘L p.val.1).det‖₊) := by
  rintro _ ⟨⟨⟨A, B⟩, hA, hB⟩, rfl⟩
  have hnorm : ‖B ∘L T ∘L A‖₊ ≤ ‖T‖₊ := by
    calc ‖B ∘L T ∘L A‖₊
        ≤ ‖B‖₊ * (‖T‖₊ * ‖A‖₊) :=
          (opNNNorm_comp_le _ _).trans (mul_le_mul_right (opNNNorm_comp_le _ _) _)
      _ ≤ 1 * (‖T‖₊ * 1) := by gcongr <;> assumption_mod_cast
      _ = ‖T‖₊ := by simp
  have hdet : ‖(B ∘L T ∘L A).det‖₊ ≤ ‖B ∘L T ∘L A‖₊ ^ n := by
    simpa only [← NNReal.coe_le_coe, coe_nnNorm, NNReal.coe_pow, finrank_euclideanSpace_fin] using
      (B ∘L T ∘L A).norm_det_le_opNorm_pow
  exact hdet.trans (pow_le_pow_left' hnorm n)

/-- For contractions `A : ℓ₂ⁿ → E` and `B : F → ℓ₂ⁿ`, `‖(B ∘L T ∘L A).det‖₊ ≤ Δₙ(T)`. -/
theorem nnnorm_det_comp_comp_le_detNumber_of_norm_le_one (T : E →L[𝕜] F) {n : ℕ}
    {A : EuclideanSpace 𝕜 (Fin n) →L[𝕜] E} {B : F →L[𝕜] EuclideanSpace 𝕜 (Fin n)}
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) :
    ‖(B ∘L T ∘L A).det‖₊ ≤ T.detNumber n :=
  le_ciSup (f := fun p :
      {p : (EuclideanSpace 𝕜 (Fin n) →L[𝕜] E) × (F →L[𝕜] EuclideanSpace 𝕜 (Fin n)) //
        ‖p.1‖ ≤ 1 ∧ ‖p.2‖ ≤ 1} ↦ ‖(p.val.2 ∘L T ∘L p.val.1).det‖₊)
    ⟨_, mem_upperBounds_range_nnnorm_det_comp_comp T n⟩ ⟨(A, B), hA, hB⟩

/-- **Upper-bound characterization.** `Δₙ(T) ≤ c` if and only if `‖(B ∘L T ∘L A).det‖₊ ≤ c` for
all contractions `A : ℓ₂ⁿ → E` and `B : F → ℓ₂ⁿ`. -/
theorem detNumber_le_iff {T : E →L[𝕜] F} {n : ℕ} {c : ℝ≥0} :
    T.detNumber n ≤ c ↔
      ∀ (A : EuclideanSpace 𝕜 (Fin n) →L[𝕜] E) (B : F →L[𝕜] EuclideanSpace 𝕜 (Fin n)),
        ‖A‖ ≤ 1 → ‖B‖ ≤ 1 → ‖(B ∘L T ∘L A).det‖₊ ≤ c := by
  rw [detNumber, ciSup_le_iff ⟨_, mem_upperBounds_range_nnnorm_det_comp_comp T n⟩, Subtype.forall,
    Prod.forall]
  exact forall₂_congr fun A B ↦ ⟨fun h hA hB ↦ h ⟨hA, hB⟩, fun h hAB ↦ h hAB.1 hAB.2⟩

/-- **Supremum characterization.** `Δₙ(T)` is the least upper bound of `‖(B ∘L T ∘L A).det‖₊` over
contractions `A : ℓ₂ⁿ → E` and `B : F → ℓ₂ⁿ`. -/
theorem isLUB_detNumber (T : E →L[𝕜] F) (n : ℕ) :
    IsLUB {c : ℝ≥0 | ∃ (A : EuclideanSpace 𝕜 (Fin n) →L[𝕜] E)
      (B : F →L[𝕜] EuclideanSpace 𝕜 (Fin n)),
        ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧ ‖(B ∘L T ∘L A).det‖₊ = c} (T.detNumber n) := by
  refine ⟨?_, fun c hc ↦ detNumber_le_iff.mpr fun A B hA hB ↦ hc ⟨A, B, hA, hB, rfl⟩⟩
  rintro c ⟨A, B, hA, hB, rfl⟩
  exact T.nnnorm_det_comp_comp_le_detNumber_of_norm_le_one hA hB

/-- **Near-optimal compressions.** If `c < Δₙ(T)`, some contraction compression of `T` through
`ℓ₂ⁿ` has determinant norm greater than `c`. -/
theorem exists_lt_nnnorm_det_of_lt_detNumber {T : E →L[𝕜] F} {n : ℕ} {c : ℝ≥0}
    (h : c < T.detNumber n) :
    ∃ (A : EuclideanSpace 𝕜 (Fin n) →L[𝕜] E) (B : F →L[𝕜] EuclideanSpace 𝕜 (Fin n)),
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧ c < ‖(B ∘L T ∘L A).det‖₊ := by
  by_contra! hc
  exact h.not_ge (detNumber_le_iff.mpr hc)

/-- The `n`-th determinant quantity is bounded by `‖T‖₊ ^ n`. -/
theorem detNumber_le_pow_nnnorm (T : E →L[𝕜] F) (n : ℕ) : T.detNumber n ≤ ‖T‖₊ ^ n :=
  ciSup_le fun p ↦ mem_upperBounds_range_nnnorm_det_comp_comp T n ⟨p, rfl⟩

/-- **Zeroth determinant quantity.** `Δ₀(T) = 1`. -/
@[simp]
theorem detNumber_zero (T : E →L[𝕜] F) : T.detNumber 0 = 1 := by
  refine le_antisymm (by simpa using T.detNumber_le_pow_nnnorm 0) ?_
  simpa [ContinuousLinearMap.det, LinearMap.det_eq_one_of_subsingleton] using
    T.nnnorm_det_comp_comp_le_detNumber_of_norm_le_one (n := 0) (A := 0) (B := 0)
      (by simp) (by simp)

/-- **Homogeneous compression bound.** For all bounded `A : ℓ₂ⁿ → E` and `B : F → ℓ₂ⁿ`,
`‖(B ∘L T ∘L A).det‖₊ ≤ ‖B‖₊ ^ n * Δₙ(T) * ‖A‖₊ ^ n`. -/
theorem nnnorm_det_comp_comp_le_detNumber {n : ℕ}
    (B : F →L[𝕜] EuclideanSpace 𝕜 (Fin n)) (T : E →L[𝕜] F)
    (A : EuclideanSpace 𝕜 (Fin n) →L[𝕜] E) :
    ‖(B ∘L T ∘L A).det‖₊ ≤ ‖B‖₊ ^ n * T.detNumber n * ‖A‖₊ ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [ContinuousLinearMap.det, LinearMap.det_eq_one_of_subsingleton]
  rcases eq_or_ne (B ∘L T ∘L A) 0 with hS | hS
  · simp [hS, ContinuousLinearMap.det, LinearMap.det_zero, zero_pow hn.ne']
  have hB₀ : ‖B‖ ≠ 0 := fun hB ↦ hS <| norm_le_zero_iff.mp <|
    (opNorm_comp_le _ _).trans (by simp [hB])
  have hA₀ : ‖A‖ ≠ 0 := fun hA ↦ hS <| norm_le_zero_iff.mp <|
    (opNorm_comp_le _ _).trans <|
      (mul_le_mul_of_nonneg_left (opNorm_comp_le _ _) (norm_nonneg _)).trans (by simp [hA])
  let A' := (‖A‖ : 𝕜)⁻¹ • A
  let B' := (‖B‖ : 𝕜)⁻¹ • B
  have hA₁ : (‖A‖ : 𝕜) • A' = A := smul_inv_smul₀ (RCLike.ofReal_ne_zero.mpr hA₀) A
  have hB₁ : (‖B‖ : 𝕜) • B' = B := smul_inv_smul₀ (RCLike.ofReal_ne_zero.mpr hB₀) B
  have hcomp : B ∘L T ∘L A = ((‖A‖ : 𝕜) * (‖B‖ : 𝕜)) • (B' ∘L T ∘L A') := by
    conv_lhs => rw [← hA₁, ← hB₁]
    ext
    simp [mul_smul]
  have hn' (r : ℝ) : ‖(r : 𝕜)‖₊ = ‖r‖₊ := by ext; simp
  calc ‖(B ∘L T ∘L A).det‖₊
      = (‖A‖₊ * ‖B‖₊) ^ n * ‖(B' ∘L T ∘L A').det‖₊ := by
        simp [hcomp, hn']
    _ ≤ (‖A‖₊ * ‖B‖₊) ^ n * T.detNumber n := by
        gcongr
        exact T.nnnorm_det_comp_comp_le_detNumber_of_norm_le_one
          (by simp [A', norm_smul, inv_mul_cancel₀ hA₀])
          (by simp [B', norm_smul, inv_mul_cancel₀ hB₀])
    _ = ‖B‖₊ ^ n * T.detNumber n * ‖A‖₊ ^ n := by ring

/-- The determinant quantities of the zero operator are `0 ^ n` (`1` at `0`, `0` for `n ≥ 1`). -/
@[simp]
theorem zero_detNumber (n : ℕ) : (0 : E →L[𝕜] F).detNumber n = 0 ^ n := by
  rcases n with _ | n
  · simp
  · simp only [zero_pow (Nat.succ_ne_zero n)]
    exact le_antisymm (by simpa using (0 : E →L[𝕜] F).detNumber_le_pow_nnnorm (n + 1)) bot_le

/-- **First determinant quantity.** `Δ₁(T) = ‖T‖₊`. -/
@[simp]
theorem detNumber_one (T : E →L[𝕜] F) : T.detNumber 1 = ‖T‖₊ := by
  refine le_antisymm (by simpa using T.detNumber_le_pow_nnnorm 1)
    (opNNNorm_le_bound _ _ fun x ↦ ?_)
  set e := EuclideanSpace.basisFun (Fin 1) 𝕜
  have he : ‖e 0‖ = 1 := e.orthonormal.1 0
  obtain ⟨g, hg, hgx⟩ := exists_dual_vector'' 𝕜 (T x)
  let A : EuclideanSpace 𝕜 (Fin 1) →L[𝕜] E := (EuclideanSpace.proj 0).smulRight x
  let B : F →L[𝕜] EuclideanSpace 𝕜 (Fin 1) := g.smulRight (e 0)
  have hA : ‖A‖₊ ≤ ‖x‖₊ := opNNNorm_le_bound _ _ fun z ↦ by
    simpa [A, nnNorm_smul, mul_comm] using mul_le_mul_right (PiLp.nnNorm_apply_le z 0) ‖x‖₊
  have hB : ‖B‖₊ ≤ 1 := by
    rw [nnNorm_smulRight_apply]
    have hen : ‖e 0‖₊ = 1 := NNReal.coe_eq_one.mp he
    have hgn : ‖g‖₊ ≤ 1 := mod_cast hg
    simpa [hen] using hgn
  have hdet : (B ∘L T ∘L A).det = (‖T x‖ : 𝕜) := by
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix e.toBasis, Matrix.det_unique]
    simp [LinearMap.toMatrix_apply, A, B, e, EuclideanSpace.basisFun_repr, hgx,
      RCLike.real_smul_eq_coe_mul]
  calc ‖T x‖₊ = ‖(B ∘L T ∘L A).det‖₊ := by
        rw [hdet, ← NNReal.coe_inj]; simp
    _ ≤ ‖B‖₊ ^ 1 * T.detNumber 1 * ‖A‖₊ ^ 1 := nnnorm_det_comp_comp_le_detNumber B T A
    _ ≤ 1 ^ 1 * T.detNumber 1 * ‖x‖₊ ^ 1 := by gcongr
    _ = T.detNumber 1 * ‖x‖₊ := by simp

/-- **Homogeneity.** `Δₙ(c • T) = ‖c‖₊ ^ n * Δₙ(T)`. -/
@[simp]
theorem detNumber_smul (c : 𝕜) (T : E →L[𝕜] F) (n : ℕ) :
    (c • T).detNumber n = ‖c‖₊ ^ n * T.detNumber n := by
  have hle (d : 𝕜) (S : E →L[𝕜] F) : (d • S).detNumber n ≤ ‖d‖₊ ^ n * S.detNumber n :=
    detNumber_le_iff.mpr fun A B hA hB ↦ by
      have hcomp : B ∘L (d • S) ∘L A = d • (B ∘L S ∘L A) := by ext; simp
      rw [hcomp, det_smul, finrank_euclideanSpace_fin, nnNorm_mul, nnNorm_pow]
      gcongr
      exact S.nnnorm_det_comp_comp_le_detNumber_of_norm_le_one hA hB
  refine (hle c T).antisymm ?_
  rcases eq_or_ne c 0 with rfl | hc
  · rcases n with _ | n <;> simp
  calc ‖c‖₊ ^ n * T.detNumber n
      = ‖c‖₊ ^ n * (c⁻¹ • c • T).detNumber n := by rw [inv_smul_smul₀ hc]
    _ ≤ ‖c‖₊ ^ n * (‖c⁻¹‖₊ ^ n * (c • T).detNumber n) := by gcongr; exact hle _ _
    _ = (c • T).detNumber n := by
        rw [nnNorm_inv, inv_pow, ← mul_assoc,
          mul_inv_cancel₀ (pow_ne_zero n (nnNorm_pos.mpr hc).ne'), one_mul]

end Basic

section Ideal

variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
  [SeminormedAddCommGroup H] [NormedSpace 𝕜 H]

/-- **Two-sided ideal inequality.** `Δₙ(B ∘ T ∘ A) ≤ ‖B‖₊ ^ n * Δₙ(T) * ‖A‖₊ ^ n`. -/
theorem detNumber_comp_comp_le (B : G →L[𝕜] H) (T : F →L[𝕜] G) (A : E →L[𝕜] F) (n : ℕ) :
    (B ∘L T ∘L A).detNumber n ≤ ‖B‖₊ ^ n * T.detNumber n * ‖A‖₊ ^ n :=
  detNumber_le_iff.mpr fun A' B' hA' hB' ↦ by
    have hA'' : ‖A ∘L A'‖₊ ≤ ‖A‖₊ :=
      (opNNNorm_comp_le _ _).trans (mul_le_of_le_one_right' (mod_cast hA'))
    have hB'' : ‖B' ∘L B‖₊ ≤ ‖B‖₊ :=
      (opNNNorm_comp_le _ _).trans (mul_le_of_le_one_left' (mod_cast hB'))
    calc ‖(B' ∘L (B ∘L T ∘L A) ∘L A').det‖₊
        = ‖((B' ∘L B) ∘L T ∘L (A ∘L A')).det‖₊ := by simp only [comp_assoc]
      _ ≤ ‖B' ∘L B‖₊ ^ n * T.detNumber n * ‖A ∘L A'‖₊ ^ n :=
        nnnorm_det_comp_comp_le_detNumber _ T _
      _ ≤ ‖B‖₊ ^ n * T.detNumber n * ‖A‖₊ ^ n := by gcongr

end Ideal

section Normalization

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **Euclidean normalization.** The identity of `EuclideanSpace 𝕜 (Fin n)` has `Δₙ = 1`. -/
theorem detNumber_id_euclideanSpace (n : ℕ) :
    (ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin n))).detNumber n = 1 := by
  set I := ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin n))
  have hI : ‖I‖ ≤ 1 := norm_id_le
  have hI_nn : ‖I‖₊ ≤ 1 := mod_cast hI
  refine le_antisymm ((I.detNumber_le_pow_nnnorm n).trans
    ((pow_le_pow_left' hI_nn n).trans_eq (one_pow n))) ?_
  simpa [I] using I.nnnorm_det_comp_comp_le_detNumber_of_norm_le_one hI hI

end Normalization

section Recursions

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Isometric zero-extension `ℓ₂ᵏ → ℓ₂ᵏ⁺¹` onto the first `k` coordinates. -/
private noncomputable def inclInit (k : ℕ) :
    EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin (k + 1)) :=
  (LinearIsometry.piLpExtendByZero 2 𝕜 𝕜 (Fin.castLEEmb (Nat.le_succ k))).toContinuousLinearMap

/-- Orthogonal coordinate restriction `ℓ₂ᵏ⁺¹ → ℓ₂ᵏ` onto the first `k` coordinates. -/
private noncomputable def projInit (k : ℕ) :
    EuclideanSpace 𝕜 (Fin (k + 1)) →L[𝕜] EuclideanSpace 𝕜 (Fin k) :=
  (inclInit (𝕜 := 𝕜) k).adjoint

private theorem projInit_apply {k : ℕ} (z : EuclideanSpace 𝕜 (Fin (k + 1))) (i : Fin k) :
    projInit k z i = z i.castSucc := by
  rw [projInit, inclInit, EuclideanSpace.adjoint_piLpExtendByZero_castLEEmb_apply,
    EuclideanSpace.take_apply]
  exact congrArg z (Fin.ext (by simp))

private theorem norm_projInit_sq_add_norm_last_sq {k : ℕ} (z : EuclideanSpace 𝕜 (Fin (k + 1))) :
    ‖projInit k z‖ ^ 2 + ‖z (Fin.last k)‖ ^ 2 = ‖z‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc]
  simp only [projInit_apply]

/-- Bordered right factor `z ↦ a • A (z_init) + (b * z_last) • x` on `ℓ₂ᵏ⁺¹`. -/
private noncomputable def extendRight {k : ℕ} (A : EuclideanSpace 𝕜 (Fin k) →L[𝕜] E) (x : E)
    (a b : ℝ) : EuclideanSpace 𝕜 (Fin (k + 1)) →L[𝕜] E :=
  (a : 𝕜) • (A ∘L projInit k) + (b : 𝕜) • (EuclideanSpace.proj (Fin.last k)).smulRight x

private theorem norm_extendRight_le_one {k : ℕ} {A : EuclideanSpace 𝕜 (Fin k) →L[𝕜] E} {x : E}
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ^ 2 + b ^ 2 = 1) (hA : ‖A‖ ≤ 1) (hx : ‖x‖ ≤ 1) :
    ‖extendRight A x a b‖ ≤ 1 := by
  refine opNorm_le_bound _ zero_le_one fun z ↦ ?_
  rw [one_mul]
  have h1 : ‖extendRight A x a b z‖ ≤ a * ‖projInit k z‖ + b * ‖z (Fin.last k)‖ := by
    calc ‖extendRight A x a b z‖
        ≤ ‖(a : 𝕜) • A (projInit k z)‖ + ‖(b : 𝕜) • (z (Fin.last k) • x)‖ :=
          norm_add_le _ _
      _ = a * ‖A (projInit k z)‖ + b * (‖z (Fin.last k)‖ * ‖x‖) := by
          simp [norm_smul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * (1 * ‖projInit k z‖) + b * (‖z (Fin.last k)‖ * 1) := by
          gcongr
          exact (A.le_opNorm _).trans (by gcongr)
      _ = a * ‖projInit k z‖ + b * ‖z (Fin.last k)‖ := by ring
  have hlhs : 0 ≤ a * ‖projInit k z‖ + b * ‖z (Fin.last k)‖ := by positivity
  refine h1.trans ((pow_le_pow_iff_left₀ hlhs (norm_nonneg z) two_ne_zero).mp ?_)
  nlinarith [norm_projInit_sq_add_norm_last_sq z,
    sq_nonneg (b * ‖projInit k z‖ - a * ‖z (Fin.last k)‖)]

private theorem extendRight_single_castSucc {k : ℕ} (A : EuclideanSpace 𝕜 (Fin k) →L[𝕜] E)
    (x : E) (a b : ℝ) (j : Fin k) :
    extendRight A x a b (EuclideanSpace.single j.castSucc 1) =
      (a : 𝕜) • A (EuclideanSpace.single j 1) := by
  have hp : projInit k (EuclideanSpace.single j.castSucc (1 : 𝕜)) = EuclideanSpace.single j 1 := by
    ext m
    simp [projInit_apply, PiLp.single_apply, Fin.castSucc_inj]
  rw [extendRight, add_apply, smul_apply, comp_apply, hp]
  simp [(Fin.castSucc_lt_last j).ne']

private theorem extendRight_single_last {k : ℕ} (A : EuclideanSpace 𝕜 (Fin k) →L[𝕜] E)
    (x : E) (a b : ℝ) :
    extendRight A x a b (EuclideanSpace.single (Fin.last k) 1) = (b : 𝕜) • x := by
  have hp : projInit k (EuclideanSpace.single (Fin.last k) (1 : 𝕜)) = 0 := by
    ext m
    simp [projInit_apply, (Fin.castSucc_lt_last m).ne]
  rw [extendRight, add_apply, smul_apply, comp_apply, hp]
  simp

/-- Bordered left factor `y ↦ (a • B y, b * φ y)` into `ℓ₂ᵏ⁺¹`. -/
private noncomputable def extendLeft {k : ℕ} (B : F →L[𝕜] EuclideanSpace 𝕜 (Fin k))
    (φ : StrongDual 𝕜 F) (a b : ℝ) : F →L[𝕜] EuclideanSpace 𝕜 (Fin (k + 1)) :=
  (a : 𝕜) • (inclInit k ∘L B) +
    (b : 𝕜) • φ.smulRight (EuclideanSpace.single (Fin.last k) (1 : 𝕜))

private theorem extendLeft_apply_castSucc {k : ℕ} (B : F →L[𝕜] EuclideanSpace 𝕜 (Fin k))
    (φ : StrongDual 𝕜 F) (a b : ℝ) (y : F) (i : Fin k) :
    extendLeft B φ a b y i.castSucc = (a : 𝕜) * B y i := by
  have h1 : inclInit k (B y) i.castSucc = B y i :=
    EuclideanSpace.piLpExtendByZero_castLEEmb_apply_castLE (Nat.le_succ k) (B y) i
  simp [extendLeft, h1, (Fin.castSucc_lt_last i).ne, RCLike.real_smul_eq_coe_mul]

private theorem extendLeft_apply_last {k : ℕ} (B : F →L[𝕜] EuclideanSpace 𝕜 (Fin k))
    (φ : StrongDual 𝕜 F) (a b : ℝ) (y : F) :
    extendLeft B φ a b y (Fin.last k) = (b : 𝕜) * φ y := by
  have h0 : inclInit k (B y) (Fin.last k) = 0 :=
    EuclideanSpace.piLpExtendByZero_castLEEmb_apply_of_le (Nat.le_succ k) (B y) le_rfl
  simp [extendLeft, h0, RCLike.real_smul_eq_coe_mul]

private theorem norm_extendLeft_le_one {k : ℕ} {B : F →L[𝕜] EuclideanSpace 𝕜 (Fin k)}
    {φ : StrongDual 𝕜 F} {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) (hB : ‖B‖ ≤ 1) (hφ : ‖φ‖ ≤ 1) :
    ‖extendLeft B φ a b‖ ≤ 1 := by
  refine opNorm_le_bound _ zero_le_one fun y ↦ ?_
  rw [one_mul]
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg y) two_ne_zero).mp ?_
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc]
  simp only [extendLeft_apply_castSucc, extendLeft_apply_last, norm_mul, RCLike.norm_ofReal,
    mul_pow, sq_abs, ← Finset.mul_sum]
  rw [← EuclideanSpace.norm_sq_eq (B y)]
  have hBy : ‖B y‖ ^ 2 ≤ ‖y‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) ((B.le_opNorm y).trans (by nlinarith [norm_nonneg y])) 2
  have hφy : ‖φ y‖ ^ 2 ≤ ‖y‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) ((φ.le_opNorm y).trans (by nlinarith [norm_nonneg y])) 2
  nlinarith [sq_nonneg a, sq_nonneg b]

private theorem toMatrix_extendLeft_comp_extendRight_castSucc_castSucc {k : ℕ} (T : E →L[𝕜] F)
    (A : EuclideanSpace 𝕜 (Fin k) →L[𝕜] E) (B : F →L[𝕜] EuclideanSpace 𝕜 (Fin k))
    (x : E) (φ : StrongDual 𝕜 F) (a b : ℝ) (i j : Fin k) :
    LinearMap.toMatrix (EuclideanSpace.basisFun (Fin (k + 1)) 𝕜).toBasis
        (EuclideanSpace.basisFun (Fin (k + 1)) 𝕜).toBasis
        (extendLeft B φ a b ∘L T ∘L extendRight A x a b).toLinearMap i.castSucc j.castSucc =
      ((a ^ 2 : ℝ) : 𝕜) * (B (T (A (EuclideanSpace.single j 1))) i) := by
  simp [LinearMap.toMatrix_apply, extendRight_single_castSucc, extendLeft_apply_castSucc,
    RCLike.real_smul_eq_coe_mul]
  ring

private theorem toMatrix_extendLeft_comp_extendRight_castSucc_last {k : ℕ} (T : E →L[𝕜] F)
    (A : EuclideanSpace 𝕜 (Fin k) →L[𝕜] E) (B : F →L[𝕜] EuclideanSpace 𝕜 (Fin k))
    (x : E) (φ : StrongDual 𝕜 F) (a b : ℝ) (i : Fin k) :
    LinearMap.toMatrix (EuclideanSpace.basisFun (Fin (k + 1)) 𝕜).toBasis
        (EuclideanSpace.basisFun (Fin (k + 1)) 𝕜).toBasis
        (extendLeft B φ a b ∘L T ∘L extendRight A x a b).toLinearMap i.castSucc (Fin.last k) =
      ((a * b : ℝ) : 𝕜) * (B (T x) i) := by
  simp [LinearMap.toMatrix_apply, extendRight_single_last, extendLeft_apply_castSucc,
    RCLike.real_smul_eq_coe_mul, RCLike.algebraMap_eq_ofReal]
  ring

private theorem toMatrix_extendLeft_comp_extendRight_last_castSucc {k : ℕ} (T : E →L[𝕜] F)
    (A : EuclideanSpace 𝕜 (Fin k) →L[𝕜] E) (B : F →L[𝕜] EuclideanSpace 𝕜 (Fin k))
    (x : E) (φ : StrongDual 𝕜 F) (a b : ℝ) (j : Fin k) :
    LinearMap.toMatrix (EuclideanSpace.basisFun (Fin (k + 1)) 𝕜).toBasis
        (EuclideanSpace.basisFun (Fin (k + 1)) 𝕜).toBasis
        (extendLeft B φ a b ∘L T ∘L extendRight A x a b).toLinearMap (Fin.last k) j.castSucc =
      ((a * b : ℝ) : 𝕜) * φ (T (A (EuclideanSpace.single j 1))) := by
  simp [LinearMap.toMatrix_apply, extendRight_single_castSucc, extendLeft_apply_last,
    RCLike.real_smul_eq_coe_mul, RCLike.algebraMap_eq_ofReal]
  ring

private theorem toMatrix_extendLeft_comp_extendRight_last_last {k : ℕ} (T : E →L[𝕜] F)
    (A : EuclideanSpace 𝕜 (Fin k) →L[𝕜] E) (B : F →L[𝕜] EuclideanSpace 𝕜 (Fin k))
    (x : E) (φ : StrongDual 𝕜 F) (a b : ℝ) :
    LinearMap.toMatrix (EuclideanSpace.basisFun (Fin (k + 1)) 𝕜).toBasis
        (EuclideanSpace.basisFun (Fin (k + 1)) 𝕜).toBasis
        (extendLeft B φ a b ∘L T ∘L extendRight A x a b).toLinearMap (Fin.last k) (Fin.last k) =
      ((b ^ 2 : ℝ) : 𝕜) * φ (T x) := by
  simp [LinearMap.toMatrix_apply, extendRight_single_last, extendLeft_apply_last,
    RCLike.real_smul_eq_coe_mul]
  ring

/-- Schur-complement determinant identity for the bordered compression `B' ∘L T ∘L A'`. -/
private theorem det_extendLeft_comp_extendRight {k : ℕ} (T : E →L[𝕜] F)
    (A : EuclideanSpace 𝕜 (Fin k) →L[𝕜] E) (B : F →L[𝕜] EuclideanSpace 𝕜 (Fin k))
    (x : E) (φ : StrongDual 𝕜 F) {u : EuclideanSpace 𝕜 (Fin k)}
    (hu : (B ∘L T ∘L A) u = B (T x)) {a b : ℝ} (ha : a ≠ 0) :
    (extendLeft B φ a b ∘L T ∘L extendRight A x a b).det =
      (((b ^ 2 : ℝ) : 𝕜) * φ (T x - T (A u))) *
        (((a ^ 2 : ℝ) : 𝕜) ^ k * (B ∘L T ∘L A).det) := by
  let e₀ := (EuclideanSpace.basisFun (Fin k) 𝕜).toBasis
  set e₁ := (EuclideanSpace.basisFun (Fin (k + 1)) 𝕜).toBasis with he₁
  set M := LinearMap.toMatrix e₁ e₁ (extendLeft B φ a b ∘L T ∘L extendRight A x a b).toLinearMap
    with hM
  let w : Fin k → 𝕜 := fun j ↦ ((b / a : ℝ) : 𝕜) * u j
  have hTAu : T (A u) = ∑ j : Fin k, u j • T (A (EuclideanSpace.single j 1)) := by
    have hu_sum : ∑ j : Fin k, u j • EuclideanSpace.single j (1 : 𝕜) = u := by
      simpa using (EuclideanSpace.basisFun (Fin k) 𝕜).sum_repr u
    simp_rw [← map_smul, ← map_sum, hu_sum]
  have hw (i : Fin k) : M i.castSucc (Fin.last k) = ∑ j : Fin k, M i.castSucc j.castSucc * w j := by
    have hlin : ∑ j : Fin k, u j * (B (T (A (EuclideanSpace.single j 1))) i) = B (T x) i := by
      have hBTx : B (T x) = B (T (A u)) := hu.symm
      rw [hBTx, hTAu, map_sum]
      simp [map_smul]
    have hab' : ((a ^ 2 : ℝ) : 𝕜) * ((b / a : ℝ) : 𝕜) = ((a * b : ℝ) : 𝕜) := by
      norm_cast; field_simp
    rw [hM, he₁, toMatrix_extendLeft_comp_extendRight_castSucc_last, ← hlin, ← hab',
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [toMatrix_extendLeft_comp_extendRight_castSucc_castSucc]
    simp only [w]; ring
  have hschur : M (Fin.last k) (Fin.last k) - ∑ j : Fin k, M (Fin.last k) j.castSucc * w j =
      ((b ^ 2 : ℝ) : 𝕜) * φ (T x - T (A u)) := by
    have hlin : ∑ j : Fin k, u j * φ (T (A (EuclideanSpace.single j 1))) = φ (T (A u)) := by
      rw [hTAu, map_sum]
      simp [map_smul]
    have hbb : ((a * b : ℝ) : 𝕜) * ((b / a : ℝ) : 𝕜) = ((b ^ 2 : ℝ) : 𝕜) := by
      norm_cast; field_simp
    have hsum : ∑ j : Fin k, M (Fin.last k) j.castSucc * w j = ((b ^ 2 : ℝ) : 𝕜) * φ (T (A u)) := by
      rw [← hlin, ← hbb, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [hM, he₁, toMatrix_extendLeft_comp_extendRight_last_castSucc]
      simp only [w]; ring
    rw [hM, he₁, toMatrix_extendLeft_comp_extendRight_last_last, hsum, map_sub, mul_sub]
  have hsub : M.submatrix Fin.castSucc Fin.castSucc =
      ((a ^ 2 : ℝ) : 𝕜) • LinearMap.toMatrix e₀ e₀ (B ∘L T ∘L A).toLinearMap := by
    ext i j
    rw [Matrix.submatrix_apply, hM, he₁, toMatrix_extendLeft_comp_extendRight_castSucc_castSucc]
    simp [e₀, LinearMap.toMatrix_apply, RCLike.algebraMap_eq_ofReal]
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix e₁, ← hM,
    M.det_eq_sub_sum_mul_det_submatrix_castSucc_of_col hw, hschur, hsub, Matrix.det_smul,
    Fintype.card_fin, LinearMap.det_toMatrix, ContinuousLinearMap.det]

omit [NormedSpace 𝕜 F] in
/-- Scalar and `ℝ≥0`-norm normalization for the bordered Schur-complement determinant product with
weights `a² = k / (k + 1)` and `b² = 1 / (k + 1)`. -/
private theorem nnnorm_ofReal_sq_mul_norm_mul_pow {k : ℕ} {a b : ℝ}
    (ha : a ^ 2 = (k : ℝ) / ((k : ℝ) + 1)) (hb : b ^ 2 = 1 / ((k : ℝ) + 1))
    (v : F) (d : 𝕜) :
    ‖(((b ^ 2 : ℝ) : 𝕜) * (‖v‖ : 𝕜)) * (((a ^ 2 : ℝ) : 𝕜) ^ k * d)‖₊ =
      ((k : ℝ≥0) ^ k / ((k : ℝ≥0) + 1) ^ (k + 1)) * ‖v‖₊ * ‖d‖₊ := by
  ext
  suffices b ^ 2 * ‖v‖ * ((a ^ 2) ^ k * ‖d‖) =
      (k : ℝ) ^ k / ((k : ℝ) + 1) ^ (k + 1) * ‖v‖ * ‖d‖ by simpa
  rw [ha, hb, div_pow]
  field_simp
  ring

/-- Single-compression step for the lower recursion when `k ≥ 1` and `det (B T A) ≠ 0`. -/
private theorem le_detNumber_succ_of_det_ne_zero {k : ℕ} (hk : 0 < k) (T : E →L[𝕜] F)
    {A : EuclideanSpace 𝕜 (Fin k) →L[𝕜] E} {B : F →L[𝕜] EuclideanSpace 𝕜 (Fin k)}
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (hdet : (B ∘L T ∘L A).det ≠ 0) :
    ((k : ℝ≥0) ^ k / ((k : ℝ≥0) + 1) ^ (k + 1)) * T.singularValue k *
      ‖(B ∘L T ∘L A).det‖₊ ≤ T.detNumber (k + 1) := by
  set S := B ∘L T ∘L A
  let eS := S.toContinuousLinearEquivOfDetNeZero hdet
  set R : E →L[𝕜] F :=
    (T ∘L A) ∘L ((eS.symm : EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k)) ∘L B ∘L T)
  set c : ℝ≥0 := (k : ℝ≥0) ^ k / ((k : ℝ≥0) + 1) ^ (k + 1)
  have hc_pos : 0 < c := div_pos (pow_pos (Nat.cast_pos.mpr hk) k)
    (pow_pos (add_pos (Nat.cast_pos.mpr hk) zero_lt_one) (k + 1))
  have hS_pos : 0 < ‖S.det‖₊ := nnNorm_pos.mpr hdet
  have hTA0 : (T ∘L A).singularValue k = 0 :=
    (T ∘L A).singularValue_eq_zero_of_rank_domain_le
      (by rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin])
  have hR0 : R.singularValue k = 0 :=
    le_antisymm (((T ∘L A).singularValue_comp_le_right _ k).trans_eq (by simp [hTA0])) bot_le
  have hR_le : T.singularValue k ≤ ‖T - R‖₊ := by
    simpa only [add_sub_cancel, hR0, zero_add] using R.singularValue_add_le (T - R) k
  refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hR_le hc_pos.le) hS_pos.le).trans ?_
  have hcS : 0 < c * ‖S.det‖₊ := mul_pos hc_pos hS_pos
  rw [mul_assoc, mul_left_comm c, ← le_div_iff₀ hcS]
  refine opNNNorm_le_of_unit_nnNorm fun x hx ↦ (le_div_iff₀ hcS).mpr ?_
  obtain ⟨φ, hφ, hφx⟩ := exists_dual_vector'' 𝕜 ((T - R) x)
  have hk_real : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hk1_real : (0 : ℝ) < (k : ℝ) + 1 := add_pos hk_real zero_lt_one
  set a : ℝ := Real.sqrt ((k : ℝ) / ((k : ℝ) + 1))
  set b : ℝ := Real.sqrt (1 / ((k : ℝ) + 1))
  have ha_pos : 0 < a := Real.sqrt_pos.mpr (div_pos hk_real hk1_real)
  have ha_sq : a ^ 2 = (k : ℝ) / ((k : ℝ) + 1) := Real.sq_sqrt (div_nonneg hk_real.le hk1_real.le)
  have hb_sq : b ^ 2 = 1 / ((k : ℝ) + 1) := Real.sq_sqrt (div_nonneg zero_le_one hk1_real.le)
  have hab : a ^ 2 + b ^ 2 = 1 := by rw [ha_sq, hb_sq, ← add_div, div_self hk1_real.ne']
  let u : EuclideanSpace 𝕜 (Fin k) := eS.symm (B (T x))
  have hu : S u = B (T x) :=
    (S.toContinuousLinearEquivOfDetNeZero_apply hdet u).symm.trans (eS.apply_symm_apply (B (T x)))
  have hdet' := det_extendLeft_comp_extendRight (b := b) T A B x φ hu ha_pos.ne'
  have hRx : T x - T (A u) = (T - R) x := by
    simp only [R, u, sub_apply, comp_apply, ContinuousLinearEquiv.coe_coe]
  have hnnorm : ‖(extendLeft B φ a b ∘L T ∘L extendRight A x a b).det‖₊ =
      ‖(T - R) x‖₊ * (c * ‖S.det‖₊) := by
    rw [hdet', hRx, hφx, nnnorm_ofReal_sq_mul_norm_mul_pow ha_sq hb_sq]
    ring
  exact hnnorm ▸ T.nnnorm_det_comp_comp_le_detNumber_of_norm_le_one
    (norm_extendRight_le_one ha_pos.le (Real.sqrt_nonneg _) hab hA (NNReal.coe_le_coe.mpr hx.le))
    (norm_extendLeft_le_one hab hB hφ)

/-- **Lower recursion for determinant quantities.** For every bounded linear map `T` and every
`k : ℕ`, `(k ^ k / (k + 1) ^ (k + 1)) * aₖ(T) * Δₖ(T) ≤ Δₖ₊₁(T)` (with `0 ^ 0 = 1`). -/
theorem pow_div_mul_singularValue_mul_detNumber_le (T : E →L[𝕜] F) (k : ℕ) :
    ((k : ℝ≥0) ^ k / ((k : ℝ≥0) + 1) ^ (k + 1)) * T.singularValue k * T.detNumber k ≤
      T.detNumber (k + 1) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  rw [detNumber, NNReal.mul_iSup]
  refine ciSup_le fun p ↦ ?_
  by_cases hdet : (p.val.2 ∘L T ∘L p.val.1).det = 0
  · simp [hdet]
  · exact le_detNumber_succ_of_det_ne_zero hk T p.property.1 p.property.2 hdet

omit [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] in
/-- Compressing a singular-value diagonalization `S = U ∘ D ∘ V` on `ℓ₂ⁿ⁺¹` to the first `n`
coordinates yields the diagonal matrix of the first `n` singular values of `S`. -/
private theorem toMatrix_projInit_comp_inclInit_eq_diagonal {n : ℕ}
    (S : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)))
    (U V : EuclideanSpace 𝕜 (Fin (n + 1)) ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)))
    (hUV : S.toLinearMap = U.toLinearMap ∘ₗ
      Matrix.toLin (EuclideanSpace.basisFun (Fin (n + 1)) 𝕜).toBasis
        (EuclideanSpace.basisFun (Fin (n + 1)) 𝕜).toBasis
        (Matrix.diagonal fun i ↦ (S.toLinearMap.singularValues i : 𝕜)) ∘ₗ
      V.toLinearMap) :
    LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) 𝕜).toBasis
        (EuclideanSpace.basisFun (Fin n) 𝕜).toBasis
        (projInit n ∘L U.symm.toLinearIsometry.toContinuousLinearMap ∘L S ∘L
          V.symm.toLinearIsometry.toContinuousLinearMap ∘L inclInit n).toLinearMap =
      Matrix.diagonal fun j : Fin n ↦ (S.toLinearMap.singularValues j.castSucc : 𝕜) := by
  ext i j
  have hJ_apply :
      inclInit n (EuclideanSpace.single j (1 : 𝕜)) = EuclideanSpace.single j.castSucc (1 : 𝕜) :=
    LinearIsometry.piLpExtendByZero_apply_single (Fin.castLEEmb (Nat.le_succ n)) j (1 : 𝕜)
  have hS_apply : S (V.symm (EuclideanSpace.single j.castSucc 1)) =
      U ((S.toLinearMap.singularValues j.castSucc : 𝕜) • EuclideanSpace.single j.castSucc 1) := by
    have hD := Matrix.toLin_diagonal_apply_self (EuclideanSpace.basisFun (Fin (n + 1)) 𝕜)
      (fun k ↦ (S.toLinearMap.singularValues k : 𝕜)) j.castSucc
    simp only [EuclideanSpace.basisFun_apply] at hD
    simpa [hD] using LinearMap.congr_fun hUV (V.symm (EuclideanSpace.single j.castSucc 1))
  simp +contextual [LinearMap.toMatrix_apply, hJ_apply, hS_apply, projInit_apply,
    Matrix.diagonal_apply, PiLp.single_apply, RCLike.real_smul_eq_coe_mul]

/-- The product of the first `n` singular values of an `ℓ₂ⁿ⁺¹` contraction compression of `T` is
at most `Δₙ(T)`. -/
private theorem prod_castSucc_singularValue_le_detNumber {n : ℕ} (T : E →L[𝕜] F)
    {A : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] E}
    {B : F →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1))} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) :
    ∏ j : Fin n, (B ∘L T ∘L A).singularValue j.castSucc ≤ T.detNumber n := by
  set S := B ∘L T ∘L A
  let e₀ := EuclideanSpace.basisFun (Fin n) 𝕜
  obtain ⟨U, V, hUV⟩ := S.toLinearMap.exists_linearIsometryEquiv_eq_comp_toLin_diagonal_comp
    (EuclideanSpace.basisFun (Fin (n + 1)) 𝕜)
  let A₀ : EuclideanSpace 𝕜 (Fin n) →L[𝕜] E :=
    A ∘L V.symm.toLinearIsometry.toContinuousLinearMap ∘L inclInit n
  let B₀ : F →L[𝕜] EuclideanSpace 𝕜 (Fin n) :=
    projInit n ∘L U.symm.toLinearIsometry.toContinuousLinearMap ∘L B
  have hJ : ‖inclInit (𝕜 := 𝕜) n‖ ≤ 1 := LinearIsometry.norm_toContinuousLinearMap_le _
  have hP : ‖projInit (𝕜 := 𝕜) n‖ ≤ 1 := by rw [projInit, LinearIsometryEquiv.norm_map]; exact hJ
  have hA₀ : ‖A₀‖ ≤ 1 := (opNorm_comp_le _ _).trans <| by
    rw [V.symm.toLinearIsometry.norm_toContinuousLinearMap_comp]
    exact (mul_le_of_le_one_right (norm_nonneg _) hJ).trans hA
  have hB₀ : ‖B₀‖ ≤ 1 := (opNorm_comp_le _ _).trans <| by
    rw [U.symm.toLinearIsometry.norm_toContinuousLinearMap_comp]
    exact (mul_le_of_le_one_right (norm_nonneg _) hB).trans hP
  have hcomp : B₀ ∘L T ∘L A₀ = projInit n ∘L U.symm.toLinearIsometry.toContinuousLinearMap ∘L S ∘L
      V.symm.toLinearIsometry.toContinuousLinearMap ∘L inclInit n := by
    simp only [A₀, B₀, S, comp_assoc]
  have hdet : ‖(B₀ ∘L T ∘L A₀).det‖₊ = ∏ j : Fin n, S.singularValue j.castSucc := by
    ext
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix e₀.toBasis, hcomp,
      toMatrix_projInit_comp_inclInit_eq_diagonal S U V hUV, Matrix.det_diagonal,
      coe_nnNorm, NNReal.coe_prod, norm_prod]
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    rw [RCLike.norm_ofReal, abs_of_nonneg (S.toLinearMap.singularValues_nonneg _),
      S.singularValue_eq_linearMap_singularValues]
  exact hdet ▸ T.nnnorm_det_comp_comp_le_detNumber_of_norm_le_one hA₀ hB₀

/-- **Upper recursion for determinant quantities.** For every bounded linear map `T` and every
`n : ℕ`, `Δₙ₊₁(T) ≤ hₙ(T) Δₙ(T)`. -/
theorem detNumber_succ_le (T : E →L[𝕜] F) (n : ℕ) :
    T.detNumber (n + 1) ≤ T.hilbertNumber n * T.detNumber n :=
  detNumber_le_iff.mpr fun A B hA hB ↦ by
    rw [(B ∘L T ∘L A).nnnorm_det_eq_prod_singularValue, finrank_euclideanSpace_fin,
      ← Fin.prod_univ_eq_prod_range, Fin.prod_univ_castSucc, mul_comm]
    gcongr
    · exact T.singularValue_comp_comp_euclideanSpace_le_hilbertNumber_of_norm_le_one hA hB n
    · exact prod_castSucc_singularValue_le_detNumber T hA hB

end Recursions

section MaxDifference

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Positivity characterization of determinant quantities.** For every `n : ℕ`,
`0 < Δₙ₊₁(T) ↔ 0 < aₙ(T)`. -/
theorem detNumber_succ_pos_iff (T : E →L[𝕜] F) (n : ℕ) :
    0 < T.detNumber (n + 1) ↔ 0 < T.singularValue n := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · by_contra! ha
    have ha0 : T.singularValue n = 0 := le_antisymm ha bot_le
    have hh0 : T.hilbertNumber n = 0 :=
      le_antisymm ((T.hilbertNumber_le_singularValue n).trans_eq ha0) bot_le
    exact h.not_ge ((T.detNumber_succ_le n).trans (by simp [hh0]))
  · induction n with
    | zero => simpa using h
    | succ m ih =>
      have hm : 0 < T.detNumber (m + 1) :=
        ih (lt_of_lt_of_le h (T.antitone_singularValue (Nat.le_succ m)))
      have hc : (0 : ℝ≥0) < ((m + 1 : ℕ) : ℝ≥0) ^ (m + 1) / ((m + 1 : ℕ) + 1) ^ (m + 2) := by
        positivity
      exact (mul_pos (mul_pos hc h) hm).trans_le
        (T.pow_div_mul_singularValue_mul_detNumber_le (m + 1))

/-- **Vanishing characterization of determinant quantities.** For every `n : ℕ`,
`Δₙ₊₁(T) = 0 ↔ aₙ(T) = 0`. -/
theorem detNumber_succ_eq_zero_iff (T : E →L[𝕜] F) (n : ℕ) :
    T.detNumber (n + 1) = 0 ↔ T.singularValue n = 0 := by
  simpa [pos_iff_ne_zero] using (T.detNumber_succ_pos_iff n).not

/-- **The maximal difference theorem, sharp form.** For every bounded linear map `T` and every
`n : ℕ`, `aₙ(T) ≤ ((n + 1) ^ (n + 1) / n ^ n) * hₙ(T)`, with `0 ^ 0 = 1`. -/
theorem singularValue_le_pow_div_pow_mul_hilbertNumber (T : E →L[𝕜] F) (n : ℕ) :
    T.singularValue n ≤ ((n : ℝ≥0) + 1) ^ (n + 1) / (n : ℝ≥0) ^ n * T.hilbertNumber n := by
  rcases n with _ | m
  · simp
  rcases eq_or_ne (T.singularValue (m + 1)) 0 with ha0 | ha0
  · simp [ha0]
  have ha : 0 < T.singularValue (m + 1) := pos_iff_ne_zero.mpr ha0
  have hΔ : 0 < T.detNumber (m + 1) := (T.detNumber_succ_pos_iff m).mpr
    (lt_of_lt_of_le ha (T.antitone_singularValue (Nat.le_succ m)))
  have hcomb := (T.pow_div_mul_singularValue_mul_detNumber_le (m + 1)).trans
    (T.detNumber_succ_le (m + 1))
  have hmul := le_of_mul_le_mul_right hcomb hΔ
  calc T.singularValue (m + 1)
      = (((m + 1 : ℕ) : ℝ≥0) + 1) ^ (m + 2) / ((m + 1 : ℕ) : ℝ≥0) ^ (m + 1) *
          ((((m + 1 : ℕ) : ℝ≥0) ^ (m + 1) / (((m + 1 : ℕ) : ℝ≥0) + 1) ^ (m + 2)) *
            T.singularValue (m + 1)) := by
        field_simp
    _ ≤ (((m + 1 : ℕ) : ℝ≥0) + 1) ^ (m + 2) / ((m + 1 : ℕ) : ℝ≥0) ^ (m + 1) *
          T.hilbertNumber (m + 1) := by
        gcongr

/-- **The maximal difference theorem.** For every bounded linear map `T` and every `n : ℕ`,
`aₙ(T) ≤ e (n + 1) hₙ(T)`. -/
theorem singularValue_le_exp_mul_hilbertNumber (T : E →L[𝕜] F) (n : ℕ) :
    (T.singularValue n : ℝ) ≤ Real.exp 1 * ((n : ℝ) + 1) * T.hilbertNumber n := by
  have hsharp : (T.singularValue n : ℝ) ≤
      ((n : ℝ) + 1) ^ (n + 1) / (n : ℝ) ^ n * T.hilbertNumber n := by
    exact_mod_cast T.singularValue_le_pow_div_pow_mul_hilbertNumber n
  refine hsharp.trans (mul_le_mul_of_nonneg_right ?_ (NNReal.coe_nonneg _))
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h1n : ((n : ℝ) + 1) / (n : ℝ) = 1 + (n : ℝ)⁻¹ := by field_simp
  calc ((n : ℝ) + 1) ^ (n + 1) / (n : ℝ) ^ n
      = (1 + (n : ℝ)⁻¹) ^ n * ((n : ℝ) + 1) := by
        rw [← h1n, pow_succ, div_pow]; field_simp
    _ ≤ Real.exp 1 * ((n : ℝ) + 1) := by
        gcongr
        exact Real.one_add_inv_pow_le_exp

/-- **Faithfulness of Hilbert numbers relative to approximation numbers.** For every bounded
linear map `T` and every `n : ℕ`, `hₙ(T) = 0 ↔ aₙ(T) = 0`. -/
theorem hilbertNumber_eq_zero_iff (T : E →L[𝕜] F) (n : ℕ) :
    T.hilbertNumber n = 0 ↔ T.singularValue n = 0 := by
  refine ⟨fun h ↦ le_antisymm ?_ bot_le, fun h ↦
    le_antisymm ((T.hilbertNumber_le_singularValue n).trans_eq h) bot_le⟩
  simpa [h] using T.singularValue_le_pow_div_pow_mul_hilbertNumber n

end MaxDifference

end ContinuousLinearMap
