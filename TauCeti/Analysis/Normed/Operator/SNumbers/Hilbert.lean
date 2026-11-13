/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import TauCeti.Analysis.Normed.Operator.SNumbers.Uniqueness
import Mathlib.Analysis.Normed.Module.HahnBanach
import TauCeti.Analysis.InnerProductSpace.HilbertBasis.FiniteSection.Basic

/-!
# Hilbert numbers

Over `ℝ` or `ℂ`, the `n`-th Hilbert number of a bounded operator `T : E →L[𝕜] F` is
`hₙ(T) = sup {aₙ(B ∘L T ∘L A) : A : ℓ²(ℕ, 𝕜) →L[𝕜] E, B : F →L[𝕜] ℓ²(ℕ, 𝕜), ‖A‖ ≤ 1, ‖B‖ ≤ 1}`,
testing `T` between contractions from and into the standard sequence space `ℓ²(ℕ, 𝕜)`.

Combining scalar factorization through `EuclideanSpace 𝕜 (Fin (n + 1))` with the finite-section
inclusion and cutoff on `ℓ²(ℕ, 𝕜)` extends the contractive test-operator bound to any complete
inner product source `H₁` and inner product target `H₂`
(`ContinuousLinearMap.le_hilbertNumber_of_innerProductSpace`). Scaling non-contractive test maps
yields the homogeneous bound `aₙ(B ∘L T ∘L A) ≤ ‖B‖ hₙ(T) ‖A‖`
(`ContinuousLinearMap.singularValue_comp_comp_le_mul_hilbertNumber_of_innerProductSpace`) and the
ratio formulas over nonzero or arbitrary test maps on `ℓ²(ℕ, 𝕜)`
(`ContinuousLinearMap.hilbertNumber_eq_iSup_ne_zero_div`,
`ContinuousLinearMap.hilbertNumber_eq_iSup_div`).

Testing `T` on the one-dimensional Hilbert space `𝕜` via `toSpanSingleton` and a norming
Hahn–Banach functional gives `h₀(T) = ‖T‖` (`ContinuousLinearMap.hilbertNumber_zero`). On operators
from a complete inner product space into an inner product space, testing with the identities gives
`hₙ(T) = aₙ(T)` (`ContinuousLinearMap.hilbertNumber_eq_singularValue`), which normalizes `hₙ` on
the finite Euclidean identities. Pushing the approximation-number calculus through the supremum
establishes Pietsch's s-number axioms (`TauCeti.SNumbers.isSNumberSequence_hilbert`) and the
mixed-index additive law `h_{m+n}(S + T) ≤ hₘ(S) + hₙ(T)`. Together with Hilbert-space uniqueness
(`TauCeti.SNumbers.IsSNumberSequence.eq_singularValue`), the Hilbert numbers are pointwise the
smallest s-number sequence (`TauCeti.SNumbers.IsSNumberSequence.hilbertNumber_le`), completing the
sandwich `hₙ(T) ≤ sₙ(T) ≤ aₙ(T)`.

## Main declarations

* `ContinuousLinearMap.hilbertNumber`: the Hilbert numbers `hₙ(T)`.
* `ContinuousLinearMap.le_hilbertNumber_of_innerProductSpace`: contractive test maps on arbitrary
  inner product spaces (with complete source) bound `hₙ(T)` from below.
* `ContinuousLinearMap.hilbertNumber_eq_iSup_ne_zero_div`: ratio formula over nonzero test maps.
* `ContinuousLinearMap.hilbertNumber_eq_singularValue`: `hₙ(T) = aₙ(T)` on operators from a
  complete inner product space into an inner product space.
* `ContinuousLinearMap.hilbertNumber_add_index_le`: `h_{m+n}(S + T) ≤ hₘ(S) + hₙ(T)`.
* `TauCeti.SNumbers.isSNumberSequence_hilbert`: the Hilbert numbers form an s-number sequence.
* `TauCeti.SNumbers.IsSNumberSequence.hilbertNumber_le`: `hₙ(T) ≤ s T n` for every s-number
  sequence `s`.

## References

* A. Pietsch, *s-Numbers of operators in Banach spaces*, Studia Math. 51 (1974), §§4–5.
* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge University Press (1987), §§2.4, 2.6.
* M. Ullrich, Lean-SNumbers (Apache-2.0), <https://github.com/mario-ullrich/Lean-SNumbers>,
  `SNumbers/Hilbert.lean`: an earlier Lean formalization of the Hilbert numbers and their
  minimality.
-/

public section

open scoped NNReal lp

namespace ContinuousLinearMap

variable {𝕜 E F G W : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G] [SeminormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- The `n`-th Hilbert number `hₙ(T)` of a bounded linear map `T`: the supremum of the
approximation numbers `aₙ(B ∘L T ∘L A)` over contractions `A : ℓ²(ℕ, 𝕜) →L[𝕜] E` and
`B : F →L[𝕜] ℓ²(ℕ, 𝕜)`. Indexing starts at zero, so `h₀(T) = ‖T‖` (`hilbertNumber_zero`). -/
noncomputable def hilbertNumber (T : E →L[𝕜] F) (n : ℕ) : ℝ≥0 :=
  ⨆ (A : {A : ℓ²(ℕ, 𝕜) →L[𝕜] E // ‖A‖ ≤ 1}) (B : {B : F →L[𝕜] ℓ²(ℕ, 𝕜) // ‖B‖ ≤ 1}),
    (B.1 ∘L T ∘L A.1).singularValue n

/-- `hₙ(T)` is the supremum of `aₙ(B ∘L T ∘L A)` over contractions `A` from `ℓ²(ℕ, 𝕜)` and `B`
into `ℓ²(ℕ, 𝕜)`. -/
theorem hilbertNumber_def (T : E →L[𝕜] F) (n : ℕ) :
    T.hilbertNumber n =
      ⨆ (A : {A : ℓ²(ℕ, 𝕜) →L[𝕜] E // ‖A‖ ≤ 1}) (B : {B : F →L[𝕜] ℓ²(ℕ, 𝕜) // ‖B‖ ≤ 1}),
        (B.1 ∘L T ∘L A.1).singularValue n := (rfl)

private theorem singularValue_comp_comp_le_of_norm_le_one (T : E →L[𝕜] F) (n : ℕ)
    {A : ℓ²(ℕ, 𝕜) →L[𝕜] E} {B : F →L[𝕜] ℓ²(ℕ, 𝕜)} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) :
    (B ∘L T ∘L A).singularValue n ≤ T.singularValue n :=
  calc (B ∘L T ∘L A).singularValue n
      ≤ ‖B‖₊ * T.singularValue n * ‖A‖₊ := B.singularValue_comp_comp_le T A n
    _ ≤ 1 * T.singularValue n * 1 := by
        gcongr
        · exact_mod_cast hB
        · exact_mod_cast hA
    _ = T.singularValue n := by rw [one_mul, mul_one]

/-- Every Hilbert number is bounded above by the corresponding approximation number. -/
theorem hilbertNumber_le_singularValue (T : E →L[𝕜] F) (n : ℕ) :
    T.hilbertNumber n ≤ T.singularValue n :=
  ciSup_le' fun A ↦ ciSup_le' fun B ↦ singularValue_comp_comp_le_of_norm_le_one T n A.2 B.2

/-- **Contractive lower bound.** Every pair of contractions `A : ℓ²(ℕ, 𝕜) →L[𝕜] E` and
`B : F →L[𝕜] ℓ²(ℕ, 𝕜)` bounds `hₙ(T)` from below by `aₙ(B ∘L T ∘L A)`. -/
theorem le_hilbertNumber (T : E →L[𝕜] F) (n : ℕ)
    {A : ℓ²(ℕ, 𝕜) →L[𝕜] E} {B : F →L[𝕜] ℓ²(ℕ, 𝕜)} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) :
    (B ∘L T ∘L A).singularValue n ≤ T.hilbertNumber n := by
  have hbddB : BddAbove (Set.range fun B : {B : F →L[𝕜] ℓ²(ℕ, 𝕜) // ‖B‖ ≤ 1} ↦
      (B.1 ∘L T ∘L A).singularValue n) :=
    ⟨T.singularValue n, Set.forall_mem_range.mpr fun B' ↦
      singularValue_comp_comp_le_of_norm_le_one T n hA B'.2⟩
  have hbddA : BddAbove (Set.range fun A' : {A : ℓ²(ℕ, 𝕜) →L[𝕜] E // ‖A‖ ≤ 1} ↦
      ⨆ B : {B : F →L[𝕜] ℓ²(ℕ, 𝕜) // ‖B‖ ≤ 1}, (B.1 ∘L T ∘L A'.1).singularValue n) :=
    ⟨T.singularValue n, Set.forall_mem_range.mpr fun A' ↦
      ciSup_le' fun B' ↦ singularValue_comp_comp_le_of_norm_le_one T n A'.2 B'.2⟩
  exact (le_ciSup hbddB ⟨B, hB⟩).trans (le_ciSup hbddA ⟨A, hA⟩)

/-- **Upper-bound characterization.** `hₙ(T) ≤ c` exactly when `aₙ(B ∘L T ∘L A) ≤ c` for all
contractions `A : ℓ²(ℕ, 𝕜) →L[𝕜] E` and `B : F →L[𝕜] ℓ²(ℕ, 𝕜)`. -/
theorem hilbertNumber_le_iff {T : E →L[𝕜] F} {n : ℕ} {c : ℝ≥0} :
    T.hilbertNumber n ≤ c ↔ ∀ (A : ℓ²(ℕ, 𝕜) →L[𝕜] E) (B : F →L[𝕜] ℓ²(ℕ, 𝕜)),
      ‖A‖ ≤ 1 → ‖B‖ ≤ 1 → (B ∘L T ∘L A).singularValue n ≤ c :=
  ⟨fun h _ _ hA hB ↦ (T.le_hilbertNumber n hA hB).trans h,
    fun h ↦ ciSup_le' fun A ↦ ciSup_le' fun B ↦ h A.1 B.1 A.2 B.2⟩

/-- **Supremum formula.** `hₙ(T)` is the least upper bound of `aₙ(B ∘L T ∘L A)` as `A` and `B`
range over contractions from and into `ℓ²(ℕ, 𝕜)`. -/
theorem isLUB_hilbertNumber (T : E →L[𝕜] F) (n : ℕ) :
    IsLUB {c : ℝ≥0 | ∃ (A : ℓ²(ℕ, 𝕜) →L[𝕜] E) (B : F →L[𝕜] ℓ²(ℕ, 𝕜)),
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧ (B ∘L T ∘L A).singularValue n = c} (T.hilbertNumber n) := by
  refine ⟨?_, fun c hc ↦ hilbertNumber_le_iff.mpr fun A B hA hB ↦ hc ⟨A, B, hA, hB, rfl⟩⟩
  rintro _ ⟨A, B, hA, hB, rfl⟩
  exact T.le_hilbertNumber n hA hB

/-- **Near-optimal test operators.** If `c < hₙ(T)`, some contractions `A : ℓ²(ℕ, 𝕜) →L[𝕜] E` and
`B : F →L[𝕜] ℓ²(ℕ, 𝕜)` satisfy `c < aₙ(B ∘L T ∘L A)`. -/
theorem exists_lt_singularValue_comp_comp_of_lt_hilbertNumber {T : E →L[𝕜] F} {n : ℕ} {c : ℝ≥0}
    (h : c < T.hilbertNumber n) :
    ∃ (A : ℓ²(ℕ, 𝕜) →L[𝕜] E) (B : F →L[𝕜] ℓ²(ℕ, 𝕜)),
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧ c < (B ∘L T ∘L A).singularValue n := by
  obtain ⟨A, B, hA, hB, hlt⟩ : ∃ (A : ℓ²(ℕ, 𝕜) →L[𝕜] E) (B : F →L[𝕜] ℓ²(ℕ, 𝕜)),
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧ ¬ (B ∘L T ∘L A).singularValue n ≤ c := by
    simpa [not_forall] using mt hilbertNumber_le_iff.mpr h.not_ge
  exact ⟨A, B, hA, hB, lt_of_not_ge hlt⟩

/-- **Arbitrary Hilbert test spaces.** If `H₁` is a complete inner product space and `H₂` is an
inner product space, any contractions `A : H₁ →L[𝕜] E` and `B : F →L[𝕜] H₂` bound `hₙ(T)` from
below by `aₙ(B ∘L T ∘L A)`. -/
theorem le_hilbertNumber_of_innerProductSpace {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
    (T : E →L[𝕜] F) (n : ℕ) {A : H₁ →L[𝕜] E} {B : F →L[𝕜] H₂}
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) :
    (B ∘L T ∘L A).singularValue n ≤ T.hilbertNumber n := by
  by_contra! hlt
  have hlt' : (T.hilbertNumber n : ℝ) < (B ∘L T ∘L A).singularValue n := mod_cast hlt
  set c : ℝ := ((T.hilbertNumber n : ℝ) + (B ∘L T ∘L A).singularValue n) / 2 with hc_def
  have hc₀ : 0 ≤ c := by positivity
  have hc₁ : (T.hilbertNumber n : ℝ) < c := by rw [hc_def]; linarith
  have hc₂ : c < (B ∘L T ∘L A).singularValue n := by rw [hc_def]; linarith
  obtain ⟨A₀, B₀, hA₀, hB₀, hBTA⟩ := (B ∘L T ∘L A).exists_comp_comp_eq_smul_id hc₀ hc₂
  -- Factor `EuclideanSpace 𝕜 (Fin (n + 1))` through the first `n + 1` coordinates of `ℓ²(ℕ, 𝕜)`.
  let b : HilbertBasis ℕ 𝕜 ℓ²(ℕ, 𝕜) := HilbertBasis.ofRepr (LinearIsometryEquiv.refl 𝕜 ℓ²(ℕ, 𝕜))
  let J : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] ℓ²(ℕ, 𝕜) :=
    (b.finiteInclusion n).toContinuousLinearMap
  let P : ℓ²(ℕ, 𝕜) →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)) := b.coordinateCutoff n
  have hJ : ‖J‖ ≤ 1 := (b.finiteInclusion n).norm_toContinuousLinearMap_le
  have hP : ‖P‖ ≤ 1 := b.norm_coordinateCutoff_le n
  let A₁ : ℓ²(ℕ, 𝕜) →L[𝕜] E := A ∘L A₀ ∘L P
  let B₁ : F →L[𝕜] ℓ²(ℕ, 𝕜) := J ∘L B₀ ∘L B
  have hA₁ : ‖A₁‖ ≤ 1 :=
    calc ‖A₁‖ ≤ ‖A‖ * (‖A₀‖ * ‖P‖) :=
          (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left (opNorm_comp_le _ _)
            (norm_nonneg _))
      _ ≤ 1 * (1 * 1) := by gcongr
      _ = 1 := by simp
  have hB₁ : ‖B₁‖ ≤ 1 :=
    calc ‖B₁‖ ≤ ‖J‖ * (‖B₀‖ * ‖B‖) :=
          (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left (opNorm_comp_le _ _)
            (norm_nonneg _))
      _ ≤ 1 * (1 * 1) := by gcongr
      _ = 1 := by simp
  have hPJ : P ∘L (B₁ ∘L T ∘L A₁) ∘L J =
      (c : 𝕜) • ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) := by
    rw [← hBTA]
    ext x
    simp [A₁, B₁, J, P]
  have hid :
      (ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1)))).singularValue n = 1 := by
    simpa using (TauCeti.SNumbers.isSNumberSequence_approximation (𝕜 := 𝕜)).normalize n
  have hle : ‖(c : 𝕜)‖₊ ≤ T.hilbertNumber n :=
    calc ‖(c : 𝕜)‖₊
        = ((c : 𝕜) • ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1)))).singularValue n :=
          by rw [singularValue_smul, hid, mul_one]
      _ = (P ∘L (B₁ ∘L T ∘L A₁) ∘L J).singularValue n := by rw [hPJ]
      _ ≤ ‖P‖₊ * (B₁ ∘L T ∘L A₁).singularValue n * ‖J‖₊ :=
          P.singularValue_comp_comp_le (B₁ ∘L T ∘L A₁) J n
      _ ≤ 1 * (B₁ ∘L T ∘L A₁).singularValue n * 1 := by
          gcongr
          · exact_mod_cast hP
          · exact_mod_cast hJ
      _ = (B₁ ∘L T ∘L A₁).singularValue n := by rw [one_mul, mul_one]
      _ ≤ T.hilbertNumber n := T.le_hilbertNumber n hA₁ hB₁
  have hle' : c ≤ T.hilbertNumber n := by
    simpa [coe_nnNorm, RCLike.norm_ofReal, abs_of_nonneg hc₀] using NNReal.coe_le_coe.mpr hle
  exact hc₁.not_ge hle'

/-- **Homogeneous bound on arbitrary Hilbert test spaces.** If `H₁` is a complete inner product
space and `H₂` is an inner product space, any bounded `A : H₁ →L[𝕜] E` and `B : F →L[𝕜] H₂`
satisfy `aₙ(B ∘L T ∘L A) ≤ ‖B‖ hₙ(T) ‖A‖`. -/
theorem singularValue_comp_comp_le_mul_hilbertNumber_of_innerProductSpace {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
    (T : E →L[𝕜] F) (A : H₁ →L[𝕜] E) (B : F →L[𝕜] H₂) (n : ℕ) :
    (B ∘L T ∘L A).singularValue n ≤ ‖B‖₊ * T.hilbertNumber n * ‖A‖₊ := by
  rcases eq_or_ne ‖A‖₊ 0 with hA0 | hA0
  · refine ((B ∘L T ∘L A).singularValue_le_nnnorm n).trans ?_
    have hnorm : ‖B ∘L T ∘L A‖₊ ≤ ‖B‖₊ * (‖T‖₊ * ‖A‖₊) :=
      (opNNNorm_comp_le _ _).trans (mul_le_mul_right (opNNNorm_comp_le _ _) _)
    simpa [hA0] using hnorm
  rcases eq_or_ne ‖B‖₊ 0 with hB0 | hB0
  · refine ((B ∘L T ∘L A).singularValue_le_nnnorm n).trans ?_
    have hnorm : ‖B ∘L T ∘L A‖₊ ≤ ‖B‖₊ * ‖T ∘L A‖₊ := opNNNorm_comp_le _ _
    simpa [hB0] using hnorm
  have hApos : 0 < ‖A‖ := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hA0)
  have hBpos : 0 < ‖B‖ := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hB0)
  let A' : H₁ →L[𝕜] E := (‖A‖ : 𝕜)⁻¹ • A
  let B' : F →L[𝕜] H₂ := (‖B‖ : 𝕜)⁻¹ • B
  have hA' : ‖A'‖ ≤ 1 := by
    rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos hApos, inv_mul_cancel₀ hApos.ne']
  have hB' : ‖B'‖ ≤ 1 := by
    rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos hBpos, inv_mul_cancel₀ hBpos.ne']
  have hcomp : B' ∘L T ∘L A' = (‖B‖ : 𝕜)⁻¹ • (‖A‖ : 𝕜)⁻¹ • (B ∘L T ∘L A) := by
    dsimp [A', B']
    rw [comp_smul, comp_smul]
  have hle := T.le_hilbertNumber_of_innerProductSpace n hA' hB'
  rw [hcomp, singularValue_smul, singularValue_smul] at hle
  have hnormA : ‖(‖A‖ : 𝕜)⁻¹‖₊ = ‖A‖₊⁻¹ := by ext; simp
  have hnormB : ‖(‖B‖ : 𝕜)⁻¹‖₊ = ‖B‖₊⁻¹ := by ext; simp
  rw [hnormA, hnormB, inv_mul_le_iff₀ (pos_iff_ne_zero.mpr hB0),
    inv_mul_le_iff₀ (pos_iff_ne_zero.mpr hA0)] at hle
  calc (B ∘L T ∘L A).singularValue n ≤ ‖A‖₊ * (‖B‖₊ * T.hilbertNumber n) := hle
    _ = ‖B‖₊ * T.hilbertNumber n * ‖A‖₊ := by ring

/-- **Homogeneous test-operator bound on `ℓ²(ℕ, 𝕜)`.** For arbitrary bounded `A : ℓ²(ℕ, 𝕜) →L[𝕜] E`
and `B : F →L[𝕜] ℓ²(ℕ, 𝕜)`, `aₙ(B ∘L T ∘L A) ≤ ‖B‖ hₙ(T) ‖A‖`. -/
theorem singularValue_comp_comp_le_mul_hilbertNumber (T : E →L[𝕜] F)
    (A : ℓ²(ℕ, 𝕜) →L[𝕜] E) (B : F →L[𝕜] ℓ²(ℕ, 𝕜)) (n : ℕ) :
    (B ∘L T ∘L A).singularValue n ≤ ‖B‖₊ * T.hilbertNumber n * ‖A‖₊ :=
  T.singularValue_comp_comp_le_mul_hilbertNumber_of_innerProductSpace A B n

private theorem singularValue_comp_comp_div_le_hilbertNumber (T : E →L[𝕜] F)
    (A : ℓ²(ℕ, 𝕜) →L[𝕜] E) (B : F →L[𝕜] ℓ²(ℕ, 𝕜)) (n : ℕ) :
    (B ∘L T ∘L A).singularValue n / (‖B‖₊ * ‖A‖₊) ≤ T.hilbertNumber n := by
  rcases eq_or_ne (‖B‖₊ * ‖A‖₊) 0 with h0 | h0
  · simp [h0]
  · rw [div_le_iff₀ (pos_iff_ne_zero.mpr h0)]
    exact (T.singularValue_comp_comp_le_mul_hilbertNumber A B n).trans_eq (by ring)

/-- **Ratio formula over nonzero test operators.** `hₙ(T)` is the supremum of
`aₙ(B ∘L T ∘L A) / (‖B‖ ‖A‖)` over nonzero `A : ℓ²(ℕ, 𝕜) →L[𝕜] E` and `B : F →L[𝕜] ℓ²(ℕ, 𝕜)`. -/
theorem hilbertNumber_eq_iSup_ne_zero_div (T : E →L[𝕜] F) (n : ℕ) :
    T.hilbertNumber n =
      ⨆ (A : {A : ℓ²(ℕ, 𝕜) →L[𝕜] E // A ≠ 0}) (B : {B : F →L[𝕜] ℓ²(ℕ, 𝕜) // B ≠ 0}),
        (B.1 ∘L T ∘L A.1).singularValue n / (‖B.1‖₊ * ‖A.1‖₊) := by
  refine le_antisymm (hilbertNumber_le_iff.mpr fun A B hA hB ↦ ?_)
    (ciSup_le' fun A ↦ ciSup_le' fun B ↦ T.singularValue_comp_comp_div_le_hilbertNumber A.1 B.1 n)
  rcases eq_or_ne ((B ∘L T ∘L A).singularValue n) 0 with h0 | h0
  · simp [h0]
  have hBTA : B ∘L T ∘L A ≠ 0 := by rintro h; exact h0 (by simp [h])
  have hAne : A ≠ 0 := by rintro rfl; exact hBTA (by simp)
  have hBne : B ≠ 0 := by rintro rfl; exact hBTA (by simp)
  have hBA_le : ‖B‖₊ * ‖A‖₊ ≤ 1 := by
    simpa using mul_le_mul' (show ‖B‖₊ ≤ 1 from mod_cast hB) (show ‖A‖₊ ≤ 1 from mod_cast hA)
  have hBA_pos : 0 < ‖B‖₊ * ‖A‖₊ := by
    by_contra! hle
    have hmul0 : ‖B‖₊ * ‖A‖₊ = 0 := nonpos_iff_eq_zero.mp hle
    have hnorm : ‖B ∘L T ∘L A‖₊ ≤ ‖T‖₊ * (‖B‖₊ * ‖A‖₊) :=
      ((opNNNorm_comp_le _ _).trans (mul_le_mul_right (opNNNorm_comp_le _ _) _)).trans_eq (by ring)
    exact h0 (le_antisymm (((B ∘L T ∘L A).singularValue_le_nnnorm n).trans
      (by simpa [hmul0] using hnorm)) bot_le)
  have hbddB : BddAbove (Set.range fun B' : {B : F →L[𝕜] ℓ²(ℕ, 𝕜) // B ≠ 0} ↦
      (B'.1 ∘L T ∘L A).singularValue n / (‖B'.1‖₊ * ‖A‖₊)) :=
    ⟨T.hilbertNumber n, Set.forall_mem_range.mpr fun B' ↦
      T.singularValue_comp_comp_div_le_hilbertNumber A B'.1 n⟩
  have hbddA : BddAbove (Set.range fun A' : {A : ℓ²(ℕ, 𝕜) →L[𝕜] E // A ≠ 0} ↦
      ⨆ B' : {B : F →L[𝕜] ℓ²(ℕ, 𝕜) // B ≠ 0},
        (B'.1 ∘L T ∘L A'.1).singularValue n / (‖B'.1‖₊ * ‖A'.1‖₊)) :=
    ⟨T.hilbertNumber n, Set.forall_mem_range.mpr fun A' ↦
      ciSup_le' fun B' ↦ T.singularValue_comp_comp_div_le_hilbertNumber A'.1 B'.1 n⟩
  refine (le_div_iff₀ hBA_pos |>.mpr (mul_le_of_le_one_right' hBA_le)).trans ?_
  exact (le_ciSup hbddB ⟨B, hBne⟩).trans (le_ciSup hbddA ⟨A, hAne⟩)

/-- **Unrestricted ratio formula.** Since division by zero in `ℝ≥0` evaluates to `0`, `hₙ(T)` is
also the supremum of `aₙ(B ∘L T ∘L A) / (‖B‖ ‖A‖)` over all bounded `A` and `B`. -/
theorem hilbertNumber_eq_iSup_div (T : E →L[𝕜] F) (n : ℕ) :
    T.hilbertNumber n =
      ⨆ (A : ℓ²(ℕ, 𝕜) →L[𝕜] E) (B : F →L[𝕜] ℓ²(ℕ, 𝕜)),
        (B ∘L T ∘L A).singularValue n / (‖B‖₊ * ‖A‖₊) := by
  refine le_antisymm ?_
    (ciSup_le' fun A ↦ ciSup_le' fun B ↦ T.singularValue_comp_comp_div_le_hilbertNumber A B n)
  rw [T.hilbertNumber_eq_iSup_ne_zero_div n]
  refine ciSup_le' fun A ↦ ciSup_le' fun B ↦ ?_
  have hbddB : BddAbove (Set.range fun B' : F →L[𝕜] ℓ²(ℕ, 𝕜) ↦
      (B' ∘L T ∘L A.1).singularValue n / (‖B'‖₊ * ‖A.1‖₊)) :=
    ⟨T.hilbertNumber n, Set.forall_mem_range.mpr fun B' ↦
      T.singularValue_comp_comp_div_le_hilbertNumber A.1 B' n⟩
  have hbddA : BddAbove (Set.range fun A' : ℓ²(ℕ, 𝕜) →L[𝕜] E ↦
      ⨆ B' : F →L[𝕜] ℓ²(ℕ, 𝕜), (B' ∘L T ∘L A').singularValue n / (‖B'‖₊ * ‖A'‖₊)) :=
    ⟨T.hilbertNumber n, Set.forall_mem_range.mpr fun A' ↦
      ciSup_le' fun B' ↦ T.singularValue_comp_comp_div_le_hilbertNumber A' B' n⟩
  exact (le_ciSup hbddB B.1).trans (le_ciSup hbddA A.1)

/-- **Hilbert numbers on Hilbert spaces.** On bounded operators from a complete inner product space
into an inner product space, the Hilbert numbers equal the approximation numbers. -/
theorem hilbertNumber_eq_singularValue {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
    (T : H₁ →L[𝕜] H₂) (n : ℕ) : T.hilbertNumber n = T.singularValue n :=
  (T.hilbertNumber_le_singularValue n).antisymm <| by
    simpa using T.le_hilbertNumber_of_innerProductSpace n
      (A := ContinuousLinearMap.id 𝕜 H₁) (B := ContinuousLinearMap.id 𝕜 H₂) norm_id_le norm_id_le

/-- **Hilbert numbers in finite dimension.** Between finite-dimensional inner product spaces, the
Hilbert numbers agree with `LinearMap.singularValues`. -/
theorem hilbertNumber_eq_linearMap_singularValues {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [FiniteDimensional 𝕜 H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [FiniteDimensional 𝕜 H₂]
    (T : H₁ →L[𝕜] H₂) (n : ℕ) :
    (T.hilbertNumber n : ℝ) = (T : H₁ →ₗ[𝕜] H₂).singularValues n := by
  have : CompleteSpace H₁ := FiniteDimensional.completeSpace 𝕜 H₁
  rw [T.hilbertNumber_eq_singularValue, T.singularValue_eq_linearMap_singularValues]

/-- Every Hilbert number is bounded by the operator norm. -/
theorem hilbertNumber_le_nnnorm (T : E →L[𝕜] F) (n : ℕ) : T.hilbertNumber n ≤ ‖T‖₊ :=
  (T.hilbertNumber_le_singularValue n).trans (T.singularValue_le_nnnorm n)

/-- The Hilbert numbers of the zero operator vanish. -/
@[simp]
theorem zero_hilbertNumber (n : ℕ) : (0 : E →L[𝕜] F).hilbertNumber n = 0 :=
  le_antisymm (by simpa using (0 : E →L[𝕜] F).hilbertNumber_le_nnnorm n) bot_le

/-- **Zeroth Hilbert number.** `h₀(T) = ‖T‖`, testing `T` on the one-dimensional Hilbert space `𝕜`
via `toSpanSingleton` and a norming Hahn–Banach functional. -/
@[simp]
theorem hilbertNumber_zero (T : E →L[𝕜] F) : T.hilbertNumber 0 = ‖T‖₊ := by
  refine (T.hilbertNumber_le_nnnorm 0).antisymm (T.opNNNorm_le_bound _ fun x ↦ ?_)
  obtain ⟨φ, hφ_norm, hφ_apply⟩ := exists_dual_vector'' 𝕜 (T x)
  let L : 𝕜 →L[𝕜] 𝕜 := φ ∘L T ∘L toSpanSingleton 𝕜 x
  have hL1 : L 1 = (‖T x‖ : 𝕜) := by simp [L, hφ_apply]
  calc ‖T x‖₊ = ‖L 1‖₊ := by ext; simp [hL1]
    _ ≤ ‖L‖₊ * ‖(1 : 𝕜)‖₊ := L.le_opNNNorm 1
    _ = L.singularValue 0 := by simp
    _ ≤ ‖φ‖₊ * T.hilbertNumber 0 * ‖toSpanSingleton 𝕜 x‖₊ :=
        T.singularValue_comp_comp_le_mul_hilbertNumber_of_innerProductSpace
          (toSpanSingleton 𝕜 x) φ 0
    _ ≤ 1 * T.hilbertNumber 0 * ‖x‖₊ := by
        gcongr
        · exact_mod_cast hφ_norm
        · exact le_of_eq (by ext; simp)
    _ = T.hilbertNumber 0 * ‖x‖₊ := by rw [one_mul]

/-- The Hilbert numbers form an antitone sequence. -/
theorem antitone_hilbertNumber (T : E →L[𝕜] F) : Antitone T.hilbertNumber :=
  fun _ _ hmn ↦ hilbertNumber_le_iff.mpr fun A B hA hB ↦
    ((B ∘L T ∘L A).antitone_singularValue hmn).trans (T.le_hilbertNumber _ hA hB)

/-- The Hilbert numbers of `T` are bounded above by `‖T‖`. -/
theorem bddAbove_range_hilbertNumber (T : E →L[𝕜] F) : BddAbove (Set.range T.hilbertNumber) :=
  ⟨‖T‖₊, Set.forall_mem_range.mpr T.hilbertNumber_le_nnnorm⟩

/-- The supremum of the Hilbert numbers is the operator norm, attained at `h₀(T)`. -/
@[simp]
theorem iSup_hilbertNumber (T : E →L[𝕜] F) : ⨆ n, T.hilbertNumber n = ‖T‖₊ :=
  (ciSup_le T.hilbertNumber_le_nnnorm).antisymm
    (T.hilbertNumber_zero ▸ le_ciSup T.bddAbove_range_hilbertNumber 0)

/-- **Vanishing from rank.** A bounded map of rank at most `n` has `hₙ(T) = 0`. -/
theorem hilbertNumber_eq_zero_of_rank_le {T : E →L[𝕜] F} {n : ℕ} (hT : T.rank ≤ n) :
    T.hilbertNumber n = 0 :=
  le_antisymm ((T.hilbertNumber_le_singularValue n).trans
    (singularValue_eq_zero_of_rank_le hT).le) bot_le

/-- **Dimension cutoff.** If the source has rank at most `n`, then `hₙ(T) = 0`. -/
theorem hilbertNumber_eq_zero_of_rank_domain_le (T : E →L[𝕜] F) {n : ℕ}
    (hE : Module.rank 𝕜 E ≤ n) : T.hilbertNumber n = 0 :=
  le_antisymm ((T.hilbertNumber_le_singularValue n).trans
    (T.singularValue_eq_zero_of_rank_domain_le hE).le) bot_le

/-- **Mixed-index additive inequality.** `h_{m+n}(S + T) ≤ hₘ(S) + hₙ(T)`. -/
theorem hilbertNumber_add_index_le (S T : E →L[𝕜] F) (m n : ℕ) :
    (S + T).hilbertNumber (m + n) ≤ S.hilbertNumber m + T.hilbertNumber n :=
  hilbertNumber_le_iff.mpr fun A B hA hB ↦ by
    have hcomp : B ∘L (S + T) ∘L A = B ∘L S ∘L A + B ∘L T ∘L A := by
      simp [add_comp, comp_add]
    rw [hcomp]
    exact ((B ∘L S ∘L A).singularValue_add_index_le (B ∘L T ∘L A) m n).trans
      (add_le_add (S.le_hilbertNumber m hA hB) (T.le_hilbertNumber n hA hB))

/-- **Perturbative triangle bound.** `hₙ(S + T) ≤ hₙ(S) + ‖T‖`. -/
theorem hilbertNumber_add_le (S T : E →L[𝕜] F) (n : ℕ) :
    (S + T).hilbertNumber n ≤ S.hilbertNumber n + ‖T‖₊ := by
  simpa using S.hilbertNumber_add_index_le T n 0

/-- **Lipschitz bound at a fixed index.** `|hₙ(S) - hₙ(T)| ≤ ‖S - T‖`. -/
theorem abs_hilbertNumber_sub_hilbertNumber_le (S T : E →L[𝕜] F) (n : ℕ) :
    |(S.hilbertNumber n : ℝ) - T.hilbertNumber n| ≤ ‖S - T‖ := by
  have key (S T : E →L[𝕜] F) : (S.hilbertNumber n : ℝ) ≤ T.hilbertNumber n + ‖S - T‖ := by
    have h := T.hilbertNumber_add_le (S - T) n
    rw [add_sub_cancel] at h
    exact_mod_cast h
  rw [abs_sub_le_iff]
  exact ⟨sub_le_iff_le_add'.mpr (key S T), sub_le_iff_le_add'.mpr (norm_sub_rev T S ▸ key T S)⟩

/-- **Lipschitz continuity.** At each index, `T ↦ hₙ(T)` is `1`-Lipschitz in operator norm. -/
theorem lipschitzWith_hilbertNumber (n : ℕ) :
    LipschitzWith 1 fun T : E →L[𝕜] F ↦ T.hilbertNumber n :=
  LipschitzWith.of_dist_le_mul fun S T ↦ by
    simpa [NNReal.dist_eq, dist_eq_norm] using abs_hilbertNumber_sub_hilbertNumber_le S T n

/-- **Norm continuity.** At each index, `T ↦ hₙ(T)` is continuous in operator norm. -/
@[fun_prop]
theorem continuous_hilbertNumber (n : ℕ) : Continuous fun T : E →L[𝕜] F ↦ T.hilbertNumber n :=
  (lipschitzWith_hilbertNumber n).continuous

/-- **Two-sided ideal inequality.** `hₙ(B ∘L T ∘L A) ≤ ‖B‖ hₙ(T) ‖A‖`. -/
theorem hilbertNumber_comp_comp_le (B : F →L[𝕜] G) (T : E →L[𝕜] F) (A : W →L[𝕜] E) (n : ℕ) :
    (B ∘L T ∘L A).hilbertNumber n ≤ ‖B‖₊ * T.hilbertNumber n * ‖A‖₊ :=
  hilbertNumber_le_iff.mpr fun A₀ B₀ hA₀ hB₀ ↦ by
    have hassoc : B₀ ∘L (B ∘L T ∘L A) ∘L A₀ = (B₀ ∘L B) ∘L T ∘L (A ∘L A₀) := by
      simp [comp_assoc]
    rw [hassoc]
    refine (T.singularValue_comp_comp_le_mul_hilbertNumber (A ∘L A₀) (B₀ ∘L B) n).trans ?_
    have hB' : ‖B₀ ∘L B‖₊ ≤ ‖B‖₊ :=
      (opNNNorm_comp_le _ _).trans (mul_le_of_le_one_left' (mod_cast hB₀))
    have hA' : ‖A ∘L A₀‖₊ ≤ ‖A‖₊ :=
      (opNNNorm_comp_le _ _).trans (mul_le_of_le_one_right' (mod_cast hA₀))
    gcongr

/-- Postcomposition with a bounded map scales Hilbert numbers by at most its norm. -/
theorem hilbertNumber_comp_le_left (B : F →L[𝕜] G) (T : E →L[𝕜] F) (n : ℕ) :
    (B ∘L T).hilbertNumber n ≤ ‖B‖₊ * T.hilbertNumber n := by
  have hid : ‖ContinuousLinearMap.id 𝕜 E‖₊ ≤ 1 := mod_cast norm_id_le
  calc (B ∘L T).hilbertNumber n
      ≤ ‖B‖₊ * T.hilbertNumber n * ‖ContinuousLinearMap.id 𝕜 E‖₊ := by
        simpa using B.hilbertNumber_comp_comp_le T (ContinuousLinearMap.id 𝕜 E) n
    _ ≤ ‖B‖₊ * T.hilbertNumber n := mul_le_of_le_one_right' hid

/-- Precomposition with a bounded map scales Hilbert numbers by at most its norm. -/
theorem hilbertNumber_comp_le_right (T : E →L[𝕜] F) (A : W →L[𝕜] E) (n : ℕ) :
    (T ∘L A).hilbertNumber n ≤ T.hilbertNumber n * ‖A‖₊ := by
  have hid : ‖ContinuousLinearMap.id 𝕜 F‖₊ ≤ 1 := mod_cast norm_id_le
  calc (T ∘L A).hilbertNumber n
      ≤ ‖ContinuousLinearMap.id 𝕜 F‖₊ * T.hilbertNumber n * ‖A‖₊ := by
        simpa using (ContinuousLinearMap.id 𝕜 F).hilbertNumber_comp_comp_le T A n
    _ ≤ T.hilbertNumber n * ‖A‖₊ := by gcongr; exact mul_le_of_le_one_left' hid

/-- **Scalar homogeneity.** `hₙ(c • T) = ‖c‖ hₙ(T)`. -/
@[simp]
theorem hilbertNumber_smul (c : 𝕜) (T : E →L[𝕜] F) (n : ℕ) :
    (c • T).hilbertNumber n = ‖c‖₊ * T.hilbertNumber n := by
  rw [hilbertNumber_def, hilbertNumber_def]
  simp_rw [smul_comp, comp_smul, singularValue_smul, ← NNReal.mul_iSup]

/-- Negation leaves the Hilbert numbers unchanged. -/
@[simp]
theorem hilbertNumber_neg (T : E →L[𝕜] F) (n : ℕ) : (-T).hilbertNumber n = T.hilbertNumber n := by
  simpa using T.hilbertNumber_smul (-1) n

/-- **Hilbert numbers of the identity on a Hilbert space.** On a complete inner product space `H`
of rank `r`, `hₙ(id_H) = 1` for `n < r` and `hₙ(id_H) = 0` for `r ≤ n`. -/
theorem hilbertNumber_id_of_innerProductSpace {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H] (n : ℕ) :
    (ContinuousLinearMap.id 𝕜 H).hilbertNumber n =
      if (n : Cardinal) < Module.rank 𝕜 H then 1 else 0 := by
  rw [hilbertNumber_eq_singularValue, singularValue_id]

/-- **Euclidean normalization.** `hₙ(id_{ℓ₂^{n+1}}) = 1`. -/
@[simp]
theorem hilbertNumber_id_euclidean (n : ℕ) :
    (ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1)))).hilbertNumber n = 1 := by
  simpa [hilbertNumber_eq_singularValue] using
    (TauCeti.SNumbers.isSNumberSequence_approximation (𝕜 := 𝕜)).normalize n

end ContinuousLinearMap

universe u

namespace TauCeti.SNumbers

variable {𝕜 : Type u} [RCLike 𝕜]

/-- The family of Hilbert numbers on all normed spaces over `𝕜`. -/
noncomputable def hilbert : SNumberFamily 𝕜 :=
  fun T ↦ T.hilbertNumber

/-- Evaluation of the Hilbert family is the Hilbert number. -/
@[simp]
theorem hilbert_apply {X Y : Type u}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (T : X →L[𝕜] Y) (n : ℕ) : hilbert T n = T.hilbertNumber n := (rfl)

/-- **Hilbert numbers are s-numbers.** Over `ℝ` or `ℂ`, the Hilbert numbers satisfy Pietsch's five
s-number axioms. -/
theorem isSNumberSequence_hilbert : IsSNumberSequence (hilbert (𝕜 := 𝕜)) where
  norm T := T.hilbertNumber_zero
  antitone T := T.antitone_hilbertNumber
  add_le S T n := S.hilbertNumber_add_le T n
  comp_le B T A n := B.hilbertNumber_comp_comp_le T A n
  eq_zero_of_rank_le hT := ContinuousLinearMap.hilbertNumber_eq_zero_of_rank_le hT
  normalize n := ContinuousLinearMap.hilbertNumber_id_euclidean n

/-- **Minimality of the Hilbert numbers.** Over `ℝ` or `ℂ`, the Hilbert numbers are pointwise the
smallest s-number sequence: `hₙ(T) ≤ s T n` for every s-number sequence `s`. -/
theorem IsSNumberSequence.hilbertNumber_le {s : SNumberFamily 𝕜} (hs : IsSNumberSequence s)
    {X Y : Type u}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (T : X →L[𝕜] Y) (n : ℕ) : T.hilbertNumber n ≤ s T n :=
  ContinuousLinearMap.hilbertNumber_le_iff.mpr fun A B hA hB ↦ by
    rw [← hs.eq_singularValue (B ∘L T ∘L A) n]
    calc s (B ∘L T ∘L A) n ≤ ‖B‖₊ * s T n * ‖A‖₊ := hs.comp_le B T A n
      _ ≤ 1 * s T n * 1 := by
          gcongr
          · exact_mod_cast hB
          · exact_mod_cast hA
      _ = s T n := by rw [one_mul, mul_one]

end TauCeti.SNumbers
